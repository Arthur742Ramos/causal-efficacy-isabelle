theory Source_Sharing_Spines
  imports "Causal_Efficacy_Contexts.Causal_Efficacy_Contexts"
begin

section \<open>Boolean link equations and cofinal forcing\<close>

definition gate_value where
  "gate_value g b z = (if g then b \<or> z else b \<and> z)"

definition spine_solution where
  "spine_solution l g u v \<longleftrightarrow>
    (\<forall>n. v n = gate_value (g n) (u (l n)) (v (Suc n)))"

definition cofinal_forcing :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "cofinal_forcing l g u \<longleftrightarrow> (\<forall>N. \<exists>n\<ge>N. g n = u (l n))"

definition link_step where
  "link_step l g u X = {n. gate_value (g n) (u (l n)) (Suc n \<in> X)}"

lemma gate_value_forcing:
  "gate_value g b z = (if g = b then g else z)"
  by (auto simp: gate_value_def)

lemma mono_link_step: "mono (link_step l g u)"
  by (auto simp: mono_def link_step_def gate_value_def)

lemma spine_solution_exists: "\<exists>v. spine_solution l g u v"
proof -
  have F: "link_step l g u (lfp (link_step l g u)) = lfp (link_step l g u)"
    by (rule lfp_unfold[OF mono_link_step, symmetric])
  show ?thesis
    using F by (intro exI[of _ "\<lambda>n. n \<in> lfp (link_step l g u)"])
      (auto simp: spine_solution_def link_step_def set_eq_iff)
qed

lemma spine_solutionD:
  assumes "spine_solution l g u v"
  shows "v n = gate_value (g n) (u (l n)) (v (Suc n))"
  using assms unfolding spine_solution_def by blast

lemma solutions_agree_before_force:
  assumes V: "spine_solution l g u v" and W: "spine_solution l g u w"
    and nm: "n \<le> m" and forced: "g m = u (l m)"
  shows "v n = w n"
proof (rule inc_induct[OF nm])
  show "v m = w m" using spine_solutionD[OF V, of m] spine_solutionD[OF W, of m] forced
    by (simp add: gate_value_forcing)
next
  fix k
  assume "n \<le> k" "k < m" "v (Suc k) = w (Suc k)"
  then show "v k = w k" using spine_solutionD[OF V, of k] spine_solutionD[OF W, of k] by simp
qed

lemma cofinal_forcing_unique:
  assumes "cofinal_forcing l g u"
  shows "\<exists>!v. spine_solution l g u v"
proof -
  obtain v where V: "spine_solution l g u v" using spine_solution_exists by blast
  show ?thesis
  proof (rule ex1I[of _ v])
    show "spine_solution l g u v" by (fact V)
  next
    fix w
    assume W: "spine_solution l g u w"
    show "w = v"
    proof (rule ext)
      fix n
      obtain m where "n \<le> m" "g m = u (l m)"
        using assms by (auto simp: cofinal_forcing_def)
      then show "w n = v n" by (rule solutions_agree_before_force[OF W V])
    qed
  qed
qed

fun prefix_value where
  "prefix_value l g u b 0 n = b"
| "prefix_value l g u b (Suc k) n = gate_value (g n) (u (l n))
    (prefix_value l g u b k (Suc n))"

definition tail_value where
  "tail_value l g u N b n = prefix_value l g u b (N-n) n"

lemma tail_value_solution:
  assumes tail: "\<forall>n\<ge>N. g n \<noteq> u (l n)"
  shows "spine_solution l g u (tail_value l g u N b)"
  unfolding spine_solution_def
proof
  fix n
  show "tail_value l g u N b n = gate_value (g n) (u (l n))
      (tail_value l g u N b (Suc n))"
  proof (cases "n < N")
    case True
    then have "N-n = Suc (N-Suc n)" by arith
    then show ?thesis by (simp add: tail_value_def)
  next
    case False
    then have "N \<le> n" by simp
    then show ?thesis using tail
      by (simp add: tail_value_def gate_value_forcing)
  qed
qed

theorem unique_solution_iff_cofinal_forcing:
  "(\<exists>!v. spine_solution l g u v) \<longleftrightarrow> cofinal_forcing l g u"
proof
  assume unique: "\<exists>!v. spine_solution l g u v"
  show "cofinal_forcing l g u"
  proof (rule ccontr)
    assume "\<not> cofinal_forcing l g u"
    then obtain N where tail: "\<forall>n\<ge>N. g n \<noteq> u (l n)"
      by (auto simp: cofinal_forcing_def)
    have A: "spine_solution l g u (tail_value l g u N True)"
      by (rule tail_value_solution) (fact tail)
    have B: "spine_solution l g u (tail_value l g u N False)"
      by (rule tail_value_solution) (fact tail)
    have eq: "tail_value l g u N True = tail_value l g u N False"
      using unique A B by blast
    have "tail_value l g u N True N = tail_value l g u N False N"
      by (simp only: eq)
    then show False by (simp add: tail_value_def)
  qed
next
  assume "cofinal_forcing l g u"
  then show "\<exists>!v. spine_solution l g u v" by (rule cofinal_forcing_unique)
qed

section \<open>Uniform contexts and shared-source synthesis\<close>

definition opposite_repeats :: "(nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "opposite_repeats l g \<longleftrightarrow>
    (\<forall>N. \<exists>i\<ge>N. \<exists>j\<ge>N. l i = l j \<and> g i \<noteq> g j)"

definition repeated_in_every_tail :: "(nat \<Rightarrow> 'a) \<Rightarrow> bool" where
  "repeated_in_every_tail l \<longleftrightarrow>
    (\<forall>N. \<exists>i\<ge>N. \<exists>j\<ge>N. i \<noteq> j \<and> l i = l j)"

theorem all_contexts_unique_iff_opposite_repeats:
  "(\<forall>u. \<exists>!v. spine_solution l g u v) \<longleftrightarrow> opposite_repeats l g"
proof (simp only: unique_solution_iff_cofinal_forcing, rule iffI)
  assume all: "\<forall>u. cofinal_forcing l g u"
  show "opposite_repeats l g"
  proof (rule ccontr)
    assume "\<not> opposite_repeats l g"
    then obtain N where same: "\<And>i j. N \<le> i \<Longrightarrow> N \<le> j \<Longrightarrow>
      l i = l j \<Longrightarrow> g i = g j"
      by (auto simp: opposite_repeats_def)
    let ?u = "\<lambda>b. \<exists>i\<ge>N. l i = b \<and> \<not> g i"
    have "\<And>n. N \<le> n \<Longrightarrow> ?u (l n) = (\<not> g n)"
      using same by blast
    then have "\<not> cofinal_forcing l g ?u" unfolding cofinal_forcing_def by auto
    then show False using all by blast
  qed
next
  assume rep: "opposite_repeats l g"
  show "\<forall>u. cofinal_forcing l g u"
  proof (intro allI, unfold cofinal_forcing_def, intro allI)
    fix u N
    obtain i j where Ni: "N \<le> i" and Nj: "N \<le> j"
      and lab: "l i = l j" and diff: "g i \<noteq> g j"
      using rep unfolding opposite_repeats_def by blast
    have "g i = u (l i) \<or> g j = u (l j)" using lab diff by auto
    then show "\<exists>n\<ge>N. g n = u (l n)" using Ni Nj by blast
  qed
qed

definition occurrence_gate :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> bool" where
  "occurrence_gate l n \<longleftrightarrow> even (card {i. i < n \<and> l i = l n})"

lemma consecutive_occurrences_opposite:
  assumes ij: "i < j" and lab: "l i = l j"
    and gap: "\<And>k. i < k \<Longrightarrow> k < j \<Longrightarrow> l k \<noteq> l i"
  shows "occurrence_gate l i \<noteq> occurrence_gate l j"
proof -
  have sets: "{k. k < j \<and> l k = l j} = insert i {k. k < i \<and> l k = l i}"
    using ij lab gap by (auto; metis less_linear less_trans)
  have fin: "finite {k. k < i \<and> l k = l i}"
    by (rule finite_subset[of _ "{..<i}"]) auto
  show ?thesis by (simp add: occurrence_gate_def sets fin)
qed

lemma repeated_tail_occurrence_gate:
  assumes rep: "repeated_in_every_tail l"
  shows "opposite_repeats l (occurrence_gate l)"
  unfolding opposite_repeats_def
proof
  fix N
  obtain i j where Ni: "N \<le> i" and Nj: "N \<le> j" and neq: "i \<noteq> j" and lab: "l i = l j"
    using rep unfolding repeated_in_every_tail_def by blast
  have ex: "\<exists>i\<ge>N. \<exists>j>i. l i = l j"
    using Ni Nj neq lab by (metis neq_iff)
  then obtain i j where Ni: "N \<le> i" and ij: "i < j" and lab: "l i = l j" by blast
  let ?j = "LEAST j. i < j \<and> l j = l i"
  have J: "i < ?j \<and> l ?j = l i" by (rule LeastI[of _ j]) (use ij lab in auto)
  have gap: "\<And>k. i < k \<Longrightarrow> k < ?j \<Longrightarrow> l k \<noteq> l i"
  proof -
    fix k
    assume ik: "i < k" and kj: "k < ?j"
    have "\<not> (i < k \<and> l k = l i)" by (rule not_less_Least[OF kj])
    then show "l k \<noteq> l i" using ik by blast
  qed
  have opp: "occurrence_gate l i \<noteq> occurrence_gate l ?j"
    by (rule consecutive_occurrences_opposite) (use J gap in auto)
  show "\<exists>i\<ge>N. \<exists>j\<ge>N. l i = l j \<and> occurrence_gate l i \<noteq> occurrence_gate l j"
    using Ni J opp by (intro exI[of _ i] conjI exI[of _ ?j]) auto
qed

theorem gate_synthesis_iff_repeated_sources:
  "(\<exists>g. \<forall>u. \<exists>!v. spine_solution l g u v) \<longleftrightarrow> repeated_in_every_tail l"
proof (simp only: all_contexts_unique_iff_opposite_repeats, rule iffI)
  assume "\<exists>g. opposite_repeats l g"
  then show "repeated_in_every_tail l"
    unfolding opposite_repeats_def repeated_in_every_tail_def by blast
next
  assume "repeated_in_every_tail l"
  then show "\<exists>g. opposite_repeats l g"
    using repeated_tail_occurrence_gate by blast
qed

section \<open>Embedding in the carrier-restricted mechanism semantics\<close>

datatype 'a labelled_node = SRoot 'a | SLink nat

definition labelled_dependency where
  "labelled_dependency l y x \<longleftrightarrow>
    (\<exists>n. x = SLink n \<and> (y = SRoot (l n) \<or> y = SLink (Suc n)))"

lemma labelled_parents [simp]:
  "efficacy_parents UNIV (labelled_dependency l) (SRoot b) = {}"
  "efficacy_parents UNIV (labelled_dependency l) (SLink n) = {SRoot (l n), SLink (Suc n)}"
  by (auto simp: efficacy_parents_def labelled_dependency_def)

lemma labelled_roots [simp]:
  "efficacy_roots UNIV (labelled_dependency l) = range SRoot"
  unfolding efficacy_roots_def by (rule set_eqI, case_tac x) auto

definition labelled_gate_mechanism where
  "labelled_gate_mechanism l g x S \<longleftrightarrow>
    (case x of SRoot b \<Rightarrow> True | SLink n \<Rightarrow>
      gate_value (g n) (SRoot (l n) \<in> S) (SLink (Suc n) \<in> S))"

lemma labelled_gate_admissible:
  "mechanism_on UNIV (labelled_dependency l) (labelled_gate_mechanism l g)"
  unfolding mechanism_on_def
  by (intro ballI, case_tac x)
    (auto simp: labelled_gate_mechanism_def gate_value_def mono_def)

lemma labelled_gate_relevant:
  "edge_relevant_on UNIV (labelled_dependency l) (labelled_gate_mechanism l g)"
  unfolding edge_relevant_on_def
proof (intro ballI)
  fix x y
  assume "x \<in> UNIV" and yp: "y \<in> efficacy_parents UNIV (labelled_dependency l) x"
  show "\<exists>S \<subseteq> efficacy_parents UNIV (labelled_dependency l) x - {y}.
    \<not> labelled_gate_mechanism l g x S \<and> labelled_gate_mechanism l g x (insert y S)"
  proof (cases x)
    case (SRoot b)
    then show ?thesis using yp by simp
  next
    case (SLink n)
    show ?thesis
    proof (cases "g n")
      case True
      show ?thesis using yp SLink True by (intro exI[of _ "{}"])
        (auto simp: labelled_gate_mechanism_def gate_value_def)
    next
      case False
      show ?thesis using yp SLink False
        by (intro exI[of _ "efficacy_parents UNIV (labelled_dependency l) x - {y}"])
          (auto simp: labelled_gate_mechanism_def gate_value_def)
    qed
  qed
qed

lemma two_relevant_inputs_classify:
  assumes pq: "p \<noteq> q" and zero: "\<not> f {}" and one: "f {p,q}"
    and rp: "\<exists>S\<subseteq>{p,q}-{p}. \<not> f S \<and> f (insert p S)"
    and rq: "\<exists>S\<subseteq>{p,q}-{q}. \<not> f S \<and> f (insert q S)"
  shows "f (X \<inter> {p,q}) = gate_value (f {p}) (p \<in> X) (q \<in> X)"
proof -
  have subp: "\<And>S. S \<subseteq> {p} \<Longrightarrow> S = {} \<or> S = {p}" by auto
  have subq: "\<And>S. S \<subseteq> {q} \<Longrightarrow> S = {} \<or> S = {q}" by auto
  have singles: "f {p} = f {q}"
    using rp rq pq subp subq zero one by auto
  show ?thesis
    using zero one singles pq
    by (cases "p \<in> X"; cases "q \<in> X") (auto simp: gate_value_def Int_insert_right)
qed

lemma relevant_mechanism_gate_reduction:
  assumes adm: "mechanism_on UNIV (labelled_dependency l) f"
    and rel: "edge_relevant_on UNIV (labelled_dependency l) f"
  shows "f (SLink n) (X \<inter> efficacy_parents UNIV (labelled_dependency l) (SLink n)) =
    gate_value (f (SLink n) {SRoot (l n)}) (SRoot (l n) \<in> X) (SLink (Suc n) \<in> X)"
proof -
  have loc: "mono (f (SLink n)) \<and>
    f (SLink n) {} = (efficacy_parents UNIV (labelled_dependency l) (SLink n) = {}) \<and>
    f (SLink n) (efficacy_parents UNIV (labelled_dependency l) (SLink n))"
    using adm unfolding mechanism_on_def by blast
  have zero: "\<not> f (SLink n) {}" and one: "f (SLink n) {SRoot (l n), SLink (Suc n)}"
    using loc by auto
  have reln: "\<forall>y\<in>efficacy_parents UNIV (labelled_dependency l) (SLink n).
    \<exists>S\<subseteq>efficacy_parents UNIV (labelled_dependency l) (SLink n)-{y}.
      \<not> f (SLink n) S \<and> f (SLink n) (insert y S)"
    using rel unfolding edge_relevant_on_def by blast
  have rp: "\<exists>S\<subseteq>{SRoot (l n), SLink (Suc n)}-{SRoot (l n)}.
    \<not> f (SLink n) S \<and> f (SLink n) (insert (SRoot (l n)) S)"
    using reln by auto
  have rq: "\<exists>S\<subseteq>{SRoot (l n), SLink (Suc n)}-{SLink (Suc n)}.
    \<not> f (SLink n) S \<and> f (SLink n) (insert (SLink (Suc n)) S)"
    using reln by auto
  show ?thesis using two_relevant_inputs_classify[OF _ zero one rp rq, of X] by simp
qed

definition labelled_state where
  "labelled_state u v = {x. case x of SRoot b \<Rightarrow> u b | SLink n \<Rightarrow> v n}"

lemma labelled_state_simps [simp]:
  "(SRoot b \<in> labelled_state u v) = u b"
  "(SLink n \<in> labelled_state u v) = v n"
  by (simp_all add: labelled_state_def)

lemma labelled_state_injective:
  "labelled_state u v = labelled_state u w \<longleftrightarrow> v = w"
  by (auto simp: labelled_state_def set_eq_iff fun_eq_iff split: labelled_node.splits)

lemma labelled_context_root:
  "(SRoot b \<in> contextual_step UNIV (labelled_dependency l) (labelled_gate_mechanism l g) U X)
    = (SRoot b \<in> U)"
  by (simp add: contextual_step_def source_off_step_def)

lemma labelled_context_link:
  assumes ctx: "U \<subseteq> efficacy_roots UNIV (labelled_dependency l)"
  shows "(SLink n \<in> contextual_step UNIV (labelled_dependency l) (labelled_gate_mechanism l g) U X)
    = gate_value (g n) (SRoot (l n) \<in> X) (SLink (Suc n) \<in> X)"
  using ctx by (auto simp: contextual_step_def source_off_step_def labelled_gate_mechanism_def)

lemma labelled_context_fixed_iff:
  assumes ctx: "U \<subseteq> efficacy_roots UNIV (labelled_dependency l)"
  shows "contextual_step UNIV (labelled_dependency l) (labelled_gate_mechanism l g) U X = X
    \<longleftrightarrow> (\<forall>b. (SRoot b \<in> X) = (SRoot b \<in> U)) \<and>
      spine_solution l g (\<lambda>b. SRoot b \<in> U) (\<lambda>n. SLink n \<in> X)"
proof
  assume F: "contextual_step UNIV (labelled_dependency l) (labelled_gate_mechanism l g) U X = X"
  have roots: "\<And>b. (SRoot b \<in> X) = (SRoot b \<in> U)"
    using labelled_context_root[of _ l g U X] by (simp only: F)
  have sol: "spine_solution l g (\<lambda>b. SRoot b \<in> U) (\<lambda>n. SLink n \<in> X)"
    unfolding spine_solution_def
  proof
    fix n
    have "(SLink n \<in> X) = gate_value (g n) (SRoot (l n) \<in> X) (SLink (Suc n) \<in> X)"
      using labelled_context_link[OF ctx, of n g X] by (simp only: F)
    then show "(SLink n \<in> X) = gate_value (g n) (SRoot (l n) \<in> U) (SLink (Suc n) \<in> X)"
      by (simp only: roots)
  qed
  show "(\<forall>b. (SRoot b \<in> X) = (SRoot b \<in> U)) \<and>
      spine_solution l g (\<lambda>b. SRoot b \<in> U) (\<lambda>n. SLink n \<in> X)"
    using roots sol by blast
next
  assume H: "(\<forall>b. (SRoot b \<in> X) = (SRoot b \<in> U)) \<and>
      spine_solution l g (\<lambda>b. SRoot b \<in> U) (\<lambda>n. SLink n \<in> X)"
  then have roots: "\<And>b. (SRoot b \<in> X) = (SRoot b \<in> U)" and
    sol: "spine_solution l g (\<lambda>b. SRoot b \<in> U) (\<lambda>n. SLink n \<in> X)" by blast+
  show "contextual_step UNIV (labelled_dependency l) (labelled_gate_mechanism l g) U X = X"
  proof (rule set_eqI)
    fix x
    show "(x \<in> contextual_step UNIV (labelled_dependency l) (labelled_gate_mechanism l g) U X) = (x \<in> X)"
    proof (cases x)
      case (SRoot b)
      then show ?thesis by (simp add: labelled_context_root roots)
    next
      case (SLink n)
      then show ?thesis using spine_solutionD[OF sol, of n]
        by (simp add: labelled_context_link[OF ctx] roots)
    qed
  qed
qed

lemma labelled_state_fixed_iff:
  assumes ctx: "U \<subseteq> efficacy_roots UNIV (labelled_dependency l)"
  shows "contextual_step UNIV (labelled_dependency l) (labelled_gate_mechanism l g) U
      (labelled_state (\<lambda>b. SRoot b \<in> U) v) = labelled_state (\<lambda>b. SRoot b \<in> U) v
    \<longleftrightarrow> spine_solution l g (\<lambda>b. SRoot b \<in> U) v"
  by (simp add: labelled_context_fixed_iff[OF ctx])

lemma labelled_fixed_as_state:
  assumes ctx: "U \<subseteq> efficacy_roots UNIV (labelled_dependency l)"
    and fixed: "contextual_step UNIV (labelled_dependency l) (labelled_gate_mechanism l g) U X = X"
  shows "X = labelled_state (\<lambda>b. SRoot b \<in> U) (\<lambda>n. SLink n \<in> X)"
  using fixed unfolding labelled_context_fixed_iff[OF ctx]
  by (auto simp: set_eq_iff labelled_state_def split: labelled_node.splits)

lemma labelled_unique_iff:
  assumes ctx: "U \<subseteq> efficacy_roots UNIV (labelled_dependency l)"
  shows "(\<exists>!X. contextual_step UNIV (labelled_dependency l) (labelled_gate_mechanism l g) U X = X)
    \<longleftrightarrow> (\<exists>!v. spine_solution l g (\<lambda>b. SRoot b \<in> U) v)"
proof
  assume unique: "\<exists>!X. contextual_step UNIV (labelled_dependency l) (labelled_gate_mechanism l g) U X = X"
  obtain v where V: "spine_solution l g (\<lambda>b. SRoot b \<in> U) v"
    using spine_solution_exists by blast
  show "\<exists>!v. spine_solution l g (\<lambda>b. SRoot b \<in> U) v"
  proof (rule ex1I[of _ v])
    show "spine_solution l g (\<lambda>b. SRoot b \<in> U) v" by (fact V)
  next
    fix w
    assume W: "spine_solution l g (\<lambda>b. SRoot b \<in> U) w"
    have "labelled_state (\<lambda>b. SRoot b \<in> U) w = labelled_state (\<lambda>b. SRoot b \<in> U) v"
      using unique V W labelled_state_fixed_iff[OF ctx] by blast
    then show "w = v" by (simp only: labelled_state_injective)
  qed
next
  assume unique: "\<exists>!v. spine_solution l g (\<lambda>b. SRoot b \<in> U) v"
  obtain X where F: "contextual_step UNIV (labelled_dependency l) (labelled_gate_mechanism l g) U X = X"
    using contextual_solution_exists[OF labelled_gate_admissible ctx] by blast
  show "\<exists>!X. contextual_step UNIV (labelled_dependency l) (labelled_gate_mechanism l g) U X = X"
  proof (rule ex1I[of _ X])
    show "contextual_step UNIV (labelled_dependency l) (labelled_gate_mechanism l g) U X = X" by (fact F)
  next
    fix Y
    assume G: "contextual_step UNIV (labelled_dependency l) (labelled_gate_mechanism l g) U Y = Y"
    have V: "spine_solution l g (\<lambda>b. SRoot b \<in> U) (\<lambda>n. SLink n \<in> X)"
      using F by (simp add: labelled_context_fixed_iff[OF ctx])
    have W: "spine_solution l g (\<lambda>b. SRoot b \<in> U) (\<lambda>n. SLink n \<in> Y)"
      using G by (simp add: labelled_context_fixed_iff[OF ctx])
    have eq: "(\<lambda>n. SLink n \<in> Y) = (\<lambda>n. SLink n \<in> X)" using unique V W by blast
    show "Y = X" using labelled_fixed_as_state[OF ctx G] labelled_fixed_as_state[OF ctx F] eq by simp
  qed
qed

lemma labelled_context_determinate_iff:
  fixes l :: "nat \<Rightarrow> 'a"
  shows "context_determinate UNIV (labelled_dependency l) (labelled_gate_mechanism l g)
    \<longleftrightarrow> (\<forall>u. \<exists>!v. spine_solution l g u v)"
proof
  assume det: "context_determinate UNIV (labelled_dependency l) (labelled_gate_mechanism l g)"
  show "\<forall>u. \<exists>!v. spine_solution l g u v"
  proof
    fix u :: "'a \<Rightarrow> bool"
    let ?U = "SRoot ` {b. u b}"
    have ctx: "?U \<subseteq> efficacy_roots UNIV (labelled_dependency l)" by auto
    have imp: "?U \<subseteq> efficacy_roots UNIV (labelled_dependency l) \<longrightarrow>
      (\<exists>!X. contextual_step UNIV (labelled_dependency l) (labelled_gate_mechanism l g) ?U X = X)"
      using det unfolding context_determinate_def by (rule spec)
    have ux: "\<exists>!X. contextual_step UNIV (labelled_dependency l) (labelled_gate_mechanism l g) ?U X = X"
      by (rule mp[OF imp ctx])
    have "\<exists>!v. spine_solution l g (\<lambda>b. SRoot b \<in> ?U) v"
      using ux by (simp only: labelled_unique_iff[OF ctx])
    moreover have "(\<lambda>b. SRoot b \<in> ?U) = u" by (rule ext) auto
    ultimately show "\<exists>!v. spine_solution l g u v" by simp
  qed
next
  assume all: "\<forall>u. \<exists>!v. spine_solution l g u v"
  show "context_determinate UNIV (labelled_dependency l) (labelled_gate_mechanism l g)"
    unfolding context_determinate_def
  proof (intro allI impI)
    fix U
    assume ctx: "U \<subseteq> efficacy_roots UNIV (labelled_dependency l)"
    have "\<exists>!v. spine_solution l g (\<lambda>b. SRoot b \<in> U) v" using all by (rule spec)
    then show "\<exists>!X. contextual_step UNIV (labelled_dependency l) (labelled_gate_mechanism l g) U X = X"
      by (simp only: labelled_unique_iff[OF ctx])
  qed
qed

lemma relevant_context_operator_reduction:
  assumes adm: "mechanism_on UNIV (labelled_dependency l) f"
    and rel: "edge_relevant_on UNIV (labelled_dependency l) f"
  shows "contextual_step UNIV (labelled_dependency l) f U =
    contextual_step UNIV (labelled_dependency l)
      (labelled_gate_mechanism l (\<lambda>n. f (SLink n) {SRoot (l n)})) U"
proof -
  have red: "\<And>n X. f (SLink n) (X \<inter> {SRoot (l n), SLink (Suc n)}) =
    gate_value (f (SLink n) {SRoot (l n)}) (SRoot (l n) \<in> X) (SLink (Suc n) \<in> X)"
    using relevant_mechanism_gate_reduction[OF adm rel] by simp
  show ?thesis unfolding contextual_step_def source_off_step_def
    by (rule ext, rule set_eqI, case_tac x)
      (auto simp: labelled_gate_mechanism_def red)
qed

theorem relevant_labelled_spine_synthesis_iff:
  "(\<exists>f. mechanism_on UNIV (labelled_dependency l) f \<and>
      edge_relevant_on UNIV (labelled_dependency l) f \<and>
      context_determinate UNIV (labelled_dependency l) f)
    \<longleftrightarrow> repeated_in_every_tail l"
proof
  assume "\<exists>f. mechanism_on UNIV (labelled_dependency l) f \<and>
      edge_relevant_on UNIV (labelled_dependency l) f \<and>
      context_determinate UNIV (labelled_dependency l) f"
  then obtain f where adm: "mechanism_on UNIV (labelled_dependency l) f"
    and rel: "edge_relevant_on UNIV (labelled_dependency l) f"
    and det: "context_determinate UNIV (labelled_dependency l) f" by blast
  have "context_determinate UNIV (labelled_dependency l)
      (labelled_gate_mechanism l (\<lambda>n. f (SLink n) {SRoot (l n)}))"
    using det relevant_context_operator_reduction[OF adm rel] unfolding context_determinate_def by simp
  then have all: "\<forall>u. \<exists>!v. spine_solution l (\<lambda>n. f (SLink n) {SRoot (l n)}) u v"
    by (simp add: labelled_context_determinate_iff)
  have "\<exists>g. \<forall>u. \<exists>!v. spine_solution l g u v"
    by (rule exI[of _ "\<lambda>n. f (SLink n) {SRoot (l n)}"]) (fact all)
  then show "repeated_in_every_tail l" by (simp only: gate_synthesis_iff_repeated_sources)
next
  assume rep: "repeated_in_every_tail l"
  have det: "context_determinate UNIV (labelled_dependency l)
    (labelled_gate_mechanism l (occurrence_gate l))"
    using repeated_tail_occurrence_gate[OF rep]
    by (simp add: labelled_context_determinate_iff all_contexts_unique_iff_opposite_repeats)
  show "\<exists>f. mechanism_on UNIV (labelled_dependency l) f \<and>
      edge_relevant_on UNIV (labelled_dependency l) f \<and>
      context_determinate UNIV (labelled_dependency l) f"
    by (intro exI[of _ "labelled_gate_mechanism l (occurrence_gate l)"] conjI)
      (rule labelled_gate_admissible, rule labelled_gate_relevant, fact det)
qed

lemma shared_source_repeats: "repeated_in_every_tail (\<lambda>n. b)"
  unfolding repeated_in_every_tail_def
proof
  fix N :: nat
  show "\<exists>i\<ge>N. \<exists>j\<ge>N. i \<noteq> j \<and> b = b"
    by (intro exI[of _ N] conjI exI[of _ "Suc N"]) auto
qed

lemma paired_sources_repeat: "repeated_in_every_tail (\<lambda>n::nat. n div 2)"
  unfolding repeated_in_every_tail_def
proof
  fix N :: nat
  show "\<exists>i\<ge>N. \<exists>j\<ge>N. i \<noteq> j \<and> i div 2 = j div 2"
    by (intro exI[of _ "2*N"] conjI exI[of _ "Suc (2*N)"]) auto
qed

lemma injective_sources_fail:
  assumes "inj l"
  shows "\<not> repeated_in_every_tail l"
  using assms by (auto simp: repeated_in_every_tail_def inj_def)

section \<open>Structural properties and hard interventions\<close>

lemma labelled_trancl_shape:
  assumes "(labelled_dependency l)\<^sup>+\<^sup>+ x y"
  shows "(\<exists>b n. x = SRoot b \<and> y = SLink n) \<or>
    (\<exists>n m. x = SLink n \<and> y = SLink m \<and> m < n)"
  using assms
proof (induction rule: tranclp_induct)
  case base
  then show ?case by (auto simp: labelled_dependency_def)
next
  case step
  then show ?case by (auto simp: labelled_dependency_def; arith)
qed

lemma labelled_spine_acyclic:
  "acyclic_on UNIV (labelled_dependency l)"
proof -
  have eq: "dependency_on UNIV (labelled_dependency l) = labelled_dependency l"
    by (rule ext, rule ext) (simp add: dependency_on_def)
  show ?thesis unfolding acyclic_on_def eq using labelled_trancl_shape by blast
qed

lemma labelled_spine_not_well_founded:
  "\<not> well_founded_on UNIV (labelled_dependency l)"
proof -
  have "\<not> chain_terminating_on UNIV (labelled_dependency l)"
    unfolding chain_terminating_on_def
    by (intro notI, erule notE, rule exI[of _ SLink])
      (simp add: dependency_on_def labelled_dependency_def)
  then show ?thesis by (simp add: well_founded_iff_chain_terminating)
qed

lemma labelled_spine_roots_reach_all:
  "local_foundation_on UNIV (labelled_dependency l) UNIV"
proof -
  have all: "or_step UNIV (labelled_dependency l) (efficacy_roots UNIV (labelled_dependency l)) = UNIV"
    unfolding or_step_def by (rule set_eqI, case_tac x) auto
  have eq: "lfp (or_step UNIV (labelled_dependency l)) =
      or_step UNIV (labelled_dependency l) (lfp (or_step UNIV (labelled_dependency l)))"
    by (rule lfp_unfold[OF mono_or_step])
  have "efficacy_roots UNIV (labelled_dependency l) \<subseteq>
      or_step UNIV (labelled_dependency l) (lfp (or_step UNIV (labelled_dependency l)))"
    by (auto simp: or_step_def efficacy_roots_def)
  then have roots: "efficacy_roots UNIV (labelled_dependency l) \<subseteq>
      lfp (or_step UNIV (labelled_dependency l))" using eq by blast
  have sub: "or_step UNIV (labelled_dependency l) (efficacy_roots UNIV (labelled_dependency l)) \<subseteq>
      or_step UNIV (labelled_dependency l) (lfp (or_step UNIV (labelled_dependency l)))"
    by (rule monoD[OF mono_or_step roots])
  have "lfp (or_step UNIV (labelled_dependency l)) = UNIV" using sub eq all by blast
  then show ?thesis by (simp only: lfp_or_eq_carrier_iff_local_foundation)

qed

definition intervened_spine_solution where
  "intervened_spine_solution l g u I w v \<longleftrightarrow>
    (\<forall>n. v n = (if n \<in> I then w n else gate_value (g n) (u (l n)) (v (Suc n))))"

lemma intervention_as_forced_links:
  "intervened_spine_solution l g u I w v \<longleftrightarrow>
    spine_solution id (\<lambda>n. if n \<in> I then w n else g n)
      (\<lambda>n. if n \<in> I then w n else u (l n)) v"
  by (auto simp: intervened_spine_solution_def spine_solution_def gate_value_forcing)

lemma forcing_survives_intervention:
  assumes "cofinal_forcing l g u"
  shows "cofinal_forcing id (\<lambda>n. if n \<in> I then w n else g n)
    (\<lambda>n. if n \<in> I then w n else u (l n))"
  using assms unfolding cofinal_forcing_def by auto

theorem relevant_synthesis_survives_all_hard_interventions:
  assumes "opposite_repeats l g"
  shows "\<exists>!v. intervened_spine_solution l g u I w v"
proof -
  have "cofinal_forcing l g u"
    using assms all_contexts_unique_iff_opposite_repeats unique_solution_iff_cofinal_forcing by blast
  then have "cofinal_forcing id (\<lambda>n. if n \<in> I then w n else g n)
    (\<lambda>n. if n \<in> I then w n else u (l n))"
    by (rule forcing_survives_intervention)
  then show ?thesis by (simp add: intervention_as_forced_links unique_solution_iff_cofinal_forcing)
qed

end
