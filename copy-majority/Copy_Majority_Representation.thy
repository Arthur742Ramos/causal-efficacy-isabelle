theory Copy_Majority_Representation
  imports "Causal_Efficacy_Contexts.Causal_Efficacy_Contexts"
begin

section \<open>The Boolean representation test\<close>

definition majority3 where
  "majority3 b c a \<longleftrightarrow> (b \<and> c) \<or> (b \<and> a) \<or> (c \<and> a)"

lemma majority3_copy [simp]: "majority3 b b a = b"
  by (auto simp: majority3_def)

lemma majority3_disagree [simp]: "majority3 False True a = a"
  by (simp add: majority3_def)

definition projection_solution where
  "projection_solution u I w a \<longleftrightarrow> (\<forall>n::nat. a n = (if n \<in> I then w n else u n))"

definition expanded_solution where
  "expanded_solution u I w c a \<longleftrightarrow>
    (\<forall>n::nat. c n = u n) \<and>
    (\<forall>n. a n = (if n \<in> I then w n else majority3 (u n) (c n) (a (Suc n))))"

lemma expanded_projection_iff:
  "expanded_solution u I w c a \<longleftrightarrow> c = u \<and> projection_solution u I w a"
  by (auto simp: expanded_solution_def projection_solution_def fun_eq_iff)

lemma projection_unique:
  "\<exists>!a. projection_solution u I w a"
  unfolding projection_solution_def by (rule ex1I[of _ "\<lambda>n. if n \<in> I then w n else u n"]) auto

lemma expanded_unique:
  "\<exists>!v. expanded_solution u I w (fst v) (snd v)"
proof (rule ex1I[of _ "(u, \<lambda>n. if n \<in> I then w n else u n)"])
  show "expanded_solution u I w (fst (u, \<lambda>n. if n \<in> I then w n else u n))
    (snd (u, \<lambda>n. if n \<in> I then w n else u n))"
    by (simp add: expanded_projection_iff projection_solution_def)
next
  fix v
  assume "expanded_solution u I w (fst v) (snd v)"
  then show "v = (u, \<lambda>n. if n \<in> I then w n else u n)"
    by (cases v) (auto simp: expanded_projection_iff projection_solution_def fun_eq_iff)
qed

text \<open>Observations may be arbitrary predicates on the retained source/link state.
The projection hides only the newly introduced copy variables.\<close>

definition old_observation where
  "old_observation Obs u a \<longleftrightarrow> Obs (u,a)"

theorem projection_observation_preservation:
  "(\<exists>c a. expanded_solution u I w c a \<and> old_observation Obs u a)
    \<longleftrightarrow> (\<exists>a. projection_solution u I w a \<and> old_observation Obs u a)"
  by (auto simp: expanded_projection_iff)

theorem every_projection_observation_preserved:
  "(\<forall>c a. expanded_solution u I w c a \<longrightarrow> old_observation Obs u a)
    \<longleftrightarrow> (\<forall>a. projection_solution u I w a \<longrightarrow> old_observation Obs u a)"
  by (auto simp: expanded_projection_iff)

section \<open>Full carrier semantics and formal edge relevance\<close>

datatype copy_node = MRoot nat | MCopy nat | MLink nat

definition copy_dependency where
  "copy_dependency y x \<longleftrightarrow>
    (\<exists>n. x = MCopy n \<and> y = MRoot n) \<or>
    (\<exists>n. x = MLink n \<and> (y = MRoot n \<or> y = MCopy n \<or> y = MLink (Suc n)))"

lemma copy_parents [simp]:
  "efficacy_parents UNIV copy_dependency (MRoot n) = {}"
  "efficacy_parents UNIV copy_dependency (MCopy n) = {MRoot n}"
  "efficacy_parents UNIV copy_dependency (MLink n) = {MRoot n, MCopy n, MLink (Suc n)}"
  by (auto simp: efficacy_parents_def copy_dependency_def)

lemma copy_roots [simp]: "efficacy_roots UNIV copy_dependency = range MRoot"
  unfolding efficacy_roots_def by (rule set_eqI, case_tac x) auto

definition copy_majority_mechanism where
  "copy_majority_mechanism x S \<longleftrightarrow>
    (case x of MRoot n \<Rightarrow> True | MCopy n \<Rightarrow> MRoot n \<in> S |
      MLink n \<Rightarrow> majority3 (MRoot n \<in> S) (MCopy n \<in> S) (MLink (Suc n) \<in> S))"

lemma copy_majority_admissible:
  "mechanism_on UNIV copy_dependency copy_majority_mechanism"
  unfolding mechanism_on_def
  by (intro ballI, case_tac x) (auto simp: copy_majority_mechanism_def majority3_def mono_def)

lemma majority_root_relevant:
  "\<not> copy_majority_mechanism (MLink n) {MCopy n} \<and>
    copy_majority_mechanism (MLink n) {MRoot n, MCopy n}"
  by (simp add: copy_majority_mechanism_def majority3_def)

lemma majority_copy_relevant:
  "\<not> copy_majority_mechanism (MLink n) {MRoot n} \<and>
    copy_majority_mechanism (MLink n) {MCopy n, MRoot n}"
  by (simp add: copy_majority_mechanism_def majority3_def)

lemma majority_successor_relevant:
  "\<not> copy_majority_mechanism (MLink n) {MRoot n} \<and>
    copy_majority_mechanism (MLink n) {MLink (Suc n), MRoot n}"
  by (simp add: copy_majority_mechanism_def majority3_def)

lemma copy_majority_relevant:
  "edge_relevant_on UNIV copy_dependency copy_majority_mechanism"
  unfolding edge_relevant_on_def
proof (intro ballI)
  fix x y
  assume x: "x \<in> UNIV" and y: "y \<in> efficacy_parents UNIV copy_dependency x"
  show "\<exists>S\<subseteq>efficacy_parents UNIV copy_dependency x - {y}.
    \<not> copy_majority_mechanism x S \<and> copy_majority_mechanism x (insert y S)"
  proof (cases x)
    case (MRoot n)
    then show ?thesis using y by simp
  next
    case (MCopy n)
    then show ?thesis using y by (intro exI[of _ "{}"]) (auto simp: copy_majority_mechanism_def)
  next
    case (MLink n)
    show ?thesis
    proof (cases "y = MRoot n")
      case True
      show ?thesis using MLink True by (intro exI[of _ "{MCopy n}"])
        (auto simp: copy_majority_mechanism_def majority3_def)
    next
      case False
      show ?thesis using MLink y False by (intro exI[of _ "{MRoot n}"])
        (auto simp: copy_majority_mechanism_def majority3_def)
    qed
  qed
qed

definition copy_state where
  "copy_state u c a = {x. case x of MRoot n \<Rightarrow> u n | MCopy n \<Rightarrow> c n | MLink n \<Rightarrow> a n}"

lemma copy_state_simps [simp]:
  "(MRoot n \<in> copy_state u c a) = u n"
  "(MCopy n \<in> copy_state u c a) = c n"
  "(MLink n \<in> copy_state u c a) = a n"
  by (simp_all add: copy_state_def)

definition copy_context where "copy_context u = {MRoot n |n. u n}"

lemma copy_context_legal: "copy_context u \<subseteq> efficacy_roots UNIV copy_dependency"
  by (auto simp: copy_context_def)

lemma copy_context_members [simp]:
  "(MRoot n \<in> copy_context u) = u n"
  "MCopy n \<notin> copy_context u"
  "MLink n \<notin> copy_context u"
  by (auto simp: copy_context_def)

lemma copy_step_members [simp]:
  "(MRoot n \<in> contextual_step UNIV copy_dependency copy_majority_mechanism (copy_context u) X) = u n"
  "(MCopy n \<in> contextual_step UNIV copy_dependency copy_majority_mechanism (copy_context u) X) = (MRoot n \<in> X)"
  "(MLink n \<in> contextual_step UNIV copy_dependency copy_majority_mechanism (copy_context u) X) =
    majority3 (MRoot n \<in> X) (MCopy n \<in> X) (MLink (Suc n) \<in> X)"
  by (simp_all add: contextual_step_def source_off_step_def copy_majority_mechanism_def)

lemma copy_fixed_iff:
  "contextual_step UNIV copy_dependency copy_majority_mechanism (copy_context u) X = X
    \<longleftrightarrow> X = copy_state u u u"
proof
  assume fixed: "contextual_step UNIV copy_dependency copy_majority_mechanism (copy_context u) X = X"
  have root: "\<And>n. (MRoot n \<in> X) = u n"
  proof -
    fix n
    have "(MRoot n \<in> contextual_step UNIV copy_dependency copy_majority_mechanism (copy_context u) X) = (MRoot n \<in> X)"
      by (simp only: fixed)
    then show "(MRoot n \<in> X) = u n" by simp
  qed
  have cp: "\<And>n. (MCopy n \<in> X) = u n"
  proof -
    fix n
    have "(MCopy n \<in> contextual_step UNIV copy_dependency copy_majority_mechanism (copy_context u) X) = (MCopy n \<in> X)"
      by (simp only: fixed)
    then show "(MCopy n \<in> X) = u n" by (simp add: root)
  qed
  have link: "\<And>n. (MLink n \<in> X) = u n"
  proof -
    fix n
    have "(MLink n \<in> contextual_step UNIV copy_dependency copy_majority_mechanism (copy_context u) X) = (MLink n \<in> X)"
      by (simp only: fixed)
    then show "(MLink n \<in> X) = u n" by (simp add: root cp)
  qed
  show "X = copy_state u u u"
    by (rule set_eqI, case_tac x) (simp_all add: root cp link)
next
  assume eq: "X = copy_state u u u"
  show "contextual_step UNIV copy_dependency copy_majority_mechanism (copy_context u) X = X"
    unfolding eq by (rule set_eqI, case_tac x) simp_all
qed

theorem copy_majority_context_unique:
  "\<exists>!X. contextual_step UNIV copy_dependency copy_majority_mechanism (copy_context u) X = X"
  by (simp add: copy_fixed_iff)

theorem copy_majority_all_contexts:
  "context_determinate UNIV copy_dependency copy_majority_mechanism"
  unfolding context_determinate_def
proof (intro allI impI)
  fix U
  assume "U \<subseteq> efficacy_roots UNIV copy_dependency"
  then have eq: "copy_context (\<lambda>n. MRoot n \<in> U) = U"
    by (auto simp: copy_context_def)
  show "\<exists>!X. contextual_step UNIV copy_dependency copy_majority_mechanism U X = X"
    using copy_majority_context_unique[of "\<lambda>n. MRoot n \<in> U"] by (simp only: eq)
qed

section \<open>Hard replacement of original link equations\<close>

definition original_link_intervention_step where
  "original_link_intervention_step u I w X = {x.
    case x of MRoot n \<Rightarrow> u n |
      MCopy n \<Rightarrow> MRoot n \<in> X |
      MLink n \<Rightarrow> (if n \<in> I then w n else
        majority3 (MRoot n \<in> X) (MCopy n \<in> X) (MLink (Suc n) \<in> X))}"

lemma original_link_step_members [simp]:
  "(MRoot n \<in> original_link_intervention_step u I w X) = u n"
  "(MCopy n \<in> original_link_intervention_step u I w X) = (MRoot n \<in> X)"
  "(MLink n \<in> original_link_intervention_step u I w X) =
    (if n \<in> I then w n else majority3 (MRoot n \<in> X) (MCopy n \<in> X) (MLink (Suc n) \<in> X))"
  by (simp_all add: original_link_intervention_step_def)

lemma no_link_intervention_is_contextual:
  "original_link_intervention_step u {} w =
    contextual_step UNIV copy_dependency copy_majority_mechanism (copy_context u)"
proof (rule ext, rule set_eqI)
  fix X x
  show "(x \<in> original_link_intervention_step u {} w X) =
    (x \<in> contextual_step UNIV copy_dependency copy_majority_mechanism (copy_context u) X)"
    by (cases x) simp_all
qed

lemma original_link_intervention_fixed_iff:
  "original_link_intervention_step u I w X = X \<longleftrightarrow>
    X = copy_state u u (\<lambda>n. if n \<in> I then w n else u n)"
proof
  assume fixed: "original_link_intervention_step u I w X = X"
  have root: "\<And>n. (MRoot n \<in> X) = u n"
  proof -
    fix n
    have "(MRoot n \<in> original_link_intervention_step u I w X) = (MRoot n \<in> X)"
      by (simp only: fixed)
    then show "(MRoot n \<in> X) = u n" by simp
  qed
  have cp: "\<And>n. (MCopy n \<in> X) = u n"
  proof -
    fix n
    have "(MCopy n \<in> original_link_intervention_step u I w X) = (MCopy n \<in> X)"
      by (simp only: fixed)
    then show "(MCopy n \<in> X) = u n" by (simp add: root)
  qed
  have link: "\<And>n. (MLink n \<in> X) = (if n \<in> I then w n else u n)"
  proof -
    fix n
    have "(MLink n \<in> original_link_intervention_step u I w X) = (MLink n \<in> X)"
      by (simp only: fixed)
    then show "(MLink n \<in> X) = (if n \<in> I then w n else u n)"
      using root[of n] cp[of n] by (cases "n \<in> I") auto
  qed
  show "X = copy_state u u (\<lambda>n. if n \<in> I then w n else u n)"
    by (rule set_eqI, case_tac x) (simp_all add: root cp link)
next
  assume eq: "X = copy_state u u (\<lambda>n. if n \<in> I then w n else u n)"
  show "original_link_intervention_step u I w X = X"
    unfolding eq by (rule set_eqI, case_tac x) simp_all
qed

theorem original_link_interventions_unique:
  "\<exists>!X. original_link_intervention_step u I w X = X"
  by (simp add: original_link_intervention_fixed_iff)

lemma copy_state_injective:
  "copy_state u c a = copy_state u d b \<longleftrightarrow> c = d \<and> a = b"
  by (auto simp: copy_state_def set_eq_iff fun_eq_iff split: copy_node.splits)

theorem carrier_expanded_solution_bridge:
  "original_link_intervention_step u I w (copy_state u c a) = copy_state u c a
    \<longleftrightarrow> expanded_solution u I w c a"
  by (auto simp: original_link_intervention_fixed_iff copy_state_injective
    expanded_projection_iff projection_solution_def fun_eq_iff)

lemma majority_context_successor_relevant:
  "majority3 b (\<not>b) False \<noteq> majority3 b (\<not>b) True"
  by (cases b) (simp_all add: majority3_def)

section \<open>Copy interventions invalidate unrestricted preservation\<close>

definition copies_clamped_solution where
  "copies_clamped_solution u J z c a \<longleftrightarrow>
    (\<forall>n::nat. c n = (if n \<in> J then z n else u n)) \<and>
    (\<forall>n. a n = majority3 (u n) (c n) (a (Suc n)))"

lemma all_copies_on_roots_off:
  "copies_clamped_solution (\<lambda>_. False) UNIV (\<lambda>_. True) c a \<longleftrightarrow>
    c = (\<lambda>_. True) \<and> (\<forall>n. a n = a (Suc n))"
  by (auto simp: copies_clamped_solution_def fun_eq_iff)

theorem copy_interventions_nonunique:
  "\<not> (\<exists>!v. copies_clamped_solution (\<lambda>_. False) UNIV (\<lambda>_. True) (fst v) (snd v))"
proof
  assume unique: "\<exists>!v. copies_clamped_solution (\<lambda>_. False) UNIV (\<lambda>_. True) (fst v) (snd v)"
  have zero: "copies_clamped_solution (\<lambda>_. False) UNIV (\<lambda>_. True) (fst ((\<lambda>_. True), (\<lambda>_. False))) (snd ((\<lambda>_. True), (\<lambda>_. False)))"
    by (simp add: all_copies_on_roots_off)
  have one: "copies_clamped_solution (\<lambda>_. False) UNIV (\<lambda>_. True) (fst ((\<lambda>_. True), (\<lambda>_. True))) (snd ((\<lambda>_. True), (\<lambda>_. True)))"
    by (simp add: all_copies_on_roots_off)
  have "((\<lambda>_::nat. True), (\<lambda>_::nat. False)) = ((\<lambda>_. True), (\<lambda>_. True))"
    using unique zero one by blast
  then show False by (simp add: fun_eq_iff)
qed

end
