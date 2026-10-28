theory Foundation_Separations
  imports Foundation_Implications
begin

section \<open>Integer Predecessor Model\<close>

text \<open>
  The integer predecessor relation is the canonical infinite separation model:
  every integer has an immediate predecessor, but no integer is independent.
  It is reused by the acyclicity, well-foundedness, essential-ordering, and
  premise-deletion results below.
\<close>

definition integer_predecessor_cause :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "integer_predecessor_cause x y \<longleftrightarrow> y = x + 1"

lemma integer_predecessor_has_incoming:
  "\<exists>y. integer_predecessor_cause y x"
  unfolding integer_predecessor_cause_def
  by (rule exI[of _ "x - 1"]) simp

lemma integer_predecessor_not_well_founded:
  "\<not> wfP integer_predecessor_cause"
proof
  assume "wfP integer_predecessor_cause"
  from wf_has_first_member[OF this, of 0] obtain m
    where "first_member_of integer_predecessor_cause m 0"
    by blast
  then show False
    using integer_predecessor_has_incoming[of m]
    by (auto simp: first_member_of_def ungrounded_def)
qed

section \<open>Acyclic but not Well-Founded\<close>

lemma integer_predecessor_dependency_trancl_less:
  "(dependency_on UNIV integer_predecessor_cause)\<^sup>+\<^sup>+ x y \<Longrightarrow> x < y"
proof (induction rule: tranclp_induct)
  case base
  then show ?case
    by (auto simp: dependency_on_def integer_predecessor_cause_def)
next
  case (step y z)
  have "x < y"
    using step.IH .
  moreover have "y < z"
    using step.hyps(2)
    by (auto simp: dependency_on_def integer_predecessor_cause_def)
  ultimately show ?case
    by (rule less_trans)
qed

lemma integer_predecessor_acyclic_on:
  "acyclic_on UNIV integer_predecessor_cause"
  unfolding acyclic_on_def
proof (intro ballI notI)
  fix x
  assume cycle:
    "(dependency_on UNIV integer_predecessor_cause)\<^sup>+\<^sup>+ x x"
  have "x < x"
    using integer_predecessor_dependency_trancl_less[OF cycle] .
  then show False
    by simp
qed

lemma integer_predecessor_not_well_founded_on:
  "\<not> well_founded_on UNIV integer_predecessor_cause"
proof
  have relation_eq:
      "dependency_on UNIV integer_predecessor_cause =
       integer_predecessor_cause"
    by (rule ext, rule ext) (simp add: dependency_on_def)
  assume "well_founded_on UNIV integer_predecessor_cause"
  have wf_rel:
      "wfp_on UNIV (dependency_on UNIV integer_predecessor_cause)"
    using \<open>well_founded_on UNIV integer_predecessor_cause\<close>
    by (simp only: well_founded_on_def)
  have wfp_rel:
      "wfp (dependency_on UNIV integer_predecessor_cause)"
    using wfp_on_iff_wfp[of UNIV
      "dependency_on UNIV integer_predecessor_cause"]
      wf_rel by simp
  have "wfP integer_predecessor_cause"
    using wfp_rel relation_eq by (simp only: relation_eq)
  then show False
    using integer_predecessor_not_well_founded by blast
qed

theorem acyclic_not_well_founded_integer_model:
  "acyclic_on UNIV integer_predecessor_cause \<and>
   \<not> well_founded_on UNIV integer_predecessor_cause"
  using integer_predecessor_acyclic_on
    integer_predecessor_not_well_founded_on by blast

section \<open>Foundation without Acyclicity\<close>

text \<open>
  A local foundation can coexist with an unrelated cycle.  The root @{term 0}
  supports the cyclic component below, but the cycle is deliberately retained
  in the immediate relation.  This separates foundation from acyclicity on
  arbitrary (in particular, non-well-founded) structures.
\<close>

definition rooted_cycle_dependency :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "rooted_cycle_dependency x y \<longleftrightarrow>
     (x = 0 \<and> y = 1) \<or>
     (x = 1 \<and> y = 2) \<or>
     (x = 2 \<and> y = 1)"

lemma rooted_cycle_zero_independent:
  "independent_in {0, 1, 2} rooted_cycle_dependency 0"
  by (auto simp: independent_in_def rooted_cycle_dependency_def)

lemma rooted_cycle_zero_ancestor:
  assumes "a \<in> {0, 1, 2}"
  shows "dependency_ancestor {0, 1, 2} rooted_cycle_dependency 0 a"
proof -
  have cases: "a = 0 \<or> a = 1 \<or> a = 2"
    using assms by auto
  then show ?thesis
  proof (elim disjE)
    assume "a = 0"
    then show ?thesis
      by (simp add: dependency_ancestor_refl)
  next
    assume "a = 1"
    then show ?thesis
      by (auto intro: dependency_ancestor_direct
        simp: rooted_cycle_dependency_def)
  next
    assume a2: "a = 2"
    have first:
        "dependency_ancestor {0, 1, 2} rooted_cycle_dependency 0 1"
      by (auto intro: dependency_ancestor_direct
        simp: rooted_cycle_dependency_def)
    have second:
        "dependency_ancestor {0, 1, 2} rooted_cycle_dependency 1 2"
      by (auto intro: dependency_ancestor_direct
        simp: rooted_cycle_dependency_def)
    have combined:
        "dependency_ancestor {0, 1, 2} rooted_cycle_dependency 0 2"
      using first second by (rule dependency_ancestor_trans)
    show ?thesis
      using combined a2 by simp
  qed
qed

lemma rooted_cycle_local_foundation:
  "local_foundation_on {0, 1, 2} rooted_cycle_dependency {0, 1, 2}"
  unfolding local_foundation_on_def
proof (intro ballI impI)
  fix a :: nat
  assume aC: "a \<in> {0, 1, 2}"
  assume "grounded_in {0, 1, 2} rooted_cycle_dependency a"
  have ancestor:
      "dependency_ancestor {0, 1, 2} rooted_cycle_dependency 0 a"
    using rooted_cycle_zero_ancestor[OF aC] .
  have first:
      "first_member_in {0, 1, 2} rooted_cycle_dependency 0 a"
    using ancestor rooted_cycle_zero_independent
    by (simp add: first_member_in_def)
  show "\<exists>f. first_member_in {0, 1, 2}
      rooted_cycle_dependency f a"
    using first by blast
qed

lemma rooted_cycle_not_acyclic:
  "\<not> acyclic_on {0, 1, 2} rooted_cycle_dependency"
proof
  assume acyclic: "acyclic_on {0, 1, 2} rooted_cycle_dependency"
  have edge12:
      "dependency_on {0, 1, 2} rooted_cycle_dependency 1 2"
    by (auto simp: dependency_on_def rooted_cycle_dependency_def)
  have edge21:
      "dependency_on {0, 1, 2} rooted_cycle_dependency 2 1"
    by (auto simp: dependency_on_def rooted_cycle_dependency_def)
  have back_path:
      "(dependency_on {0, 1, 2} rooted_cycle_dependency)\<^sup>*\<^sup>* 2 1"
    by (rule r_into_rtranclp) (rule edge21)
  have cycle:
      "(dependency_on {0, 1, 2} rooted_cycle_dependency)\<^sup>+\<^sup>+ 1 1"
    using rtranclp_into_tranclp2[OF edge12 back_path] .
  show False
    using acyclic cycle by (auto simp: acyclic_on_def)
qed

theorem local_foundation_not_acyclic_rooted_cycle:
  "local_foundation_on {0, 1, 2} rooted_cycle_dependency {0, 1, 2} \<and>
   global_foundation_on {0, 1, 2} rooted_cycle_dependency {0, 1, 2} \<and>
   \<not> acyclic_on {0, 1, 2} rooted_cycle_dependency"
proof -
  have local:
      "local_foundation_on {0, 1, 2} rooted_cycle_dependency {0, 1, 2}"
    using rooted_cycle_local_foundation .
  have global:
      "global_foundation_on {0, 1, 2} rooted_cycle_dependency {0, 1, 2}"
    using local
      local_foundation_implies_global_foundation[of
        "{0, 1, 2}" rooted_cycle_dependency "{0, 1, 2}"]
    by (auto simp: subset_iff)
  show ?thesis
    using local global rooted_cycle_not_acyclic by blast
qed

section \<open>A Fully Pedestalled Infinite Structure\<close>

text \<open>
  The pedestal relation has a distinguished independent member @{term 0}.
  It supports every nonzero member, while the negative tail still contains an
  infinite predecessor chain.  Thus a local or global foundation witness need
  not make the whole immediate relation well-founded.
\<close>

definition pedestal_dependency :: "int \<Rightarrow> int \<Rightarrow> bool"
where
  "pedestal_dependency x y \<longleftrightarrow>
     (y = x + 1 \<and> y < 0) \<or> (x = 0 \<and> y \<noteq> 0)"

definition pedestal_chain :: "nat \<Rightarrow> int"
where
  "pedestal_chain n = - of_nat n - 1"

lemma pedestal_chain_negative:
  "pedestal_chain n < 0"
  by (simp add: pedestal_chain_def)

lemma pedestal_chain_successor:
  "pedestal_chain n = pedestal_chain (Suc n) + 1"
  by (simp add: pedestal_chain_def)

lemma pedestal_chain_edge:
  "pedestal_dependency (pedestal_chain (Suc n)) (pedestal_chain n)"
  using pedestal_chain_negative[of n] pedestal_chain_successor[of n]
  by (auto simp: pedestal_dependency_def)

lemma pedestal_zero_independent:
  "independent_in UNIV pedestal_dependency 0"
  by (auto simp: independent_in_def pedestal_dependency_def)

lemma pedestal_zero_ancestor:
  "dependency_ancestor UNIV pedestal_dependency 0 x"
proof (cases "x = 0")
  case True
  then show ?thesis
    by (simp add: dependency_ancestor_def)
next
  case False
  have "pedestal_dependency 0 x"
    using False by (auto simp: pedestal_dependency_def)
  then show ?thesis
    by (auto intro: dependency_ancestor_direct)
qed

lemma pedestal_local_foundation:
  "local_foundation_on UNIV pedestal_dependency UNIV"
  unfolding local_foundation_on_def
proof (intro ballI impI)
  fix a
  have "first_member_in UNIV pedestal_dependency 0 a"
    using pedestal_zero_ancestor[of a] pedestal_zero_independent
    by (simp add: first_member_in_def)
  then show "\<exists>f. first_member_in UNIV pedestal_dependency f a"
    by blast
qed

lemma pedestal_global_foundation:
  "global_foundation_on UNIV pedestal_dependency UNIV"
  unfolding global_foundation_on_def
  by (intro exI[of _ "{0}"])
    (auto simp: foundation_set_for_def pedestal_zero_independent
      pedestal_zero_ancestor)

lemma pedestal_chain_exists:
  "\<exists>f. \<forall>n.
    dependency_on UNIV pedestal_dependency (f (Suc n)) (f n)"
  by (intro exI[of _ pedestal_chain] allI)
    (simp add: dependency_on_def pedestal_chain_edge)

lemma pedestal_not_chain_terminating:
  "\<not> chain_terminating_on UNIV pedestal_dependency"
  unfolding chain_terminating_on_def
  using pedestal_chain_exists by blast

lemma pedestal_not_well_founded:
  "\<not> well_founded_on UNIV pedestal_dependency"
  using well_founded_iff_chain_terminating[of UNIV pedestal_dependency]
    pedestal_not_chain_terminating by blast

theorem foundation_without_well_foundedness_pedestal:
  "local_foundation_on UNIV pedestal_dependency UNIV \<and>
   global_foundation_on UNIV pedestal_dependency UNIV \<and>
   \<not> well_founded_on UNIV pedestal_dependency"
  using pedestal_local_foundation pedestal_global_foundation
    pedestal_not_well_founded by blast

section \<open>Partial and Full Grounding Diverge\<close>

definition paired_dependency :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "paired_dependency x y \<longleftrightarrow>
     (x = 0 \<and> y = 1) \<or>
     (x = 0 \<and> y = 2) \<or>
     (x = 1 \<and> y = 2)"

definition paired_full_grounding :: "nat set \<Rightarrow> nat \<Rightarrow> bool"
where
  "paired_full_grounding S x \<longleftrightarrow> S = {0, 1} \<and> x = 2"

lemma paired_full_grounding_example:
  "full_grounding_on {0, 1, 2} paired_full_grounding {0, 1} 2"
  by (auto simp: full_grounding_on_def paired_full_grounding_def)

lemma paired_partial_grounding_example:
  "partial_grounding_on {0, 1, 2} paired_full_grounding 0 2"
  using paired_full_grounding_example
  by (rule partial_grounding_onI) simp

lemma paired_zero_independent:
  "independent_in {0, 1, 2} paired_dependency 0"
  by (auto simp: independent_in_def paired_dependency_def)

lemma paired_zero_ancestor:
  "dependency_ancestor {0, 1, 2} paired_dependency 0 2"
  by (rule dependency_ancestor_direct)
    (auto simp: paired_dependency_def)

lemma paired_partial_local_foundation:
  "local_foundation_on {0, 1, 2} paired_dependency {2}"
  unfolding local_foundation_on_def
proof (intro ballI impI)
  fix a :: nat
  assume "a \<in> {2}"
  then have "a = 2"
    by simp
  have first_two:
      "first_member_in {0, 1, 2} paired_dependency 0 2"
    using paired_zero_ancestor paired_zero_independent
    by (simp add: first_member_in_def)
  show "\<exists>f. first_member_in {0, 1, 2} paired_dependency f a"
    using first_two \<open>a = 2\<close>
    by (intro exI[of _ 0]) (simp add: first_member_in_def)
qed

lemma paired_full_foundation_fails:
  "\<not> full_foundation_on {0, 1, 2} paired_dependency
    paired_full_grounding {2}"
proof
  assume full:
    "full_foundation_on {0, 1, 2} paired_dependency
      paired_full_grounding {2}"
  obtain F where foundation:
      "full_foundation_for {0, 1, 2} paired_dependency
        paired_full_grounding {2} F"
    using full_foundation_onD[OF full] .
  obtain F_sub: "F \<subseteq> {0, 1, 2}"
    and R_sub: " {2} \<subseteq> {0, 1, 2}"
    and F_independent:
      "\<forall>f \<in> F. independent_in {0, 1, 2} paired_dependency f"
    and F_supports:
      "\<forall>a \<in> {2}.
        grounded_in {0, 1, 2}
          (partial_grounding_on {0, 1, 2} paired_full_grounding) a
        \<longrightarrow>
        (\<exists>S. full_grounding_on {0, 1, 2}
          paired_full_grounding S a \<and> S \<subseteq> F)"
    using full_foundation_forD[OF foundation] by blast
  have grounded:
      "grounded_in {0, 1, 2}
        (partial_grounding_on {0, 1, 2} paired_full_grounding) 2"
    using paired_partial_grounding_example
    by (auto simp: grounded_in_def)
  have support:
      "grounded_in {0, 1, 2}
        (partial_grounding_on {0, 1, 2} paired_full_grounding) 2
        \<longrightarrow>
        (\<exists>S. full_grounding_on {0, 1, 2}
          paired_full_grounding S 2 \<and> S \<subseteq> F)"
    using F_supports by blast
  obtain S where full_S:
      "full_grounding_on {0, 1, 2} paired_full_grounding S 2"
    and S_sub: "S \<subseteq> F"
    using support grounded by blast
  have S_eq: "S = {0, 1}"
    using full_S
    by (auto simp: full_grounding_on_def paired_full_grounding_def)
  have "1 \<in> F"
    using S_eq S_sub by auto
  have "independent_in {0, 1, 2} paired_dependency 1"
    using F_independent \<open>1 \<in> F\<close> by blast
  then show False
    by (auto simp: independent_in_def paired_dependency_def)
qed

theorem partial_full_grounding_diverge:
  "local_foundation_on {0, 1, 2} paired_dependency {2} \<and>
   partial_grounding_on {0, 1, 2} paired_full_grounding 0 2 \<and>
   \<not> full_foundation_on {0, 1, 2} paired_dependency
     paired_full_grounding {2}"
  using paired_partial_local_foundation paired_partial_grounding_example
    paired_full_foundation_fails by blast

end
