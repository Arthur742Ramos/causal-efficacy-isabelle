theory Causal_Efficacy_Mechanisms
  imports "Thomistic_Causal_Arguments.Research_Results"
begin

section \<open>Local mechanisms and their extremal operators\<close>

text \<open>
  This extension supplies an explicit Boolean source-generation semantics.
  It does not identify that semantics with a complete metaphysics of causal
  power. Roots are stipulated active. Least-fixed-point selection is separate
  from local consistency, and functional edge relevance is weaker than
  actual-state indispensability.
\<close>

definition efficacy_parents ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set"
where "efficacy_parents C D x = {y \<in> C. D y x}"

definition and_step ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set"
where "and_step C D X = {x \<in> C. efficacy_parents C D x \<subseteq> X}"

definition or_step ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set"
where "or_step C D X = {x \<in> C. efficacy_parents C D x = {} \<or>
    efficacy_parents C D x \<inter> X \<noteq> {}}"

definition efficacy_step ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'a set \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set"
where "efficacy_step C D f X =
  {x \<in> C. f x (X \<inter> efficacy_parents C D x)}"

definition mechanism_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'a set \<Rightarrow> bool) \<Rightarrow> bool"
where "mechanism_on C D f \<longleftrightarrow>
  (\<forall>x \<in> C. mono (f x) \<and>
    (f x {} \<longleftrightarrow> efficacy_parents C D x = {}) \<and>
    f x (efficacy_parents C D x))"

definition edge_relevant_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
    ('a \<Rightarrow> 'a set \<Rightarrow> bool) \<Rightarrow> bool"
where "edge_relevant_on C D f \<longleftrightarrow>
  (\<forall>x \<in> C. \<forall>y \<in> efficacy_parents C D x.
    \<exists>S \<subseteq> efficacy_parents C D x - {y}.
      \<not> f x S \<and> f x (insert y S))"

definition and_mechanism where
  "and_mechanism C D x S \<longleftrightarrow> efficacy_parents C D x \<subseteq> S"

definition or_mechanism where
  "or_mechanism C D x S \<longleftrightarrow> efficacy_parents C D x = {} \<or>
    efficacy_parents C D x \<inter> S \<noteq> {}"

lemma mono_and_step: "mono (and_step C D)"
  unfolding mono_def and_step_def by blast

lemma mono_or_step: "mono (or_step C D)"
  unfolding mono_def or_step_def by blast

lemma and_step_subset_carrier: "and_step C D X \<subseteq> C"
  by (auto simp: and_step_def)

lemma or_step_subset_carrier: "or_step C D X \<subseteq> C"
  by (auto simp: or_step_def)

lemma and_stepI:
  assumes "x \<in> C" "efficacy_parents C D x \<subseteq> X"
  shows "x \<in> and_step C D X"
  using assms by (simp add: and_step_def)

lemma or_step_parentI:
  assumes "x \<in> C" "y \<in> C" "D y x" "y \<in> X"
  shows "x \<in> or_step C D X"
  using assms by (auto simp: or_step_def efficacy_parents_def)

lemma lfp_and_subset_carrier: "lfp (and_step C D) \<subseteq> C"
  by (rule lfp_lowerbound) (rule and_step_subset_carrier)

lemma lfp_or_subset_carrier: "lfp (or_step C D) \<subseteq> C"
  by (rule lfp_lowerbound) (rule or_step_subset_carrier)

lemma mechanism_extremal_bounds:
  assumes admissible: "mechanism_on C D f"
  shows "and_step C D X \<subseteq> efficacy_step C D f X"
    and "efficacy_step C D f X \<subseteq> or_step C D X"
proof -
  show "and_step C D X \<subseteq> efficacy_step C D f X"
  proof (rule subsetI)
    fix x
    assume "x \<in> and_step C D X"
    then have xC: "x \<in> C" and sub: "efficacy_parents C D x \<subseteq> X"
      by (auto simp: and_step_def)
    have eq: "X \<inter> efficacy_parents C D x = efficacy_parents C D x"
      using sub by blast
    show "x \<in> efficacy_step C D f X"
      using admissible xC by (simp add: efficacy_step_def eq mechanism_on_def)
  qed
  show "efficacy_step C D f X \<subseteq> or_step C D X"
    using admissible unfolding mechanism_on_def efficacy_step_def or_step_def
    by (auto simp: Int_commute)
qed

lemma mono_efficacy_step:
  fixes C :: "'a set"
  assumes admissible: "mechanism_on C D f"
  shows "mono (efficacy_step C D f)"
proof (rule monoI)
  fix X Y :: "'a set"
  assume XY: "X \<subseteq> Y"
  show "efficacy_step C D f X \<subseteq> efficacy_step C D f Y"
  proof (rule subsetI)
    fix x
    assume "x \<in> efficacy_step C D f X"
    then have xC: "x \<in> C" and active: "f x (X \<inter> efficacy_parents C D x)"
      by (auto simp: efficacy_step_def)
    have local_mono: "mono (f x)"
      using admissible xC by (auto simp: mechanism_on_def)
    have inputs: "X \<inter> efficacy_parents C D x \<subseteq> Y \<inter> efficacy_parents C D x"
      using XY by blast
    have "f x (Y \<inter> efficacy_parents C D x)"
      using monoD[OF local_mono inputs] active by simp
    then show "x \<in> efficacy_step C D f Y"
      using xC by (simp add: efficacy_step_def)
  qed
qed

lemma and_mechanism_admissible: "mechanism_on C D (and_mechanism C D)"
  by (auto simp: mechanism_on_def and_mechanism_def mono_def)

lemma or_mechanism_admissible: "mechanism_on C D (or_mechanism C D)"
  by (auto simp: mechanism_on_def or_mechanism_def mono_def)

lemma and_mechanism_relevant: "edge_relevant_on C D (and_mechanism C D)"
  unfolding edge_relevant_on_def
proof (intro ballI)
  fix x y
  assume "x \<in> C" and yP: "y \<in> efficacy_parents C D x"
  show "\<exists>S \<subseteq> efficacy_parents C D x - {y}.
    \<not> and_mechanism C D x S \<and> and_mechanism C D x (insert y S)"
    using yP by (intro exI[of _ "efficacy_parents C D x - {y}"])
      (auto simp: and_mechanism_def)
qed

lemma or_mechanism_relevant: "edge_relevant_on C D (or_mechanism C D)"
  unfolding edge_relevant_on_def or_mechanism_def
  by (intro ballI, rule exI[of _ "{}"]) auto

lemma and_mechanism_step:
  "efficacy_step C D (and_mechanism C D) = and_step C D"
  unfolding efficacy_step_def and_mechanism_def and_step_def
  by (rule ext) auto

lemma or_mechanism_step:
  "efficacy_step C D (or_mechanism C D) = or_step C D"
  unfolding efficacy_step_def or_mechanism_def or_step_def
  by (rule ext) auto

lemma efficacy_lfp_sandwich:
  assumes "mechanism_on C D f"
  shows "lfp (and_step C D) \<subseteq> lfp (efficacy_step C D f)"
    and "lfp (efficacy_step C D f) \<subseteq> lfp (or_step C D)"
  by (rule lfp_mono, rule mechanism_extremal_bounds[OF assms])+ 

lemma all_active_is_fixed:
  assumes "mechanism_on C D f"
  shows "efficacy_step C D f C = C"
proof -
  have eq: "\<And>x. C \<inter> efficacy_parents C D x = efficacy_parents C D x"
    by (auto simp: efficacy_parents_def)
  show ?thesis
    using assms by (auto simp: mechanism_on_def efficacy_step_def eq)
qed

section \<open>Exact identification of the extreme least fixed points\<close>

definition root_reachable where
  "root_reachable C D = {x. \<exists>b. first_member_in C D b x}"

lemma lfp_or_eq_root_reachable:
  "lfp (or_step C D) = root_reachable C D"
proof (rule subset_antisym)
  show "lfp (or_step C D) \<subseteq> root_reachable C D"
  proof (rule lfp_lowerbound, rule subsetI)
    fix x
    assume "x \<in> or_step C D (root_reachable C D)"
    then have xC: "x \<in> C"
      and cases: "efficacy_parents C D x = {} \<or>
        efficacy_parents C D x \<inter> root_reachable C D \<noteq> {}"
      by (auto simp: or_step_def)
    from cases show "x \<in> root_reachable C D"
    proof
      assume "efficacy_parents C D x = {}"
      then have "independent_in C D x"
        using xC by (auto simp: efficacy_parents_def independent_in_def)
      then show ?thesis
        using dependency_ancestor_refl[OF xC]
        by (auto simp: root_reachable_def first_member_in_def)
    next
      assume "efficacy_parents C D x \<inter> root_reachable C D \<noteq> {}"
      then obtain y b where yC: "y \<in> C" and edge: "D y x"
        and root_y: "first_member_in C D b y"
        by (auto simp: efficacy_parents_def root_reachable_def)
      have direct: "dependency_ancestor C D y x"
        using yC xC edge by (rule dependency_ancestor_direct)
      have "dependency_ancestor C D b x"
        using root_y direct
        by (auto simp: first_member_in_def intro: dependency_ancestor_trans)
      then show ?thesis
        using root_y by (auto simp: root_reachable_def first_member_in_def)
    qed
  qed
next
  show "root_reachable C D \<subseteq> lfp (or_step C D)"
  proof (rule subsetI)
    fix x
    assume "x \<in> root_reachable C D"
    then obtain b where bC: "b \<in> C" and root: "independent_in C D b"
      and path: "(dependency_on C D)\<^sup>*\<^sup>* b x"
      by (auto simp: root_reachable_def first_member_in_def dependency_ancestor_def)
    have unfold: "lfp (or_step C D) = or_step C D (lfp (or_step C D))"
      by (rule lfp_unfold[OF mono_or_step])
    have root_mem: "b \<in> lfp (or_step C D)"
      using root by (subst unfold) (auto simp: or_step_def efficacy_parents_def independent_in_def)
    from path show "x \<in> lfp (or_step C D)"
    proof (induction rule: rtranclp_induct)
      case base
      then show ?case using root_mem by blast
    next
      case (step y z)
      have "z \<in> or_step C D (lfp (or_step C D))"
        using step.IH step.hyps(2)
        by (auto simp: dependency_on_def intro: or_step_parentI)
      then show ?case using unfold by simp
    qed
  qed
qed

lemma lfp_and_eq_accessible:
  "lfp (and_step C D) = {x \<in> C. Wellfounded.accp (dependency_on C D) x}"
proof (rule subset_antisym)
  show "lfp (and_step C D) \<subseteq> {x \<in> C. Wellfounded.accp (dependency_on C D) x}"
  proof (rule lfp_lowerbound, rule subsetI)
    fix x
    assume xin: "x \<in> and_step C D {x \<in> C. Wellfounded.accp (dependency_on C D) x}"
    have acc: "Wellfounded.accp (dependency_on C D) x"
    proof (rule accp.accI)
      fix y
      assume "dependency_on C D y x"
      then show "Wellfounded.accp (dependency_on C D) y"
        using xin by (auto simp: and_step_def efficacy_parents_def dependency_on_def)
    qed
    show "x \<in> {x \<in> C. Wellfounded.accp (dependency_on C D) x}"
      using xin acc by (auto simp: and_step_def)
  qed
next
  show "{x \<in> C. Wellfounded.accp (dependency_on C D) x} \<subseteq> lfp (and_step C D)"
  proof (rule subsetI)
    fix x
    assume xin: "x \<in> {x \<in> C. Wellfounded.accp (dependency_on C D) x}"
    have "Wellfounded.accp (dependency_on C D) x" using xin by simp
    then have "x \<in> C \<longrightarrow> x \<in> lfp (and_step C D)"
    proof (induction rule: accp.induct)
      case (accI x)
      show ?case
      proof
        assume xC: "x \<in> C"
        have parents: "efficacy_parents C D x \<subseteq> lfp (and_step C D)"
          using accI.IH xC by (auto simp: efficacy_parents_def dependency_on_def)
        have "x \<in> and_step C D (lfp (and_step C D))"
          using xC parents by (rule and_stepI)
        then show "x \<in> lfp (and_step C D)"
          using lfp_unfold[OF mono_and_step[of C D]] by simp
      qed
    qed
    then show "x \<in> lfp (and_step C D)" using xin by simp
  qed
qed

lemma lfp_or_eq_carrier_iff_local_foundation:
  "lfp (or_step C D) = C \<longleftrightarrow> local_foundation_on C D C"
  unfolding lfp_or_eq_root_reachable
proof
  assume eq: "root_reachable C D = C"
  show "local_foundation_on C D C"
    using eq by (auto simp: local_foundation_on_def root_reachable_def)
next
  assume lf: "local_foundation_on C D C"
  show "root_reachable C D = C"
  proof (rule subset_antisym)
    show "root_reachable C D \<subseteq> C"
      by (auto simp: root_reachable_def first_member_in_def dependency_ancestor_def)
    show "C \<subseteq> root_reachable C D"
    proof (rule subsetI)
      fix x
      assume xC: "x \<in> C"
      show "x \<in> root_reachable C D"
      proof (cases "grounded_in C D x")
        case True
        then show ?thesis
          using lf xC by (auto simp: local_foundation_on_def root_reachable_def)
      next
        case False
        have "first_member_in C D x x"
          using xC False by (auto simp: first_member_in_def dependency_ancestor_def
            independent_in_def grounded_in_def)
        then show ?thesis by (auto simp: root_reachable_def)
      qed
    qed
  qed
qed

lemma lfp_and_eq_carrier_iff_well_founded:
  "lfp (and_step C D) = C \<longleftrightarrow> well_founded_on C D"
proof -
  have outside: "\<And>x. x \<notin> C \<Longrightarrow> Wellfounded.accp (dependency_on C D) x"
    by (rule accp.accI) (auto simp: dependency_on_def)
  have relation_eq:
    "(\<lambda>x y. dependency_on C D x y \<and> x \<in> C \<and> y \<in> C) =
      dependency_on C D"
    by (rule ext, rule ext) (auto simp: dependency_on_def)
  have wf_eq: "well_founded_on C D \<longleftrightarrow> wfp (dependency_on C D)"
    unfolding well_founded_on_def
    using wfp_on_iff_wfp[of C "dependency_on C D"] relation_eq by simp
  show ?thesis
    unfolding lfp_and_eq_accessible wf_eq wfp_iff_accp
    using outside by blast
qed

section \<open>Mechanism quantifiers\<close>

theorem some_mechanism_iff_root_reachable:
  "(\<exists>f. mechanism_on C D f \<and> T \<subseteq> lfp (efficacy_step C D f))
    \<longleftrightarrow> T \<subseteq> root_reachable C D"
proof
  assume "\<exists>f. mechanism_on C D f \<and> T \<subseteq> lfp (efficacy_step C D f)"
  then show "T \<subseteq> root_reachable C D"
    using efficacy_lfp_sandwich(2)[of C D] lfp_or_eq_root_reachable[of C D] by blast
next
  assume "T \<subseteq> root_reachable C D"
  then show "\<exists>f. mechanism_on C D f \<and> T \<subseteq> lfp (efficacy_step C D f)"
    by (intro exI[of _ "or_mechanism C D"])
      (simp add: or_mechanism_admissible or_mechanism_step lfp_or_eq_root_reachable)
qed

theorem every_mechanism_iff_accessible:
  "(\<forall>f. mechanism_on C D f \<longrightarrow> T \<subseteq> lfp (efficacy_step C D f))
    \<longleftrightarrow> T \<subseteq> {x \<in> C. Wellfounded.accp (dependency_on C D) x}"
proof
  assume "\<forall>f. mechanism_on C D f \<longrightarrow> T \<subseteq> lfp (efficacy_step C D f)"
  then show "T \<subseteq> {x \<in> C. Wellfounded.accp (dependency_on C D) x}"
    using and_mechanism_admissible[of C D]
    by (metis and_mechanism_step lfp_and_eq_accessible)
next
  assume "T \<subseteq> {x \<in> C. Wellfounded.accp (dependency_on C D) x}"
  then show "\<forall>f. mechanism_on C D f \<longrightarrow> T \<subseteq> lfp (efficacy_step C D f)"
    using efficacy_lfp_sandwich(1)[of C D] lfp_and_eq_accessible[of C D] by blast
qed

theorem some_relevant_mechanism_iff_root_reachable:
  "(\<exists>f. mechanism_on C D f \<and> edge_relevant_on C D f \<and>
      T \<subseteq> lfp (efficacy_step C D f))
    \<longleftrightarrow> T \<subseteq> root_reachable C D"
proof
  assume "\<exists>f. mechanism_on C D f \<and> edge_relevant_on C D f \<and>
      T \<subseteq> lfp (efficacy_step C D f)"
  then show "T \<subseteq> root_reachable C D"
    using some_mechanism_iff_root_reachable[of C D T] by blast
next
  assume "T \<subseteq> root_reachable C D"
  then show "\<exists>f. mechanism_on C D f \<and> edge_relevant_on C D f \<and>
      T \<subseteq> lfp (efficacy_step C D f)"
    by (intro exI[of _ "or_mechanism C D"])
      (simp add: or_mechanism_admissible or_mechanism_relevant
        or_mechanism_step lfp_or_eq_root_reachable)
qed

theorem every_relevant_mechanism_iff_accessible:
  "(\<forall>f. mechanism_on C D f \<and> edge_relevant_on C D f \<longrightarrow>
      T \<subseteq> lfp (efficacy_step C D f))
    \<longleftrightarrow> T \<subseteq> {x \<in> C. Wellfounded.accp (dependency_on C D) x}"
proof
  assume all: "\<forall>f. mechanism_on C D f \<and> edge_relevant_on C D f \<longrightarrow>
      T \<subseteq> lfp (efficacy_step C D f)"
  have "T \<subseteq> lfp (efficacy_step C D (and_mechanism C D))"
    using all and_mechanism_admissible[of C D] and_mechanism_relevant[of C D] by blast
  then show "T \<subseteq> {x \<in> C. Wellfounded.accp (dependency_on C D) x}"
    by (simp add: and_mechanism_step lfp_and_eq_accessible)
next
  assume "T \<subseteq> {x \<in> C. Wellfounded.accp (dependency_on C D) x}"
  then show "\<forall>f. mechanism_on C D f \<and> edge_relevant_on C D f \<longrightarrow>
      T \<subseteq> lfp (efficacy_step C D f)"
    using every_mechanism_iff_accessible[of C D T] by blast
qed

theorem some_total_mechanism_iff_local_foundation:
  "(\<exists>f. mechanism_on C D f \<and> lfp (efficacy_step C D f) = C)
    \<longleftrightarrow> local_foundation_on C D C"
proof -
  have sub: "\<And>f. lfp (efficacy_step C D f) \<subseteq> C"
    by (rule lfp_lowerbound) (auto simp: efficacy_step_def)
  show ?thesis
    using some_mechanism_iff_root_reachable[of C D C]
      lfp_or_eq_carrier_iff_local_foundation[of C D]
      lfp_or_eq_root_reachable[of C D] lfp_or_subset_carrier[of C D] sub
    by blast
qed

theorem every_total_mechanism_iff_well_founded:
  "(\<forall>f. mechanism_on C D f \<longrightarrow> lfp (efficacy_step C D f) = C)
    \<longleftrightarrow> well_founded_on C D"
proof -
  have sub: "\<And>f. lfp (efficacy_step C D f) \<subseteq> C"
    by (rule lfp_lowerbound) (auto simp: efficacy_step_def)
  have eqf: "\<And>f. lfp (efficacy_step C D f) = C \<longleftrightarrow>
      C \<subseteq> lfp (efficacy_step C D f)"
    using sub by blast
  have eqand: "C \<subseteq> {x \<in> C. Wellfounded.accp (dependency_on C D) x}
      \<longleftrightarrow> well_founded_on C D"
    using lfp_and_eq_carrier_iff_well_founded[of C D]
      lfp_and_eq_accessible[of C D] lfp_and_subset_carrier[of C D] by blast
  show ?thesis
    by (simp only: eqf every_mechanism_iff_accessible eqand)
qed


section \<open>Local-equation determinacy without a solution-selection policy\<close>

text \<open>
  Membership in the least fixed point is equivalent to truth in every fixed
  point. Since the all-active assignment is always a solution, total least
  efficacy is equivalent to uniqueness of a solution. These statements permit
  a local-equation determinacy reading without first selecting the least
  solution as metaphysically actual.
\<close>

theorem target_lfp_iff_all_fixed_points:
  assumes admissible: "mechanism_on C D f"
  shows "T \<subseteq> lfp (efficacy_step C D f) \<longleftrightarrow>
    (\<forall>X. efficacy_step C D f X = X \<longrightarrow> T \<subseteq> X)"
proof
  assume target: "T \<subseteq> lfp (efficacy_step C D f)"
  show "\<forall>X. efficacy_step C D f X = X \<longrightarrow> T \<subseteq> X"
  proof (intro allI impI)
    fix X
    assume fixed: "efficacy_step C D f X = X"
    have "lfp (efficacy_step C D f) \<subseteq> X"
      by (rule lfp_lowerbound) (simp add: fixed)
    then show "T \<subseteq> X" using target by blast
  qed
next
  assume all: "\<forall>X. efficacy_step C D f X = X \<longrightarrow> T \<subseteq> X"
  have fixed: "efficacy_step C D f (lfp (efficacy_step C D f)) =
      lfp (efficacy_step C D f)"
    using lfp_unfold[OF mono_efficacy_step[OF admissible]] by simp
  show "T \<subseteq> lfp (efficacy_step C D f)"
    using all fixed by blast
qed

theorem total_lfp_iff_unique_fixed_point:
  assumes admissible: "mechanism_on C D f"
  shows "lfp (efficacy_step C D f) = C \<longleftrightarrow>
    (\<exists>!X. efficacy_step C D f X = X)"
proof
  assume total: "lfp (efficacy_step C D f) = C"
  show "\<exists>!X. efficacy_step C D f X = X"
  proof (rule ex1I[of _ C])
    show "efficacy_step C D f C = C"
      by (rule all_active_is_fixed[OF admissible])
    fix X
    assume fixed: "efficacy_step C D f X = X"
    have upper: "X \<subseteq> C"
      using fixed by (auto simp: efficacy_step_def)
    have lower: "lfp (efficacy_step C D f) \<subseteq> X"
      by (rule lfp_lowerbound) (simp add: fixed)
    show "X = C" using upper lower total by blast
  qed
next
  assume unique: "\<exists>!X. efficacy_step C D f X = X"
  have fixed: "efficacy_step C D f (lfp (efficacy_step C D f)) =
      lfp (efficacy_step C D f)"
    using lfp_unfold[OF mono_efficacy_step[OF admissible]] by simp
  show "lfp (efficacy_step C D f) = C"
    using unique fixed all_active_is_fixed[OF admissible] by blast
qed

theorem some_unique_fixed_point_iff_local_foundation:
  "(\<exists>f. mechanism_on C D f \<and> (\<exists>!X. efficacy_step C D f X = X))
    \<longleftrightarrow> local_foundation_on C D C"
proof
  assume "\<exists>f. mechanism_on C D f \<and> (\<exists>!X. efficacy_step C D f X = X)"
  then obtain f where admissible: "mechanism_on C D f"
    and unique: "\<exists>!X. efficacy_step C D f X = X" by (elim exE conjE)
  have total: "lfp (efficacy_step C D f) = C"
    by (rule iffD2[OF total_lfp_iff_unique_fixed_point[OF admissible] unique])
  have "\<exists>f. mechanism_on C D f \<and> lfp (efficacy_step C D f) = C"
    using admissible total by blast
  then show "local_foundation_on C D C"
    by (simp only: some_total_mechanism_iff_local_foundation)
next
  assume "local_foundation_on C D C"
  then obtain f where admissible: "mechanism_on C D f"
    and total: "lfp (efficacy_step C D f) = C"
    using some_total_mechanism_iff_local_foundation[of C D] by blast
  have unique: "\<exists>!X. efficacy_step C D f X = X"
    by (rule iffD1[OF total_lfp_iff_unique_fixed_point[OF admissible] total])
  show "\<exists>f. mechanism_on C D f \<and> (\<exists>!X. efficacy_step C D f X = X)"
    by (intro exI[of _ f] conjI) (fact admissible, fact unique)
qed

theorem every_unique_fixed_point_iff_well_founded:
  "(\<forall>f. mechanism_on C D f \<longrightarrow> (\<exists>!X. efficacy_step C D f X = X))
    \<longleftrightarrow> well_founded_on C D"
proof
  assume all: "\<forall>f. mechanism_on C D f \<longrightarrow> (\<exists>!X. efficacy_step C D f X = X)"
  have "\<forall>f. mechanism_on C D f \<longrightarrow> lfp (efficacy_step C D f) = C"
  proof (intro allI impI)
    fix f
    assume admissible: "mechanism_on C D f"
    have unique: "\<exists>!X. efficacy_step C D f X = X"
      by (rule all[rule_format, OF admissible])
    show "lfp (efficacy_step C D f) = C"
      by (rule iffD2[OF total_lfp_iff_unique_fixed_point[OF admissible] unique])
  qed
  then show "well_founded_on C D"
    by (simp only: every_total_mechanism_iff_well_founded)
next
  assume wf: "well_founded_on C D"
  have all: "\<forall>f. mechanism_on C D f \<longrightarrow> lfp (efficacy_step C D f) = C"
    using wf by (simp only: every_total_mechanism_iff_well_founded)
  show "\<forall>f. mechanism_on C D f \<longrightarrow> (\<exists>!X. efficacy_step C D f X = X)"
  proof (intro allI impI)
    fix f
    assume admissible: "mechanism_on C D f"
    have total: "lfp (efficacy_step C D f) = C"
      by (rule all[rule_format, OF admissible])
    show "\<exists>!X. efficacy_step C D f X = X"
      by (rule iffD1[OF total_lfp_iff_unique_fixed_point[OF admissible] total])
  qed
qed

section \<open>Indispensability fixes conjunctive aggregation\<close>

definition all_on_indispensable_on where
  "all_on_indispensable_on C D f \<longleftrightarrow>
    (\<forall>x \<in> C. \<forall>y \<in> efficacy_parents C D x.
      \<not> f x (efficacy_parents C D x - {y}))"

lemma all_on_indispensability_forces_and:
  assumes admissible: "mechanism_on C D f"
    and indispensable: "all_on_indispensable_on C D f"
  shows "efficacy_step C D f = and_step C D"
proof (rule ext, rule subset_antisym)
  fix X
  show "efficacy_step C D f X \<subseteq> and_step C D X"
  proof (rule subsetI)
    fix x
    assume xin: "x \<in> efficacy_step C D f X"
    then have xC: "x \<in> C" and active: "f x (X \<inter> efficacy_parents C D x)"
      by (auto simp: efficacy_step_def)
    have parents: "efficacy_parents C D x \<subseteq> X"
    proof (rule ccontr)
      assume "\<not> efficacy_parents C D x \<subseteq> X"
      then obtain y where yP: "y \<in> efficacy_parents C D x" and yX: "y \<notin> X"
        by blast
      have sub: "X \<inter> efficacy_parents C D x \<subseteq> efficacy_parents C D x - {y}"
        using yX by blast
      have mono: "mono (f x)"
        using admissible xC by (auto simp: mechanism_on_def)
      have "f x (efficacy_parents C D x - {y})"
        using monoD[OF mono sub] active by simp
      then show False
        using indispensable xC yP by (auto simp: all_on_indispensable_on_def)
    qed
    show "x \<in> and_step C D X"
      using xC parents by (simp add: and_step_def)
  qed
  show "and_step C D X \<subseteq> efficacy_step C D f X"
    by (rule mechanism_extremal_bounds[OF admissible])
qed

theorem indispensable_total_efficacy_iff_well_founded:
  assumes "mechanism_on C D f" and "all_on_indispensable_on C D f"
  shows "lfp (efficacy_step C D f) = C \<longleftrightarrow> well_founded_on C D"
  by (simp add: all_on_indispensability_forces_and[OF assms]
    lfp_and_eq_carrier_iff_well_founded)

section \<open>Acyclic rooted spine with two relevant aggregation policies\<close>

datatype efficacy_spine = Source | Link nat

definition spine_dependency where
  "spine_dependency x y \<longleftrightarrow>
    (x = Source \<and> (\<exists>n. y = Link n)) \<or>
    (\<exists>n. x = Link (Suc n) \<and> y = Link n)"

lemma spine_source_parents [simp]:
  "efficacy_parents UNIV spine_dependency Source = {}"
  by (auto simp: efficacy_parents_def spine_dependency_def)

lemma spine_link_parents [simp]:
  "efficacy_parents UNIV spine_dependency (Link n) = {Source, Link (Suc n)}"
  by (auto simp: efficacy_parents_def spine_dependency_def)

lemma spine_and_source_fixed:
  "and_step UNIV spine_dependency {Source} = {Source}"
  unfolding and_step_def by (rule set_eqI, case_tac x) auto

lemma spine_or_source_total:
  "or_step UNIV spine_dependency {Source} = UNIV"
  unfolding or_step_def by (rule set_eqI, case_tac x) auto

lemma spine_lfp_and:
  "lfp (and_step UNIV spine_dependency) = {Source}"
proof (rule subset_antisym)
  show "lfp (and_step UNIV spine_dependency) \<subseteq> {Source}"
    by (rule lfp_lowerbound) (simp add: spine_and_source_fixed)
  have "Source \<in> and_step UNIV spine_dependency
      (lfp (and_step UNIV spine_dependency))"
    by (simp add: and_step_def)
  then show "{Source} \<subseteq> lfp (and_step UNIV spine_dependency)"
    using lfp_unfold[OF mono_and_step[of UNIV spine_dependency]] by auto
qed

lemma spine_lfp_or:
  "lfp (or_step UNIV spine_dependency) = UNIV"
proof -
  have eq: "lfp (or_step UNIV spine_dependency) =
      or_step UNIV spine_dependency (lfp (or_step UNIV spine_dependency))"
    by (rule lfp_unfold[OF mono_or_step])
  have "Source \<in> or_step UNIV spine_dependency
      (lfp (or_step UNIV spine_dependency))"
    by (simp add: or_step_def)
  then have sub: "{Source} \<subseteq> lfp (or_step UNIV spine_dependency)"
    using eq by auto
  have "or_step UNIV spine_dependency {Source} \<subseteq>
      or_step UNIV spine_dependency (lfp (or_step UNIV spine_dependency))"
    by (rule monoD[OF mono_or_step sub])
  then show ?thesis using eq spine_or_source_total by blast
qed

lemma spine_trancl_shape:
  assumes "spine_dependency\<^sup>+\<^sup>+ x y"
  shows "(x = Source \<and> y \<noteq> Source) \<or>
    (\<exists>n m. x = Link n \<and> y = Link m \<and> m < n)"
  using assms
proof (induction rule: tranclp_induct)
  case base
  then show ?case by (auto simp: spine_dependency_def)
next
  case step
  then show ?case by (auto simp: spine_dependency_def; arith)
qed

lemma spine_acyclic:
  "acyclic_on UNIV spine_dependency"
proof -
  have eq: "dependency_on UNIV spine_dependency = spine_dependency"
    by (rule ext, rule ext) (simp add: dependency_on_def)
  show ?thesis
    unfolding acyclic_on_def eq using spine_trancl_shape by blast
qed

lemma spine_not_chain_terminating:
  "\<not> chain_terminating_on UNIV spine_dependency"
  unfolding chain_terminating_on_def
  by (intro notI, erule notE, rule exI[of _ Link])
    (simp add: dependency_on_def spine_dependency_def)

theorem rooted_spine_mechanism_separation:
  "acyclic_on UNIV spine_dependency \<and>
    local_foundation_on UNIV spine_dependency UNIV \<and>
    \<not> well_founded_on UNIV spine_dependency \<and>
    lfp (efficacy_step UNIV spine_dependency
      (or_mechanism UNIV spine_dependency)) = UNIV \<and>
    lfp (efficacy_step UNIV spine_dependency
      (and_mechanism UNIV spine_dependency)) = {Source} \<and>
    edge_relevant_on UNIV spine_dependency (or_mechanism UNIV spine_dependency) \<and>
    edge_relevant_on UNIV spine_dependency (and_mechanism UNIV spine_dependency)"
  using spine_acyclic spine_lfp_or spine_lfp_and
    lfp_or_eq_carrier_iff_local_foundation[of UNIV spine_dependency]
    well_founded_iff_chain_terminating[of UNIV spine_dependency]
    spine_not_chain_terminating
    and_mechanism_relevant[of UNIV spine_dependency]
    or_mechanism_relevant[of UNIV spine_dependency]
  by (simp add: and_mechanism_step or_mechanism_step)

section \<open>Source-free nonconstant copying\<close>

definition copying_dependency :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where "copying_dependency y x \<longleftrightarrow> y = Suc x"

lemma copying_parents [simp]:
  "efficacy_parents UNIV copying_dependency n = {Suc n}"
  by (auto simp: efficacy_parents_def copying_dependency_def)

lemma copying_and_or_equal:
  "and_step UNIV copying_dependency = or_step UNIV copying_dependency"
  unfolding and_step_def or_step_def by (rule ext) auto

lemma copying_lfp_empty:
  "lfp (or_step UNIV copying_dependency) = {}"
  by (rule equalityI, rule lfp_lowerbound) (auto simp: or_step_def)

lemma copying_all_on_indispensable:
  "all_on_indispensable_on UNIV copying_dependency (or_mechanism UNIV copying_dependency)"
  by (auto simp: all_on_indispensable_on_def or_mechanism_def)

lemma copying_trancl_less:
  assumes "copying_dependency\<^sup>+\<^sup>+ x y"
  shows "y < x"
  using assms
proof (induction rule: tranclp_induct)
  case base
  then show ?case by (auto simp: copying_dependency_def)
next
  case step
  then show ?case by (auto simp: copying_dependency_def; arith)
qed

lemma copying_acyclic:
  "acyclic_on UNIV copying_dependency"
proof -
  have eq: "dependency_on UNIV copying_dependency = copying_dependency"
    by (rule ext, rule ext) (simp add: dependency_on_def)
  show ?thesis
    unfolding acyclic_on_def eq using copying_trancl_less by blast
qed

theorem copying_local_consistency_not_source_generation:
  "acyclic_on UNIV copying_dependency \<and>
    mechanism_on UNIV copying_dependency (or_mechanism UNIV copying_dependency) \<and>
    all_on_indispensable_on UNIV copying_dependency (or_mechanism UNIV copying_dependency) \<and>
    edge_relevant_on UNIV copying_dependency (or_mechanism UNIV copying_dependency) \<and>
    efficacy_step UNIV copying_dependency (or_mechanism UNIV copying_dependency) UNIV = UNIV \<and>
    lfp (efficacy_step UNIV copying_dependency (or_mechanism UNIV copying_dependency)) = {}"
  using copying_acyclic copying_all_on_indispensable
    or_mechanism_admissible[of UNIV copying_dependency]
    or_mechanism_relevant[of UNIV copying_dependency]
    all_active_is_fixed[OF or_mechanism_admissible[of UNIV copying_dependency]]
    copying_lfp_empty
  by (simp add: or_mechanism_step)

end
