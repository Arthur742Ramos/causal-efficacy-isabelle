theory Causal_Efficacy_Revision_Extras
  imports "Causal_Efficacy_Ancestors.Target_Ancestral_Cone"
begin

section \<open>Single-parent collapse\<close>

definition single_parent_on where
  "single_parent_on C D \<longleftrightarrow>
    (\<forall>x \<in> C. \<forall>y \<in> efficacy_parents C D x.
      \<forall>z \<in> efficacy_parents C D x. y = z)"

lemma single_parent_and_or_equal:
  assumes "single_parent_on C D"
  shows "and_step C D = or_step C D"
  using assms unfolding single_parent_on_def and_step_def or_step_def
  by (intro ext set_eqI) (auto; metis)

lemma single_parent_mechanism_coincides:
  assumes single: "single_parent_on C D" and admissible: "mechanism_on C D f"
  shows "efficacy_step C D f = and_step C D"
proof (rule ext, rule subset_antisym)
  fix X
  show "efficacy_step C D f X \<subseteq> and_step C D X"
    using mechanism_extremal_bounds(2)[OF admissible, of X]
    by (simp only: single_parent_and_or_equal[OF single])
  show "and_step C D X \<subseteq> efficacy_step C D f X"
    by (rule mechanism_extremal_bounds(1)[OF admissible])
qed

theorem single_parent_foundation_iff_well_founded:
  assumes "single_parent_on C D"
  shows "local_foundation_on C D C \<longleftrightarrow> well_founded_on C D"
  using lfp_or_eq_carrier_iff_local_foundation[of C D]
    lfp_and_eq_carrier_iff_well_founded[of C D]
  by (simp only: single_parent_and_or_equal[OF assms])

section \<open>Source-generated observations and roots\<close>

lemma source_generated_target_has_root_ancestor:
  assumes admissible: "mechanism_on C D f"
    and active: "a \<in> lfp (efficacy_step C D f)"
  shows "\<exists>b. first_member_in C D b a"
proof -
  have "a \<in> lfp (or_step C D)"
    using efficacy_lfp_sandwich(2)[OF admissible] active by blast
  then show ?thesis
    by (simp add: lfp_or_eq_root_reachable root_reachable_def)
qed

theorem nonempty_source_generated_targets_have_root:
  assumes admissible: "mechanism_on C D f"
    and nonempty: "T \<noteq> {}"
    and active: "T \<subseteq> lfp (efficacy_step C D f)"
  shows "\<exists>b \<in> C. independent_in C D b"
proof -
  obtain a where aT: "a \<in> T" using nonempty by blast
  have aactive: "a \<in> lfp (efficacy_step C D f)" using active aT by blast
  obtain b where "first_member_in C D b a"
    using source_generated_target_has_root_ancestor[OF admissible aactive] by blast
  then show ?thesis
    by (auto simp: first_member_in_def independent_in_def)
qed

theorem dependent_source_generated_target_has_distinct_root:
  assumes admissible: "mechanism_on C D f"
    and active: "a \<in> lfp (efficacy_step C D f)"
    and dependent: "grounded_in C D a"
  shows "\<exists>b. first_cause_in C D b a"
proof -
  obtain b where first: "first_member_in C D b a"
    using source_generated_target_has_root_ancestor[OF admissible active] by blast
  have independent: "independent_in C D b"
    using first by (simp add: first_member_in_def)
  have distinct: "b \<noteq> a"
    using independent grounded_not_independent[OF dependent] by blast
  show ?thesis
    using first distinct by (auto simp: first_cause_in_def)
qed

section \<open>Copying: observational versus unconditional uniqueness\<close>

lemma copying_step_membership:
  "n \<in> efficacy_step UNIV copying_dependency (or_mechanism UNIV copying_dependency) X
    \<longleftrightarrow> Suc n \<in> X"
  by (simp add: or_mechanism_step or_step_def)

theorem copying_fixed_points_exact:
  "efficacy_step UNIV copying_dependency (or_mechanism UNIV copying_dependency) X = X
    \<longleftrightarrow> X = {} \<or> X = UNIV"
proof
  assume fixed: "efficacy_step UNIV copying_dependency (or_mechanism UNIV copying_dependency) X = X"
  have adjacent: "\<And>n. (n \<in> X) = (Suc n \<in> X)"
  proof -
    fix n
    have "(n \<in> X) = (n \<in> efficacy_step UNIV copying_dependency
        (or_mechanism UNIV copying_dependency) X)"
      by (simp only: fixed)
    then show "(n \<in> X) = (Suc n \<in> X)"
      by (simp only: copying_step_membership)
  qed
  have uniform_membership: "\<And>n. (n \<in> X) = (0 \<in> X)"
  proof -
    fix n
    show "(n \<in> X) = (0 \<in> X)"
    proof (induction n)
      case 0
      then show ?case by simp
    next
      case (Suc n)
      then show ?case using adjacent[of n] by blast
    qed
  qed
  show "X = {} \<or> X = UNIV"
    using uniform_membership by auto
next
  assume cases: "X = {} \<or> X = UNIV"
  show "efficacy_step UNIV copying_dependency (or_mechanism UNIV copying_dependency) X = X"
  proof (rule set_eqI)
    fix n
    show "(n \<in> efficacy_step UNIV copying_dependency (or_mechanism UNIV copying_dependency) X) = (n \<in> X)"
      using cases by (simp only: copying_step_membership) auto
  qed
qed

theorem copying_observed_fixed_point_exact:
  "(efficacy_step UNIV copying_dependency (or_mechanism UNIV copying_dependency) X = X
      \<and> (0 :: nat) \<in> X) \<longleftrightarrow> X = UNIV"
  by (auto simp: copying_fixed_points_exact)

theorem copying_observation_conditioned_unique:
  "\<exists>!X. efficacy_step UNIV copying_dependency (or_mechanism UNIV copying_dependency) X = X
      \<and> (0 :: nat) \<in> X"
  by (simp only: copying_observed_fixed_point_exact) auto

lemma copying_no_root:
  "\<not> (\<exists>x. independent_in UNIV copying_dependency x)"
  by (simp add: independent_in_def copying_dependency_def)

theorem copying_not_unconditionally_unique:
  "\<not> (\<exists>!X. efficacy_step UNIV copying_dependency
    (or_mechanism UNIV copying_dependency) X = X)"
  by (simp only: copying_fixed_points_exact) auto

section \<open>Switching root boundary values off without changing the graph\<close>

text \<open>
  This comparison keeps C and D fixed, and leaves each nonroot mechanism
  unchanged. It switches only the root boundary value from active to inactive.
  Where roots exist this operator lies outside the normalized mechanism class.
  No vertex or edge is deleted.
\<close>

definition source_off_step where
  "source_off_step C D f X = {x \<in> C. efficacy_parents C D x \<noteq> {} \<and>
    f x (X \<inter> efficacy_parents C D x)}"

lemma source_off_as_restriction:
  "source_off_step C D f X = efficacy_step C D f X \<inter>
    {x \<in> C. efficacy_parents C D x \<noteq> {}}"
  by (auto simp: source_off_step_def efficacy_step_def)

lemma source_off_nonroot_unchanged:
  assumes "efficacy_parents C D x \<noteq> {}"
  shows "x \<in> source_off_step C D f X \<longleftrightarrow> x \<in> efficacy_step C D f X"
  using assms by (simp add: source_off_step_def efficacy_step_def)

lemma source_off_root_inactive:
  assumes "independent_in C D x"
  shows "x \<notin> source_off_step C D f X"
  using assms by (auto simp: source_off_step_def efficacy_parents_def independent_in_def)

lemma mono_source_off_step:
  fixes C :: "'a set"
  assumes admissible: "mechanism_on C D f"
  shows "mono (source_off_step C D f)"
proof (rule monoI)
  fix X Y :: "'a set"
  assume "X \<subseteq> Y"
  then have "efficacy_step C D f X \<subseteq> efficacy_step C D f Y"
    by (rule monoD[OF mono_efficacy_step[OF admissible]])
  then show "source_off_step C D f X \<subseteq> source_off_step C D f Y"
    by (auto simp only: source_off_as_restriction)
qed

lemma source_off_empty_fixed:
  assumes "mechanism_on C D f"
  shows "source_off_step C D f {} = {}"
  using assms by (auto simp: source_off_step_def mechanism_on_def)

theorem source_off_least_efficacy_empty:
  assumes "mechanism_on C D f"
  shows "lfp (source_off_step C D f) = {}"
  by (rule equalityI, rule lfp_lowerbound)
    (simp add: source_off_empty_fixed[OF assms], simp)

end
