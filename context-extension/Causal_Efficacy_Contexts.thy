theory Causal_Efficacy_Contexts
  imports "Causal_Efficacy_Revision.Causal_Efficacy_Revision_Extras"
begin

section \<open>Root contexts on a fixed dependency structure\<close>

definition efficacy_roots where
  "efficacy_roots C D = {x \<in> C. efficacy_parents C D x = {}}"

definition contextual_step where
  "contextual_step C D f U X = U \<union> source_off_step C D f X"

definition context_determinate where
  "context_determinate C D f \<longleftrightarrow>
    (\<forall>U \<subseteq> efficacy_roots C D. \<exists>!X. contextual_step C D f U X = X)"

lemma efficacy_roots_subset_carrier:
  "efficacy_roots C D \<subseteq> C"
  by (auto simp: efficacy_roots_def)

lemma mono_contextual_step:
  fixes C :: "'a set"
  assumes admissible: "mechanism_on C D f"
  shows "mono (contextual_step C D f U)"
proof (rule monoI)
  fix X Y :: "'a set"
  assume "X \<subseteq> Y"
  then have "source_off_step C D f X \<subseteq> source_off_step C D f Y"
    by (rule monoD[OF mono_source_off_step[OF admissible]])
  then show "contextual_step C D f U X \<subseteq> contextual_step C D f U Y"
    by (auto simp: contextual_step_def)
qed

lemma contextual_step_subset_carrier:
  assumes "U \<subseteq> efficacy_roots C D"
  shows "contextual_step C D f U X \<subseteq> C"
  using assms by (auto simp: contextual_step_def source_off_step_def efficacy_roots_def)

lemma contextual_fixed_subset_carrier:
  assumes ctx: "U \<subseteq> efficacy_roots C D"
    and fixed: "contextual_step C D f U X = X"
  shows "X \<subseteq> C"
  using contextual_step_subset_carrier[OF ctx, of f X] fixed by simp

theorem contextual_solution_exists:
  assumes admissible: "mechanism_on C D f"
    and ctx: "U \<subseteq> efficacy_roots C D"
  shows "\<exists>X \<subseteq> C. contextual_step C D f U X = X"
proof -
  have fixed: "contextual_step C D f U (lfp (contextual_step C D f U)) =
      lfp (contextual_step C D f U)"
    using lfp_unfold[OF mono_contextual_step[OF admissible, of U]] by simp
  have sub: "lfp (contextual_step C D f U) \<subseteq> C"
    by (rule lfp_lowerbound, rule contextual_step_subset_carrier[OF ctx])
  show ?thesis
    by (intro exI[of _ "lfp (contextual_step C D f U)"] conjI) (fact sub, fact fixed)
qed

lemma all_roots_context_is_original:
  assumes "mechanism_on C D f"
  shows "contextual_step C D f (efficacy_roots C D) = efficacy_step C D f"
  using assms unfolding contextual_step_def source_off_step_def efficacy_roots_def
    efficacy_step_def mechanism_on_def
  by (intro ext set_eqI) auto

lemma empty_context_empty_fixed:
  assumes "mechanism_on C D f"
  shows "contextual_step C D f {} {} = {}"
  by (simp add: contextual_step_def source_off_empty_fixed[OF assms])

section \<open>Well-foundedness and uniform contextual uniqueness\<close>

lemma well_founded_contextual_solutions_equal:
  assumes wf: "well_founded_on C D"
    and ctx: "U \<subseteq> efficacy_roots C D"
    and fixedX: "contextual_step C D f U X = X"
    and fixedY: "contextual_step C D f U Y = Y"
  shows "X = Y"
proof -
  have XC: "X \<subseteq> C" by (rule contextual_fixed_subset_carrier[OF ctx fixedX])
  have YC: "Y \<subseteq> C" by (rule contextual_fixed_subset_carrier[OF ctx fixedY])
  have wf_pred: "wfp_on C (dependency_on C D)"
    using wf by (simp add: well_founded_on_def)
  have equal_in: "\<And>x. x \<in> C \<Longrightarrow> (x \<in> X) = (x \<in> Y)"
  proof -
    fix x
    assume xC: "x \<in> C"
    show "(x \<in> X) = (x \<in> Y)"
    proof (rule wfp_on_induct[OF wf_pred xC])
      fix x
      assume xC: "x \<in> C"
        and IH: "\<And>y. y \<in> C \<Longrightarrow> dependency_on C D y x \<Longrightarrow>
          (y \<in> X) = (y \<in> Y)"
      have inputs: "X \<inter> efficacy_parents C D x = Y \<inter> efficacy_parents C D x"
      proof (rule set_eqI)
        fix y
        show "(y \<in> X \<inter> efficacy_parents C D x) = (y \<in> Y \<inter> efficacy_parents C D x)"
        proof (cases "y \<in> efficacy_parents C D x")
          case True
          then have yC: "y \<in> C" and D: "D y x"
            by (auto simp: efficacy_parents_def)
          have edge: "dependency_on C D y x"
            using yC xC D by (simp add: dependency_on_def)
          show ?thesis using IH[OF yC edge] by simp
        next
          case False
          then show ?thesis by simp
        qed
      qed
      have "(x \<in> X) = (x \<in> contextual_step C D f U X)"
        by (simp only: fixedX)
      also have "... = (x \<in> contextual_step C D f U Y)"
        by (simp add: contextual_step_def source_off_step_def inputs)
      also have "... = (x \<in> Y)" by (simp only: fixedY)
      finally show "(x \<in> X) = (x \<in> Y)" .
    qed
  qed
  show ?thesis using XC YC equal_in by auto
qed

theorem well_founded_contextual_unique:
  assumes wf: "well_founded_on C D"
    and admissible: "mechanism_on C D f"
    and ctx: "U \<subseteq> efficacy_roots C D"
  shows "\<exists>!X. contextual_step C D f U X = X"
proof -
  obtain X where fixed: "contextual_step C D f U X = X"
    using contextual_solution_exists[OF admissible ctx] by blast
  show ?thesis
  proof (rule ex1I[of _ X])
    show "contextual_step C D f U X = X" by (fact fixed)
    fix Y
    assume "contextual_step C D f U Y = Y"
    then show "Y = X"
      by (rule well_founded_contextual_solutions_equal[OF wf ctx _ fixed])
  qed
qed

lemma well_founded_mechanism_context_determinate:
  assumes "well_founded_on C D" "mechanism_on C D f"
  shows "context_determinate C D f"
  unfolding context_determinate_def
  by (intro allI impI, rule well_founded_contextual_unique[OF assms]) assumption

lemma conjunctive_context_determinate_implies_well_founded:
  assumes "context_determinate C D (and_mechanism C D)"
  shows "well_founded_on C D"
proof -
  have unique_context: "\<exists>!X. contextual_step C D (and_mechanism C D)
      (efficacy_roots C D) X = X"
    using assms by (simp add: context_determinate_def)
  have unique_original: "\<exists>!X. efficacy_step C D (and_mechanism C D) X = X"
    using unique_context
    by (simp only: all_roots_context_is_original[OF and_mechanism_admissible])
  have total: "lfp (efficacy_step C D (and_mechanism C D)) = C"
    by (rule iffD2[OF total_lfp_iff_unique_fixed_point[OF and_mechanism_admissible] unique_original])
  show ?thesis
    using total by (simp add: and_mechanism_step lfp_and_eq_carrier_iff_well_founded)
qed

theorem every_mechanism_every_context_unique_iff_well_founded:
  "(\<forall>f. mechanism_on C D f \<longrightarrow> context_determinate C D f)
    \<longleftrightarrow> well_founded_on C D"
proof
  assume all: "\<forall>f. mechanism_on C D f \<longrightarrow> context_determinate C D f"
  have "context_determinate C D (and_mechanism C D)"
    using all and_mechanism_admissible[of C D] by blast
  then show "well_founded_on C D"
    by (rule conjunctive_context_determinate_implies_well_founded)
next
  assume "well_founded_on C D"
  then show "\<forall>f. mechanism_on C D f \<longrightarrow> context_determinate C D f"
    using well_founded_mechanism_context_determinate[of C D] by blast
qed

theorem every_relevant_mechanism_every_context_unique_iff_well_founded:
  "(\<forall>f. mechanism_on C D f \<and> edge_relevant_on C D f \<longrightarrow>
      context_determinate C D f) \<longleftrightarrow> well_founded_on C D"
proof
  assume all: "\<forall>f. mechanism_on C D f \<and> edge_relevant_on C D f \<longrightarrow>
      context_determinate C D f"
  have "context_determinate C D (and_mechanism C D)"
    using all and_mechanism_admissible[of C D] and_mechanism_relevant[of C D] by blast
  then show "well_founded_on C D"
    by (rule conjunctive_context_determinate_implies_well_founded)
next
  assume "well_founded_on C D"
  then show "\<forall>f. mechanism_on C D f \<and> edge_relevant_on C D f \<longrightarrow>
      context_determinate C D f"
    using well_founded_mechanism_context_determinate[of C D] by blast
qed

section \<open>One mechanism may be determinate in every ctx without well-foundedness\<close>

definition alternating_spine_mechanism where
  "alternating_spine_mechanism x S \<longleftrightarrow>
    (case x of Source \<Rightarrow> True | Link n \<Rightarrow>
      if even n then (Source \<in> S \<or> Link (Suc n) \<in> S)
      else (Source \<in> S \<and> Link (Suc n) \<in> S))"

lemma alternating_spine_admissible:
  "mechanism_on UNIV spine_dependency alternating_spine_mechanism"
  unfolding mechanism_on_def
  by (intro ballI, case_tac x)
    (auto simp: alternating_spine_mechanism_def mono_def)

lemma alternating_spine_relevant:
  "edge_relevant_on UNIV spine_dependency alternating_spine_mechanism"
  unfolding edge_relevant_on_def
proof (intro ballI)
  fix x y
  assume "x \<in> UNIV" and yP: "y \<in> efficacy_parents UNIV spine_dependency x"
  show "\<exists>S \<subseteq> efficacy_parents UNIV spine_dependency x - {y}.
    \<not> alternating_spine_mechanism x S \<and> alternating_spine_mechanism x (insert y S)"
  proof (cases x)
    case Source
    then show ?thesis using yP by simp
  next
    case (Link n)
    show ?thesis
    proof (cases "even n")
      case True
      show ?thesis
        using yP Link True by (intro exI[of _ "{}"])
          (auto simp: alternating_spine_mechanism_def)
    next
      case False
      show ?thesis
        using yP Link False
        by (intro exI[of _ "efficacy_parents UNIV spine_dependency x - {y}"])
          (auto simp: alternating_spine_mechanism_def)
    qed
  qed
qed

lemma spine_roots_exact:
  "efficacy_roots UNIV spine_dependency = {Source}"
  unfolding efficacy_roots_def by (rule set_eqI, case_tac x) auto

lemma alternating_context_source_membership:
  "Source \<in> contextual_step UNIV spine_dependency alternating_spine_mechanism U X
    \<longleftrightarrow> Source \<in> U"
  by (simp add: contextual_step_def source_off_step_def)

lemma alternating_context_link_membership:
  assumes "U \<subseteq> efficacy_roots UNIV spine_dependency"
  shows "Link n \<in> contextual_step UNIV spine_dependency alternating_spine_mechanism U X
    \<longleftrightarrow> (if even n then (Source \<in> X \<or> Link (Suc n) \<in> X)
      else (Source \<in> X \<and> Link (Suc n) \<in> X))"
  using assms by (auto simp: contextual_step_def source_off_step_def spine_roots_exact
    alternating_spine_mechanism_def)

lemma alternating_spine_fixed_is_boundary:
  assumes ctx: "U \<subseteq> efficacy_roots UNIV spine_dependency"
    and fixed: "contextual_step UNIV spine_dependency alternating_spine_mechanism U X = X"
  shows "X = (if Source \<in> U then UNIV else {})"
proof -
  have root: "(Source \<in> X) = (Source \<in> U)"
    using alternating_context_source_membership[of U X] by (simp only: fixed)
  have links: "\<And>n. (Link n \<in> X) =
      (if even n then (Source \<in> X \<or> Link (Suc n) \<in> X)
      else (Source \<in> X \<and> Link (Suc n) \<in> X))"
  proof -
    fix n
    have "(Link n \<in> X) = (Link n \<in> contextual_step UNIV spine_dependency
        alternating_spine_mechanism U X)" by (simp only: fixed)
    also have "... = (if even n then (Source \<in> X \<or> Link (Suc n) \<in> X)
      else (Source \<in> X \<and> Link (Suc n) \<in> X))"
      by (rule alternating_context_link_membership[OF ctx])
    finally show "(Link n \<in> X) = (if even n then (Source \<in> X \<or> Link (Suc n) \<in> X)
      else (Source \<in> X \<and> Link (Suc n) \<in> X))" .
  qed
  have link_value: "\<And>n. (Link n \<in> X) = (Source \<in> U)"
  proof -
    fix n
    show "(Link n \<in> X) = (Source \<in> U)"
      using links[of n] links[of "Suc n"] root
      by (cases "even n") auto
  qed
  show ?thesis
  proof (rule set_eqI)
    fix x
    show "(x \<in> X) = (x \<in> (if Source \<in> U then UNIV else {}))"
      using root link_value by (cases x) auto
  qed
qed

theorem alternating_spine_context_fixed_points_exact:
  assumes ctx: "U \<subseteq> efficacy_roots UNIV spine_dependency"
  shows "contextual_step UNIV spine_dependency alternating_spine_mechanism U X = X
    \<longleftrightarrow> X = (if Source \<in> U then UNIV else {})"
proof
  assume "contextual_step UNIV spine_dependency alternating_spine_mechanism U X = X"
  then show "X = (if Source \<in> U then UNIV else {})"
    by (rule alternating_spine_fixed_is_boundary[OF ctx])
next
  assume X: "X = (if Source \<in> U then UNIV else {})"
  obtain Y where fixed: "contextual_step UNIV spine_dependency alternating_spine_mechanism U Y = Y"
    using contextual_solution_exists[OF alternating_spine_admissible ctx] by blast
  have Y: "Y = (if Source \<in> U then UNIV else {})"
    by (rule alternating_spine_fixed_is_boundary[OF ctx fixed])
  show "contextual_step UNIV spine_dependency alternating_spine_mechanism U X = X"
    using fixed X Y by simp
qed

lemma alternating_spine_context_determinate:
  "context_determinate UNIV spine_dependency alternating_spine_mechanism"
  unfolding context_determinate_def
proof (intro allI impI)
  fix U
  assume ctx: "U \<subseteq> efficacy_roots UNIV spine_dependency"
  show "\<exists>!X. contextual_step UNIV spine_dependency alternating_spine_mechanism U X = X"
    by (simp only: alternating_spine_context_fixed_points_exact[OF ctx]) auto
qed

theorem some_relevant_mechanism_every_context_without_well_foundedness:
  "acyclic_on UNIV spine_dependency \<and>
    \<not> well_founded_on UNIV spine_dependency \<and>
    (\<exists>f. mechanism_on UNIV spine_dependency f \<and>
      edge_relevant_on UNIV spine_dependency f \<and>
      context_determinate UNIV spine_dependency f)"
proof (intro conjI)
  show "acyclic_on UNIV spine_dependency" by (rule spine_acyclic)
  show "\<not> well_founded_on UNIV spine_dependency"
    using spine_not_chain_terminating
    by (simp add: well_founded_iff_chain_terminating)
  show "\<exists>f. mechanism_on UNIV spine_dependency f \<and>
      edge_relevant_on UNIV spine_dependency f \<and>
      context_determinate UNIV spine_dependency f"
    by (intro exI[of _ alternating_spine_mechanism] conjI)
      (fact alternating_spine_admissible, fact alternating_spine_relevant,
       fact alternating_spine_context_determinate)
qed

end
