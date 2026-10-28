theory Target_Ancestral_Cone
  imports "Causal_Efficacy_Extension.Causal_Efficacy_Mechanisms"
begin

section \<open>Target-relative well-foundedness\<close>

text \<open>
  The cone includes each target itself, provided that the target belongs to
  the carrier. Its predecessor closure permits a target-relative refinement
  of the checked mechanism-robustness theorem. Unrelated components of the
  dependency structure do not enter this condition.
\<close>

definition ancestor_cone ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set"
where
  "ancestor_cone C D T = {x \<in> C. \<exists>t \<in> T. dependency_ancestor C D x t}"

lemma ancestor_cone_subset_carrier:
  "ancestor_cone C D T \<subseteq> C"
  by (auto simp: ancestor_cone_def)

lemma targets_in_ancestor_cone:
  assumes "T \<subseteq> C"
  shows "T \<subseteq> ancestor_cone C D T"
  using assms by (auto simp: ancestor_cone_def dependency_ancestor_def)

lemma ancestor_cone_predecessor_closed:
  assumes xcone: "x \<in> ancestor_cone C D T"
    and edge: "dependency_on C D y x"
  shows "y \<in> ancestor_cone C D T"
proof -
  obtain t where tT: "t \<in> T" and xt: "dependency_ancestor C D x t"
    using xcone by (auto simp: ancestor_cone_def)
  have yC: "y \<in> C" and xC: "x \<in> C" and D: "D y x"
    using edge by (auto simp: dependency_on_def)
  have yx: "dependency_ancestor C D y x"
    using yC xC D by (rule dependency_ancestor_direct)
  have "dependency_ancestor C D y t"
    using yx xt by (rule dependency_ancestor_trans)
  then show ?thesis
    using yC tT by (auto simp: ancestor_cone_def)
qed

lemma ancestor_cone_accessibility_downward:
  assumes targets: "T \<subseteq> {x \<in> C. Wellfounded.accp (dependency_on C D) x}"
  shows "ancestor_cone C D T \<subseteq> {x \<in> C. Wellfounded.accp (dependency_on C D) x}"
proof (rule subsetI)
  fix x
  assume xcone: "x \<in> ancestor_cone C D T"
  then obtain t where tT: "t \<in> T" and xC: "x \<in> C"
    and path: "(dependency_on C D)\<^sup>*\<^sup>* x t"
    by (auto simp: ancestor_cone_def dependency_ancestor_def)
  have tacc: "Wellfounded.accp (dependency_on C D) t"
    using targets tT by auto
  have "Wellfounded.accp (dependency_on C D) x"
    using tacc path by (rule accp_downwards)
  then show "x \<in> {x \<in> C. Wellfounded.accp (dependency_on C D) x}"
    using xC by simp
qed

lemma well_founded_on_iff_accessible_members:
  "well_founded_on C D \<longleftrightarrow>
    (\<forall>x \<in> C. Wellfounded.accp (dependency_on C D) x)"
  using lfp_and_eq_carrier_iff_well_founded[of C D]
    lfp_and_eq_accessible[of C D] by auto

theorem target_accessibility_iff_ancestral_well_founded:
  assumes targets_carrier: "T \<subseteq> C"
  shows "T \<subseteq> {x \<in> C. Wellfounded.accp (dependency_on C D) x}
    \<longleftrightarrow> well_founded_on (ancestor_cone C D T) D"
proof
  assume target_acc: "T \<subseteq> {x \<in> C. Wellfounded.accp (dependency_on C D) x}"
  have cone_acc: "ancestor_cone C D T \<subseteq>
      {x \<in> C. Wellfounded.accp (dependency_on C D) x}"
    by (rule ancestor_cone_accessibility_downward[OF target_acc])
  have relation_sub: "dependency_on (ancestor_cone C D T) D \<le> dependency_on C D"
    by (auto simp: le_fun_def dependency_on_def ancestor_cone_def)
  have acc_sub: "Wellfounded.accp (dependency_on C D) \<le>
      Wellfounded.accp (dependency_on (ancestor_cone C D T) D)"
    by (rule accp_subset[OF relation_sub])
  have "\<forall>x \<in> ancestor_cone C D T.
      Wellfounded.accp (dependency_on (ancestor_cone C D T) D) x"
    using cone_acc acc_sub by (auto simp: le_fun_def)
  then show "well_founded_on (ancestor_cone C D T) D"
    by (simp only: well_founded_on_iff_accessible_members)
next
  assume wf: "well_founded_on (ancestor_cone C D T) D"
  have wf_pred: "wfp_on (ancestor_cone C D T) (dependency_on (ancestor_cone C D T) D)"
    using wf by (simp add: well_founded_on_def)
  have cone_acc: "\<And>x. x \<in> ancestor_cone C D T \<Longrightarrow>
      Wellfounded.accp (dependency_on C D) x"
  proof -
    fix x
    assume xcone: "x \<in> ancestor_cone C D T"
    show "Wellfounded.accp (dependency_on C D) x"
    proof (rule wfp_on_induct[OF wf_pred xcone])
      fix x
      assume xcone: "x \<in> ancestor_cone C D T"
        and IH: "\<And>y. y \<in> ancestor_cone C D T \<Longrightarrow>
          dependency_on (ancestor_cone C D T) D y x \<Longrightarrow>
          Wellfounded.accp (dependency_on C D) y"
      show "Wellfounded.accp (dependency_on C D) x"
      proof (rule accp.accI)
        fix y
        assume edge: "dependency_on C D y x"
        have ycone: "y \<in> ancestor_cone C D T"
          by (rule ancestor_cone_predecessor_closed[OF xcone edge])
        have restricted: "dependency_on (ancestor_cone C D T) D y x"
          using xcone ycone edge by (auto simp: dependency_on_def)
        show "Wellfounded.accp (dependency_on C D) y"
          by (rule IH[OF ycone restricted])
      qed
    qed
  qed
  show "T \<subseteq> {x \<in> C. Wellfounded.accp (dependency_on C D) x}"
    using targets_carrier targets_in_ancestor_cone[OF targets_carrier] cone_acc by auto
qed

section \<open>Mechanism robustness on the target cone\<close>

theorem every_mechanism_target_iff_ancestral_well_founded:
  assumes "T \<subseteq> C"
  shows "(\<forall>f. mechanism_on C D f \<longrightarrow> T \<subseteq> lfp (efficacy_step C D f))
    \<longleftrightarrow> well_founded_on (ancestor_cone C D T) D"
  by (simp only: every_mechanism_iff_accessible
    target_accessibility_iff_ancestral_well_founded[OF assms])

theorem every_relevant_mechanism_target_iff_ancestral_well_founded:
  assumes "T \<subseteq> C"
  shows "(\<forall>f. mechanism_on C D f \<and> edge_relevant_on C D f \<longrightarrow>
      T \<subseteq> lfp (efficacy_step C D f))
    \<longleftrightarrow> well_founded_on (ancestor_cone C D T) D"
  by (simp only: every_relevant_mechanism_iff_accessible
    target_accessibility_iff_ancestral_well_founded[OF assms])

end
