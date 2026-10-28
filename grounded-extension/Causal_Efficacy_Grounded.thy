theory Causal_Efficacy_Grounded
  imports "Causal_Efficacy_Contexts.Causal_Efficacy_Contexts"
begin

text \<open>This powerset specialization credits Bogaerts, Vennekens and Denecker,
Grounded fixpoints and their applications in knowledge representation (2015),
Proposition 3.10. It is not a new general fixed-point result.\<close>

definition externally_supported_parts where
  "externally_supported_parts F X \<longleftrightarrow>
    (\<forall>S \<subseteq> X. S \<noteq> {} \<longrightarrow> (\<exists>x \<in> S. x \<in> F (X - S)))"

theorem grounded_fixed_iff_least:
  fixes F :: "'a set \<Rightarrow> 'a set"
  assumes mono: "mono F" and fixed: "F X = X"
  shows "externally_supported_parts F X \<longleftrightarrow> X = lfp F"
proof
  assume grounded: "externally_supported_parts F X"
  have sub: "lfp F \<subseteq> X"
    by (rule lfp_lowerbound) (simp add: fixed)
  have lf: "F (lfp F) = lfp F"
    using lfp_unfold[OF mono] by simp
  show "X = lfp F"
  proof (rule ccontr)
    assume "X \<noteq> lfp F"
    then have nonempty: "X - lfp F \<noteq> {}" using sub by blast
    obtain x where xs: "x \<in> X - lfp F" and xf: "x \<in> F (X - (X - lfp F))"
      using grounded nonempty unfolding externally_supported_parts_def by blast
    have "X - (X - lfp F) = lfp F" using sub by blast
    then show False using xs xf lf by simp
  qed
next
  assume least: "X = lfp F"
  show "externally_supported_parts F X"
    unfolding externally_supported_parts_def
  proof (intro allI impI)
    fix S
    assume SX: "S \<subseteq> X" and nonempty: "S \<noteq> {}"
    show "\<exists>x\<in>S. x \<in> F (X - S)"
    proof (rule ccontr)
      assume no: "\<not> (\<exists>x\<in>S. x \<in> F (X - S))"
      have sub: "F (X - S) \<subseteq> X"
        using monoD[OF mono, of "X-S" X] fixed by auto
      have pre: "F (X - S) \<subseteq> X - S" using sub no by blast
      have "lfp F \<subseteq> X - S" by (rule lfp_lowerbound) (fact pre)
      then show False using least SX nonempty by blast
    qed
  qed
qed

theorem mechanism_least_iff_external_support:
  assumes admissible: "mechanism_on C D f"
    and fixed: "efficacy_step C D f X = X"
  shows "X = lfp (efficacy_step C D f) \<longleftrightarrow>
    (\<forall>S \<subseteq> X. S \<noteq> {} \<longrightarrow>
      (\<exists>x \<in> S. f x ((X-S) \<inter> efficacy_parents C D x)))"
proof -
  have XC: "X \<subseteq> C" using fixed by (auto simp: efficacy_step_def)
  have eq: "externally_supported_parts (efficacy_step C D f) X \<longleftrightarrow>
    (\<forall>S \<subseteq> X. S \<noteq> {} \<longrightarrow>
      (\<exists>x \<in> S. f x ((X-S) \<inter> efficacy_parents C D x)))"
    using XC unfolding externally_supported_parts_def efficacy_step_def by blast
  show ?thesis using grounded_fixed_iff_least[OF mono_efficacy_step[OF admissible] fixed] eq
    by blast
qed

end
