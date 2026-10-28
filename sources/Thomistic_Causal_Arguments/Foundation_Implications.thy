theory Foundation_Implications
  imports Foundation_Principles
begin

section \<open>Well-Foundedness and Minimal Ancestors\<close>

lemma well_founded_has_minimal_ancestor:
  assumes "well_founded_on C D" and "x \<in> C"
  obtains m where "m \<in> C"
    and "dependency_ancestor C D m x"
    and "independent_in C D m"
proof -
  have wf: "wfp_on C (dependency_on C D)"
    using assms(1) by (simp add: well_founded_on_def)
  obtain m where mC: "m \<in> C"
    and m_ancestor: "(dependency_on C D)\<^sup>*\<^sup>* m x"
    and m_minimal: "\<not> (\<exists>z \<in> C. dependency_on C D z m)"
    using bex_rtransclp_min_element_if_wfp_on[OF wf assms(2)] by blast
  have "dependency_ancestor C D m x"
    using mC assms(2) m_ancestor
    by (simp add: dependency_ancestor_def)
  then have m_ancestor': "dependency_ancestor C D m x" .
  have m_independent: "independent_in C D m"
    using mC m_minimal
    by (auto simp: independent_in_def dependency_on_def)
  show thesis
    using mC m_ancestor' m_independent by (rule that)
qed

lemma well_founded_implies_local_foundation:
  assumes "well_founded_on C D"
  shows "local_foundation_on C D R"
proof -
  show ?thesis
    unfolding local_foundation_on_def
  proof (intro ballI impI)
    fix a
    assume "a \<in> R" and "grounded_in C D a"
    have "a \<in> C"
      using \<open>grounded_in C D a\<close> by (auto simp: grounded_in_def)
    obtain f where "f \<in> C"
      and "dependency_ancestor C D f a"
      and "independent_in C D f"
      using well_founded_has_minimal_ancestor[OF assms \<open>a \<in> C\<close>] .
    show "\<exists>f. first_member_in C D f a"
      using \<open>dependency_ancestor C D f a\<close> \<open>independent_in C D f\<close>
      by (intro exI) (simp add: first_member_in_def)
  qed
qed

section \<open>Well-Foundedness and Explicit Chains\<close>

lemma well_founded_iff_chain_terminating:
  "well_founded_on C D \<longleftrightarrow> chain_terminating_on C D"
proof -
  have relation_eq:
      "(\<lambda>x y. dependency_on C D x y \<and> x \<in> C \<and> y \<in> C) =
       dependency_on C D"
    by (rule ext, rule ext) (auto simp: dependency_on_def)
  have relation:
      "well_founded_on C D \<longleftrightarrow>
       wf {(x, y). dependency_on C D x y}"
  proof -
    have h_wfp:
        "wfp_on C (dependency_on C D) \<longleftrightarrow>
         wfp (dependency_on C D)"
      using wfp_on_iff_wfp[of C "dependency_on C D"] relation_eq
      by simp
    show ?thesis
      unfolding well_founded_on_def
      using h_wfp
      by (simp add: wfp_def)
  qed
  have chain_relation:
      "wf {(x, y). dependency_on C D x y} \<longleftrightarrow>
       chain_terminating_on C D"
    unfolding chain_terminating_on_def
    by (simp add: wf_iff_no_infinite_down_chain)
  show ?thesis
    using relation chain_relation by blast
qed

lemma well_founded_implies_chain_terminating:
  assumes "well_founded_on C D"
  shows "chain_terminating_on C D"
  using well_founded_iff_chain_terminating assms by blast

lemma dependency_trancl_to_set:
  "(dependency_on C D)\<^sup>+\<^sup>+ x y \<Longrightarrow>
   (x, y) \<in> {(u, v). dependency_on C D u v}\<^sup>+"
proof (induction rule: tranclp_induct)
  case base
  then show ?case
    by (auto intro: trancl.r_into_trancl)
next
  case step
  show ?case
    using step.IH step.hyps(2)
    by (auto intro: trancl_into_trancl)
qed

lemma dependency_set_to_trancl:
  "(x, y) \<in> {(u, v). dependency_on C D u v}\<^sup>+ \<Longrightarrow>
   (dependency_on C D)\<^sup>+\<^sup>+ x y"
proof (induction rule: trancl_induct)
  case base
  then show ?case by simp
next
  case step
  then show ?case
    by (auto intro: tranclp_into_rtranclp rtranclp_into_tranclp1)
qed

lemma well_founded_implies_acyclic:
  assumes "well_founded_on C D"
  shows "acyclic_on C D"
proof -
  have relation_eq:
      "(\<lambda>x y. dependency_on C D x y \<and> x \<in> C \<and> y \<in> C) =
       dependency_on C D"
    by (rule ext, rule ext) (auto simp: dependency_on_def)
  have wfp_rel: "wfp (dependency_on C D)"
    using assms wfp_on_iff_wfp[of C "dependency_on C D"] relation_eq
    by (simp add: well_founded_on_def)
  have acyclic_rel:
      "acyclic {(x, y). dependency_on C D x y}"
    using wfp_rel by (rule wfp_acyclicP)
  show "acyclic_on C D"
    unfolding acyclic_on_def
  proof (intro ballI notI)
    fix x
    assume "x \<in> C"
    assume cycle: "(dependency_on C D)\<^sup>+\<^sup>+ x x"
    have set_cycle:
        "(x, x) \<in> {(u, v). dependency_on C D u v}\<^sup>+"
      using dependency_trancl_to_set[OF cycle] .
    show False
      using acyclic_rel set_cycle by (auto simp: acyclic_def)
  qed
qed

section \<open>Finite Acyclicity Collapse\<close>

lemma finite_well_founded_iff_acyclic_on:
  assumes "finite C"
  shows "well_founded_on C D \<longleftrightarrow> acyclic_on C D"
proof -
  have relation_eq:
      "(\<lambda>x y. dependency_on C D x y \<and> x \<in> C \<and> y \<in> C) =
       dependency_on C D"
    by (rule ext, rule ext) (auto simp: dependency_on_def)
  have finite_relation:
      "finite {(x, y). dependency_on C D x y}"
  proof -
    have subset: "{(x, y). dependency_on C D x y} \<subseteq> C \<times> C"
      by (auto simp: dependency_on_def)
    have finite_CC: "finite (C \<times> C)"
      using assms by simp
    show ?thesis
      by (rule finite_subset[OF subset finite_CC])
  qed
  show ?thesis
  proof (rule iffI)
    assume well: "well_founded_on C D"
    have wfp_rel: "wfp (dependency_on C D)"
      using well wfp_on_iff_wfp[of C "dependency_on C D"] relation_eq
      by (simp add: well_founded_on_def)
    have acyclic_rel:
        "acyclic {(x, y). dependency_on C D x y}"
      using wfp_rel by (rule wfp_acyclicP)
    show "acyclic_on C D"
      unfolding acyclic_on_def
    proof (intro ballI notI)
      fix x
      assume "x \<in> C"
      assume cycle: "(dependency_on C D)\<^sup>+\<^sup>+ x x"
      have set_cycle:
        "(x, x) \<in> {(u, v). dependency_on C D u v}\<^sup>+"
        using dependency_trancl_to_set[OF cycle] .
      show False
        using acyclic_rel set_cycle by (auto simp: acyclic_def)
    qed
  next
    assume acyclic: "acyclic_on C D"
    have acyclic_rel:
        "acyclic {(x, y). dependency_on C D x y}"
    proof (unfold acyclic_def, intro allI notI)
      fix x
      assume set_cycle:
        "(x, x) \<in> {(u, v). dependency_on C D u v}\<^sup>+"
      obtain y where edge:
          "(x, y) \<in> {(u, v). dependency_on C D u v}"
        using tranclD[OF set_cycle] by blast
      have xC: "x \<in> C"
        using edge by (auto simp: dependency_on_def)
      have pred_cycle:
          "(dependency_on C D)\<^sup>+\<^sup>+ x x"
        using dependency_set_to_trancl[OF set_cycle] .
      show False
        using acyclic xC pred_cycle
        by (auto simp: acyclic_on_def)
    qed
    have wf_rel: "wf {(x, y). dependency_on C D x y}"
      using finite_acyclic_wf[OF finite_relation acyclic_rel] .
    have wfp_rel: "wfp (dependency_on C D)"
      using wf_rel by (simp add: wfp_def)
    show "well_founded_on C D"
      unfolding well_founded_on_def
      using wfp_on_iff_wfp[of C "dependency_on C D"] relation_eq wfp_rel
      by simp
  qed
qed

section \<open>Global Foundation\<close>

lemma global_foundation_implies_local_foundation:
  assumes "global_foundation_on C D R"
  shows "local_foundation_on C D R"
proof -
  obtain F where foundation: "foundation_set_for C D R F"
    using global_foundation_onD[OF assms] .
  obtain F_sub: "F \<subseteq> C"
    and R_sub: "R \<subseteq> C"
    and F_independent:
      "\<forall>f \<in> F. independent_in C D f"
    and F_supports:
      "\<forall>a \<in> R. grounded_in C D a \<longrightarrow>
        (\<exists>f \<in> F. dependency_ancestor C D f a)"
    using foundation_set_forD[OF foundation] by blast
  show ?thesis
    unfolding local_foundation_on_def
  proof (intro ballI impI)
    fix a
    assume "a \<in> R" and "grounded_in C D a"
    have F_supports_a:
        "a \<in> R \<longrightarrow> grounded_in C D a \<longrightarrow>
          (\<exists>f \<in> F. dependency_ancestor C D f a)"
      using F_supports by blast
    obtain f where "f \<in> F" and "dependency_ancestor C D f a"
      using F_supports_a \<open>a \<in> R\<close> \<open>grounded_in C D a\<close> by blast
    have "independent_in C D f"
      using F_independent \<open>f \<in> F\<close> by blast
    show "\<exists>f. first_member_in C D f a"
      using \<open>dependency_ancestor C D f a\<close> \<open>independent_in C D f\<close>
      by (intro exI) (simp add: first_member_in_def)
  qed
qed

lemma local_foundation_implies_global_foundation:
  assumes local: "local_foundation_on C D R"
    and R_sub: "R \<subseteq> C"
  shows "global_foundation_on C D R"
proof -
  let ?F = "{f. independent_in C D f}"
  have F_sub: "?F \<subseteq> C"
  proof (intro subsetI)
    fix f
    assume "f \<in> ?F"
    have "independent_in C D f"
      using \<open>f \<in> ?F\<close> by simp
    then show "f \<in> C"
      by (rule independent_inD)
  qed
  have F_independent:
      "\<forall>f \<in> ?F. independent_in C D f"
  proof (intro ballI)
    fix f
    assume "f \<in> ?F"
    then show "independent_in C D f"
      by simp
  qed
  have supports:
      "\<forall>a \<in> R. grounded_in C D a \<longrightarrow>
        (\<exists>f \<in> ?F. dependency_ancestor C D f a)"
  proof (intro ballI impI)
    fix a
    assume aR: "a \<in> R"
      and grounded: "grounded_in C D a"
    have local_expanded:
        "\<forall>a \<in> R. grounded_in C D a \<longrightarrow>
          (\<exists>f. first_member_in C D f a)"
      using local by (simp only: local_foundation_on_def)
    have first_exists:
        "\<exists>f. first_member_in C D f a"
      using local_expanded aR grounded by blast
    obtain f where first: "first_member_in C D f a"
      using first_exists by blast
    have f_ancestor: "dependency_ancestor C D f a"
      using first by (rule first_member_inD)
    have f_independent: "independent_in C D f"
      using first by (rule first_member_inD)
    show "\<exists>f \<in> ?F. dependency_ancestor C D f a"
    proof (rule bexI[of _ f])
      show "f \<in> ?F"
        using f_independent by simp
      show "dependency_ancestor C D f a"
        by (rule f_ancestor)
    qed
  qed
  have foundation_unfolded:
      "?F \<subseteq> C \<and> R \<subseteq> C \<and>
       (\<forall>f \<in> ?F. independent_in C D f) \<and>
       (\<forall>a \<in> R. grounded_in C D a \<longrightarrow>
         (\<exists>f \<in> ?F. dependency_ancestor C D f a))"
  proof -
    show ?thesis
    proof (rule conjI)
      show "?F \<subseteq> C"
        by (rule F_sub)
      show "R \<subseteq> C \<and>
          (\<forall>f \<in> ?F. independent_in C D f) \<and>
          (\<forall>a \<in> R. grounded_in C D a \<longrightarrow>
            (\<exists>f \<in> ?F. dependency_ancestor C D f a))"
      proof (rule conjI)
        show "R \<subseteq> C"
          by (rule R_sub)
        show "(\<forall>f \<in> ?F. independent_in C D f) \<and>
            (\<forall>a \<in> R. grounded_in C D a \<longrightarrow>
              (\<exists>f \<in> ?F. dependency_ancestor C D f a))"
        proof (rule conjI)
          show "\<forall>f \<in> ?F. independent_in C D f"
            by (rule F_independent)
          show "\<forall>a \<in> R. grounded_in C D a \<longrightarrow>
              (\<exists>f \<in> ?F. dependency_ancestor C D f a)"
            by (rule supports)
        qed
      qed
    qed
  qed
  have foundation:
      "foundation_set_for C D R ?F"
    unfolding foundation_set_for_def
    by (rule foundation_unfolded)
  show ?thesis
    using foundation by (rule global_foundation_onI)
qed

theorem local_foundation_iff_global_foundation:
  assumes "R \<subseteq> C"
  shows "local_foundation_on C D R \<longleftrightarrow>
   global_foundation_on C D R"
  using global_foundation_implies_local_foundation
    local_foundation_implies_global_foundation[OF _ assms] by blast

section \<open>Full-to-Binary Comparison\<close>

text \<open>
  A plural grounding relation does not determine a binary relation by itself.
  The bridge theorem therefore exposes the required endpoint, nonemptiness,
  and closure assumptions as hypotheses.
\<close>

lemma full_foundation_implies_local_foundation:
  assumes full: "full_foundation_on C D G R"
    and singleton_endpoint:
      "\<And>x a. x \<in> C \<Longrightarrow> a \<in> C \<Longrightarrow> D x a \<Longrightarrow>
        partial_grounding_on C G x a"
    and nonempty:
      "\<And>S a. full_grounding_on C G S a \<Longrightarrow> S \<noteq> {}"
    and closure:
      "\<And>S a x. full_grounding_on C G S a \<Longrightarrow> x \<in> S \<Longrightarrow>
        dependency_ancestor C D x a"
  shows "local_foundation_on C D R"
proof -
  obtain F where foundation: "full_foundation_for C D G R F"
    using full_foundation_onD[OF full] .
  obtain F_sub: "F \<subseteq> C"
    and R_sub: "R \<subseteq> C"
    and F_independent:
      "\<forall>f \<in> F. independent_in C D f"
    and F_supports:
      "\<forall>a \<in> R.
        grounded_in C (partial_grounding_on C G) a \<longrightarrow>
        (\<exists>S. full_grounding_on C G S a \<and> S \<subseteq> F)"
    using full_foundation_forD[OF foundation] by blast
  show ?thesis
    unfolding local_foundation_on_def
  proof (intro ballI impI)
    fix a
    assume aR: "a \<in> R" and grounded: "grounded_in C D a"
    obtain x where xC: "x \<in> C" and xC': "a \<in> C" and Dxa: "D x a"
      using grounded_inD[OF grounded] by blast
    have partial: "partial_grounding_on C G x a"
      using singleton_endpoint[OF xC xC' Dxa] .
    have grounded_full:
        "grounded_in C (partial_grounding_on C G) a"
      using xC xC' partial
      by (auto simp: grounded_in_def)
    have F_supports_a:
        "a \<in> R \<longrightarrow>
          grounded_in C (partial_grounding_on C G) a \<longrightarrow>
          (\<exists>S. full_grounding_on C G S a \<and> S \<subseteq> F)"
      using F_supports by blast
    obtain S where full_S: "full_grounding_on C G S a" and "S \<subseteq> F"
      using F_supports_a aR grounded_full by blast
    obtain f where "f \<in> S"
      using nonempty[OF full_S] by blast
    have "f \<in> F"
      using \<open>S \<subseteq> F\<close> \<open>f \<in> S\<close> by blast
    have "independent_in C D f"
      using F_independent \<open>f \<in> F\<close> by blast
    have "dependency_ancestor C D f a"
      using closure[OF full_S \<open>f \<in> S\<close>] .
    show "\<exists>f. first_member_in C D f a"
      using \<open>dependency_ancestor C D f a\<close> \<open>independent_in C D f\<close>
      by (intro exI) (simp add: first_member_in_def)
  qed
qed

theorem foundation_implication_atlas:
  assumes singleton_endpoint:
    "\<And>x a. x \<in> C \<Longrightarrow> a \<in> C \<Longrightarrow> D x a \<Longrightarrow>
      partial_grounding_on C G x a"
    and nonempty:
      "\<And>S a. full_grounding_on C G S a \<Longrightarrow> S \<noteq> {}"
    and closure:
      "\<And>S a x. full_grounding_on C G S a \<Longrightarrow> x \<in> S \<Longrightarrow>
        dependency_ancestor C D x a"
  shows
    "(well_founded_on C D \<longrightarrow> local_foundation_on C D R) \<and>
     (well_founded_on C D \<longrightarrow> acyclic_on C D) \<and>
     (well_founded_on C D \<longrightarrow> chain_terminating_on C D) \<and>
     (global_foundation_on C D R \<longrightarrow> local_foundation_on C D R) \<and>
     (full_foundation_on C D G R \<longrightarrow> local_foundation_on C D R)"
proof -
  have wf_local:
      "well_founded_on C D \<longrightarrow> local_foundation_on C D R"
    by (blast intro: well_founded_implies_local_foundation)
  have wf_chain:
      "well_founded_on C D \<longrightarrow> chain_terminating_on C D"
    by (blast intro: well_founded_implies_chain_terminating)
  have wf_acyclic:
      "well_founded_on C D \<longrightarrow> acyclic_on C D"
    by (blast intro: well_founded_implies_acyclic)
  have global_local:
      "global_foundation_on C D R \<longrightarrow> local_foundation_on C D R"
    by (blast intro: global_foundation_implies_local_foundation)
  have full_local:
      "full_foundation_on C D G R \<longrightarrow> local_foundation_on C D R"
  proof (intro impI)
    assume full: "full_foundation_on C D G R"
    then show "local_foundation_on C D R"
      using full_foundation_implies_local_foundation[
        where C = C and D = D and G = G and R = R]
        singleton_endpoint nonempty closure by blast
  qed
  show ?thesis
    using wf_local wf_acyclic wf_chain global_local full_local by blast
qed

end
