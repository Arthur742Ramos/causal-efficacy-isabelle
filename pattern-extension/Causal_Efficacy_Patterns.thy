theory Causal_Efficacy_Patterns
  imports "Causal_Efficacy_Determination.Causal_Efficacy_Determination"
    "Causal_Efficacy_Grounded.Causal_Efficacy_Grounded"
begin

section \<open>Finite paths internal to a status region\<close>

definition internal_reach where
  "internal_reach A D B = {x \<in> A. \<exists>b \<in> B. (dependency_on A D)\<^sup>*\<^sup>* b x}"

lemma internal_reach_subset: "internal_reach A D B \<subseteq> A"
  by (auto simp: internal_reach_def)

lemma internal_reach_seeds:
  assumes "B \<subseteq> A"
  shows "B \<subseteq> internal_reach A D B"
  using assms by (auto simp: internal_reach_def)

lemma internal_reach_step:
  assumes "y \<in> internal_reach A D B" "x \<in> A" "D y x"
  shows "x \<in> internal_reach A D B"
proof -
  obtain b where b: "b \<in> B" and p: "(dependency_on A D)\<^sup>*\<^sup>* b y" and y: "y \<in> A"
    using assms(1) by (auto simp: internal_reach_def)
  have e: "dependency_on A D y x" using y assms by (simp add: dependency_on_def)
  have "(dependency_on A D)\<^sup>*\<^sup>* b x" by (rule rtranclp.rtrancl_into_rtrancl[OF p e])
  then show ?thesis using b assms(2) by (auto simp: internal_reach_def)
qed

lemma internal_reach_minimal:
  assumes seeds: "B \<subseteq> X"
    and closed: "\<And>x y. x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> y \<in> X \<Longrightarrow> D y x \<Longrightarrow> x \<in> X"
  shows "internal_reach A D B \<subseteq> X"
proof
  fix x
  assume "x \<in> internal_reach A D B"
  then obtain b where bB: "b \<in> B" and path: "(dependency_on A D)\<^sup>*\<^sup>* b x"
    by (auto simp: internal_reach_def)
  from path show "x \<in> X"
    by (induction rule: rtranclp_induct) (use seeds bB closed in \<open>auto simp: dependency_on_def\<close>)
qed

lemma internal_reach_mono:
  assumes AC: "A \<subseteq> C" and BV: "B \<subseteq> V"
  shows "internal_reach A D B \<subseteq> internal_reach C D V"
proof -
  have rel: "dependency_on A D \<le> dependency_on C D"
    using AC by (auto simp: dependency_on_def)
  have paths: "(dependency_on A D)\<^sup>*\<^sup>* \<le> (dependency_on C D)\<^sup>*\<^sup>*"
    by (rule rtranclp_mono[OF rel])
  have pathsD: "\<And>a b. (dependency_on A D)\<^sup>*\<^sup>* a b \<Longrightarrow> (dependency_on C D)\<^sup>*\<^sup>* a b"
    by (rule predicate2D[OF paths])
  show ?thesis using AC BV by (auto simp: internal_reach_def intro: pathsD)
qed

lemma internal_root_is_seed:
  assumes x: "x \<in> internal_reach A D B" and root: "x \<in> efficacy_roots A D"
  shows "x \<in> B"
proof -
  obtain b where bB: "b \<in> B" and path: "(dependency_on A D)\<^sup>*\<^sup>* b x"
    using x by (auto simp: internal_reach_def)
  show ?thesis using path root bB
    by (cases rule: rtranclp.cases) (auto simp: efficacy_roots_def efficacy_parents_def dependency_on_def)
qed

lemma root_reachable_eq_internal:
  "root_reachable C D = internal_reach C D (efficacy_roots C D)"
  by (auto simp: root_reachable_def internal_reach_def first_member_in_def
    dependency_ancestor_def efficacy_roots_def efficacy_parents_def independent_in_def)

lemma contextual_fixed_roots:
  assumes ctx: "U \<subseteq> efficacy_roots C D" and fx: "contextual_step C D f U X = X"
  shows "X \<inter> efficacy_roots C D = U"
  using ctx fx by (auto simp: contextual_step_def source_off_step_def efficacy_roots_def)

lemma contextual_least_internal_paths:
  assumes adm: "mechanism_on C D f" and ctx: "U \<subseteq> efficacy_roots C D"
  defines "L \<equiv> lfp (contextual_step C D f U)"
  shows "internal_reach L D U = L"
proof -
  let ?F = "contextual_step C D f U"
  let ?R = "internal_reach L D U"
  have fixL: "?F L = L" unfolding L_def by (rule contextual_extrema_fixed(1)[OF adm])
  have LC: "L \<subseteq> C" unfolding L_def by (rule contextual_extrema_subset_carrier(1)[OF adm ctx])
  have UL: "U \<subseteq> L" using contextual_fixed_roots[OF ctx fixL] by blast
  have RL: "?R \<subseteq> L" by (rule internal_reach_subset)
  have image: "?F ?R \<subseteq> L"
    using monoD[OF mono_contextual_step[OF adm, of U] RL] fixL by simp
  have pre: "?F ?R \<subseteq> ?R"
  proof
    fix x
    assume xF: "x \<in> ?F ?R"
    have xL: "x \<in> L" using image xF by blast
    show "x \<in> ?R"
    proof (cases "x \<in> U")
      case True
      show ?thesis using internal_reach_seeds[OF UL] True by blast
    next
      case False
      have xC: "x \<in> C" using xL LC by blast
      have P: "efficacy_parents C D x \<noteq> {}" and active: "f x (?R \<inter> efficacy_parents C D x)"
        using xF False by (auto simp: contextual_step_def source_off_step_def)
      have "?R \<inter> efficacy_parents C D x \<noteq> {}"
        using active P adm xC unfolding mechanism_on_def by force
      then obtain y where yR: "y \<in> ?R" and edge: "D y x" by (auto simp: efficacy_parents_def)
      show ?thesis by (rule internal_reach_step[OF yR xL edge])
    qed
  qed
  have "lfp ?F \<subseteq> ?R" by (rule lfp_lowerbound) (fact pre)
  then have "L \<subseteq> ?R" by (simp only: L_def)
  with RL show ?thesis by blast
qed

lemma contextual_greatest_internal_zero_paths:
  assumes adm: "mechanism_on C D f" and ctx: "U \<subseteq> efficacy_roots C D"
  defines "N \<equiv> gfp (contextual_step C D f U)"
  shows "internal_reach (C-N) D (efficacy_roots C D-U) = C-N"
proof -
  let ?F = "contextual_step C D f U"
  let ?B0 = "efficacy_roots C D-U"
  let ?R = "internal_reach (C-N) D ?B0"
  let ?Y = "C-?R"
  have fixN: "?F N = N" unfolding N_def by (rule contextual_extrema_fixed(2)[OF adm])
  have NC: "N \<subseteq> C" unfolding N_def by (rule contextual_extrema_subset_carrier(2)[OF adm ctx])
  have roots: "N \<inter> efficacy_roots C D = U" by (rule contextual_fixed_roots[OF ctx fixN])
  have BZ: "?B0 \<subseteq> C-N" using roots efficacy_roots_subset_carrier[of C D] by blast
  have BR: "?B0 \<subseteq> ?R" by (rule internal_reach_seeds[OF BZ])
  have RZ: "?R \<subseteq> C-N" by (rule internal_reach_subset)
  have NY: "N \<subseteq> ?Y" using NC RZ by blast
  have NF: "N \<subseteq> ?F ?Y"
    using monoD[OF mono_contextual_step[OF adm, of U] NY] fixN by simp
  have post: "?Y \<subseteq> ?F ?Y"
  proof
    fix x
    assume xY: "x \<in> ?Y"
    show "x \<in> ?F ?Y"
    proof (cases "x \<in> N")
      case True
      then show ?thesis using NF by blast
    next
      case False
      have xZ: "x \<in> C-N" using xY False by blast
      have ne: "efficacy_parents C D x \<noteq> {}"
        using xY False roots BR by (auto simp: efficacy_roots_def)
      have PR: "efficacy_parents C D x \<inter> ?R = {}"
        using internal_reach_step[of _ "C-N" D ?B0 x] xY xZ
        by (auto simp: efficacy_parents_def)
      have inputs: "?Y \<inter> efficacy_parents C D x = efficacy_parents C D x"
        using PR by (auto simp: efficacy_parents_def)
      show ?thesis using xY ne adm
        by (simp add: contextual_step_def source_off_step_def inputs mechanism_on_def)
    qed
  qed
  have "?Y \<subseteq> gfp ?F" by (rule gfp_upperbound) (fact post)
  then have "?Y \<subseteq> N" by (simp only: N_def)
  with RZ show ?thesis by blast
qed

lemma ambiguity_has_ambiguous_parent:
  assumes adm: "mechanism_on C D f" and ctx: "U \<subseteq> efficacy_roots C D"
  defines "L \<equiv> lfp (contextual_step C D f U)" and "N \<equiv> gfp (contextual_step C D f U)"
  assumes x: "x \<in> N-L"
  shows "efficacy_parents C D x \<inter> (N-L) \<noteq> {}"
proof
  let ?F = "contextual_step C D f U"
  assume no: "efficacy_parents C D x \<inter> (N-L) = {}"
  have lf: "?F L = L" and nf: "?F N = N"
    unfolding L_def N_def by (rule contextual_extrema_fixed[OF adm])+
  have LN: "L \<subseteq> N" unfolding L_def by (rule lfp_lowerbound) (simp only: nf)
  have inputs: "L \<inter> efficacy_parents C D x = N \<inter> efficacy_parents C D x" using no LN by blast
  have "(x \<in> L) = (x \<in> N)"
    using arg_cong[OF lf, of "\<lambda>S. x \<in> S"] arg_cong[OF nf, of "\<lambda>S. x \<in> S"]
    by (simp add: contextual_step_def source_off_step_def inputs)
  then show False using x by blast
qed

section \<open>Exact three-status realization\<close>

definition status_partition where
  "status_partition C L Z Q \<longleftrightarrow> C = L \<union> Z \<union> Q \<and>
    L \<inter> Z = {} \<and> L \<inter> Q = {} \<and> Z \<inter> Q = {}"

definition pattern_conditions where
  "pattern_conditions C D U L Z Q \<longleftrightarrow>
    U \<subseteq> L \<and> efficacy_roots C D-U \<subseteq> Z \<and>
    internal_reach L D U = L \<and>
    internal_reach Z D (efficacy_roots C D-U) = Z \<and>
    (\<forall>x\<in>Q. efficacy_parents C D x \<inter> Q \<noteq> {})"

definition status_mechanism where
  "status_mechanism C D L Z Q x S \<longleftrightarrow>
    (if x \<in> L then or_mechanism C D x S else if x \<in> Z then and_mechanism C D x S
     else split_gate (efficacy_parents C D x \<inter> Q)
       (efficacy_parents C D x \<inter> L) (efficacy_parents C D x \<inter> Z) S)"

lemma internal_reach_cases:
  assumes "x \<in> internal_reach A D B"
  shows "x \<in> B \<or> (\<exists>y\<in>A. D y x \<and> y \<in> internal_reach A D B)"
proof -
  obtain b where b: "b \<in> B" and p: "(dependency_on A D)\<^sup>*\<^sup>* b x"
    using assms by (auto simp: internal_reach_def)
  from p show ?thesis using b
    by (cases rule: rtranclp.cases) (auto simp: internal_reach_def dependency_on_def)
qed

lemma status_mechanism_admissible:
  assumes part: "status_partition C L Z Q"
    and qp: "\<forall>x\<in>Q. efficacy_parents C D x \<inter> Q \<noteq> {}"
  shows "mechanism_on C D (status_mechanism C D L Z Q)"
  unfolding mechanism_on_def
proof (intro ballI conjI)
  fix x
  assume xC: "x \<in> C"
  show "mono (status_mechanism C D L Z Q x)"
    by (auto simp: status_mechanism_def or_mechanism_def and_mechanism_def split_gate_def mono_def)
  show "status_mechanism C D L Z Q x {} = (efficacy_parents C D x = {})"
    using part qp xC by (auto simp: status_partition_def status_mechanism_def or_mechanism_def and_mechanism_def split_gate_def)
  show "status_mechanism C D L Z Q x (efficacy_parents C D x)"
    using part qp xC by (auto simp: status_partition_def status_mechanism_def or_mechanism_def and_mechanism_def split_gate_def)
qed

lemma status_mechanism_relevant:
  assumes part: "status_partition C L Z Q"
    and qp: "\<forall>x\<in>Q. efficacy_parents C D x \<inter> Q \<noteq> {}"
  shows "edge_relevant_on C D (status_mechanism C D L Z Q)"
  unfolding edge_relevant_on_def
proof (intro ballI)
  fix x y
  assume xC: "x \<in> C" and yp: "y \<in> efficacy_parents C D x"
  show "\<exists>S \<subseteq> efficacy_parents C D x-{y}.
    \<not> status_mechanism C D L Z Q x S \<and> status_mechanism C D L Z Q x (insert y S)"
  proof (cases "x \<in> L")
    case True
    show ?thesis using True yp by (intro exI[of _ "{}"]) (auto simp: status_mechanism_def or_mechanism_def)
  next
    case notL: False
    show ?thesis
    proof (cases "x \<in> Z")
      case True
      show ?thesis using True notL yp by (intro exI[of _ "efficacy_parents C D x-{y}"])
        (auto simp: status_mechanism_def and_mechanism_def)
    next
      case notZ: False
      have xQ: "x \<in> Q" using part xC notL notZ by (auto simp: status_partition_def)
      have ne: "efficacy_parents C D x \<inter> Q \<noteq> {}" using qp xQ by blast
      have partition: "efficacy_parents C D x = (efficacy_parents C D x \<inter> Q) \<union>
        (efficacy_parents C D x \<inter> L) \<union> (efficacy_parents C D x \<inter> Z)"
        using part by (auto simp: status_partition_def efficacy_parents_def)
      have d1: "(efficacy_parents C D x \<inter> Q) \<inter> (efficacy_parents C D x \<inter> L) = {}"
        and d2: "(efficacy_parents C D x \<inter> Q) \<inter> (efficacy_parents C D x \<inter> Z) = {}"
        and d3: "(efficacy_parents C D x \<inter> L) \<inter> (efficacy_parents C D x \<inter> Z) = {}"
        using part by (auto simp: status_partition_def)
      show ?thesis using split_gate_relevant[OF partition ne d1 d2 d3 yp] notL notZ
        by (simp add: status_mechanism_def)
    qed
  qed
qed

lemma status_two_fixed_points:
  assumes part: "status_partition C L Z Q" and cond: "pattern_conditions C D U L Z Q"
  shows "contextual_step C D (status_mechanism C D L Z Q) U L = L"
    "contextual_step C D (status_mechanism C D L Z Q) U (C-Z) = C-Z"
proof -
  have UL: "U \<subseteq> L" and reachL: "internal_reach L D U = L"
    and reachZ: "internal_reach Z D (efficacy_roots C D-U) = Z"
    and qp: "\<forall>x\<in>Q. efficacy_parents C D x \<inter> Q \<noteq> {}"
    using cond by (auto simp: pattern_conditions_def)
  have lc: "\<And>x. x \<in> L \<Longrightarrow> x \<in> U \<or> efficacy_parents C D x \<inter> L \<noteq> {}"
  proof -
    fix x
    assume xL: "x \<in> L"
    have "x \<in> internal_reach L D U" using xL reachL by simp
    then have "x \<in> U \<or> (\<exists>y\<in>L. D y x \<and> y \<in> internal_reach L D U)"
      by (rule internal_reach_cases)
    then show "x \<in> U \<or> efficacy_parents C D x \<inter> L \<noteq> {}"
      using part by (auto simp: status_partition_def efficacy_parents_def)
  qed
  have zc: "\<And>x. x \<in> Z \<Longrightarrow> efficacy_parents C D x = {} \<or> efficacy_parents C D x \<inter> Z \<noteq> {}"
  proof -
    fix x
    assume xZ: "x \<in> Z"
    have "x \<in> internal_reach Z D (efficacy_roots C D-U)" using xZ reachZ by simp
    then have "x \<in> efficacy_roots C D-U \<or>
      (\<exists>y\<in>Z. D y x \<and> y \<in> internal_reach Z D (efficacy_roots C D-U))"
      by (rule internal_reach_cases)
    then show "efficacy_parents C D x = {} \<or> efficacy_parents C D x \<inter> Z \<noteq> {}"
      using part by (auto simp: status_partition_def efficacy_parents_def efficacy_roots_def)
  qed
  have LC: "L \<subseteq> C" and ZC: "Z \<subseteq> C" and QC: "Q \<subseteq> C"
    and LZ: "L \<inter> Z = {}" and LQ: "L \<inter> Q = {}" and ZQ: "Z \<inter> Q = {}"
    using part by (auto simp: status_partition_def)
  show "contextual_step C D (status_mechanism C D L Z Q) U L = L"
  proof (rule set_eqI)
    fix x
    show "(x \<in> contextual_step C D (status_mechanism C D L Z Q) U L) = (x \<in> L)"
    proof (cases "x \<in> L")
      case True
      show ?thesis using True lc[OF True] LC
        by (auto simp: contextual_step_def source_off_step_def status_mechanism_def or_mechanism_def)
    next
      case notL: False
      show ?thesis
      proof (cases "x \<in> Z")
        case True
        show ?thesis using notL True zc[OF True] UL LZ
          by (auto simp: contextual_step_def source_off_step_def status_mechanism_def and_mechanism_def)
      next
        case False
        show ?thesis using notL False UL LQ LZ
          by (auto simp: contextual_step_def source_off_step_def status_mechanism_def split_gate_def)
      qed
    qed
  qed
  show "contextual_step C D (status_mechanism C D L Z Q) U (C-Z) = C-Z"
  proof (rule set_eqI)
    fix x
    show "(x \<in> contextual_step C D (status_mechanism C D L Z Q) U (C-Z)) = (x \<in> C-Z)"
    proof (cases "x \<in> L")
      case True
      show ?thesis using True lc[OF True] LC LZ
        by (auto simp: contextual_step_def source_off_step_def status_mechanism_def or_mechanism_def)
    next
      case notL: False
      show ?thesis
      proof (cases "x \<in> Z")
        case True
        show ?thesis using notL True zc[OF True] UL
          by (auto simp: contextual_step_def source_off_step_def status_mechanism_def and_mechanism_def)
      next
        case notZ: False
        show ?thesis
        proof (cases "x \<in> C")
          case True
          then have xQ: "x \<in> Q" using part notL notZ by (auto simp: status_partition_def)
          have ne: "efficacy_parents C D x \<inter> Q \<noteq> {}" using qp xQ by blast
          show ?thesis using True notL notZ ne LC QC LZ ZQ
            by (auto simp: contextual_step_def source_off_step_def status_mechanism_def split_gate_def)
        next
          case False
          show ?thesis using False UL LC by (auto simp: contextual_step_def source_off_step_def)
        qed
      qed
    qed
  qed
qed

lemma status_forces_paths:
  assumes part: "status_partition C L Z Q" and cond: "pattern_conditions C D U L Z Q"
    and ctx: "U \<subseteq> efficacy_roots C D"
    and fixX: "contextual_step C D (status_mechanism C D L Z Q) U X = X"
  shows "L \<subseteq> X" "X \<subseteq> C-Z"
proof -
  let ?f = "status_mechanism C D L Z Q"
  have roots: "X \<inter> efficacy_roots C D = U" by (rule contextual_fixed_roots[OF ctx fixX])
  have XC: "X \<subseteq> C" by (rule contextual_fixed_subset_carrier[OF ctx fixX])
  have eq: "\<And>x. (x \<in> X) = (x \<in> contextual_step C D ?f U X)" by (simp only: fixX)
  have "internal_reach L D U \<subseteq> X"
  proof (rule internal_reach_minimal)
    show "U \<subseteq> X" using roots by blast
    fix x y
    assume xL: "x \<in> L" and yL: "y \<in> L" and yX: "y \<in> X" and dyx: "D y x"
    show "x \<in> X" using eq[of x] part xL yL yX dyx
      by (auto simp: contextual_step_def source_off_step_def status_mechanism_def
        status_partition_def or_mechanism_def efficacy_parents_def)
  qed
  then show "L \<subseteq> X" using cond by (simp add: pattern_conditions_def)
  have "internal_reach Z D (efficacy_roots C D-U) \<subseteq> C-X"
  proof (rule internal_reach_minimal)
    show "efficacy_roots C D-U \<subseteq> C-X"
      using roots efficacy_roots_subset_carrier[of C D] by blast
    fix x y
    assume xZ: "x \<in> Z" and yZ: "y \<in> Z" and yoff: "y \<in> C-X" and dyx: "D y x"
    show "x \<in> C-X" using eq[of x] part cond xZ yZ yoff dyx
      by (auto simp: contextual_step_def source_off_step_def status_mechanism_def
        status_partition_def pattern_conditions_def and_mechanism_def efficacy_parents_def)
  qed
  then show "X \<subseteq> C-Z" using cond XC by (auto simp: pattern_conditions_def)
qed

theorem pattern_witness_extrema:
  assumes part: "status_partition C L Z Q" and cond: "pattern_conditions C D U L Z Q"
    and ctx: "U \<subseteq> efficacy_roots C D"
  shows "mechanism_on C D (status_mechanism C D L Z Q)"
    "edge_relevant_on C D (status_mechanism C D L Z Q)"
    "lfp (contextual_step C D (status_mechanism C D L Z Q) U) = L"
    "gfp (contextual_step C D (status_mechanism C D L Z Q) U) = C-Z"
proof -
  have qp: "\<forall>x\<in>Q. efficacy_parents C D x \<inter> Q \<noteq> {}"
    using cond by (simp add: pattern_conditions_def)
  show adm: "mechanism_on C D (status_mechanism C D L Z Q)"
    by (rule status_mechanism_admissible[OF part qp])
  show "edge_relevant_on C D (status_mechanism C D L Z Q)"
    by (rule status_mechanism_relevant[OF part qp])
  let ?F = "contextual_step C D (status_mechanism C D L Z Q) U"
  have low: "?F L = L" and high: "?F (C-Z) = C-Z" by (rule status_two_fixed_points[OF part cond])+
  have le: "lfp ?F \<subseteq> L" by (rule lfp_lowerbound) (simp only: low)
  have ge: "L \<subseteq> lfp ?F"
    by (rule status_forces_paths(1)[OF part cond ctx contextual_extrema_fixed(1)[OF adm]])
  show "lfp ?F = L" using le ge by blast
  have le: "gfp ?F \<subseteq> C-Z"
    by (rule status_forces_paths(2)[OF part cond ctx contextual_extrema_fixed(2)[OF adm]])
  have ge: "C-Z \<subseteq> gfp ?F" by (rule gfp_upperbound) (simp only: high)
  show "gfp ?F = C-Z" using le ge by blast
qed

lemma realized_pattern_necessary:
  assumes part: "status_partition C L Z Q" and ctx: "U \<subseteq> efficacy_roots C D"
    and adm: "mechanism_on C D f"
    and low: "lfp (contextual_step C D f U) = L"
    and high: "gfp (contextual_step C D f U) = C-Z"
  shows "pattern_conditions C D U L Z Q"
proof -
  let ?F = "contextual_step C D f U"
  have lf: "?F L = L" and hf: "?F (C-Z) = C-Z"
    using contextual_extrema_fixed[OF adm, of U] low high by simp_all
  have lr: "L \<inter> efficacy_roots C D = U" and hr: "(C-Z) \<inter> efficacy_roots C D = U"
    by (rule contextual_fixed_roots[OF ctx lf], rule contextual_fixed_roots[OF ctx hf])
  have rL: "internal_reach L D U = L" using contextual_least_internal_paths[OF adm ctx] low by simp
  have zcomp: "C-(C-Z) = Z" and qcomp: "(C-Z)-L = Q"
    using part by (auto simp: status_partition_def)
  have rZ: "internal_reach Z D (efficacy_roots C D-U) = Z"
    using contextual_greatest_internal_zero_paths[OF adm ctx]
    by (simp only: high zcomp)
  have q: "\<forall>x\<in>Q. efficacy_parents C D x \<inter> Q \<noteq> {}"
    using ambiguity_has_ambiguous_parent[OF adm ctx]
    by (auto simp: low high qcomp)
  show ?thesis using lr hr rL rZ q efficacy_roots_subset_carrier[of C D]
    by (auto simp: pattern_conditions_def)
qed

theorem exact_relevant_pattern_realization:
  assumes part: "status_partition C L Z Q" and ctx: "U \<subseteq> efficacy_roots C D"
  shows "(\<exists>f. mechanism_on C D f \<and> edge_relevant_on C D f \<and>
    lfp (contextual_step C D f U) = L \<and> gfp (contextual_step C D f U) = C-Z)
    \<longleftrightarrow> pattern_conditions C D U L Z Q"
proof
  assume "\<exists>f. mechanism_on C D f \<and> edge_relevant_on C D f \<and>
    lfp (contextual_step C D f U) = L \<and> gfp (contextual_step C D f U) = C-Z"
  then obtain f where "mechanism_on C D f" "lfp (contextual_step C D f U) = L"
    "gfp (contextual_step C D f U) = C-Z" by blast
  then show "pattern_conditions C D U L Z Q" by (rule realized_pattern_necessary[OF part ctx])
next
  assume cond: "pattern_conditions C D U L Z Q"
  show "\<exists>f. mechanism_on C D f \<and> edge_relevant_on C D f \<and>
    lfp (contextual_step C D f U) = L \<and> gfp (contextual_step C D f U) = C-Z"
    by (intro exI[of _ "status_mechanism C D L Z Q"] conjI)
      (rule pattern_witness_extrema[OF part cond ctx])+
qed

section \<open>Every attainable determinate region\<close>

definition region_conditions where
  "region_conditions C D K \<longleftrightarrow> K \<subseteq> C \<and> efficacy_roots C D \<subseteq> K \<and>
    internal_reach K D (efficacy_roots C D) = K \<and> and_step C D K \<subseteq> K"

lemma extremal_status_partition:
  assumes adm: "mechanism_on C D f" and ctx: "U \<subseteq> efficacy_roots C D"
  shows "status_partition C (lfp (contextual_step C D f U))
    (C-gfp (contextual_step C D f U))
    (gfp (contextual_step C D f U)-lfp (contextual_step C D f U))"
proof -
  let ?F = "contextual_step C D f U"
  have LN: "lfp ?F \<subseteq> gfp ?F"
    by (rule lfp_lowerbound) (simp only: contextual_extrema_fixed(2)[OF adm])
  show ?thesis using LN contextual_extrema_subset_carrier[OF adm ctx]
    by (auto simp: status_partition_def)
qed

lemma pattern_region_conditions:
  assumes part: "status_partition C L Z Q" and cond: "pattern_conditions C D U L Z Q"
    and ctx: "U \<subseteq> efficacy_roots C D"
  shows "region_conditions C D (L \<union> Z)"
proof -
  have reachL: "internal_reach L D U = L" and reachZ: "internal_reach Z D (efficacy_roots C D-U) = Z"
    using cond by (auto simp: pattern_conditions_def)
  have rL: "L \<subseteq> internal_reach (L \<union> Z) D (efficacy_roots C D)"
    using internal_reach_mono[of L "L \<union> Z" U "efficacy_roots C D" D] ctx reachL by auto
  have rZ: "Z \<subseteq> internal_reach (L \<union> Z) D (efficacy_roots C D)"
    using internal_reach_mono[of Z "L \<union> Z" "efficacy_roots C D-U" "efficacy_roots C D" D] reachZ by auto
  have reach: "internal_reach (L \<union> Z) D (efficacy_roots C D) = L \<union> Z"
    using rL rZ internal_reach_subset[of "L \<union> Z" D "efficacy_roots C D"] by blast
  have pre: "and_step C D (L \<union> Z) \<subseteq> L \<union> Z"
  proof
    fix x
    assume ax: "x \<in> and_step C D (L \<union> Z)"
    show "x \<in> L \<union> Z"
    proof (rule ccontr)
      assume no: "x \<notin> L \<union> Z"
      have xQ: "x \<in> Q" using ax no part by (auto simp: and_step_def status_partition_def)
      have ne: "efficacy_parents C D x \<inter> Q \<noteq> {}"
        using cond xQ unfolding pattern_conditions_def by blast
      obtain y where yp: "y \<in> efficacy_parents C D x" and yQ: "y \<in> Q"
        using ne by blast
      have "y \<in> L \<union> Z" using ax yp by (auto simp: and_step_def)
      then show False using part yQ by (auto simp: status_partition_def)
    qed
  qed
  show ?thesis using part cond ctx reach pre
    by (auto simp: region_conditions_def status_partition_def pattern_conditions_def)
qed

theorem determined_region_conditions:
  assumes adm: "mechanism_on C D f" and ctx: "U \<subseteq> efficacy_roots C D"
  shows "region_conditions C D (determined_region C D f U)"
proof -
  let ?F = "contextual_step C D f U"
  have part: "status_partition C (lfp ?F) (C-gfp ?F) (gfp ?F-lfp ?F)"
    by (rule extremal_status_partition[OF adm ctx])
  have high: "gfp ?F = C-(C-gfp ?F)" using contextual_extrema_subset_carrier(2)[OF adm ctx] by blast
  have cond: "pattern_conditions C D U (lfp ?F) (C-gfp ?F) (gfp ?F-lfp ?F)"
    by (rule realized_pattern_necessary[OF part ctx adm HOL.refl high])
  show ?thesis unfolding determined_region_def by (rule pattern_region_conditions[OF part cond ctx])
qed

lemma region_induced_roots:
  assumes reg: "region_conditions C D K"
  shows "efficacy_roots K D = efficacy_roots C D"
proof (rule subset_antisym)
  show "efficacy_roots C D \<subseteq> efficacy_roots K D"
    using reg by (auto simp: region_conditions_def efficacy_roots_def efficacy_parents_def)
  show "efficacy_roots K D \<subseteq> efficacy_roots C D"
  proof
    fix x
    assume root: "x \<in> efficacy_roots K D"
    then have xK: "x \<in> K" by (simp add: efficacy_roots_def)
    have path: "x \<in> internal_reach K D (efficacy_roots C D)"
      using reg xK by (auto simp: region_conditions_def)
    show "x \<in> efficacy_roots C D" by (rule internal_root_is_seed[OF path root])
  qed
qed

lemma region_induced_local_foundation:
  assumes reg: "region_conditions C D K"
  shows "local_foundation_on K D K"
proof -
  have "root_reachable K D = K"
    using reg region_induced_roots[OF reg] by (simp add: root_reachable_eq_internal region_conditions_def)
  then show ?thesis using reachable_carrier_iff_local_foundation[of K D] by simp
qed

theorem region_conditions_sufficient:
  assumes reg: "region_conditions C D K" and ctx: "U \<subseteq> efficacy_roots C D"
  shows "\<exists>f. mechanism_on C D f \<and> edge_relevant_on C D f \<and> determined_region C D f U = K"
proof -
  have rootsK: "efficacy_roots K D = efficacy_roots C D" by (rule region_induced_roots[OF reg])
  have ctxK: "U \<subseteq> efficacy_roots K D" using ctx rootsK by simp
  have exists: "\<exists>g. mechanism_on K D g \<and> edge_relevant_on K D g \<and>
    (\<exists>!X. contextual_step K D g U X = X)"
    by (rule iffD2[OF some_relevant_context_unique_iff_local_foundation[OF ctxK]
      region_induced_local_foundation[OF reg]])
  obtain g where adm: "mechanism_on K D g" and rel: "edge_relevant_on K D g"
    and uniq: "\<exists>!X. contextual_step K D g U X = X" using exists by (elim exE conjE)
  let ?G = "contextual_step K D g U"
  let ?L = "lfp ?G"
  let ?Z = "K-?L"
  let ?Q = "C-K"
  have LC: "?L \<subseteq> K" by (rule contextual_extrema_subset_carrier(1)[OF adm ctxK])
  have KC: "K \<subseteq> C" using reg by (simp add: region_conditions_def)
  have eq: "gfp ?G = ?L" using uniq contextual_extrema_fixed[OF adm, of U] by blast
  have fixL: "?G ?L = ?L" by (rule contextual_extrema_fixed(1)[OF adm])
  have rootvals: "?L \<inter> efficacy_roots C D = U"
    using contextual_fixed_roots[OF ctxK fixL] rootsK by simp
  have part: "status_partition C ?L ?Z ?Q" using LC KC by (auto simp: status_partition_def)
  have pathL: "internal_reach ?L D U = ?L" by (rule contextual_least_internal_paths[OF adm ctxK])
  have pathZ: "internal_reach ?Z D (efficacy_roots C D-U) = ?Z"
    using contextual_greatest_internal_zero_paths[OF adm ctxK] eq rootsK by simp
  have qp: "\<forall>x\<in>?Q. efficacy_parents C D x \<inter> ?Q \<noteq> {}"
    using reg by (auto simp: region_conditions_def and_step_def efficacy_parents_def)
  have cond: "pattern_conditions C D U ?L ?Z ?Q"
    using rootvals reg pathL pathZ qp by (auto simp: pattern_conditions_def region_conditions_def)
  let ?f = "status_mechanism C D ?L ?Z ?Q"
  have madm: "mechanism_on C D ?f" and mrel: "edge_relevant_on C D ?f"
    and low: "lfp (contextual_step C D ?f U) = ?L"
    and high: "gfp (contextual_step C D ?f U) = C-?Z"
    by (rule pattern_witness_extrema[OF part cond ctx])+
  have det: "determined_region C D ?f U = K"
    using LC KC by (auto simp: determined_region_def low high)
  show ?thesis by (intro exI[of _ ?f] conjI) (fact madm, fact mrel, fact det)
qed

theorem exact_relevant_region_realization:
  assumes ctx: "U \<subseteq> efficacy_roots C D"
  shows "(\<exists>f. mechanism_on C D f \<and> edge_relevant_on C D f \<and> determined_region C D f U = K)
    \<longleftrightarrow> region_conditions C D K"
  using region_conditions_sufficient[OF _ ctx] determined_region_conditions[OF _ ctx] by blast

theorem exact_region_realization:
  assumes ctx: "U \<subseteq> efficacy_roots C D"
  shows "(\<exists>f. mechanism_on C D f \<and> determined_region C D f U = K)
    \<longleftrightarrow> region_conditions C D K"
  using exact_relevant_region_realization[OF ctx] determined_region_conditions[OF _ ctx] by blast

theorem attainable_regions_context_independent:
  assumes "U \<subseteq> efficacy_roots C D" "V \<subseteq> efficacy_roots C D"
  shows "(\<exists>f. mechanism_on C D f \<and> edge_relevant_on C D f \<and> determined_region C D f U = K)
    \<longleftrightarrow> (\<exists>g. mechanism_on C D g \<and> edge_relevant_on C D g \<and> determined_region C D g V = K)"
  by (simp only: exact_relevant_region_realization[OF assms(1)] exact_relevant_region_realization[OF assms(2)])

section \<open>Positive source inference and contextual groundedness\<close>

theorem active_determinate_is_least:
  assumes adm: "mechanism_on C D f" and ctx: "U \<subseteq> efficacy_roots C D"
    and fixed: "contextual_step C D f U X = X"
    and active: "a \<in> X" and det: "a \<in> determined_region C D f U"
  shows "a \<in> lfp (contextual_step C D f U)"
proof -
  have "X \<subseteq> gfp (contextual_step C D f U)" by (rule gfp_upperbound) (simp only: fixed)
  then show ?thesis using active det by (auto simp: determined_region_def)
qed

theorem active_determinate_internal_root_path:
  assumes adm: "mechanism_on C D f" and ctx: "U \<subseteq> efficacy_roots C D"
    and fixed: "contextual_step C D f U X = X"
    and active: "a \<in> X" and det: "a \<in> determined_region C D f U"
  shows "a \<in> internal_reach (lfp (contextual_step C D f U)) D U"
  using active_determinate_is_least[OF assms] contextual_least_internal_paths[OF adm ctx] by simp

theorem unique_unconditioned_solution_is_least:
  assumes adm: "mechanism_on C D f"
    and unique: "\<exists>!Y. contextual_step C D f U Y = Y"
    and fixed: "contextual_step C D f U X = X"
  shows "X = lfp (contextual_step C D f U)"
  using unique fixed contextual_extrema_fixed(1)[OF adm, of U] by blast

theorem contextual_grounded_fixed_iff_least:
  assumes adm: "mechanism_on C D f" and ctx: "U \<subseteq> efficacy_roots C D"
    and fixed: "contextual_step C D f U X = X"
  shows "(\<forall>S\<subseteq>X. S \<noteq> {} \<longrightarrow> S \<inter> contextual_step C D f U (X-S) \<noteq> {})
    \<longleftrightarrow> X = lfp (contextual_step C D f U)"
  using grounded_fixed_iff_least[OF mono_contextual_step[OF adm] fixed]
  by (simp add: externally_supported_parts_def disjoint_iff Bex_def)

section \<open>All determinate regions of the shared-root spine\<close>

definition spine_prefix where
  "spine_prefix N = {Source} \<union> Link ` {..<N}"

lemma shared_spine_region_conditions:
  "region_conditions UNIV spine_dependency K \<longleftrightarrow>
    Source \<in> K \<and> (\<forall>n. Link (Suc n) \<in> K \<longrightarrow> Link n \<in> K)"
proof
  assume reg: "region_conditions UNIV spine_dependency K"
  then have src: "Source \<in> K" by (simp add: region_conditions_def spine_roots_exact)
  show "Source \<in> K \<and> (\<forall>n. Link (Suc n) \<in> K \<longrightarrow> Link n \<in> K)"
  proof (intro conjI allI impI)
    show "Source \<in> K" by (fact src)
    fix n
    assume succK: "Link (Suc n) \<in> K"
    have "Link n \<in> and_step UNIV spine_dependency K" using src succK by (simp add: and_step_def)
    then show "Link n \<in> K" using reg by (auto simp: region_conditions_def)
  qed
next
  assume H: "Source \<in> K \<and> (\<forall>n. Link (Suc n) \<in> K \<longrightarrow> Link n \<in> K)"
  then have src: "Source \<in> K" and down: "\<And>n. Link (Suc n) \<in> K \<Longrightarrow> Link n \<in> K" by auto
  have seeds: "Source \<in> internal_reach K spine_dependency {Source}"
    using src by (auto simp: internal_reach_def)
  have reach: "internal_reach K spine_dependency {Source} = K"
  proof (rule subset_antisym[OF internal_reach_subset])
    show "K \<subseteq> internal_reach K spine_dependency {Source}"
    proof
      fix x
      assume xK: "x \<in> K"
      show "x \<in> internal_reach K spine_dependency {Source}"
      proof (cases x)
        case Source
        then show ?thesis using seeds by simp
      next
        case (Link n)
        show ?thesis by (rule internal_reach_step[OF seeds xK]) (simp add: Link spine_dependency_def)
      qed
    qed
  qed
  have pre: "and_step UNIV spine_dependency K \<subseteq> K"
  proof
    fix x
    assume xA: "x \<in> and_step UNIV spine_dependency K"
    show "x \<in> K" using xA src down by (cases x) (auto simp: and_step_def)
  qed
  show "region_conditions UNIV spine_dependency K"
    using src reach pre by (simp add: region_conditions_def spine_roots_exact)
qed

lemma shared_spine_downward:
  assumes down: "\<forall>n. Link (Suc n) \<in> K \<longrightarrow> Link n \<in> K"
    and mn: "m \<le> n" and nk: "Link n \<in> K"
  shows "Link m \<in> K"
proof (rule inc_induct[OF mn])
  show "Link n \<in> K" by (fact nk)
  fix k
  assume "m \<le> k" "k < n" "Link (Suc k) \<in> K"
  then show "Link k \<in> K" using down by blast
qed

lemma shared_spine_initial_segments:
  "(Source \<in> K \<and> (\<forall>n. Link (Suc n) \<in> K \<longrightarrow> Link n \<in> K))
    \<longleftrightarrow> (K = UNIV \<or> (\<exists>N. K = spine_prefix N))"
proof
  assume H: "Source \<in> K \<and> (\<forall>n. Link (Suc n) \<in> K \<longrightarrow> Link n \<in> K)"
  then have src: "Source \<in> K" and down: "\<forall>n. Link (Suc n) \<in> K \<longrightarrow> Link n \<in> K" by auto
  show "K = UNIV \<or> (\<exists>N. K = spine_prefix N)"
  proof (cases "\<forall>n. Link n \<in> K")
    case True
    have "K = UNIV"
    proof (rule set_eqI)
      fix x
      show "(x \<in> K) = (x \<in> UNIV)" using True src by (cases x) auto
    qed
    then show ?thesis by simp
  next
    case False
    let ?N = "LEAST n. Link n \<notin> K"
    have missing: "Link ?N \<notin> K" by (rule LeastI_ex) (use False in blast)
    have before: "\<And>n. n < ?N \<Longrightarrow> Link n \<in> K"
    proof -
      fix n
      assume nN: "n < ?N"
      have "\<not> (Link n \<notin> K)" by (rule not_less_Least[OF nN])
      then show "Link n \<in> K" by simp
    qed
    have exact: "\<And>n. (Link n \<in> K) = (n < ?N)"
    proof -
      fix n
      show "(Link n \<in> K) = (n < ?N)"
      proof
        assume nk: "Link n \<in> K"
        show "n < ?N"
        proof (rule ccontr)
          assume "\<not> n < ?N"
          then have "?N \<le> n" by simp
          then have "Link ?N \<in> K" by (rule shared_spine_downward[OF down _ nk])
          then show False using missing by contradiction
        qed
      next
        assume "n < ?N"
        then show "Link n \<in> K" by (rule before)
      qed
    qed
    have "K = spine_prefix ?N"
    proof (rule set_eqI)
      fix x
      show "(x \<in> K) = (x \<in> spine_prefix ?N)"
      proof (cases x)
        case Source
        then show ?thesis using src by (simp add: spine_prefix_def)
      next
        case (Link n)
        then show ?thesis using exact[of n] by (auto simp: spine_prefix_def)
      qed
    qed
    then show ?thesis by blast
  qed
next
  assume "K = UNIV \<or> (\<exists>N. K = spine_prefix N)"
  then show "Source \<in> K \<and> (\<forall>n. Link (Suc n) \<in> K \<longrightarrow> Link n \<in> K)"
    by (auto simp: spine_prefix_def)
qed

theorem shared_spine_attainable_regions:
  assumes ctx: "U \<subseteq> {Source}"
  shows "(\<exists>f. mechanism_on UNIV spine_dependency f \<and>
    edge_relevant_on UNIV spine_dependency f \<and> determined_region UNIV spine_dependency f U = K)
    \<longleftrightarrow> Source \<in> K \<and> (\<forall>n. Link (Suc n) \<in> K \<longrightarrow> Link n \<in> K)"
proof -
  have legal: "U \<subseteq> efficacy_roots UNIV spine_dependency" using ctx by (simp add: spine_roots_exact)
  show ?thesis by (simp only: exact_relevant_region_realization[OF legal] shared_spine_region_conditions)
qed

theorem shared_spine_attainable_initial_segments:
  assumes "U \<subseteq> {Source}"
  shows "(\<exists>f. mechanism_on UNIV spine_dependency f \<and>
    edge_relevant_on UNIV spine_dependency f \<and> determined_region UNIV spine_dependency f U = K)
    \<longleftrightarrow> K = UNIV \<or> (\<exists>N. K = spine_prefix N)"
  by (simp only: shared_spine_attainable_regions[OF assms] shared_spine_initial_segments)

end
