theory Causal_Efficacy_Determination
  imports "Causal_Efficacy_Contexts.Causal_Efficacy_Contexts"
begin

definition determined_region where
  "determined_region C D f U = lfp (contextual_step C D f U) \<union>
    (C - gfp (contextual_step C D f U))"

abbreviation accessible_region where
  "accessible_region C D \<equiv> {x \<in> C. Wellfounded.accp (dependency_on C D) x}"

lemma contextual_extrema_fixed:
  assumes "mechanism_on C D f"
  shows "contextual_step C D f U (lfp (contextual_step C D f U)) = lfp (contextual_step C D f U)"
    "contextual_step C D f U (gfp (contextual_step C D f U)) = gfp (contextual_step C D f U)"
  using lfp_unfold[OF mono_contextual_step[OF assms]]
    gfp_unfold[OF mono_contextual_step[OF assms]] by simp_all

lemma contextual_extrema_subset_carrier:
  assumes "mechanism_on C D f" "U \<subseteq> efficacy_roots C D"
  shows "lfp (contextual_step C D f U) \<subseteq> C"
    "gfp (contextual_step C D f U) \<subseteq> C"
  using contextual_fixed_subset_carrier[OF assms(2) contextual_extrema_fixed(1)[OF assms(1)]]
    contextual_fixed_subset_carrier[OF assms(2) contextual_extrema_fixed(2)[OF assms(1)]] by auto

lemma accessible_fixed_agreement:
  assumes ctx: "U \<subseteq> efficacy_roots C D"
    and fixedX: "contextual_step C D f U X = X"
    and fixedY: "contextual_step C D f U Y = Y"
    and acc: "x \<in> accessible_region C D"
  shows "(x \<in> X) = (x \<in> Y)"
proof -
  have "Wellfounded.accp (dependency_on C D) x" using acc by simp
  then have "x \<in> C \<longrightarrow> (x \<in> X) = (x \<in> Y)"
  proof (induction rule: accp.induct)
    case (accI x)
    show ?case
    proof
      assume xC: "x \<in> C"
      have inputs: "X \<inter> efficacy_parents C D x = Y \<inter> efficacy_parents C D x"
        using accI.IH xC by (auto simp: efficacy_parents_def dependency_on_def)
      have "(x \<in> X) = (x \<in> contextual_step C D f U X)" by (simp only: fixedX)
      also have "... = (x \<in> contextual_step C D f U Y)"
        by (simp add: contextual_step_def source_off_step_def inputs)
      also have "... = (x \<in> Y)" by (simp only: fixedY)
      finally show "(x \<in> X) = (x \<in> Y)" .
    qed
  qed
  then show ?thesis using acc by simp
qed

lemma accessible_subset_determined:
  assumes adm: "mechanism_on C D f" and ctx: "U \<subseteq> efficacy_roots C D"
  shows "accessible_region C D \<subseteq> determined_region C D f U"
  using accessible_fixed_agreement[OF ctx contextual_extrema_fixed(1)[OF adm]
    contextual_extrema_fixed(2)[OF adm]]
  by (auto simp: determined_region_def)

lemma contextual_below_original:
  assumes "mechanism_on C D f" "U \<subseteq> efficacy_roots C D"
  shows "contextual_step C D f U X \<subseteq> efficacy_step C D f X"
  using assms by (auto simp: contextual_step_def source_off_step_def efficacy_step_def
    efficacy_roots_def mechanism_on_def)

lemma reachable_is_or_fixed:
  "or_step C D (root_reachable C D) = root_reachable C D"
  using lfp_unfold[OF mono_or_step[of C D]] by (simp add: lfp_or_eq_root_reachable)

lemma reachable_subset_carrier: "root_reachable C D \<subseteq> C"
  using lfp_or_subset_carrier[of C D] by (simp add: lfp_or_eq_root_reachable)

lemma contextual_lfp_subset_reachable:
  assumes adm: "mechanism_on C D f" and ctx: "U \<subseteq> efficacy_roots C D"
  shows "lfp (contextual_step C D f U) \<subseteq> root_reachable C D"
proof (rule lfp_lowerbound)
  have "contextual_step C D f U (root_reachable C D) \<subseteq> or_step C D (root_reachable C D)"
    using contextual_below_original[OF adm ctx] mechanism_extremal_bounds(2)[OF adm] by blast
  then show "contextual_step C D f U (root_reachable C D) \<subseteq> root_reachable C D"
    by (simp add: reachable_is_or_fixed)
qed

lemma unreachable_postfixed:
  assumes adm: "mechanism_on C D f"
  shows "C - root_reachable C D \<subseteq> contextual_step C D f U (C - root_reachable C D)"
proof
  fix x
  assume x: "x \<in> C - root_reachable C D"
  have "x \<notin> or_step C D (root_reachable C D)"
    using x by (simp add: reachable_is_or_fixed)
  then have nonempty: "efficacy_parents C D x \<noteq> {}"
    and inputs: "(C - root_reachable C D) \<inter> efficacy_parents C D x = efficacy_parents C D x"
    using x by (auto simp: or_step_def efficacy_parents_def)
  show "x \<in> contextual_step C D f U (C - root_reachable C D)"
    using x adm nonempty by (simp add: contextual_step_def source_off_step_def inputs mechanism_on_def)
qed

lemma determined_subset_reachable:
  assumes adm: "mechanism_on C D f" and ctx: "U \<subseteq> efficacy_roots C D"
  shows "determined_region C D f U \<subseteq> root_reachable C D"
proof -
  have "C - root_reachable C D \<subseteq> gfp (contextual_step C D f U)"
    by (rule gfp_upperbound, rule unreachable_postfixed[OF adm])
  with contextual_lfp_subset_reachable[OF adm ctx] show ?thesis
    by (auto simp: determined_region_def)
qed

theorem contextual_determination_interval:
  assumes "mechanism_on C D f" "U \<subseteq> efficacy_roots C D"
  shows "accessible_region C D \<subseteq> determined_region C D f U"
    "determined_region C D f U \<subseteq> root_reachable C D"
  using accessible_subset_determined[OF assms] determined_subset_reachable[OF assms] by auto

lemma determined_iff_fixed_agreement:
  assumes adm: "mechanism_on C D f" and ctx: "U \<subseteq> efficacy_roots C D" and xC: "x \<in> C"
  shows "x \<in> determined_region C D f U \<longleftrightarrow>
    (\<forall>X Y. contextual_step C D f U X = X \<longrightarrow>
      contextual_step C D f U Y = Y \<longrightarrow> (x \<in> X) = (x \<in> Y))"
proof
  assume x: "x \<in> determined_region C D f U"
  show "\<forall>X Y. contextual_step C D f U X = X \<longrightarrow>
      contextual_step C D f U Y = Y \<longrightarrow> (x \<in> X) = (x \<in> Y)"
  proof (intro allI impI)
    fix X Y
    assume fx: "contextual_step C D f U X = X" and fy: "contextual_step C D f U Y = Y"
    have bounds: "lfp (contextual_step C D f U) \<subseteq> X" "X \<subseteq> gfp (contextual_step C D f U)"
      "lfp (contextual_step C D f U) \<subseteq> Y" "Y \<subseteq> gfp (contextual_step C D f U)"
      using lfp_lowerbound[of "contextual_step C D f U" X]
        gfp_upperbound[of X "contextual_step C D f U"]
        lfp_lowerbound[of "contextual_step C D f U" Y]
        gfp_upperbound[of Y "contextual_step C D f U"] fx fy by simp_all
    show "(x \<in> X) = (x \<in> Y)" using x bounds by (auto simp: determined_region_def)
  qed
next
  assume all: "\<forall>X Y. contextual_step C D f U X = X \<longrightarrow>
      contextual_step C D f U Y = Y \<longrightarrow> (x \<in> X) = (x \<in> Y)"
  have "(x \<in> lfp (contextual_step C D f U)) = (x \<in> gfp (contextual_step C D f U))"
    using all contextual_extrema_fixed[OF adm, of U] by blast
  then show "x \<in> determined_region C D f U" using xC by (auto simp: determined_region_def)
qed

lemma determined_carrier_iff_unique:
  assumes adm: "mechanism_on C D f" and ctx: "U \<subseteq> efficacy_roots C D"
  shows "determined_region C D f U = C \<longleftrightarrow> (\<exists>!X. contextual_step C D f U X = X)"
proof
  assume eq: "determined_region C D f U = C"
  show "\<exists>!X. contextual_step C D f U X = X"
  proof (rule ex1I[of _ "lfp (contextual_step C D f U)"])
    show "contextual_step C D f U (lfp (contextual_step C D f U)) = lfp (contextual_step C D f U)"
      by (rule contextual_extrema_fixed(1)[OF adm])
    fix Y
    assume fy: "contextual_step C D f U Y = Y"
    have Ysub: "Y \<subseteq> C" by (rule contextual_fixed_subset_carrier[OF ctx fy])
    have Lsub: "lfp (contextual_step C D f U) \<subseteq> C" by (rule contextual_extrema_subset_carrier(1)[OF adm ctx])
    show "Y = lfp (contextual_step C D f U)"
      using determined_iff_fixed_agreement[OF adm ctx] eq Ysub Lsub fy contextual_extrema_fixed(1)[OF adm, of U]
      by blast
  qed
next
  assume uniq: "\<exists>!X. contextual_step C D f U X = X"
  have eq: "lfp (contextual_step C D f U) = gfp (contextual_step C D f U)"
    using uniq contextual_extrema_fixed[OF adm, of U] by blast
  show "determined_region C D f U = C"
    using contextual_extrema_subset_carrier(1)[OF adm ctx] by (auto simp: determined_region_def eq)
qed

section \<open>The reachable endpoint: a relevant context-dependent witness\<close>

definition polar_mechanism where
  "polar_mechanism C D V x S \<longleftrightarrow>
    (if x \<in> V then or_mechanism C D x S else and_mechanism C D x S)"

lemma polar_admissible: "mechanism_on C D (polar_mechanism C D V)"
  using and_mechanism_admissible[of C D] or_mechanism_admissible[of C D]
  by (auto simp: mechanism_on_def polar_mechanism_def mono_def)

lemma polar_relevant: "edge_relevant_on C D (polar_mechanism C D V)"
  unfolding edge_relevant_on_def
proof (intro ballI)
  fix x y
  assume "x \<in> C" and y: "y \<in> efficacy_parents C D x"
  show "\<exists>S \<subseteq> efficacy_parents C D x - {y}.
    \<not> polar_mechanism C D V x S \<and> polar_mechanism C D V x (insert y S)"
  proof (cases "x \<in> V")
    case True
    show ?thesis using True y by (intro exI[of _ "{}"]) (auto simp: polar_mechanism_def or_mechanism_def)
  next
    case False
    show ?thesis using False y by (intro exI[of _ "efficacy_parents C D x - {y}"])
      (auto simp: polar_mechanism_def and_mechanism_def)
  qed
qed

lemma polar_context_below_or:
  "contextual_step C D (polar_mechanism C D V) U X \<subseteq>
    contextual_step C D (or_mechanism C D) U X"
  by (auto simp: contextual_step_def source_off_step_def polar_mechanism_def
    or_mechanism_def and_mechanism_def)

lemma polar_lfp_eq_context_or:
  fixes C D U
  defines "V \<equiv> lfp (contextual_step C D (or_mechanism C D) U)"
  shows "lfp (contextual_step C D (polar_mechanism C D V) U) = V"
proof -
  let ?F = "contextual_step C D (polar_mechanism C D V) U"
  let ?O = "contextual_step C D (or_mechanism C D) U"
  have Vfix: "?O V = V"
    unfolding V_def by (rule contextual_extrema_fixed(1)[OF or_mechanism_admissible])
  have Lfix: "?F (lfp ?F) = lfp ?F"
    by (rule contextual_extrema_fixed(1)[OF polar_admissible])
  have sub: "lfp ?F \<subseteq> V"
    unfolding V_def by (rule lfp_mono, rule polar_context_below_or)
  have Osub: "?O (lfp ?F) \<subseteq> V"
    using monoD[OF mono_contextual_step[OF or_mechanism_admissible[of C D], of U] sub] Vfix by simp
  have "?O (lfp ?F) \<subseteq> lfp ?F"
  proof
    fix x
    assume xO: "x \<in> ?O (lfp ?F)"
    then have "x \<in> V" using Osub by blast
    then have "x \<in> ?F (lfp ?F)"
      using xO by (simp add: contextual_step_def source_off_step_def polar_mechanism_def)
    then show "x \<in> lfp ?F" by (simp only: Lfix)
  qed
  then have "V \<subseteq> lfp ?F" unfolding V_def by (rule lfp_lowerbound)
  with sub show ?thesis by blast
qed

theorem reachable_endpoint_attained:
  assumes ctx: "U \<subseteq> efficacy_roots C D"
  defines "V \<equiv> lfp (contextual_step C D (or_mechanism C D) U)"
  shows "determined_region C D (polar_mechanism C D V) U = root_reachable C D"
proof (rule subset_antisym)
  show "determined_region C D (polar_mechanism C D V) U \<subseteq> root_reachable C D"
    by (rule determined_subset_reachable[OF polar_admissible ctx])
next
  let ?F = "contextual_step C D (polar_mechanism C D V) U"
  let ?N = "gfp ?F"
  have Vfix: "contextual_step C D (or_mechanism C D) U V = V"
    unfolding V_def by (rule contextual_extrema_fixed(1)[OF or_mechanism_admissible])
  have Nfix: "?F ?N = ?N" by (rule contextual_extrema_fixed(2)[OF polar_admissible])
  have lower: "lfp ?F = V" unfolding V_def by (rule polar_lfp_eq_context_or)
  have closed: "or_step C D (V \<union> (C - ?N)) \<subseteq> V \<union> (C - ?N)"
  proof
    fix x
    assume xO: "x \<in> or_step C D (V \<union> (C - ?N))"
    have xC: "x \<in> C" using xO by (simp add: or_step_def)
    have vx: "(x \<in> V) = (x \<in> contextual_step C D (or_mechanism C D) U V)"
      by (simp only: Vfix)
    have nx: "(x \<in> ?N) = (x \<in> ?F ?N)" by (simp only: Nfix)
    show "x \<in> V \<union> (C - ?N)"
      using xO vx nx xC
      by (auto simp: or_step_def contextual_step_def source_off_step_def
        polar_mechanism_def or_mechanism_def and_mechanism_def)
  qed
  have "root_reachable C D \<subseteq> V \<union> (C - ?N)"
    unfolding lfp_or_eq_root_reachable[symmetric] by (rule lfp_lowerbound, rule closed)
  then show "root_reachable C D \<subseteq> determined_region C D (polar_mechanism C D V) U"
    by (simp add: determined_region_def lower)
qed

section \<open>The accessible endpoint: preserving every input's relevance\<close>

definition split_gate where
  "split_gate I A B S \<longleftrightarrow> ((S \<inter> I \<noteq> {}) \<and> A \<subseteq> S) \<or> S \<inter> B \<noteq> {}"

lemma split_gate_mono: "mono (split_gate I A B)"
  by (auto simp: split_gate_def mono_def)

lemma split_gate_relevant:
  assumes part: "P = I \<union> A \<union> B" and nonempty: "I \<noteq> {}"
    and disjoint: "I \<inter> A = {}" "I \<inter> B = {}" "A \<inter> B = {}"
    and y: "y \<in> P"
  shows "\<exists>S \<subseteq> P - {y}. \<not> split_gate I A B S \<and> split_gate I A B (insert y S)"
proof (cases "y \<in> B")
  case True
  show ?thesis using True by (intro exI[of _ "{}"]) (auto simp: split_gate_def)
next
  case notB: False
  show ?thesis
  proof (cases "y \<in> I")
    case True
    show ?thesis using True disjoint part
      by (intro exI[of _ A]) (auto simp: split_gate_def)
  next
    case notI: False
    have yA: "y \<in> A" using part y notB notI by blast
    obtain i where i: "i \<in> I" using nonempty by blast
    show ?thesis using i yA disjoint part
      by (intro exI[of _ "insert i (A - {y})"]) (auto simp: split_gate_def)
  qed
qed

definition ambiguity_mechanism where
  "ambiguity_mechanism C D W V x S \<longleftrightarrow>
    (if x \<in> W then and_mechanism C D x S
     else split_gate (efficacy_parents C D x - W)
       (efficacy_parents C D x \<inter> V) (efficacy_parents C D x \<inter> (W - V)) S)"

lemma inaccessible_parent_exists:
  assumes W: "and_step C D W = W" and x: "x \<in> C - W"
  shows "efficacy_parents C D x - W \<noteq> {}"
  using W x by (auto simp: and_step_def)

lemma roots_subset_and_fixed:
  assumes "and_step C D W = W"
  shows "efficacy_roots C D \<subseteq> W"
  using assms by (auto simp: and_step_def efficacy_roots_def)

lemma ambiguity_admissible:
  assumes W: "and_step C D W = W" and V: "V \<subseteq> W"
  shows "mechanism_on C D (ambiguity_mechanism C D W V)"
  unfolding mechanism_on_def
proof (intro ballI conjI)
  fix x
  assume xC: "x \<in> C"
  show "mono (ambiguity_mechanism C D W V x)"
    using split_gate_mono[of "efficacy_parents C D x - W" "efficacy_parents C D x \<inter> V"
      "efficacy_parents C D x \<inter> (W - V)"]
    by (auto simp: ambiguity_mechanism_def and_mechanism_def mono_def)
  show "ambiguity_mechanism C D W V x {} = (efficacy_parents C D x = {})"
    using roots_subset_and_fixed[OF W] xC
    by (auto simp: ambiguity_mechanism_def and_mechanism_def split_gate_def efficacy_roots_def)
  show "ambiguity_mechanism C D W V x (efficacy_parents C D x)"
    using inaccessible_parent_exists[OF W, of x] xC V
    by (auto simp: ambiguity_mechanism_def and_mechanism_def split_gate_def)
qed

lemma ambiguity_relevant:
  assumes V: "V \<subseteq> W" and W: "and_step C D W = W"
  shows "edge_relevant_on C D (ambiguity_mechanism C D W V)"
  unfolding edge_relevant_on_def
proof (intro ballI)
  fix x y
  assume xC: "x \<in> C" and yP: "y \<in> efficacy_parents C D x"
  show "\<exists>S \<subseteq> efficacy_parents C D x - {y}.
    \<not> ambiguity_mechanism C D W V x S \<and> ambiguity_mechanism C D W V x (insert y S)"
  proof (cases "x \<in> W")
    case True
    show ?thesis using and_mechanism_relevant[of C D] xC yP True
      by (auto simp: edge_relevant_on_def ambiguity_mechanism_def)
  next
    case False
    have part: "efficacy_parents C D x = (efficacy_parents C D x - W) \<union>
        (efficacy_parents C D x \<inter> V) \<union> (efficacy_parents C D x \<inter> (W - V))"
      using V by blast
    have ne: "efficacy_parents C D x - W \<noteq> {}"
      by (rule inaccessible_parent_exists[OF W]) (use xC False in auto)
    have d1: "(efficacy_parents C D x - W) \<inter> (efficacy_parents C D x \<inter> V) = {}"
      using V by blast
    have d2: "(efficacy_parents C D x - W) \<inter> (efficacy_parents C D x \<inter> (W - V)) = {}" by blast
    have d3: "(efficacy_parents C D x \<inter> V) \<inter> (efficacy_parents C D x \<inter> (W - V)) = {}" by blast
    show ?thesis using split_gate_relevant[OF part ne d1 d2 d3 yP] False
      by (simp add: ambiguity_mechanism_def)
  qed
qed

lemma ambiguity_two_fixed_points:
  assumes ctx: "U \<subseteq> efficacy_roots C D"
    and W: "and_step C D W = W" and WC: "W \<subseteq> C" and VW: "V \<subseteq> W"
    and Vfix: "contextual_step C D (and_mechanism C D) U V = V"
  shows "contextual_step C D (ambiguity_mechanism C D W V) U V = V"
    "contextual_step C D (ambiguity_mechanism C D W V) U (V \<union> (C-W)) = V \<union> (C-W)"
proof -
  have UW: "U \<subseteq> W" using ctx roots_subset_and_fixed[OF W] by blast
  have parentsW: "\<And>x. x \<in> W \<Longrightarrow> efficacy_parents C D x \<subseteq> W"
    using W by (auto simp: and_step_def)
  show "contextual_step C D (ambiguity_mechanism C D W V) U V = V"
  proof (rule set_eqI)
    fix x
    have vx: "(x \<in> contextual_step C D (and_mechanism C D) U V) = (x \<in> V)"
      by (simp only: Vfix)
    show "(x \<in> contextual_step C D (ambiguity_mechanism C D W V) U V) = (x \<in> V)"
      using vx VW UW by (auto simp: contextual_step_def source_off_step_def
        ambiguity_mechanism_def split_gate_def)
  qed
  show "contextual_step C D (ambiguity_mechanism C D W V) U (V \<union> (C-W)) = V \<union> (C-W)"
  proof (rule set_eqI)
    fix x
    have vx: "(x \<in> contextual_step C D (and_mechanism C D) U V) = (x \<in> V)"
      by (simp only: Vfix)
    show "(x \<in> contextual_step C D (ambiguity_mechanism C D W V) U (V \<union> (C-W))) = (x \<in> V \<union> (C-W))"
    proof (cases "x \<in> W")
      case True
      have inputs: "(V \<union> (C-W)) \<inter> efficacy_parents C D x = V \<inter> efficacy_parents C D x"
        using parentsW[OF True] by blast
      show ?thesis using vx True
        by (simp add: contextual_step_def source_off_step_def ambiguity_mechanism_def inputs)
    next
      case False
      show ?thesis using False VW UW inaccessible_parent_exists[OF W, of x]
        by (auto simp: contextual_step_def source_off_step_def ambiguity_mechanism_def
          split_gate_def efficacy_parents_def)
    qed
  qed
qed

lemma contextual_and_lfp_subset_accessible:
  assumes ctx: "U \<subseteq> efficacy_roots C D"
  shows "lfp (contextual_step C D (and_mechanism C D) U) \<subseteq> accessible_region C D"
proof -
  have "lfp (contextual_step C D (and_mechanism C D) U) \<subseteq> lfp (and_step C D)"
    by (rule lfp_mono) (use contextual_below_original[OF and_mechanism_admissible ctx] in
      \<open>simp add: and_mechanism_step\<close>)
  then show ?thesis by (simp add: lfp_and_eq_accessible)
qed

theorem accessible_endpoint_attained:
  assumes ctx: "U \<subseteq> efficacy_roots C D"
  defines "W \<equiv> accessible_region C D"
    and "V \<equiv> lfp (contextual_step C D (and_mechanism C D) U)"
  shows "mechanism_on C D (ambiguity_mechanism C D W V)"
    "edge_relevant_on C D (ambiguity_mechanism C D W V)"
    "determined_region C D (ambiguity_mechanism C D W V) U = W"
proof -
  have Wfix: "and_step C D W = W"
    unfolding W_def lfp_and_eq_accessible[symmetric]
    using lfp_unfold[OF mono_and_step[of C D]] by simp
  have WC: "W \<subseteq> C" by (auto simp: W_def)
  have VW: "V \<subseteq> W"
    unfolding V_def W_def by (rule contextual_and_lfp_subset_accessible[OF ctx])
  have Vfix: "contextual_step C D (and_mechanism C D) U V = V"
    unfolding V_def by (rule contextual_extrema_fixed(1)[OF and_mechanism_admissible])
  show adm: "mechanism_on C D (ambiguity_mechanism C D W V)"
    by (rule ambiguity_admissible[OF Wfix VW])
  show "edge_relevant_on C D (ambiguity_mechanism C D W V)"
    by (rule ambiguity_relevant[OF VW Wfix])
  let ?F = "contextual_step C D (ambiguity_mechanism C D W V) U"
  have lowfix: "?F V = V" and highfix: "?F (V \<union> (C-W)) = V \<union> (C-W)"
    by (rule ambiguity_two_fixed_points[OF ctx Wfix WC VW Vfix])+
  have low: "lfp ?F \<subseteq> V" by (rule lfp_lowerbound) (simp only: lowfix)
  have high: "V \<union> (C-W) \<subseteq> gfp ?F" by (rule gfp_upperbound) (simp only: highfix)
  have "determined_region C D (ambiguity_mechanism C D W V) U \<subseteq> W"
    using low high VW by (auto simp: determined_region_def)
  moreover have "W \<subseteq> determined_region C D (ambiguity_mechanism C D W V) U"
    using accessible_subset_determined[OF adm ctx] by (simp only: W_def)
  ultimately show "determined_region C D (ambiguity_mechanism C D W V) U = W" by blast
qed

section \<open>Exact target and whole-carrier mechanism quantifiers\<close>

theorem some_relevant_context_determination_iff_reachable:
  assumes ctx: "U \<subseteq> efficacy_roots C D"
  shows "(\<exists>f. mechanism_on C D f \<and> edge_relevant_on C D f \<and>
    T \<subseteq> determined_region C D f U) \<longleftrightarrow> T \<subseteq> root_reachable C D"
proof
  assume "\<exists>f. mechanism_on C D f \<and> edge_relevant_on C D f \<and> T \<subseteq> determined_region C D f U"
  then show "T \<subseteq> root_reachable C D" using determined_subset_reachable[OF _ ctx] by blast
next
  assume sub: "T \<subseteq> root_reachable C D"
  let ?V = "lfp (contextual_step C D (or_mechanism C D) U)"
  show "\<exists>f. mechanism_on C D f \<and> edge_relevant_on C D f \<and> T \<subseteq> determined_region C D f U"
    by (intro exI[of _ "polar_mechanism C D ?V"] conjI polar_admissible polar_relevant)
      (use sub reachable_endpoint_attained[OF ctx] in simp)
qed

theorem some_context_determination_iff_reachable:
  assumes ctx: "U \<subseteq> efficacy_roots C D"
  shows "(\<exists>f. mechanism_on C D f \<and> T \<subseteq> determined_region C D f U)
    \<longleftrightarrow> T \<subseteq> root_reachable C D"
  using some_relevant_context_determination_iff_reachable[OF ctx, of T]
    determined_subset_reachable[OF _ ctx] by blast

theorem every_relevant_context_determination_iff_accessible:
  assumes ctx: "U \<subseteq> efficacy_roots C D"
  shows "(\<forall>f. mechanism_on C D f \<and> edge_relevant_on C D f \<longrightarrow>
    T \<subseteq> determined_region C D f U) \<longleftrightarrow> T \<subseteq> accessible_region C D"
proof
  assume all: "\<forall>f. mechanism_on C D f \<and> edge_relevant_on C D f \<longrightarrow> T \<subseteq> determined_region C D f U"
  let ?W = "accessible_region C D"
  let ?V = "lfp (contextual_step C D (and_mechanism C D) U)"
  have "T \<subseteq> determined_region C D (ambiguity_mechanism C D ?W ?V) U"
    using all accessible_endpoint_attained(1,2)[OF ctx] by blast
  then show "T \<subseteq> accessible_region C D"
    by (simp only: accessible_endpoint_attained(3)[OF ctx])
next
  assume "T \<subseteq> accessible_region C D"
  then show "\<forall>f. mechanism_on C D f \<and> edge_relevant_on C D f \<longrightarrow> T \<subseteq> determined_region C D f U"
    using accessible_subset_determined[OF _ ctx] by blast
qed

theorem every_context_determination_iff_accessible:
  assumes ctx: "U \<subseteq> efficacy_roots C D"
  shows "(\<forall>f. mechanism_on C D f \<longrightarrow> T \<subseteq> determined_region C D f U)
    \<longleftrightarrow> T \<subseteq> accessible_region C D"
  using every_relevant_context_determination_iff_accessible[OF ctx, of T]
    accessible_subset_determined[OF _ ctx] by blast

lemma determined_region_subset_carrier:
  assumes "mechanism_on C D f" "U \<subseteq> efficacy_roots C D"
  shows "determined_region C D f U \<subseteq> C"
  using contextual_extrema_subset_carrier(1)[OF assms] by (auto simp: determined_region_def)

lemma accessible_carrier_iff_well_founded:
  "C \<subseteq> accessible_region C D \<longleftrightarrow> well_founded_on C D"
  using lfp_and_subset_carrier[of C D] lfp_and_eq_carrier_iff_well_founded[of C D]
  by (auto simp: lfp_and_eq_accessible)

lemma reachable_carrier_iff_local_foundation:
  "C \<subseteq> root_reachable C D \<longleftrightarrow> local_foundation_on C D C"
  using reachable_subset_carrier[of C D] lfp_or_eq_carrier_iff_local_foundation[of C D]
  by (auto simp: lfp_or_eq_root_reachable)

lemma whole_determined_iff_unique:
  assumes "mechanism_on C D f" "U \<subseteq> efficacy_roots C D"
  shows "C \<subseteq> determined_region C D f U \<longleftrightarrow> (\<exists>!X. contextual_step C D f U X = X)"
  using determined_region_subset_carrier[OF assms] determined_carrier_iff_unique[OF assms] by blast

theorem some_relevant_context_unique_iff_local_foundation:
  assumes ctx: "U \<subseteq> efficacy_roots C D"
  shows "(\<exists>f. mechanism_on C D f \<and> edge_relevant_on C D f \<and>
    (\<exists>!X. contextual_step C D f U X = X)) \<longleftrightarrow> local_foundation_on C D C"
proof -
  have swap: "(\<exists>f. mechanism_on C D f \<and> edge_relevant_on C D f \<and> (\<exists>!X. contextual_step C D f U X = X)) = (\<exists>f. mechanism_on C D f \<and> edge_relevant_on C D f \<and> C \<subseteq> determined_region C D f U)"
  proof (rule ex_cong1)
    fix f
    show "(mechanism_on C D f \<and> edge_relevant_on C D f \<and> (\<exists>!X. contextual_step C D f U X = X)) = (mechanism_on C D f \<and> edge_relevant_on C D f \<and> C \<subseteq> determined_region C D f U)"
      by (cases "mechanism_on C D f") (simp_all add: whole_determined_iff_unique[OF _ ctx])
  qed
  show ?thesis
    using some_relevant_context_determination_iff_reachable[OF ctx, of C]
    by (simp only: swap reachable_carrier_iff_local_foundation)
qed

theorem some_context_unique_iff_local_foundation:
  assumes ctx: "U \<subseteq> efficacy_roots C D"
  shows "(\<exists>f. mechanism_on C D f \<and> (\<exists>!X. contextual_step C D f U X = X))
    \<longleftrightarrow> local_foundation_on C D C"
proof -
  have swap: "(\<exists>f. mechanism_on C D f \<and> (\<exists>!X. contextual_step C D f U X = X)) = (\<exists>f. mechanism_on C D f \<and> C \<subseteq> determined_region C D f U)"
  proof (rule ex_cong1)
    fix f
    show "(mechanism_on C D f \<and> (\<exists>!X. contextual_step C D f U X = X)) = (mechanism_on C D f \<and> C \<subseteq> determined_region C D f U)"
      by (cases "mechanism_on C D f") (simp_all add: whole_determined_iff_unique[OF _ ctx])
  qed
  show ?thesis
    using some_context_determination_iff_reachable[OF ctx, of C]
    by (simp only: swap reachable_carrier_iff_local_foundation)
qed

theorem every_relevant_context_unique_iff_well_founded:
  assumes ctx: "U \<subseteq> efficacy_roots C D"
  shows "(\<forall>f. mechanism_on C D f \<and> edge_relevant_on C D f \<longrightarrow>
    (\<exists>!X. contextual_step C D f U X = X)) \<longleftrightarrow> well_founded_on C D"
proof -
  have swap: "(\<forall>f. mechanism_on C D f \<and> edge_relevant_on C D f \<longrightarrow> (\<exists>!X. contextual_step C D f U X = X)) = (\<forall>f. mechanism_on C D f \<and> edge_relevant_on C D f \<longrightarrow> C \<subseteq> determined_region C D f U)"
  proof (rule all_cong1)
    fix f
    show "(mechanism_on C D f \<and> edge_relevant_on C D f \<longrightarrow> (\<exists>!X. contextual_step C D f U X = X)) = (mechanism_on C D f \<and> edge_relevant_on C D f \<longrightarrow> C \<subseteq> determined_region C D f U)"
      by (cases "mechanism_on C D f") (simp_all add: whole_determined_iff_unique[OF _ ctx])
  qed
  show ?thesis
    using every_relevant_context_determination_iff_accessible[OF ctx, of C]
    by (simp only: swap accessible_carrier_iff_well_founded)
qed

theorem every_context_unique_iff_well_founded:
  assumes ctx: "U \<subseteq> efficacy_roots C D"
  shows "(\<forall>f. mechanism_on C D f \<longrightarrow> (\<exists>!X. contextual_step C D f U X = X))
    \<longleftrightarrow> well_founded_on C D"
proof -
  have swap: "(\<forall>f. mechanism_on C D f \<longrightarrow> (\<exists>!X. contextual_step C D f U X = X)) = (\<forall>f. mechanism_on C D f \<longrightarrow> C \<subseteq> determined_region C D f U)"
  proof (rule all_cong1)
    fix f
    show "(mechanism_on C D f \<longrightarrow> (\<exists>!X. contextual_step C D f U X = X)) = (mechanism_on C D f \<longrightarrow> C \<subseteq> determined_region C D f U)"
      by (cases "mechanism_on C D f") (simp_all add: whole_determined_iff_unique[OF _ ctx])
  qed
  show ?thesis
    using every_context_determination_iff_accessible[OF ctx, of C]
    by (simp only: swap accessible_carrier_iff_well_founded)
qed

section \<open>One unrestricted mechanism for every root context\<close>

definition root_rank where
  "root_rank C D x = (LEAST n. \<exists>b \<in> efficacy_roots C D. ((dependency_on C D) ^^ n) b x)"

definition ranked_parent where
  "ranked_parent C D x = (SOME y. y \<in> efficacy_parents C D x \<and> root_rank C D y < root_rank C D x)"

definition forest_copy_mechanism where
  "forest_copy_mechanism C D x S \<longleftrightarrow>
    efficacy_parents C D x = {} \<or> ranked_parent C D x \<in> S"

lemma reachable_has_root_path:
  assumes "x \<in> root_reachable C D"
  shows "\<exists>n. \<exists>b \<in> efficacy_roots C D. ((dependency_on C D) ^^ n) b x"
proof -
  obtain b where root: "b \<in> efficacy_roots C D" and path: "(dependency_on C D)\<^sup>*\<^sup>* b x"
    using assms by (auto simp: root_reachable_def first_member_in_def dependency_ancestor_def
      efficacy_roots_def efficacy_parents_def independent_in_def)
  obtain n where "((dependency_on C D) ^^ n) b x"
    using rtranclp_imp_relpowp[OF path] by blast
  then show ?thesis using root by blast
qed

lemma root_rank_witness:
  assumes "x \<in> root_reachable C D"
  shows "\<exists>b \<in> efficacy_roots C D. ((dependency_on C D) ^^ root_rank C D x) b x"
  unfolding root_rank_def by (rule LeastI_ex, rule reachable_has_root_path[OF assms])

lemma root_rank_parent_exists:
  assumes reach: "x \<in> root_reachable C D" and nonroot: "efficacy_parents C D x \<noteq> {}"
  shows "\<exists>y \<in> efficacy_parents C D x. root_rank C D y < root_rank C D x"
proof -
  obtain b where root: "b \<in> efficacy_roots C D"
    and path: "((dependency_on C D) ^^ root_rank C D x) b x"
    using root_rank_witness[OF reach] by blast
  have ne: "root_rank C D x \<noteq> 0"
    using path root nonroot by (auto simp: efficacy_roots_def)
  obtain n where rank: "root_rank C D x = Suc n" using ne by (cases "root_rank C D x") auto
  obtain y where pathy: "((dependency_on C D) ^^ n) b y" and edge: "dependency_on C D y x"
    using path unfolding rank by (rule relpowp_Suc_E)
  have le: "root_rank C D y \<le> n"
    unfolding root_rank_def by (rule Least_le) (use root pathy in blast)
  show ?thesis using le edge rank by (auto simp: efficacy_parents_def dependency_on_def)
qed

lemma ranked_parent_properties:
  assumes "x \<in> root_reachable C D" "efficacy_parents C D x \<noteq> {}"
  shows "ranked_parent C D x \<in> efficacy_parents C D x"
    "root_rank C D (ranked_parent C D x) < root_rank C D x"
proof -
  have "ranked_parent C D x \<in> efficacy_parents C D x \<and>
      root_rank C D (ranked_parent C D x) < root_rank C D x"
    unfolding ranked_parent_def by (rule someI_ex) (use root_rank_parent_exists[OF assms] in blast)
  then show "ranked_parent C D x \<in> efficacy_parents C D x"
    "root_rank C D (ranked_parent C D x) < root_rank C D x" by auto
qed

lemma forest_copy_admissible:
  assumes reach: "C \<subseteq> root_reachable C D"
  shows "mechanism_on C D (forest_copy_mechanism C D)"
  unfolding mechanism_on_def
proof (intro ballI conjI)
  fix x
  assume xC: "x \<in> C"
  show "mono (forest_copy_mechanism C D x)" by (auto simp: forest_copy_mechanism_def mono_def)
  show "forest_copy_mechanism C D x {} = (efficacy_parents C D x = {})"
    by (simp add: forest_copy_mechanism_def)
  show "forest_copy_mechanism C D x (efficacy_parents C D x)"
    using ranked_parent_properties(1)[of x C D] reach xC by (auto simp: forest_copy_mechanism_def)
qed

lemma forest_copy_solutions_equal:
  assumes reach: "C \<subseteq> root_reachable C D"
    and ctx: "U \<subseteq> efficacy_roots C D"
    and fx: "contextual_step C D (forest_copy_mechanism C D) U X = X"
    and fy: "contextual_step C D (forest_copy_mechanism C D) U Y = Y"
  shows "X = Y"
proof -
  have XC: "X \<subseteq> C" and YC: "Y \<subseteq> C"
    by (rule contextual_fixed_subset_carrier[OF ctx fx], rule contextual_fixed_subset_carrier[OF ctx fy])
  have agree: "\<And>n x. root_rank C D x = n \<Longrightarrow> x \<in> C \<Longrightarrow> (x \<in> X) = (x \<in> Y)"
  proof -
    fix n
    show "\<And>x. root_rank C D x = n \<Longrightarrow> x \<in> C \<Longrightarrow> (x \<in> X) = (x \<in> Y)"
    proof (induction n rule: less_induct)
      case (less n)
      have vx: "(x \<in> X) = (x \<in> contextual_step C D (forest_copy_mechanism C D) U X)" by (simp only: fx)
      have vy: "(x \<in> Y) = (x \<in> contextual_step C D (forest_copy_mechanism C D) U Y)" by (simp only: fy)
      show ?case
      proof (cases "efficacy_parents C D x = {}")
        case True
        show ?thesis using vx vy True by (simp add: contextual_step_def source_off_step_def)
      next
        case False
        have xr: "x \<in> root_reachable C D" using reach less.prems(2) by blast
        have p: "ranked_parent C D x \<in> efficacy_parents C D x"
          by (rule ranked_parent_properties(1)[OF xr False])
        have lt: "root_rank C D (ranked_parent C D x) < n"
          using ranked_parent_properties(2)[OF xr False] less.prems(1) by simp
        have pC: "ranked_parent C D x \<in> C" using p by (simp add: efficacy_parents_def)
        have pa: "(ranked_parent C D x \<in> X) = (ranked_parent C D x \<in> Y)"
          by (rule less.IH[OF lt HOL.refl pC])
        show ?thesis using vx vy p pa by (simp add: contextual_step_def source_off_step_def forest_copy_mechanism_def)
      qed
    qed
  qed
  show ?thesis using agree[OF HOL.refl] XC YC by blast
qed

lemma forest_copy_every_context_unique:
  assumes reach: "C \<subseteq> root_reachable C D"
  shows "context_determinate C D (forest_copy_mechanism C D)"
  unfolding context_determinate_def
proof (intro allI impI)
  fix U
  assume ctx: "U \<subseteq> efficacy_roots C D"
  obtain X where fx: "contextual_step C D (forest_copy_mechanism C D) U X = X"
    using contextual_solution_exists[OF forest_copy_admissible[OF reach] ctx] by blast
  show "\<exists>!X. contextual_step C D (forest_copy_mechanism C D) U X = X"
  proof (rule ex1I[of _ X])
    show "contextual_step C D (forest_copy_mechanism C D) U X = X" by (fact fx)
    fix Y
    assume fy: "contextual_step C D (forest_copy_mechanism C D) U Y = Y"
    show "Y = X" by (rule forest_copy_solutions_equal[OF reach ctx fy fx])
  qed
qed

theorem some_mechanism_every_context_unique_iff_local_foundation:
  "(\<exists>f. mechanism_on C D f \<and> context_determinate C D f) \<longleftrightarrow> local_foundation_on C D C"
proof
  assume "\<exists>f. mechanism_on C D f \<and> context_determinate C D f"
  then obtain f where adm: "mechanism_on C D f" and all: "context_determinate C D f" by blast
  have uniq: "\<exists>!X. contextual_step C D f (efficacy_roots C D) X = X"
    using all by (simp add: context_determinate_def)
  have "\<exists>g. mechanism_on C D g \<and> (\<exists>!X. contextual_step C D g (efficacy_roots C D) X = X)"
    by (intro exI[of _ f] conjI) (fact adm, fact uniq)
  then show "local_foundation_on C D C"
    by (rule iffD1[OF some_context_unique_iff_local_foundation[OF subset_refl]])
next
  assume "local_foundation_on C D C"
  then have reach: "C \<subseteq> root_reachable C D" by (simp only: reachable_carrier_iff_local_foundation)
  show "\<exists>f. mechanism_on C D f \<and> context_determinate C D f"
    by (intro exI[of _ "forest_copy_mechanism C D"] conjI)
      (rule forest_copy_admissible[OF reach], rule forest_copy_every_context_unique[OF reach])
qed

end
