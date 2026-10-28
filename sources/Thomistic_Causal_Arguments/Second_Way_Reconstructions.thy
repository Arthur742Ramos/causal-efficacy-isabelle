theory Second_Way_Reconstructions
  imports Foundation_Separations
begin

section \<open>An Explicit Essentially Ordered-Series Interface\<close>

text \<open>
  The phrase essentially ordered is not identified with well-foundedness.  We
  expose one additional, source-facing predicate @{term derivative} for one
  explicit formal explication of the claim that members of a selected causal
  series have derivative causal efficacy.  In this explication, on the
  selected ancestry, derivative status is tied to the dependency relation
  itself: a member is derivative exactly when it has an immediate predecessor
  in the carrier.  Thus an independent member is a genuine non-derivative
  endpoint of the series, rather than merely receiving an arbitrary
  annotation.  This is a modeling choice, not a definition of derivative
  causal efficacy in every metaphysical respect.  The separate possession and
  exercise interface in the research layer deliberately tests a different
  local reading.  Well-foundedness remains a separate hypothesis,
  so this interface can describe an infinite derivative series as well as a
  founded one.
\<close>

definition essentially_ordered_series ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
where
  "essentially_ordered_series C D derivative a \<longleftrightarrow>
     a \<in> C \<and> derivative a \<and> grounded_in C D a \<and>
     (\<forall>x. dependency_ancestor C D x a \<longrightarrow>
       (derivative x \<longleftrightarrow> grounded_in C D x))"

lemma essentially_ordered_seriesD:
  assumes "essentially_ordered_series C D derivative a"
  shows "a \<in> C" "derivative a" "grounded_in C D a"
    and "\<forall>x. dependency_ancestor C D x a \<longrightarrow>
      (derivative x \<longleftrightarrow> grounded_in C D x)"
  using assms by (auto simp: essentially_ordered_series_def)

lemma essentially_ordered_series_derivative_iff:
  assumes "essentially_ordered_series C D derivative a"
    and "dependency_ancestor C D x a"
  shows "derivative x \<longleftrightarrow> grounded_in C D x"
  using assms by (auto simp: essentially_ordered_series_def)

lemma essentially_ordered_series_has_non_derivative_endpoint:
  assumes "essentially_ordered_series C D derivative a"
    and "first_member_in C D f a"
  shows "\<not> derivative f"
proof -
  have ancestor: "dependency_ancestor C D f a"
    using first_member_inD[OF assms(2)] by blast
  have independent: "independent_in C D f"
    using first_member_inD[OF assms(2)] by blast
  have not_grounded: "\<not> grounded_in C D f"
    using independent by (auto simp: grounded_in_def independent_in_def)
  have derivative_iff: "derivative f \<longleftrightarrow> grounded_in C D f"
    using essentially_ordered_series_derivative_iff[OF assms(1) ancestor] .
  then show ?thesis
    using not_grounded by blast
qed

lemma integer_predecessor_is_essentially_ordered:
  "essentially_ordered_series UNIV integer_predecessor_cause
    (\<lambda>_. True) (0 :: int)"
proof -
  have incoming0:
      "\<exists>y. integer_predecessor_cause y (0 :: int)"
    using integer_predecessor_has_incoming[of "0 :: int"] .
  have incoming:
      "\<forall>x. \<exists>y. integer_predecessor_cause y x"
    using integer_predecessor_has_incoming by blast
  show ?thesis
    unfolding essentially_ordered_series_def
    using incoming0 incoming
    by (auto simp: grounded_in_def integer_predecessor_cause_def)
qed

theorem essentially_ordered_does_not_mean_well_founded:
  "essentially_ordered_series UNIV integer_predecessor_cause
    (\<lambda>_. True) (0 :: int) \<and>
   \<not> well_founded_on UNIV integer_predecessor_cause"
  using integer_predecessor_is_essentially_ordered
    integer_predecessor_not_well_founded_on by blast

section \<open>Cohoe-Style Formal Translation Package\<close>

text \<open>
  The formal Cohoe-style translation keeps three interpretive commitments separate:
  there is a caused target, every caused target belongs to an essentially
  ordered derivative series, and a full-grounding relation supplies a
  foundation witness.  These are formal explications of source-level claims,
  not literal quotations.  The series predicate itself already states that its
  target lies in the carrier, so carrier membership is not an independent
  premise.  Because it also states that the target is grounded, no duplicate
  predecessor premise is needed.  The endpoint, nonemptiness, and
  ancestry-closure bridges from plural grounding to binary dependence are
  explicit locale assumptions.
\<close>

definition cohoe_second_way_premises ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "cohoe_second_way_premises C D G derivative caused \<longleftrightarrow>
     (\<exists>a. caused a) \<and>
     (\<forall>a. caused a \<longrightarrow>
       essentially_ordered_series C D derivative a) \<and>
     full_foundation_on C D G C"

definition cohoe_second_way_conclusion ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "cohoe_second_way_conclusion C D derivative caused \<longleftrightarrow>
     (\<forall>a. caused a \<longrightarrow>
       (\<exists>x. first_cause_in C D x a \<and> \<not> derivative x))"

locale cohoe_second_way_reconstruction =
  fixes C :: "'a set"
    and D :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and G :: "'a set \<Rightarrow> 'a \<Rightarrow> bool"
    and derivative :: "'a \<Rightarrow> bool"
    and caused :: "'a \<Rightarrow> bool"
  assumes cohoe_assumptions:
    "cohoe_second_way_premises C D G derivative caused"
    and singleton_endpoint:
    "\<And>x a. x \<in> C \<Longrightarrow> a \<in> C \<Longrightarrow> D x a \<Longrightarrow>
      partial_grounding_on C G x a"
    and full_nonempty:
    "\<And>S a. full_grounding_on C G S a \<Longrightarrow> S \<noteq> {}"
    and full_ancestry:
    "\<And>S a x. full_grounding_on C G S a \<Longrightarrow> x \<in> S \<Longrightarrow>
      dependency_ancestor C D x a"
begin

lemma cohoe_has_local_foundation:
  "local_foundation_on C D C"
proof -
  obtain "full_foundation_on C D G C"
    using cohoe_assumptions by (auto simp: cohoe_second_way_premises_def)
  then show ?thesis
    using full_foundation_implies_local_foundation[
      where C = C and D = D and G = G and R = C]
      singleton_endpoint full_nonempty full_ancestry by blast
qed

theorem cohoe_first_cause_of:
  assumes "caused a"
  shows "\<exists>x. first_cause_in C D x a"
proof -
  have premises_expanded:
      "(\<forall>a. caused a \<longrightarrow>
        essentially_ordered_series C D derivative a)"
    using cohoe_assumptions by (auto simp: cohoe_second_way_premises_def)
  obtain series: "essentially_ordered_series C D derivative a"
    using premises_expanded assms by blast
  have aC: "a \<in> C"
    using series by (rule essentially_ordered_seriesD)
  have grounded: "grounded_in C D a"
    using series by (rule essentially_ordered_seriesD)
  have local:
      "\<forall>u \<in> C. grounded_in C D u \<longrightarrow>
        (\<exists>f. first_member_in C D f u)"
    using cohoe_has_local_foundation
    by (simp add: local_foundation_on_def)
  have first_exists:
      "\<exists>f. first_member_in C D f a"
    using local aC grounded by blast
  then obtain f where first_member: "first_member_in C D f a"
    by blast
  have f_neq: "f \<noteq> a"
  proof
    assume "f = a"
    have f_independent: "independent_in C D f"
      using first_member_inD[OF first_member] by blast
    obtain b where "b \<in> C" and "D b a"
      using grounded by (auto simp: grounded_in_def)
    then show False
      using f_independent \<open>f = a\<close>
      by (auto simp: independent_in_def)
  qed
  show ?thesis
    using first_member f_neq
    by (auto simp: first_cause_in_def)
qed

theorem cohoe_non_derivative_first_cause_of:
  assumes "caused a"
  shows "\<exists>x. first_cause_in C D x a \<and> \<not> derivative x"
proof -
  have premises_expanded:
      "(\<forall>a. caused a \<longrightarrow>
        essentially_ordered_series C D derivative a)"
    using cohoe_assumptions by (auto simp: cohoe_second_way_premises_def)
  obtain series: "essentially_ordered_series C D derivative a"
    using premises_expanded assms by blast
  obtain x where first_cause: "first_cause_in C D x a"
    using cohoe_first_cause_of[OF assms] by blast
  have first_member: "first_member_in C D x a"
    using first_cause_inD[OF first_cause] by blast
  have not_derivative: "\<not> derivative x"
    using essentially_ordered_series_has_non_derivative_endpoint
      [OF series first_member] .
  then show ?thesis
    using first_cause by blast
qed

theorem cohoe_exact_conclusion:
  "cohoe_second_way_conclusion C D derivative caused"
  unfolding cohoe_second_way_conclusion_def
  using cohoe_non_derivative_first_cause_of by blast

theorem cohoe_global_first_cause:
  assumes "\<exists>a. caused a"
  shows "\<exists>x. independent_in C D x"
proof -
  obtain a where "caused a"
    using assms by blast
  obtain x where first_cause: "first_cause_in C D x a"
    using cohoe_first_cause_of[OF \<open>caused a\<close>] by blast
  have first_member: "first_member_in C D x a"
    using first_cause_inD[OF first_cause] by blast
  have independent: "independent_in C D x"
    using first_member_inD[OF first_member] by blast
  then show ?thesis by blast
qed

end

section \<open>Romero--Pérez Reconstruction\<close>

text \<open>
  Romero and Pérez present a first-order reconstruction in the source
  discussion.  The Isabelle/HOL encoding below is not itself a first-order
  sentence: @{term well_founded_on} is a higher-order predicate quantifying
  over carrier subsets.  The section therefore separates the source-level
  presentation from the formal encoding.  Its conclusion is the existence of
  at least one member of the carrier with no immediate dependency predecessor.
  It does not assert uniqueness, necessity, agency, or that the first member is
  the cause of the universe.  The equivalence between well-foundedness and
  absence of an infinite descending sequence uses Isabelle/HOL's classical
  well-foundedness library, including its standard choice-based background.
\<close>

definition romero_perez_second_way_premises ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "romero_perez_second_way_premises C D caused \<longleftrightarrow>
     (\<exists>a \<in> C. caused a) \<and>
     (\<forall>a. caused a \<longrightarrow>
       a \<in> C \<and> (\<exists>b \<in> C. D b a)) \<and>
     well_founded_on C D"

definition romero_perez_second_way_conclusion ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "romero_perez_second_way_conclusion C D \<longleftrightarrow>
     (\<exists>x \<in> C. independent_in C D x)"

locale romero_perez_second_way_reconstruction =
  fixes C :: "'a set"
    and D :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and caused :: "'a \<Rightarrow> bool"
  assumes rp_assumptions:
    "romero_perez_second_way_premises C D caused"
begin

lemma romero_perez_well_founded:
  "well_founded_on C D"
  using rp_assumptions by (auto simp: romero_perez_second_way_premises_def)

theorem romero_perez_exact_conclusion:
  "romero_perez_second_way_conclusion C D"
proof -
  obtain a where "a \<in> C" and "caused a"
    using rp_assumptions by (auto simp: romero_perez_second_way_premises_def)
  obtain x where "x \<in> C"
    and "dependency_ancestor C D x a"
    and "independent_in C D x"
    using well_founded_has_minimal_ancestor[
      OF romero_perez_well_founded \<open>a \<in> C\<close>] .
  then show ?thesis
    by (auto simp: romero_perez_second_way_conclusion_def)
qed

theorem romero_perez_first_cause_of:
  assumes "caused a"
  shows "\<exists>x. first_cause_in C D x a"
proof -
  have aC: "a \<in> C"
    using rp_assumptions assms
    by (auto simp: romero_perez_second_way_premises_def)
  have predecessor: "\<exists>b \<in> C. D b a"
    using rp_assumptions assms
    by (auto simp: romero_perez_second_way_premises_def)
  have grounded: "grounded_in C D a"
    using aC predecessor by (auto simp: grounded_in_def)
  obtain f where first_member: "first_member_in C D f a"
    using well_founded_implies_local_foundation[
      OF romero_perez_well_founded, of C]
      unfolding local_foundation_on_def
    using aC grounded by blast
  have f_neq: "f \<noteq> a"
  proof
    assume "f = a"
    have f_independent: "independent_in C D f"
      using first_member_inD[OF first_member] by blast
    obtain b where "b \<in> C" and "D b a"
      using predecessor by blast
    then show False
      using f_independent \<open>f = a\<close>
      by (auto simp: independent_in_def)
  qed
  show ?thesis
    using first_member f_neq
    by (auto simp: first_cause_in_def)
qed

end

section \<open>Comparison and Separation Summary\<close>

theorem cohoe_conclusion_implies_global_independence:
  assumes "cohoe_second_way_conclusion C D derivative caused"
    and "\<exists>a. caused a"
  shows "\<exists>x. independent_in C D x"
  using assms
  unfolding cohoe_second_way_conclusion_def
  by (meson first_cause_inD first_member_inD)

theorem romero_perez_premises_imply_cohoe_style_conclusion:
  assumes "romero_perez_second_way_premises C D caused"
  shows "\<forall>a. caused a \<longrightarrow>
    (\<exists>x. first_cause_in C D x a)"
proof (intro allI impI)
  fix a
  assume "caused a"
  interpret R: romero_perez_second_way_reconstruction C D caused
    by (rule romero_perez_second_way_reconstruction.intro[OF assms])
  show "\<exists>x. first_cause_in C D x a"
    using R.romero_perez_first_cause_of[OF \<open>caused a\<close>] .
qed

theorem local_foundation_does_not_imply_well_founded:
  "local_foundation_on UNIV pedestal_dependency UNIV \<and>
   \<not> well_founded_on UNIV pedestal_dependency"
  using pedestal_local_foundation pedestal_not_well_founded by blast

theorem global_foundation_does_not_imply_full_foundation:
  "local_foundation_on {0, 1, 2} paired_dependency {2} \<and>
   partial_grounding_on {0, 1, 2} paired_full_grounding 0 2 \<and>
   \<not> full_foundation_on {0, 1, 2} paired_dependency
     paired_full_grounding {2}"
  using partial_full_grounding_diverge by blast

theorem second_way_reconstruction_comparison:
  "(\<forall>a. caused a \<longrightarrow>
      (\<exists>x. first_cause_in C D x a)) \<longrightarrow>
      ((\<exists>a. caused a) \<longrightarrow> (\<exists>x. independent_in C D x))"
  by (auto simp: first_cause_in_def first_member_in_def
    independent_in_def)

theorem second_way_separation_summary:
  "(\<exists>a. essentially_ordered_series UNIV
      integer_predecessor_cause (\<lambda>_. True) (a :: int)) \<and>
   \<not> well_founded_on UNIV integer_predecessor_cause \<and>
   local_foundation_on UNIV pedestal_dependency UNIV \<and>
   global_foundation_on UNIV pedestal_dependency UNIV \<and>
   \<not> well_founded_on UNIV pedestal_dependency \<and>
   partial_grounding_on {0, 1, 2} paired_full_grounding 0 2 \<and>
   \<not> full_foundation_on {0, 1, 2} paired_dependency
     paired_full_grounding {2}"
  using integer_predecessor_is_essentially_ordered
    integer_predecessor_not_well_founded_on
    foundation_without_well_foundedness_pedestal
    partial_full_grounding_diverge by blast

theorem second_way_foundation_headline:
  assumes "(\<forall>a. caused a \<longrightarrow>
      (\<exists>x. first_cause_in C D x a))"
  shows "(\<exists>a. caused a) \<longrightarrow> (\<exists>x. independent_in C D x)"
  using second_way_reconstruction_comparison assms by blast

end
