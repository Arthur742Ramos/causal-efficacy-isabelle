theory Research_Results
  imports Second_Way_Reconstructions
begin

section \<open>Exact Binary Foundation Classification\<close>

text \<open>
  The central binary vocabulary admits an exact classification theorem.  Under
  carrier coverage, meaning that the selected target set is a subset of C, the
  two apparently different foundation notions coincide because the set of all
  independent members is itself a foundation set whenever local foundation
  holds.  This is stronger than merely recording the implication from a
  designated global witness to local first members.
\<close>

lemma integer_predecessor_not_local_foundation:
  "\<not> local_foundation_on UNIV integer_predecessor_cause UNIV"
proof
  assume local:
    "local_foundation_on UNIV integer_predecessor_cause UNIV"
  have grounded_zero:
      "grounded_in UNIV integer_predecessor_cause (0 :: int)"
    using integer_predecessor_has_incoming[of "0 :: int"]
    by (auto simp: grounded_in_def)
  obtain f where first:
      "first_member_in UNIV integer_predecessor_cause f (0 :: int)"
    using local grounded_zero
    by (auto simp: local_foundation_on_def)
  have independent:
      "independent_in UNIV integer_predecessor_cause f"
    using first by (rule first_member_inD)
  obtain y where "integer_predecessor_cause y f"
    using integer_predecessor_has_incoming[of f] by blast
  then show False
    using independent by (auto simp: independent_in_def)
qed

theorem binary_foundation_lattice:
  assumes "R \<subseteq> C"
  shows "(well_founded_on C D \<longleftrightarrow> chain_terminating_on C D) \<and>
   (well_founded_on C D \<longrightarrow> acyclic_on C D) \<and>
   (local_foundation_on C D R \<longleftrightarrow>
      global_foundation_on C D R) \<and>
   (well_founded_on C D \<longrightarrow> local_foundation_on C D R)"
  using well_founded_iff_chain_terminating
    well_founded_implies_acyclic
    local_foundation_iff_global_foundation[OF assms]
    well_founded_implies_local_foundation by blast

theorem finite_binary_foundation_lattice:
  assumes "finite C" and "R \<subseteq> C"
  shows
    "(well_founded_on C D \<longleftrightarrow> acyclic_on C D) \<and>
     (well_founded_on C D \<longleftrightarrow> chain_terminating_on C D) \<and>
     (local_foundation_on C D R \<longleftrightarrow>
        global_foundation_on C D R)"
  using finite_well_founded_iff_acyclic_on[OF assms(1)]
    well_founded_iff_chain_terminating
    local_foundation_iff_global_foundation[OF assms(2)] by blast

theorem finite_acyclic_implies_foundation:
  assumes "finite C" and "R \<subseteq> C" and "acyclic_on C D"
  shows "local_foundation_on C D R \<and>
    global_foundation_on C D R"
proof -
  have well_founded:
      "well_founded_on C D"
    using finite_well_founded_iff_acyclic_on[OF assms(1)] assms(3)
    by blast
  have local:
      "local_foundation_on C D R"
    using well_founded_implies_local_foundation[OF well_founded] .
  have global:
      "global_foundation_on C D R"
    using local_foundation_implies_global_foundation[OF local assms(2)] .
  show ?thesis
    using local global by blast
qed

theorem finite_foundation_not_acyclic_rooted_cycle:
  "finite ({0, 1, 2} :: nat set) \<and>
   local_foundation_on {0, 1, 2} rooted_cycle_dependency {0, 1, 2} \<and>
   global_foundation_on {0, 1, 2} rooted_cycle_dependency {0, 1, 2} \<and>
   \<not> acyclic_on {0, 1, 2} rooted_cycle_dependency"
  using local_foundation_not_acyclic_rooted_cycle by simp

theorem binary_foundation_separation_matrix:
  "acyclic_on UNIV integer_predecessor_cause \<and>
   \<not> local_foundation_on UNIV integer_predecessor_cause UNIV \<and>
   local_foundation_on UNIV pedestal_dependency UNIV \<and>
   global_foundation_on UNIV pedestal_dependency UNIV \<and>
   \<not> well_founded_on UNIV pedestal_dependency \<and>
   local_foundation_on {0, 1, 2} rooted_cycle_dependency {0, 1, 2} \<and>
   global_foundation_on {0, 1, 2} rooted_cycle_dependency {0, 1, 2} \<and>
   \<not> acyclic_on {0, 1, 2} rooted_cycle_dependency \<and>
   local_foundation_on {0, 1, 2} paired_dependency {2} \<and>
   \<not> full_foundation_on {0, 1, 2} paired_dependency
     paired_full_grounding {2}"
  using integer_predecessor_acyclic_on
    integer_predecessor_not_local_foundation
    foundation_without_well_foundedness_pedestal
    local_foundation_not_acyclic_rooted_cycle
    partial_full_grounding_diverge by blast

lemma integer_predecessor_is_essentially_ordered_grounded:
  "essentially_ordered_series UNIV integer_predecessor_cause
    (\<lambda>x. grounded_in UNIV integer_predecessor_cause x) (0 :: int)"
proof -
  have incoming:
      "\<forall>x. grounded_in UNIV integer_predecessor_cause x"
    using integer_predecessor_has_incoming
    by (auto simp: grounded_in_def)
  show ?thesis
    unfolding essentially_ordered_series_def
    using incoming by auto
qed

section \<open>Auxiliary Local Causal-Efficacy Stress Test\<close>

text \<open>
  As an auxiliary stress test rather than a full semantics of derivative
  causal efficacy, we introduce a small structural efficacy interface.
  @{term "H x p"} says
  that entity @{term x} possesses causal power @{term p}; @{term "E x p a"}
  says that it exercises that power toward effect @{term a}.  A locally
  borrowed exercise requires an immediate cause @{term x} of @{term a}, and
  requires the exercised power to be possessed by an earlier supporter of
  @{term x}.  This is deliberately local: it expresses transmission at each
  step without postulating a global well-foundedness or foundation principle.
\<close>

definition locally_borrowed_power_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> 'p \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> 'p \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   'a set \<Rightarrow> bool"
where
  "locally_borrowed_power_on C D H E R \<longleftrightarrow>
     (\<forall>a \<in> R. grounded_in C D a \<longrightarrow>
       (\<exists>x p y. x \<in> C \<and> D x a \<and> H x p \<and> E x p a \<and>
          y \<in> C \<and> D y x \<and> H y p))"

lemma integer_regress_has_local_borrowed_power:
  "locally_borrowed_power_on UNIV integer_predecessor_cause
    (\<lambda>(_ :: int) (_ :: unit). True)
    (\<lambda>(_ :: int) (_ :: unit) (_ :: int). True) UNIV"
proof -
  show ?thesis
    unfolding locally_borrowed_power_on_def
  proof (intro ballI impI)
    fix a :: int
    assume "a \<in> (UNIV :: int set)"
      and "grounded_in UNIV integer_predecessor_cause a"
    show "\<exists>x p y. x \<in> (UNIV :: int set) \<and>
        integer_predecessor_cause x a \<and>
        (\<lambda>(_ :: int) (_ :: unit). True) x p \<and>
        (\<lambda>(_ :: int) (_ :: unit) (_ :: int). True) x p a \<and>
        y \<in> (UNIV :: int set) \<and>
        integer_predecessor_cause y x \<and>
        (\<lambda>(_ :: int) (_ :: unit). True) y p"
      by (intro exI[of _ "a - 1"] exI[of _ "()"] exI[of _ "a - 2"])
        (simp add: integer_predecessor_cause_def)
  qed
qed

theorem essential_ordering_local_efficacy_countermodel:
  "acyclic_on UNIV integer_predecessor_cause \<and>
   locally_borrowed_power_on UNIV integer_predecessor_cause
     (\<lambda>(_ :: int) (_ :: unit). True)
     (\<lambda>(_ :: int) (_ :: unit) (_ :: int). True) UNIV \<and>
   essentially_ordered_series UNIV integer_predecessor_cause
     (\<lambda>x. grounded_in UNIV integer_predecessor_cause x) (0 :: int) \<and>
   \<not> local_foundation_on UNIV integer_predecessor_cause UNIV"
  using integer_predecessor_acyclic_on
    integer_regress_has_local_borrowed_power
    integer_predecessor_is_essentially_ordered_grounded
    integer_predecessor_not_local_foundation by blast

text \<open>
  Thus the formalized local support/transmission condition leaves an infinite
  descending regress possible.  Any theorem excluding this model must add a
  genuinely global principle such as well-foundedness, local/global foundation,
  or an equivalent termination condition.  This is a result about the precise
  interface formalized here, not a claim about every possible metaphysical
  theory of causal efficacy.
\<close>

end
