theory Premise_Minimality
  imports Research_Results
begin

section \<open>Premise Factorisation\<close>

text \<open>
  The Romero--Pérez package contains four logically distinct ingredients:
  existence of a caused item, carrier membership of caused items, an immediate
  predecessor for each caused item, and well-foundedness.  The published
  package writes the first two ingredients together in one bounded
  existential.  We factor them here so that premise deletion is a literal
  theorem rather than an informal checklist.
\<close>

definition rp_existence_premise ::
  "('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "rp_existence_premise caused \<longleftrightarrow> (\<exists>a. caused a)"

definition rp_carrier_premise ::
  "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "rp_carrier_premise C caused \<longleftrightarrow>
     (\<forall>a. caused a \<longrightarrow> a \<in> C)"

definition rp_predecessor_premise ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "rp_predecessor_premise C D caused \<longleftrightarrow>
     (\<forall>a. caused a \<longrightarrow> (\<exists>b \<in> C. D b a))"

definition rp_well_founded_premise ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "rp_well_founded_premise C D \<longleftrightarrow> well_founded_on C D"

definition rp_global_root_conclusion ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "rp_global_root_conclusion C D \<longleftrightarrow>
     (\<exists>x \<in> C. independent_in C D x)"

definition rp_local_first_cause_conclusion ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "rp_local_first_cause_conclusion C D caused \<longleftrightarrow>
     (\<forall>a. caused a \<longrightarrow>
       (\<exists>x. first_cause_in C D x a))"

definition rp_combined_conclusion ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "rp_combined_conclusion C D caused \<longleftrightarrow>
     rp_global_root_conclusion C D \<and>
     rp_local_first_cause_conclusion C D caused"

lemma romero_perez_premises_factor:
  "romero_perez_second_way_premises C D caused \<longleftrightarrow>
   rp_existence_premise caused \<and>
   rp_carrier_premise C caused \<and>
   rp_predecessor_premise C D caused \<and>
   rp_well_founded_premise C D"
  unfolding romero_perez_second_way_premises_def
    rp_existence_premise_def rp_carrier_premise_def
    rp_predecessor_premise_def rp_well_founded_premise_def
  by blast

lemma rp_premises_yield_combined_conclusion:
  assumes "rp_existence_premise caused"
    and "rp_carrier_premise C caused"
    and "rp_predecessor_premise C D caused"
    and "rp_well_founded_premise C D"
  shows "rp_combined_conclusion C D caused"
proof -
  have package:
      "romero_perez_second_way_premises C D caused"
    using assms by (simp add: romero_perez_premises_factor)
  interpret reconstruction:
      romero_perez_second_way_reconstruction C D caused
    by (rule romero_perez_second_way_reconstruction.intro[OF package])
  have global_raw:
      "romero_perez_second_way_conclusion C D"
    using reconstruction.romero_perez_exact_conclusion .
  have global:
      "rp_global_root_conclusion C D"
    using global_raw
    by (simp add: romero_perez_second_way_conclusion_def
      rp_global_root_conclusion_def)
  have local:
      "rp_local_first_cause_conclusion C D caused"
    unfolding rp_local_first_cause_conclusion_def
  proof (intro allI impI)
    fix a
    assume "caused a"
    then show "\<exists>x. first_cause_in C D x a"
      by (rule reconstruction.romero_perez_first_cause_of)
  qed
  show ?thesis
    unfolding rp_combined_conclusion_def
    using global local by blast
qed

lemma rp_local_first_cause_implies_global_root:
  assumes "rp_existence_premise caused"
    and "rp_local_first_cause_conclusion C D caused"
  shows "rp_global_root_conclusion C D"
proof -
  obtain a where "caused a"
    using assms(1) by (auto simp: rp_existence_premise_def)
  have local_expanded:
      "\<forall>a. caused a \<longrightarrow> (\<exists>x. first_cause_in C D x a)"
    using assms(2)
    by (simp only: rp_local_first_cause_conclusion_def)
  have first_exists:
      "\<exists>x. first_cause_in C D x a"
    using local_expanded \<open>caused a\<close> by blast
  obtain x where "first_cause_in C D x a"
    using first_exists by blast
  have first_member: "first_member_in C D x a"
    using first_cause_inD[OF \<open>first_cause_in C D x a\<close>] by blast
  have independent: "independent_in C D x"
    using first_member_inD[OF first_member] by blast
  have xC: "x \<in> C"
    using independent by (rule independent_inD)
  show ?thesis
    unfolding rp_global_root_conclusion_def
    using xC independent by blast
qed

section \<open>Romero--Pérez Deletion Certificates\<close>

text \<open>
  Each theorem below retains all but the named premise and refutes one fixed
  combined conclusion: a global independent root together with a first cause
  for every caused item.  This makes the deletion results premise-minimal
  relative to a single target, rather than switching conclusions between
  countermodels.
\<close>

lemma no_tranclp_if_no_edge:
  assumes "\<And>u v. \<not> R u v"
  shows "\<not> R\<^sup>+\<^sup>+ x y"
proof
  assume path: "R\<^sup>+\<^sup>+ x y"
  from path show False
  proof (induction rule: tranclp_induct)
    case base
    then show False
      using assms by blast
  next
    case (step y z)
    then show False
      using assms by blast
  qed
qed

lemma rp_empty_well_founded:
  "well_founded_on ({} :: nat set) (\<lambda>(_ :: nat) _. False)"
proof -
  have finite: "finite ({} :: nat set)"
    by simp
  have acyclic:
      "acyclic_on ({} :: nat set) (\<lambda>(_ :: nat) _. False)"
    unfolding acyclic_on_def
    by simp
  then show ?thesis
    using finite_well_founded_iff_acyclic_on[OF finite] by blast
qed

theorem romero_perez_delete_existence:
  "rp_carrier_premise ({} :: nat set) (\<lambda>_. False) \<and>
   rp_predecessor_premise {} (\<lambda>(_ :: nat) _. False) (\<lambda>_. False) \<and>
   rp_well_founded_premise {} (\<lambda>(_ :: nat) _. False) \<and>
   \<not> rp_combined_conclusion {} (\<lambda>(_ :: nat) _. False)
     (\<lambda>_. False)"
  using rp_empty_well_founded
  by (simp add: rp_carrier_premise_def rp_predecessor_premise_def
    rp_well_founded_premise_def rp_combined_conclusion_def
    rp_global_root_conclusion_def rp_local_first_cause_conclusion_def
    )

definition rp_no_carrier_dependency :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "rp_no_carrier_dependency x y \<longleftrightarrow> x = 0 \<and> y = 1"

definition rp_no_carrier_caused :: "nat \<Rightarrow> bool"
where
  "rp_no_carrier_caused a \<longleftrightarrow> a = 1"

lemma rp_no_carrier_well_founded:
  "well_founded_on {0 :: nat} rp_no_carrier_dependency"
proof -
  have finite: "finite ({0 :: nat})"
    by simp
  have acyclic:
      "acyclic_on {0 :: nat} rp_no_carrier_dependency"
    unfolding acyclic_on_def
  proof (intro ballI impI)
    fix x
    assume "x \<in> ({0 :: nat})"
    have no_edge:
        "\<And>u v. \<not> dependency_on {0 :: nat}
          rp_no_carrier_dependency u v"
      by (auto simp: dependency_on_def rp_no_carrier_dependency_def)
    show "\<not> (dependency_on {0 :: nat}
        rp_no_carrier_dependency)\<^sup>+\<^sup>+ x x"
      by (rule no_tranclp_if_no_edge[OF no_edge])
  qed
  then show ?thesis
    using finite_well_founded_iff_acyclic_on[OF finite] by blast
qed

theorem romero_perez_delete_carrier:
  "rp_existence_premise rp_no_carrier_caused \<and>
   rp_predecessor_premise {0 :: nat} rp_no_carrier_dependency
     rp_no_carrier_caused \<and>
   rp_well_founded_premise {0 :: nat} rp_no_carrier_dependency \<and>
   \<not> rp_carrier_premise {0 :: nat} rp_no_carrier_caused \<and>
   \<not> rp_combined_conclusion {0 :: nat}
     rp_no_carrier_dependency rp_no_carrier_caused"
  using rp_no_carrier_well_founded
  unfolding rp_existence_premise_def rp_predecessor_premise_def
    rp_well_founded_premise_def rp_carrier_premise_def
    rp_combined_conclusion_def rp_local_first_cause_conclusion_def
    rp_global_root_conclusion_def first_cause_in_def
    first_member_in_def dependency_ancestor_def dependency_on_def
    rp_no_carrier_dependency_def rp_no_carrier_caused_def
  by simp

definition rp_no_predecessor_dependency :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "rp_no_predecessor_dependency _ _ \<longleftrightarrow> False"

definition rp_no_predecessor_caused :: "nat \<Rightarrow> bool"
where
  "rp_no_predecessor_caused a \<longleftrightarrow> a = 0"

lemma rp_no_predecessor_well_founded:
  "well_founded_on {0 :: nat} rp_no_predecessor_dependency"
proof -
  have finite: "finite ({0 :: nat})"
    by simp
  have acyclic:
      "acyclic_on {0 :: nat} rp_no_predecessor_dependency"
    unfolding acyclic_on_def
  proof (intro ballI impI)
    fix x
    assume "x \<in> ({0 :: nat})"
    have no_edge:
        "\<And>u v. \<not> dependency_on {0 :: nat}
          rp_no_predecessor_dependency u v"
      by (simp add: dependency_on_def rp_no_predecessor_dependency_def)
    show "\<not> (dependency_on {0 :: nat}
        rp_no_predecessor_dependency)\<^sup>+\<^sup>+ x x"
      by (rule no_tranclp_if_no_edge[OF no_edge])
  qed
  then show ?thesis
    using finite_well_founded_iff_acyclic_on[OF finite] by blast
qed

theorem romero_perez_delete_predecessor:
  "rp_existence_premise rp_no_predecessor_caused \<and>
   rp_carrier_premise {0 :: nat} rp_no_predecessor_caused \<and>
   rp_well_founded_premise {0 :: nat} rp_no_predecessor_dependency \<and>
   \<not> rp_predecessor_premise {0 :: nat} rp_no_predecessor_dependency
     rp_no_predecessor_caused \<and>
   \<not> rp_combined_conclusion {0 :: nat}
     rp_no_predecessor_dependency rp_no_predecessor_caused"
  using rp_no_predecessor_well_founded
  unfolding rp_existence_premise_def rp_carrier_premise_def
    rp_well_founded_premise_def rp_predecessor_premise_def
    rp_combined_conclusion_def rp_local_first_cause_conclusion_def
    rp_global_root_conclusion_def first_cause_in_def
    first_member_in_def dependency_ancestor_def dependency_on_def
    rp_no_predecessor_dependency_def rp_no_predecessor_caused_def
  by simp

theorem romero_perez_delete_well_foundedness:
  "rp_existence_premise (\<lambda>(_ :: int). True) \<and>
   rp_carrier_premise UNIV (\<lambda>_. True) \<and>
   rp_predecessor_premise UNIV integer_predecessor_cause
     (\<lambda>_. True) \<and>
   \<not> rp_well_founded_premise UNIV integer_predecessor_cause \<and>
   \<not> rp_combined_conclusion UNIV integer_predecessor_cause
     (\<lambda>_. True)"
proof -
  have existence:
      "rp_existence_premise (\<lambda>(_ :: int). True)"
    by (simp add: rp_existence_premise_def)
  have carrier:
      "rp_carrier_premise UNIV (\<lambda>_. True)"
    by (simp add: rp_carrier_premise_def)
  have predecessor:
      "rp_predecessor_premise UNIV integer_predecessor_cause
        (\<lambda>_. True)"
    unfolding rp_predecessor_premise_def
  proof (intro allI impI)
    fix a :: int
    assume "(\<lambda>_. True) a"
    obtain b where "integer_predecessor_cause b a"
      using integer_predecessor_has_incoming[of a] by blast
    show "\<exists>b \<in> (UNIV :: int set).
        integer_predecessor_cause b a"
      using \<open>integer_predecessor_cause b a\<close> by blast
  qed
  have not_well_founded:
      "\<not> rp_well_founded_premise UNIV integer_predecessor_cause"
    using integer_predecessor_not_well_founded_on
    by (simp add: rp_well_founded_premise_def)
  have no_first_cause:
      "\<And>x a. \<not> first_cause_in UNIV integer_predecessor_cause x a"
  proof -
    fix x a :: int
    show "\<not> first_cause_in UNIV integer_predecessor_cause x a"
      using integer_predecessor_has_incoming[of x]
      by (auto simp: first_cause_in_def first_member_in_def
        independent_in_def integer_predecessor_cause_def)
  qed
  have not_local:
      "\<not> rp_local_first_cause_conclusion UNIV
        integer_predecessor_cause (\<lambda>_. True)"
    unfolding rp_local_first_cause_conclusion_def
    using no_first_cause
    by simp
  have not_combined:
      "\<not> rp_combined_conclusion UNIV integer_predecessor_cause
        (\<lambda>_. True)"
    unfolding rp_combined_conclusion_def
    using not_local by blast
  show ?thesis
  proof (rule conjI)
    show "rp_existence_premise (\<lambda>(_ :: int). True)"
      using existence .
    show "rp_carrier_premise UNIV (\<lambda>_. True) \<and>
        rp_predecessor_premise UNIV integer_predecessor_cause
          (\<lambda>_. True) \<and>
        \<not> rp_well_founded_premise UNIV integer_predecessor_cause \<and>
        \<not> rp_combined_conclusion UNIV
          integer_predecessor_cause (\<lambda>_. True)"
    proof (rule conjI)
      show "rp_carrier_premise UNIV (\<lambda>_. True)"
        using carrier .
      show "rp_predecessor_premise UNIV integer_predecessor_cause
          (\<lambda>_. True) \<and>
          \<not> rp_well_founded_premise UNIV integer_predecessor_cause \<and>
          \<not> rp_combined_conclusion UNIV
            integer_predecessor_cause (\<lambda>_. True)"
      proof (rule conjI)
        show "rp_predecessor_premise UNIV integer_predecessor_cause
            (\<lambda>_. True)"
          using predecessor .
        show "\<not> rp_well_founded_premise UNIV integer_predecessor_cause \<and>
            \<not> rp_combined_conclusion UNIV
              integer_predecessor_cause (\<lambda>_. True)"
        proof (rule conjI)
          show "\<not> rp_well_founded_premise UNIV integer_predecessor_cause"
            using not_well_founded .
          show "\<not> rp_combined_conclusion UNIV
              integer_predecessor_cause (\<lambda>_. True)"
            using not_combined .
        qed
      qed
    qed
  qed
qed

section \<open>Cohoe-Style Formal-Translation Deletion\<close>

definition cohoe_existence_premise ::
  "('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "cohoe_existence_premise caused \<longleftrightarrow> (\<exists>a. caused a)"

definition cohoe_carrier_premise ::
  "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "cohoe_carrier_premise C caused \<longleftrightarrow>
     (\<forall>a. caused a \<longrightarrow> a \<in> C)"

definition cohoe_essential_ordering_premise ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "cohoe_essential_ordering_premise C D derivative caused \<longleftrightarrow>
     (\<forall>a. caused a \<longrightarrow>
       essentially_ordered_series C D derivative a)"

lemma cohoe_essential_ordering_implies_carrier:
  assumes essential:
    "cohoe_essential_ordering_premise C D derivative caused"
  shows "cohoe_carrier_premise C caused"
proof -
  have essential_all:
      "\<forall>a. caused a \<longrightarrow>
        essentially_ordered_series C D derivative a"
    using essential
    by (simp only: cohoe_essential_ordering_premise_def)
  show ?thesis
    unfolding cohoe_carrier_premise_def
  proof (intro allI impI)
    fix a
    assume caused_a: "caused a"
    obtain series: "essentially_ordered_series C D derivative a"
      using essential_all caused_a by blast
    show "a \<in> C"
      using series by (rule essentially_ordered_seriesD)
  qed
qed

definition cohoe_full_foundation_premise ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "cohoe_full_foundation_premise C D G \<longleftrightarrow>
     full_foundation_on C D G C"

definition cohoe_singleton_endpoint_premise ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "cohoe_singleton_endpoint_premise C D G \<longleftrightarrow>
     (\<forall>x a. x \<in> C \<longrightarrow> a \<in> C \<longrightarrow> D x a \<longrightarrow>
       partial_grounding_on C G x a)"

definition cohoe_full_nonempty_premise ::
  "'a set \<Rightarrow> ('a set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "cohoe_full_nonempty_premise C G \<longleftrightarrow>
     (\<forall>S a. full_grounding_on C G S a \<longrightarrow> S \<noteq> {})"

definition cohoe_full_ancestry_premise ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "cohoe_full_ancestry_premise C D G \<longleftrightarrow>
     (\<forall>S a x. full_grounding_on C G S a \<longrightarrow> x \<in> S \<longrightarrow>
       dependency_ancestor C D x a)"

definition cohoe_global_non_derivative_conclusion ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "cohoe_global_non_derivative_conclusion C D derivative \<longleftrightarrow>
     (\<exists>x. independent_in C D x \<and> \<not> derivative x)"

lemma cohoe_premises_factor:
  "cohoe_second_way_premises C D G derivative caused \<longleftrightarrow>
   cohoe_existence_premise caused \<and>
   cohoe_essential_ordering_premise C D derivative caused \<and>
   cohoe_full_foundation_premise C D G"
  unfolding cohoe_second_way_premises_def
    cohoe_existence_premise_def
    cohoe_essential_ordering_premise_def
    cohoe_full_foundation_premise_def
  by blast

lemma cohoe_premises_yield_global_non_derivative:
  assumes "cohoe_existence_premise caused"
    and "cohoe_essential_ordering_premise C D derivative caused"
    and "cohoe_full_foundation_premise C D G"
    and "cohoe_singleton_endpoint_premise C D G"
    and "cohoe_full_nonempty_premise C G"
    and "cohoe_full_ancestry_premise C D G"
  shows "cohoe_global_non_derivative_conclusion C D derivative"
proof -
  have package:
      "cohoe_second_way_premises C D G derivative caused"
    using assms(1-3) by (simp add: cohoe_premises_factor)
  have endpoint_all:
      "\<forall>x a. x \<in> C \<longrightarrow> a \<in> C \<longrightarrow> D x a \<longrightarrow>
        partial_grounding_on C G x a"
    using assms(4)
    by (simp only: cohoe_singleton_endpoint_premise_def)
  have nonempty_all:
      "\<forall>S a. full_grounding_on C G S a \<longrightarrow> S \<noteq> {}"
    using assms(5)
    by (simp only: cohoe_full_nonempty_premise_def)
  have ancestry_all:
      "\<forall>S a x. full_grounding_on C G S a \<longrightarrow> x \<in> S \<longrightarrow>
        dependency_ancestor C D x a"
    using assms(6)
    by (simp only: cohoe_full_ancestry_premise_def)
  interpret reconstruction:
      cohoe_second_way_reconstruction C D G derivative caused
  proof (rule cohoe_second_way_reconstruction.intro[OF package])
    show "\<And>x a. x \<in> C \<Longrightarrow> a \<in> C \<Longrightarrow> D x a \<Longrightarrow>
        partial_grounding_on C G x a"
      using endpoint_all by blast
    show "\<And>S a. full_grounding_on C G S a \<Longrightarrow> S \<noteq> {}"
      using nonempty_all by blast
    show "\<And>S a x. full_grounding_on C G S a \<Longrightarrow> x \<in> S \<Longrightarrow>
        dependency_ancestor C D x a"
      using ancestry_all by blast
  qed
  have exists_caused: "\<exists>a. caused a"
    using assms(1) by (simp only: cohoe_existence_premise_def)
  obtain a where "caused a"
    using exists_caused by blast
  obtain x where first_cause:
      "first_cause_in C D x a \<and> \<not> derivative x"
    using reconstruction.cohoe_non_derivative_first_cause_of[
      OF \<open>caused a\<close>] by blast
  have first_cause_only: "first_cause_in C D x a"
    using first_cause by (rule conjunct1)
  have first_member: "first_member_in C D x a"
    using first_cause_inD[OF first_cause_only] by blast
  have not_derivative: "\<not> derivative x"
    using first_cause by (rule conjunct2)
  have independent: "independent_in C D x"
    using first_member by (rule first_member_inD)
  show ?thesis
    unfolding cohoe_global_non_derivative_conclusion_def
    using independent not_derivative by blast
qed

definition cohoe_chain_dependency :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "cohoe_chain_dependency x y \<longleftrightarrow> x = 0 \<and> y = 1"

definition cohoe_chain_grounding :: "nat set \<Rightarrow> nat \<Rightarrow> bool"
where
  "cohoe_chain_grounding S a \<longleftrightarrow> S = {0} \<and> a = 1"

definition cohoe_integer_singleton_grounding ::
  "int set \<Rightarrow> int \<Rightarrow> bool"
where
  "cohoe_integer_singleton_grounding S a \<longleftrightarrow>
     (\<exists>x. S = {x} \<and> integer_predecessor_cause x a)"

definition cohoe_integer_empty_or_singleton_grounding ::
  "int set \<Rightarrow> int \<Rightarrow> bool"
where
  "cohoe_integer_empty_or_singleton_grounding S a \<longleftrightarrow>
     S = {} \<or>
     (\<exists>x. S = {x} \<and> integer_predecessor_cause x a)"

lemma cohoe_chain_full_foundation:
  "full_foundation_on {0, 1} cohoe_chain_dependency
    cohoe_chain_grounding {0, 1}"
proof -
  have foundation:
      "full_foundation_for {0, 1} cohoe_chain_dependency
        cohoe_chain_grounding {0, 1} {0}"
    unfolding full_foundation_for_def
    by (simp add: full_grounding_on_def partial_grounding_on_def
      grounded_in_def dependency_on_def cohoe_chain_dependency_def
      cohoe_chain_grounding_def independent_in_def)
  then show ?thesis
    by (rule full_foundation_onI)
qed

lemma cohoe_chain_endpoint:
  "cohoe_singleton_endpoint_premise {0, 1} cohoe_chain_dependency
    cohoe_chain_grounding"
  unfolding cohoe_singleton_endpoint_premise_def
proof (intro allI impI)
  fix x a :: nat
  assume "x \<in> {0, 1}" "a \<in> {0, 1}"
    and Dxa: "cohoe_chain_dependency x a"
  have x0: "x = 0"
    using Dxa by (simp add: cohoe_chain_dependency_def)
  have a1: "a = 1"
    using Dxa by (simp add: cohoe_chain_dependency_def)
  have full:
      "full_grounding_on {0, 1} cohoe_chain_grounding {0} 1"
    by (simp add: full_grounding_on_def cohoe_chain_grounding_def)
  have partial01:
      "partial_grounding_on {0, 1} cohoe_chain_grounding 0 1"
    using full by (rule partial_grounding_onI) simp
  show "partial_grounding_on {0, 1} cohoe_chain_grounding x a"
    using partial01 x0 a1 by simp
qed

lemma cohoe_chain_nonempty:
  "cohoe_full_nonempty_premise {0, 1} cohoe_chain_grounding"
  unfolding cohoe_full_nonempty_premise_def
  by (auto simp: full_grounding_on_def cohoe_chain_grounding_def)

lemma cohoe_chain_ancestry:
  "cohoe_full_ancestry_premise {0, 1} cohoe_chain_dependency
    cohoe_chain_grounding"
  unfolding cohoe_full_ancestry_premise_def
proof (intro allI impI impI)
  fix S :: "nat set" and a x :: nat
  assume full: "full_grounding_on {0, 1} cohoe_chain_grounding S a"
    and "x \<in> S"
  have S0: "S = {0}" and a1: "a = 1"
    using full by (auto simp: full_grounding_on_def cohoe_chain_grounding_def)
  have x0: "x = 0"
    using S0 \<open>x \<in> S\<close> by simp
  show "dependency_ancestor {0, 1} cohoe_chain_dependency x a"
    using x0 a1 by (simp add: dependency_ancestor_direct
      cohoe_chain_dependency_def)
qed

theorem cohoe_delete_existence:
  "cohoe_essential_ordering_premise {} (\<lambda>(_ :: nat) _. False)
     (\<lambda>_. False) (\<lambda>_. False) \<and>
   cohoe_full_foundation_premise {} (\<lambda>(_ :: nat) _. False)
     (\<lambda>_ _. False) \<and>
   cohoe_singleton_endpoint_premise {} (\<lambda>(_ :: nat) _. False)
     (\<lambda>_ _. False) \<and>
   cohoe_full_nonempty_premise {} (\<lambda>_ _. False) \<and>
   cohoe_full_ancestry_premise {} (\<lambda>(_ :: nat) _. False)
     (\<lambda>_ _. False) \<and>
   \<not> cohoe_global_non_derivative_conclusion {}
     (\<lambda>(_ :: nat) _. False) (\<lambda>_. False)"
  by (simp add: cohoe_essential_ordering_premise_def
    cohoe_full_foundation_premise_def
    cohoe_singleton_endpoint_premise_def
    cohoe_full_nonempty_premise_def
    cohoe_full_ancestry_premise_def
    cohoe_global_non_derivative_conclusion_def
    full_foundation_on_def full_foundation_for_def
    full_grounding_on_def partial_grounding_on_def
    independent_in_def)

theorem cohoe_delete_essential_ordering:
  "cohoe_existence_premise (\<lambda>(a :: nat). a = 1) \<and>
   cohoe_full_foundation_premise {0, 1} cohoe_chain_dependency
     cohoe_chain_grounding \<and>
   cohoe_singleton_endpoint_premise {0, 1} cohoe_chain_dependency
     cohoe_chain_grounding \<and>
   cohoe_full_nonempty_premise {0, 1} cohoe_chain_grounding \<and>
   cohoe_full_ancestry_premise {0, 1} cohoe_chain_dependency
     cohoe_chain_grounding \<and>
   \<not> cohoe_global_non_derivative_conclusion {0, 1}
     cohoe_chain_dependency (\<lambda>_. True)"
  using cohoe_chain_full_foundation cohoe_chain_endpoint
    cohoe_chain_nonempty cohoe_chain_ancestry
  by (simp add: cohoe_existence_premise_def
    cohoe_full_foundation_premise_def
    cohoe_singleton_endpoint_premise_def
    cohoe_full_nonempty_premise_def cohoe_full_ancestry_premise_def
    cohoe_global_non_derivative_conclusion_def)

lemma cohoe_integer_singleton_endpoint:
  "cohoe_singleton_endpoint_premise UNIV integer_predecessor_cause
    cohoe_integer_singleton_grounding"
  unfolding cohoe_singleton_endpoint_premise_def
proof (intro allI impI)
  fix x a :: int
  assume "x \<in> (UNIV :: int set)" "a \<in> (UNIV :: int set)"
    and Dxa: "integer_predecessor_cause x a"
  have full:
      "full_grounding_on (UNIV :: int set)
        cohoe_integer_singleton_grounding {x} a"
    by (simp add: full_grounding_on_def
      cohoe_integer_singleton_grounding_def Dxa)
  show "partial_grounding_on (UNIV :: int set)
      cohoe_integer_singleton_grounding x a"
    using partial_grounding_onI[OF full] by simp
qed

lemma cohoe_integer_singleton_nonempty:
  "cohoe_full_nonempty_premise (UNIV :: int set)
    cohoe_integer_singleton_grounding"
  unfolding cohoe_full_nonempty_premise_def
proof (intro allI impI)
  fix S :: "int set" and a :: int
  assume full:
    "full_grounding_on (UNIV :: int set)
      cohoe_integer_singleton_grounding S a"
  obtain x where "S = {x}"
    using full by (auto simp: full_grounding_on_def
      cohoe_integer_singleton_grounding_def)
  show "S \<noteq> {}"
    using \<open>S = {x}\<close> by simp
qed

lemma cohoe_integer_singleton_ancestry:
  "cohoe_full_ancestry_premise (UNIV :: int set)
    integer_predecessor_cause cohoe_integer_singleton_grounding"
  unfolding cohoe_full_ancestry_premise_def
proof (intro allI impI impI)
  fix S :: "int set" and a x :: int
  assume full:
    "full_grounding_on (UNIV :: int set)
      cohoe_integer_singleton_grounding S a"
    and "x \<in> S"
  obtain y where "S = {y}" and Dya:
      "integer_predecessor_cause y a"
    using full by (auto simp: full_grounding_on_def
      cohoe_integer_singleton_grounding_def)
  have xy: "x = y"
    using \<open>S = {y}\<close> \<open>x \<in> S\<close> by simp
  show "dependency_ancestor (UNIV :: int set)
      integer_predecessor_cause x a"
    using dependency_ancestor_direct[
      where C = "UNIV :: int set"
        and D = integer_predecessor_cause and x = y and y = a]
      Dya xy by simp
qed

definition cohoe_empty_grounding :: "int set \<Rightarrow> int \<Rightarrow> bool"
where
  "cohoe_empty_grounding S a \<longleftrightarrow> False"

lemma cohoe_empty_full_foundation:
  "full_foundation_on (UNIV :: int set) integer_predecessor_cause
    cohoe_empty_grounding UNIV"
proof -
  have foundation:
      "full_foundation_for (UNIV :: int set) integer_predecessor_cause
        cohoe_empty_grounding UNIV {}"
    unfolding full_foundation_for_def
    by (simp add: cohoe_empty_grounding_def grounded_in_def
      partial_grounding_on_def full_grounding_on_def independent_in_def)
  then show ?thesis
    by (rule full_foundation_onI)
qed

lemma cohoe_empty_nonempty:
  "cohoe_full_nonempty_premise (UNIV :: int set)
    cohoe_empty_grounding"
  unfolding cohoe_full_nonempty_premise_def
  by (simp add: full_grounding_on_def cohoe_empty_grounding_def)

lemma cohoe_empty_ancestry:
  "cohoe_full_ancestry_premise (UNIV :: int set)
    integer_predecessor_cause cohoe_empty_grounding"
  unfolding cohoe_full_ancestry_premise_def
  by (simp add: full_grounding_on_def cohoe_empty_grounding_def)

lemma cohoe_empty_endpoint_fails:
  "\<not> cohoe_singleton_endpoint_premise (UNIV :: int set)
    integer_predecessor_cause cohoe_empty_grounding"
proof
  assume endpoint:
    "cohoe_singleton_endpoint_premise (UNIV :: int set)
      integer_predecessor_cause cohoe_empty_grounding"
  have endpoint_all:
      "\<And>x a. x \<in> (UNIV :: int set) \<Longrightarrow>
        a \<in> (UNIV :: int set) \<Longrightarrow>
        integer_predecessor_cause x a \<Longrightarrow>
        partial_grounding_on (UNIV :: int set) cohoe_empty_grounding x a"
    using endpoint
    by (simp only: cohoe_singleton_endpoint_premise_def)
  have partial:
      "partial_grounding_on (UNIV :: int set) cohoe_empty_grounding (-1) 0"
  proof (rule endpoint_all)
    show "(-1 :: int) \<in> (UNIV :: int set)" by simp
    show "(0 :: int) \<in> (UNIV :: int set)" by simp
    show "integer_predecessor_cause (-1 :: int) 0"
      by (simp add: integer_predecessor_cause_def)
  qed
  show False
    using partial
    by (simp add: partial_grounding_on_def full_grounding_on_def
      cohoe_empty_grounding_def)
qed

theorem cohoe_delete_singleton_endpoint:
  "cohoe_existence_premise (\<lambda>(a :: int). a = 0) \<and>
   cohoe_essential_ordering_premise (UNIV :: int set)
     integer_predecessor_cause (\<lambda>_::int. True) (\<lambda>a::int. a = 0) \<and>
   cohoe_full_foundation_premise (UNIV :: int set)
     integer_predecessor_cause cohoe_empty_grounding \<and>
   \<not> cohoe_singleton_endpoint_premise (UNIV :: int set)
     integer_predecessor_cause cohoe_empty_grounding \<and>
   cohoe_full_nonempty_premise (UNIV :: int set) cohoe_empty_grounding \<and>
   cohoe_full_ancestry_premise (UNIV :: int set) integer_predecessor_cause
     cohoe_empty_grounding \<and>
   \<not> cohoe_global_non_derivative_conclusion (UNIV :: int set)
     integer_predecessor_cause (\<lambda>_::int. True)"
proof -
  have existence:
      "cohoe_existence_premise (\<lambda>(a :: int). a = 0)"
    by (simp add: cohoe_existence_premise_def)
  have essential:
      "cohoe_essential_ordering_premise (UNIV :: int set)
        integer_predecessor_cause (\<lambda>_::int. True) (\<lambda>a::int. a = 0)"
    unfolding cohoe_essential_ordering_premise_def
  proof (intro allI impI)
    fix a :: int
    assume "a = 0"
    then show "essentially_ordered_series UNIV integer_predecessor_cause
        (\<lambda>_. True) a"
      using integer_predecessor_is_essentially_ordered by simp
  qed
  have full:
      "cohoe_full_foundation_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_empty_grounding"
    unfolding cohoe_full_foundation_premise_def
    by (rule cohoe_empty_full_foundation)
  have not_endpoint:
      "\<not> cohoe_singleton_endpoint_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_empty_grounding"
    by (rule cohoe_empty_endpoint_fails)
  have nonempty:
      "cohoe_full_nonempty_premise (UNIV :: int set) cohoe_empty_grounding"
    using cohoe_empty_nonempty by blast
  have ancestry:
      "cohoe_full_ancestry_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_empty_grounding"
    by (rule cohoe_empty_ancestry)
  have not_global:
      "\<not> cohoe_global_non_derivative_conclusion (UNIV :: int set)
        integer_predecessor_cause (\<lambda>_::int. True)"
    by (simp add: cohoe_global_non_derivative_conclusion_def)
  show ?thesis
    using existence essential full not_endpoint nonempty ancestry
      not_global by blast
qed

lemma cohoe_empty_or_singleton_full_foundation:
  "full_foundation_on (UNIV :: int set) integer_predecessor_cause
    cohoe_integer_empty_or_singleton_grounding UNIV"
proof -
  have foundation:
      "full_foundation_for (UNIV :: int set) integer_predecessor_cause
        cohoe_integer_empty_or_singleton_grounding UNIV {}"
    unfolding full_foundation_for_def
    by (simp add: full_grounding_on_def
      cohoe_integer_empty_or_singleton_grounding_def)
  then show ?thesis
    by (rule full_foundation_onI)
qed

lemma cohoe_empty_or_singleton_endpoint:
  "cohoe_singleton_endpoint_premise (UNIV :: int set)
    integer_predecessor_cause cohoe_integer_empty_or_singleton_grounding"
  unfolding cohoe_singleton_endpoint_premise_def
proof (intro allI impI)
  fix x a :: int
  assume "x \<in> (UNIV :: int set)" "a \<in> (UNIV :: int set)"
    and Dxa: "integer_predecessor_cause x a"
  have full:
      "full_grounding_on (UNIV :: int set)
        cohoe_integer_empty_or_singleton_grounding {x} a"
    by (simp add: full_grounding_on_def
      cohoe_integer_empty_or_singleton_grounding_def Dxa)
  show "partial_grounding_on (UNIV :: int set)
      cohoe_integer_empty_or_singleton_grounding x a"
    using partial_grounding_onI[OF full] by simp
qed

lemma cohoe_empty_or_singleton_nonempty_fails:
  "\<not> cohoe_full_nonempty_premise (UNIV :: int set)
    cohoe_integer_empty_or_singleton_grounding"
proof
  assume nonempty:
    "cohoe_full_nonempty_premise (UNIV :: int set)
      cohoe_integer_empty_or_singleton_grounding"
  have empty_full:
      "full_grounding_on (UNIV :: int set)
        cohoe_integer_empty_or_singleton_grounding {} 0"
    by (simp add: full_grounding_on_def
      cohoe_integer_empty_or_singleton_grounding_def)
  have nonempty_all:
      "\<forall>S a. (full_grounding_on (UNIV :: int set)
        cohoe_integer_empty_or_singleton_grounding S a \<longrightarrow>
        S \<noteq> {})"
    using nonempty
    by (simp only: cohoe_full_nonempty_premise_def)
  have false_nonempty: "({} :: int set) \<noteq> {}"
    using nonempty_all empty_full by blast
  show False
    using false_nonempty by simp
qed

lemma cohoe_empty_or_singleton_ancestry:
  "cohoe_full_ancestry_premise (UNIV :: int set)
    integer_predecessor_cause cohoe_integer_empty_or_singleton_grounding"
  unfolding cohoe_full_ancestry_premise_def
proof (intro allI impI impI)
  fix S :: "int set" and a x :: int
  assume full:
    "full_grounding_on (UNIV :: int set)
      cohoe_integer_empty_or_singleton_grounding S a"
    and "x \<in> S"
  have G:
      "S = {} \<or>
       (\<exists>y. S = {y} \<and> integer_predecessor_cause y a)"
    using full
    by (simp only: full_grounding_on_def
      cohoe_integer_empty_or_singleton_grounding_def)
  show "dependency_ancestor (UNIV :: int set)
      integer_predecessor_cause x a"
  proof (rule disjE[OF G])
    assume S_empty: "S = {}"
    then show ?thesis
      using \<open>x \<in> S\<close> by simp
  next
    assume singleton:
      "\<exists>y. S = {y} \<and> integer_predecessor_cause y a"
    obtain y where "S = {y}" and Dya:
        "integer_predecessor_cause y a"
      using singleton by blast
    have xy: "x = y"
      using \<open>S = {y}\<close> \<open>x \<in> S\<close> by simp
    show ?thesis
      using dependency_ancestor_direct[
        where C = "UNIV :: int set"
          and D = integer_predecessor_cause and x = y and y = a]
        Dya xy by simp
  qed
qed

theorem cohoe_delete_full_nonempty:
  "cohoe_existence_premise (\<lambda>(a :: int). a = 0) \<and>
   cohoe_essential_ordering_premise (UNIV :: int set)
     integer_predecessor_cause (\<lambda>_::int. True) (\<lambda>a::int. a = 0) \<and>
   cohoe_full_foundation_premise (UNIV :: int set)
     integer_predecessor_cause cohoe_integer_empty_or_singleton_grounding \<and>
   cohoe_singleton_endpoint_premise (UNIV :: int set)
     integer_predecessor_cause cohoe_integer_empty_or_singleton_grounding \<and>
   \<not> cohoe_full_nonempty_premise (UNIV :: int set)
     cohoe_integer_empty_or_singleton_grounding \<and>
   cohoe_full_ancestry_premise (UNIV :: int set) integer_predecessor_cause
     cohoe_integer_empty_or_singleton_grounding \<and>
   \<not> cohoe_global_non_derivative_conclusion (UNIV :: int set)
     integer_predecessor_cause (\<lambda>_::int. True)"
proof -
  have existence:
      "cohoe_existence_premise (\<lambda>(a :: int). a = 0)"
    by (simp add: cohoe_existence_premise_def)
  have essential:
      "cohoe_essential_ordering_premise (UNIV :: int set)
        integer_predecessor_cause (\<lambda>_::int. True) (\<lambda>a::int. a = 0)"
    unfolding cohoe_essential_ordering_premise_def
  proof (intro allI impI)
    fix a :: int
    assume "a = 0"
    then show "essentially_ordered_series UNIV integer_predecessor_cause
        (\<lambda>_. True) a"
      using integer_predecessor_is_essentially_ordered by simp
  qed
  have full:
      "cohoe_full_foundation_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_integer_empty_or_singleton_grounding"
    unfolding cohoe_full_foundation_premise_def
    by (rule cohoe_empty_or_singleton_full_foundation)
  have endpoint:
      "cohoe_singleton_endpoint_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_integer_empty_or_singleton_grounding"
    by (rule cohoe_empty_or_singleton_endpoint)
  have not_nonempty:
      "\<not> cohoe_full_nonempty_premise (UNIV :: int set)
        cohoe_integer_empty_or_singleton_grounding"
    by (rule cohoe_empty_or_singleton_nonempty_fails)
  have ancestry:
      "cohoe_full_ancestry_premise (UNIV :: int set) integer_predecessor_cause
        cohoe_integer_empty_or_singleton_grounding"
    by (rule cohoe_empty_or_singleton_ancestry)
  have not_global:
      "\<not> cohoe_global_non_derivative_conclusion (UNIV :: int set)
        integer_predecessor_cause (\<lambda>_::int. True)"
    by (simp add: cohoe_global_non_derivative_conclusion_def)
  show ?thesis
    using existence essential full endpoint not_nonempty ancestry
      not_global by blast
qed

definition cohoe_cycle_dependency :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "cohoe_cycle_dependency x y \<longleftrightarrow>
     (x = 0 \<and> y = 1) \<or> (x = 1 \<and> y = 0)"

definition cohoe_cycle_bogus_grounding :: "nat set \<Rightarrow> nat \<Rightarrow> bool"
where
  "cohoe_cycle_bogus_grounding S a \<longleftrightarrow>
     (S = {2} \<and> a \<in> {0, 1}) \<or>
     (\<exists>x. S = {x} \<and> cohoe_cycle_dependency x a)"

lemma cohoe_cycle_ancestor_source:
  assumes "dependency_ancestor {0, 1, 2} cohoe_cycle_dependency x (1 :: nat)"
  shows "x \<in> {0, 1}"
proof -
  have path:
      "(dependency_on {0, 1, 2} cohoe_cycle_dependency)\<^sup>*\<^sup>* x (1 :: nat)"
    using assms by (simp add: dependency_ancestor_def)
  have edge_source:
      "\<And>u v. dependency_on {0, 1, 2} cohoe_cycle_dependency u v
        \<Longrightarrow> u \<in> {0, 1}"
    by (auto simp: dependency_on_def cohoe_cycle_dependency_def)
  show ?thesis
  using path
  proof (induction rule: converse_rtranclp_induct)
    case base
    show ?case by simp
  next
    case step
    then show ?case
      using edge_source[OF step.hyps(1)] by simp
  qed
qed

lemma cohoe_cycle_two_not_ancestor:
  "\<not> dependency_ancestor {0, 1, 2} cohoe_cycle_dependency
    (2 :: nat) 1"
proof
  assume ancestor:
    "dependency_ancestor {0, 1, 2} cohoe_cycle_dependency (2 :: nat) 1"
  have path:
      "(dependency_on {0, 1, 2} cohoe_cycle_dependency)\<^sup>*\<^sup>* (2 :: nat) 1"
    using ancestor by (simp add: dependency_ancestor_def)
  show False
  proof (rule converse_rtranclpE[OF path])
    assume "2 = (1 :: nat)"
    then show False by simp
  next
    fix y
    assume edge:
      "dependency_on {0, 1, 2} cohoe_cycle_dependency (2 :: nat) y"
    show False
      using edge by (auto simp: dependency_on_def
        cohoe_cycle_dependency_def)
  qed
qed

lemma cohoe_cycle_full_foundation:
  "full_foundation_on {0, 1, 2} cohoe_cycle_dependency
    cohoe_cycle_bogus_grounding {0, 1, 2}"
proof -
  have support:
      "\<forall>a \<in> ({0, 1, 2} :: nat set).
        grounded_in {0, 1, 2}
          (partial_grounding_on {0, 1, 2}
            cohoe_cycle_bogus_grounding) a \<longrightarrow>
        (\<exists>S. full_grounding_on {0, 1, 2}
          cohoe_cycle_bogus_grounding S a \<and> S \<subseteq> {2})"
  proof (intro ballI impI)
    fix a :: nat
    assume "a \<in> ({0, 1, 2} :: nat set)"
      and grounded:
        "grounded_in {0, 1, 2}
          (partial_grounding_on {0, 1, 2}
            cohoe_cycle_bogus_grounding) a"
    obtain y where "y \<in> ({0, 1, 2} :: nat set)"
      and partial:
        "partial_grounding_on {0, 1, 2}
          cohoe_cycle_bogus_grounding y a"
      using grounded by (auto simp: grounded_in_def)
    obtain S where full_S:
        "full_grounding_on {0, 1, 2}
          cohoe_cycle_bogus_grounding S a"
      and "y \<in> S"
      using partial by (auto simp: partial_grounding_on_def)
    have G:
        "(S = {2} \<and> a \<in> {0, 1}) \<or>
         (\<exists>x. S = {x} \<and> cohoe_cycle_dependency x a)"
      using full_S
      by (simp only: full_grounding_on_def
        cohoe_cycle_bogus_grounding_def)
    have a01: "a \<in> ({0, 1} :: nat set)"
    proof (rule disjE[OF G])
      assume first: "S = {2} \<and> a \<in> {0, 1}"
      then show ?thesis by simp
    next
      assume second:
        "\<exists>x. S = {x} \<and> cohoe_cycle_dependency x a"
      obtain x where "S = {x}"
        and Dxa: "cohoe_cycle_dependency x a"
        using second by blast
      have cycle_values:
          "(x = 0 \<and> a = 1) \<or> (x = 1 \<and> a = 0)"
        using Dxa by (simp add: cohoe_cycle_dependency_def)
      show ?thesis
        using cycle_values by blast
    qed
    have aC: "a \<in> ({0, 1, 2} :: nat set)"
      using a01 by auto
    have full2:
        "full_grounding_on {0, 1, 2}
          cohoe_cycle_bogus_grounding {2} a"
      unfolding full_grounding_on_def
      using aC a01 by (auto simp: cohoe_cycle_bogus_grounding_def)
    show "\<exists>S. full_grounding_on {0, 1, 2}
        cohoe_cycle_bogus_grounding S a \<and> S \<subseteq> {2}"
      using full2 by blast
  qed
  have foundation:
      "full_foundation_for {0, 1, 2} cohoe_cycle_dependency
        cohoe_cycle_bogus_grounding {0, 1, 2} {2}"
  proof -
    have base:
        "{2} \<subseteq> ({0, 1, 2} :: nat set) \<and>
         {0, 1, 2} \<subseteq> ({0, 1, 2} :: nat set) \<and>
         (\<forall>f \<in> {2}.
           independent_in {0, 1, 2} cohoe_cycle_dependency f)"
      by (simp add: independent_in_def cohoe_cycle_dependency_def)
    show ?thesis
      unfolding full_foundation_for_def
      using base support by blast
  qed
  then show ?thesis
    by (rule full_foundation_onI)
qed

lemma cohoe_cycle_endpoint:
  "cohoe_singleton_endpoint_premise {0, 1, 2} cohoe_cycle_dependency
    cohoe_cycle_bogus_grounding"
  unfolding cohoe_singleton_endpoint_premise_def
proof (intro allI impI)
  fix x a :: nat
  assume "x \<in> {0, 1, 2}" "a \<in> {0, 1, 2}"
    and Dxa: "cohoe_cycle_dependency x a"
  have cycle_values:
      "(x = 0 \<and> a = 1) \<or> (x = 1 \<and> a = 0)"
    using Dxa by (simp add: cohoe_cycle_dependency_def)
  have full:
      "full_grounding_on {0, 1, 2} cohoe_cycle_bogus_grounding {x} a"
    unfolding full_grounding_on_def
    using cycle_values by (auto simp: cohoe_cycle_bogus_grounding_def
      cohoe_cycle_dependency_def)
  show "partial_grounding_on {0, 1, 2} cohoe_cycle_bogus_grounding x a"
    using partial_grounding_onI[OF full] by simp
qed

lemma cohoe_cycle_nonempty:
  "cohoe_full_nonempty_premise {0, 1, 2} cohoe_cycle_bogus_grounding"
  unfolding cohoe_full_nonempty_premise_def
proof (intro allI impI)
  fix S :: "nat set" and a :: nat
  assume full:
    "full_grounding_on {0, 1, 2} cohoe_cycle_bogus_grounding S a"
  have G:
      "(S = {2} \<and> a \<in> {0, 1}) \<or>
       (\<exists>x. S = {x} \<and> cohoe_cycle_dependency x a)"
    using full
    by (simp only: full_grounding_on_def cohoe_cycle_bogus_grounding_def)
  show "S \<noteq> {}"
  proof (rule disjE[OF G])
    assume first: "S = {2} \<and> a \<in> {0, 1}"
    then show ?thesis by simp
  next
    assume second:
      "\<exists>x. S = {x} \<and> cohoe_cycle_dependency x a"
    then obtain x where "S = {x}" by blast
    then show ?thesis by simp
  qed
qed

lemma cohoe_cycle_ancestry_fails:
  "\<not> cohoe_full_ancestry_premise {0, 1, 2} cohoe_cycle_dependency
    cohoe_cycle_bogus_grounding"
proof
  assume ancestry:
    "cohoe_full_ancestry_premise {0, 1, 2} cohoe_cycle_dependency
      cohoe_cycle_bogus_grounding"
  have full:
      "full_grounding_on {0, 1, 2} cohoe_cycle_bogus_grounding {2} 1"
    by (simp add: full_grounding_on_def
      cohoe_cycle_bogus_grounding_def)
  have ancestor:
      "dependency_ancestor {0, 1, 2} cohoe_cycle_dependency (2 :: nat) 1"
  proof -
    have ancestry_all:
        "\<forall>S a x. full_grounding_on {0, 1, 2}
          cohoe_cycle_bogus_grounding S a \<longrightarrow> x \<in> S \<longrightarrow>
          dependency_ancestor {0, 1, 2} cohoe_cycle_dependency x a"
      using ancestry
      by (simp only: cohoe_full_ancestry_premise_def)
    show ?thesis
      using ancestry_all full by blast
  qed
  show False
    using cohoe_cycle_two_not_ancestor ancestor by blast
qed

lemma cohoe_cycle_essential_ordering:
  "cohoe_essential_ordering_premise {0, 1, 2} cohoe_cycle_dependency
    (\<lambda>_::nat. True) (\<lambda>a::nat. a = 1)"
  unfolding cohoe_essential_ordering_premise_def
proof (intro allI impI)
  fix a :: nat
  assume "a = 1"
  have grounded1:
      "grounded_in {0, 1, 2} cohoe_cycle_dependency (1 :: nat)"
    by (simp add: grounded_in_def cohoe_cycle_dependency_def)
  have ancestors_grounded:
      "\<forall>x. dependency_ancestor {0, 1, 2}
        cohoe_cycle_dependency x (1 :: nat) \<longrightarrow>
        grounded_in {0, 1, 2} cohoe_cycle_dependency x"
  proof (intro allI impI)
    fix x
    assume ancestor:
      "dependency_ancestor {0, 1, 2} cohoe_cycle_dependency x (1 :: nat)"
    have x01: "x \<in> {0, 1}"
      by (rule cohoe_cycle_ancestor_source[OF ancestor])
    show "grounded_in {0, 1, 2} cohoe_cycle_dependency x"
      using x01 by (auto simp: grounded_in_def cohoe_cycle_dependency_def)
  qed
  show "essentially_ordered_series {0, 1, 2} cohoe_cycle_dependency
      (\<lambda>_::nat. True) a"
    using \<open>a = 1\<close> grounded1 ancestors_grounded
    by (auto simp: essentially_ordered_series_def)
qed

theorem cohoe_delete_full_ancestry:
  "cohoe_existence_premise (\<lambda>(a :: nat). a = 1) \<and>
   cohoe_essential_ordering_premise {0, 1, 2} cohoe_cycle_dependency
     (\<lambda>_::nat. True) (\<lambda>a::nat. a = 1) \<and>
   cohoe_full_foundation_premise {0, 1, 2} cohoe_cycle_dependency
     cohoe_cycle_bogus_grounding \<and>
   cohoe_singleton_endpoint_premise {0, 1, 2} cohoe_cycle_dependency
     cohoe_cycle_bogus_grounding \<and>
   cohoe_full_nonempty_premise {0, 1, 2} cohoe_cycle_bogus_grounding \<and>
   \<not> cohoe_full_ancestry_premise {0, 1, 2} cohoe_cycle_dependency
     cohoe_cycle_bogus_grounding \<and>
   \<not> cohoe_global_non_derivative_conclusion {0, 1, 2}
     cohoe_cycle_dependency (\<lambda>_::nat. True)"
proof -
  have existence:
      "cohoe_existence_premise (\<lambda>(a :: nat). a = 1)"
    by (simp add: cohoe_existence_premise_def)
  have essential:
      "cohoe_essential_ordering_premise {0, 1, 2}
        cohoe_cycle_dependency (\<lambda>_::nat. True) (\<lambda>a::nat. a = 1)"
    by (rule cohoe_cycle_essential_ordering)
  have full:
      "cohoe_full_foundation_premise {0, 1, 2} cohoe_cycle_dependency
        cohoe_cycle_bogus_grounding"
    unfolding cohoe_full_foundation_premise_def
    by (rule cohoe_cycle_full_foundation)
  have endpoint:
      "cohoe_singleton_endpoint_premise {0, 1, 2} cohoe_cycle_dependency
        cohoe_cycle_bogus_grounding"
    by (rule cohoe_cycle_endpoint)
  have nonempty:
      "cohoe_full_nonempty_premise {0, 1, 2}
        cohoe_cycle_bogus_grounding"
    by (rule cohoe_cycle_nonempty)
  have not_ancestry:
      "\<not> cohoe_full_ancestry_premise {0, 1, 2} cohoe_cycle_dependency
        cohoe_cycle_bogus_grounding"
    by (rule cohoe_cycle_ancestry_fails)
  have not_global:
      "\<not> cohoe_global_non_derivative_conclusion {0, 1, 2}
        cohoe_cycle_dependency (\<lambda>_::nat. True)"
    by (simp add: cohoe_global_non_derivative_conclusion_def)
  show ?thesis
    using existence essential full endpoint nonempty not_ancestry
      not_global by blast
qed

theorem cohoe_delete_full_foundation:
  "cohoe_existence_premise (\<lambda>(a :: int). a = 0) \<and>
   cohoe_essential_ordering_premise (UNIV :: int set)
     integer_predecessor_cause (\<lambda>_::int. True) (\<lambda>a::int. a = 0) \<and>
   \<not> cohoe_full_foundation_premise (UNIV :: int set)
     integer_predecessor_cause
     cohoe_integer_singleton_grounding \<and>
   cohoe_singleton_endpoint_premise (UNIV :: int set) integer_predecessor_cause
     cohoe_integer_singleton_grounding \<and>
   cohoe_full_nonempty_premise (UNIV :: int set) cohoe_integer_singleton_grounding \<and>
   cohoe_full_ancestry_premise (UNIV :: int set) integer_predecessor_cause
     cohoe_integer_singleton_grounding \<and>
   \<not> cohoe_global_non_derivative_conclusion (UNIV :: int set)
     integer_predecessor_cause (\<lambda>_::int. True)"
proof -
  have existence:
      "cohoe_existence_premise (\<lambda>(a :: int). a = 0)"
    by (simp add: cohoe_existence_premise_def)
  have essential:
      "cohoe_essential_ordering_premise (UNIV :: int set)
        integer_predecessor_cause (\<lambda>_. True) (\<lambda>a. a = 0)"
    unfolding cohoe_essential_ordering_premise_def
  proof (intro allI impI)
    fix a :: int
    assume "a = 0"
    then show "essentially_ordered_series UNIV integer_predecessor_cause
        (\<lambda>_. True) a"
      using integer_predecessor_is_essentially_ordered by simp
  qed
  have endpoint:
      "cohoe_singleton_endpoint_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_integer_singleton_grounding"
    by (rule cohoe_integer_singleton_endpoint)
  have nonempty:
      "cohoe_full_nonempty_premise (UNIV :: int set)
        cohoe_integer_singleton_grounding"
    by (rule cohoe_integer_singleton_nonempty)
  have ancestry:
      "cohoe_full_ancestry_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_integer_singleton_grounding"
    by (rule cohoe_integer_singleton_ancestry)
  have not_full:
      "\<not> cohoe_full_foundation_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_integer_singleton_grounding"
  proof
    assume full_premise:
      "cohoe_full_foundation_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_integer_singleton_grounding"
    have full:
        "full_foundation_on (UNIV :: int set) integer_predecessor_cause
          cohoe_integer_singleton_grounding UNIV"
      using full_premise by (simp only: cohoe_full_foundation_premise_def)
    have endpoint_all:
        "\<And>x a. x \<in> (UNIV :: int set) \<Longrightarrow>
          a \<in> (UNIV :: int set) \<Longrightarrow>
          integer_predecessor_cause x a \<Longrightarrow>
          partial_grounding_on (UNIV :: int set)
            cohoe_integer_singleton_grounding x a"
      using endpoint
      by (simp only: cohoe_singleton_endpoint_premise_def)
    have nonempty_all:
        "\<forall>S a. (full_grounding_on (UNIV :: int set)
          cohoe_integer_singleton_grounding S a \<longrightarrow> S \<noteq> {})"
      using nonempty
      by (simp only: cohoe_full_nonempty_premise_def)
    have ancestry_all:
        "\<forall>S a x. (full_grounding_on (UNIV :: int set)
          cohoe_integer_singleton_grounding S a \<longrightarrow> x \<in> S \<longrightarrow>
          dependency_ancestor (UNIV :: int set)
            integer_predecessor_cause x a)"
      using ancestry
      by (simp only: cohoe_full_ancestry_premise_def)
    have local:
        "local_foundation_on (UNIV :: int set)
          integer_predecessor_cause UNIV"
      using full_foundation_implies_local_foundation[OF full]
        endpoint_all nonempty_all ancestry_all by blast
    show False
      using integer_predecessor_not_local_foundation local by blast
  qed
  have not_global:
      "\<not> cohoe_global_non_derivative_conclusion (UNIV :: int set)
        integer_predecessor_cause (\<lambda>_. True)"
    by (simp add: cohoe_global_non_derivative_conclusion_def)
  have h_ancestry:
      "cohoe_full_ancestry_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_integer_singleton_grounding \<and>
       \<not> cohoe_global_non_derivative_conclusion (UNIV :: int set)
        integer_predecessor_cause (\<lambda>_. True)"
    using ancestry not_global by (rule conjI)
  have h_nonempty:
      "cohoe_full_nonempty_premise (UNIV :: int set)
        cohoe_integer_singleton_grounding \<and>
       cohoe_full_ancestry_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_integer_singleton_grounding \<and>
       \<not> cohoe_global_non_derivative_conclusion (UNIV :: int set)
        integer_predecessor_cause (\<lambda>_. True)"
    using nonempty h_ancestry by (rule conjI)
  have h_endpoint:
      "cohoe_singleton_endpoint_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_integer_singleton_grounding \<and>
       cohoe_full_nonempty_premise (UNIV :: int set)
        cohoe_integer_singleton_grounding \<and>
       cohoe_full_ancestry_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_integer_singleton_grounding \<and>
       \<not> cohoe_global_non_derivative_conclusion (UNIV :: int set)
        integer_predecessor_cause (\<lambda>_. True)"
    using endpoint h_nonempty by (rule conjI)
  have h_full:
      "\<not> cohoe_full_foundation_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_integer_singleton_grounding \<and>
       cohoe_singleton_endpoint_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_integer_singleton_grounding \<and>
       cohoe_full_nonempty_premise (UNIV :: int set)
        cohoe_integer_singleton_grounding \<and>
       cohoe_full_ancestry_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_integer_singleton_grounding \<and>
       \<not> cohoe_global_non_derivative_conclusion (UNIV :: int set)
        integer_predecessor_cause (\<lambda>_. True)"
    using not_full h_endpoint by (rule conjI)
  have h_essential:
      "cohoe_essential_ordering_premise (UNIV :: int set)
        integer_predecessor_cause (\<lambda>_. True) (\<lambda>a. a = 0) \<and>
       \<not> cohoe_full_foundation_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_integer_singleton_grounding \<and>
       cohoe_singleton_endpoint_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_integer_singleton_grounding \<and>
       cohoe_full_nonempty_premise (UNIV :: int set)
        cohoe_integer_singleton_grounding \<and>
       cohoe_full_ancestry_premise (UNIV :: int set)
        integer_predecessor_cause cohoe_integer_singleton_grounding \<and>
       \<not> cohoe_global_non_derivative_conclusion (UNIV :: int set)
        integer_predecessor_cause (\<lambda>_. True)"
    using essential h_full by (rule conjI)
  show ?thesis
  proof (rule conjI)
    show "cohoe_existence_premise (\<lambda>(a :: int). a = 0)"
      using existence .
    show "cohoe_essential_ordering_premise (UNIV :: int set)
          integer_predecessor_cause
          (\<lambda>_::int. True) (\<lambda>a::int. a = 0) \<and>
        \<not> cohoe_full_foundation_premise (UNIV :: int set)
          integer_predecessor_cause
          cohoe_integer_singleton_grounding \<and>
        cohoe_singleton_endpoint_premise (UNIV :: int set)
          integer_predecessor_cause
          cohoe_integer_singleton_grounding \<and>
        cohoe_full_nonempty_premise (UNIV :: int set)
          cohoe_integer_singleton_grounding \<and>
        cohoe_full_ancestry_premise (UNIV :: int set)
          integer_predecessor_cause
          cohoe_integer_singleton_grounding \<and>
        \<not> cohoe_global_non_derivative_conclusion (UNIV :: int set)
          integer_predecessor_cause (\<lambda>_::int. True)"
      using h_essential .
  qed
qed

end
