theory Foundation_Principles
  imports Dependency_Structures
begin

section \<open>Competing Binary Principles\<close>

text \<open>
  The same immediate relation supports several non-equivalent readings of a
  regress argument.  We keep them as separate predicates.  In particular,
  acyclicity is only a prohibition on nonempty cycles, while
  well-foundedness is a global condition on all predecessor chains.
\<close>

definition acyclic_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "acyclic_on C D \<longleftrightarrow>
     (\<forall>x \<in> C. \<not> (dependency_on C D)\<^sup>+\<^sup>+ x x)"

definition well_founded_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "well_founded_on C D \<longleftrightarrow> wfp_on C (dependency_on C D)"

definition chain_terminating_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where
  "chain_terminating_on C D \<longleftrightarrow>
     (\<nexists>f. \<forall>n. dependency_on C D (f (Suc n)) (f n))"

definition local_foundation_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "local_foundation_on C D R \<longleftrightarrow>
     (\<forall>a \<in> R. grounded_in C D a \<longrightarrow>
       (\<exists>f. first_member_in C D f a))"

definition global_foundation_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "global_foundation_on C D R \<longleftrightarrow>
     (\<exists>F. foundation_set_for C D R F)"

lemma global_foundation_onI:
  assumes "foundation_set_for C D R F"
  shows "global_foundation_on C D R"
  using assms by (auto simp: global_foundation_on_def)

lemma global_foundation_onD:
  assumes "global_foundation_on C D R"
  obtains F where "foundation_set_for C D R F"
  using assms by (auto simp: global_foundation_on_def)

section \<open>Plural Grounding\<close>

text \<open>
  A full ground may be a set rather than a single member.  The carrier
  restriction is part of the interface.  This makes the later comparison with
  binary dependence explicit instead of silently identifying singleton and
  plural grounding.
\<close>

definition full_grounding_on ::
  "'a set \<Rightarrow> ('a set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
where
  "full_grounding_on C G S x \<longleftrightarrow>
     S \<subseteq> C \<and> x \<in> C \<and> G S x"

definition partial_grounding_on ::
  "'a set \<Rightarrow> ('a set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "partial_grounding_on C G x y \<longleftrightarrow>
     x \<in> C \<and> y \<in> C \<and>
     (\<exists>S. full_grounding_on C G S y \<and> x \<in> S)"

definition full_foundation_for ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "full_foundation_for C D G R F \<longleftrightarrow>
     F \<subseteq> C \<and> R \<subseteq> C \<and>
     (\<forall>f \<in> F. independent_in C D f) \<and>
     (\<forall>a \<in> R.
       grounded_in C (partial_grounding_on C G) a \<longrightarrow>
       (\<exists>S. full_grounding_on C G S a \<and> S \<subseteq> F))"

definition full_foundation_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a set \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "full_foundation_on C D G R \<longleftrightarrow>
     (\<exists>F. full_foundation_for C D G R F)"

lemma full_grounding_onD:
  assumes "full_grounding_on C G S x"
  shows "S \<subseteq> C" "x \<in> C" "G S x"
  using assms by (auto simp: full_grounding_on_def)

lemma full_grounding_onI:
  assumes "S \<subseteq> C" and "x \<in> C" and "G S x"
  shows "full_grounding_on C G S x"
  using assms by (auto simp: full_grounding_on_def)

lemma partial_grounding_onI:
  assumes "full_grounding_on C G S y" and "x \<in> S"
  shows "partial_grounding_on C G x y"
  using assms
  by (auto simp: partial_grounding_on_def full_grounding_on_def)

lemma partial_grounding_onD:
  assumes "partial_grounding_on C G x y"
  shows "x \<in> C" "y \<in> C"
    and "\<exists>S. full_grounding_on C G S y \<and> x \<in> S"
  using assms by (auto simp: partial_grounding_on_def)

lemma full_foundation_forD:
  assumes "full_foundation_for C D G R F"
  shows "F \<subseteq> C" "R \<subseteq> C"
    and "\<forall>f \<in> F. independent_in C D f"
    and "\<forall>a \<in> R.
      grounded_in C (partial_grounding_on C G) a \<longrightarrow>
      (\<exists>S. full_grounding_on C G S a \<and> S \<subseteq> F)"
  using assms by (auto simp: full_foundation_for_def)

lemma full_foundation_onI:
  assumes "full_foundation_for C D G R F"
  shows "full_foundation_on C D G R"
  using assms by (auto simp: full_foundation_on_def)

lemma full_foundation_onD:
  assumes "full_foundation_on C D G R"
  obtains F where "full_foundation_for C D G R F"
  using assms by (auto simp: full_foundation_on_def)

end
