theory Dependency_Structures
  imports Preliminaries
begin

section \<open>Carrier-Restricted Dependency\<close>

text \<open>
  A dependency structure consists of a carrier and an immediate relation.  The
  orientation is fixed throughout this development: @{term "D x y"} means that
  @{term x} is prior to, grounds, or immediately supports @{term y}.  The
  carrier restriction is explicit so that unrelated elements cannot become
  accidental first causes.
\<close>

definition dependency_on ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "dependency_on C D x y \<longleftrightarrow> x \<in> C \<and> y \<in> C \<and> D x y"

lemma dependency_onI:
  assumes "x \<in> C" and "y \<in> C" and "D x y"
  shows "dependency_on C D x y"
  using assms by (simp add: dependency_on_def)

lemma dependency_onD:
  assumes "dependency_on C D x y"
  shows "x \<in> C" "y \<in> C" "D x y"
  using assms by (auto simp: dependency_on_def)

definition dependency_ancestor ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "dependency_ancestor C D x y \<longleftrightarrow>
     x \<in> C \<and> y \<in> C \<and> (dependency_on C D)\<^sup>*\<^sup>* x y"

lemma dependency_ancestor_refl:
  assumes "x \<in> C"
  shows "dependency_ancestor C D x x"
  using assms by (simp add: dependency_ancestor_def)

lemma dependency_ancestor_direct:
  assumes "x \<in> C" and "y \<in> C" and "D x y"
  shows "dependency_ancestor C D x y"
proof -
  have "dependency_on C D x y"
    using assms by (simp add: dependency_on_def)
  then have "(dependency_on C D)\<^sup>*\<^sup>* x y"
    by (rule r_into_rtranclp)
  then show ?thesis
    using assms by (simp add: dependency_ancestor_def)
qed

lemma dependency_ancestor_trans:
  assumes "dependency_ancestor C D x y"
    and "dependency_ancestor C D y z"
  shows "dependency_ancestor C D x z"
proof -
  from assms obtain
      "x \<in> C" "y \<in> C" "(dependency_on C D)\<^sup>*\<^sup>* x y"
      "z \<in> C" "(dependency_on C D)\<^sup>*\<^sup>* y z"
    by (auto simp: dependency_ancestor_def)
  then show ?thesis
    by (auto simp: dependency_ancestor_def intro: rtranclp_trans)
qed

section \<open>Compatibility with the Existing Ancestry Predicate\<close>

lemma ancestor_iff_rtranclp:
  "ancestor D x y \<longleftrightarrow> D\<^sup>*\<^sup>* x y"
proof
  assume "ancestor D x y"
  then show "D\<^sup>*\<^sup>* x y"
  proof (induction rule: ancestor.induct)
    case refl
    show ?case by (rule rtranclp.rtrancl_refl)
  next
    case (step x y z)
    have "D\<^sup>*\<^sup>* x y"
      using step.hyps(1) by (rule r_into_rtranclp)
    with step.IH show ?case
      by (blast intro: rtranclp_trans)
  qed
next
  assume "D\<^sup>*\<^sup>* x y"
  then show "ancestor D x y"
  proof (induction rule: rtranclp_induct)
    case base
    show ?case by (rule ancestor.refl)
  next
    case (step y z)
    have "ancestor D y z"
      using step.hyps(2) by (rule ancestor_direct)
    then show ?case
      using step.IH by (blast intro: ancestor_trans)
  qed
qed

lemma legacy_ancestor_iff_dependency_ancestor:
  "ancestor D x y \<longleftrightarrow> dependency_ancestor UNIV D x y"
proof -
  have relation_eq: "dependency_on UNIV D = D"
    by (rule ext, rule ext) (simp add: dependency_on_def)
  then show ?thesis
    by (simp add: ancestor_iff_rtranclp dependency_ancestor_def)
qed

section \<open>Grounded and Independent Members\<close>

definition grounded_in ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
where
  "grounded_in C D x \<longleftrightarrow> x \<in> C \<and> (\<exists>y \<in> C. D y x)"

definition independent_in ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool"
where
  "independent_in C D x \<longleftrightarrow> x \<in> C \<and>
     (\<not> (\<exists>y \<in> C. D y x))"

lemma grounded_inD:
  assumes "grounded_in C D x"
  shows "x \<in> C" "\<exists>y \<in> C. D y x"
  using assms by (auto simp: grounded_in_def)

lemma independent_inD:
  assumes "independent_in C D x"
  shows "x \<in> C" "\<not> (\<exists>y \<in> C. D y x)"
  using assms by (auto simp: independent_in_def)

lemma grounded_not_independent:
  assumes "grounded_in C D x"
  shows "\<not> independent_in C D x"
  using assms by (auto simp: grounded_in_def independent_in_def)

definition first_member_in ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "first_member_in C D x a \<longleftrightarrow>
     dependency_ancestor C D x a \<and> independent_in C D x"

definition first_cause_in ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "first_cause_in C D x a \<longleftrightarrow>
     first_member_in C D x a \<and> x \<noteq> a"

lemma first_member_inD:
  assumes "first_member_in C D x a"
  shows "dependency_ancestor C D x a" "independent_in C D x"
  using assms by (auto simp: first_member_in_def)

lemma first_cause_inD:
  assumes "first_cause_in C D x a"
  shows "first_member_in C D x a" "x \<noteq> a"
  using assms by (auto simp: first_cause_in_def)

definition foundation_set_for ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "foundation_set_for C D R F \<longleftrightarrow>
     F \<subseteq> C \<and> R \<subseteq> C \<and>
     (\<forall>f \<in> F. independent_in C D f) \<and>
     (\<forall>a \<in> R. grounded_in C D a \<longrightarrow>
       (\<exists>f \<in> F. dependency_ancestor C D f a))"

lemma foundation_set_forD:
  assumes "foundation_set_for C D R F"
  shows "F \<subseteq> C" "R \<subseteq> C"
    and "\<forall>f \<in> F. independent_in C D f"
    and "\<forall>a \<in> R. grounded_in C D a \<longrightarrow>
      (\<exists>f \<in> F. dependency_ancestor C D f a)"
  using assms by (auto simp: foundation_set_for_def)

end
