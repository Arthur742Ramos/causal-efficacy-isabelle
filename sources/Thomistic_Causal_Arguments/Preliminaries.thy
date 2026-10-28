theory Preliminaries
  imports Main
begin

section \<open>Dependency Ancestry\<close>

text \<open>
  The relation @{term "D x y"} is read as: @{term x} is an immediate
  essential ground, cause, or actualizer of @{term y}.  The inductive
  predicate @{term "ancestor D x y"} is the reflexive transitive closure of
  that dependency relation, oriented from earlier or more fundamental members
  toward later or dependent members.
\<close>

inductive ancestor :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
  for D :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  refl: "ancestor D x x"
| step: "D x y \<Longrightarrow> ancestor D y z \<Longrightarrow> ancestor D x z"

lemma ancestor_direct:
  assumes "D x y"
  shows "ancestor D x y"
proof -
  have "ancestor D y y"
    by (rule ancestor.refl)
  with assms show ?thesis
    by (rule ancestor.step)
qed

lemma ancestor_trans:
  assumes "ancestor D x y" and "ancestor D y z"
  shows "ancestor D x z"
  using assms(1) assms(2)
proof (induction arbitrary: z rule: ancestor.induct)
  case (refl x)
  then show ?case .
next
  case (step x y u)
  have "ancestor D y z"
    by (rule step.IH[OF step.prems])
  with step.hyps(1) show ?case
    by (rule ancestor.step)
qed

lemma ancestor_nontrivial_has_successor:
  assumes "ancestor D x y" and "x \<noteq> y"
  shows "\<exists>z. D x z"
  using assms
proof cases
  case refl
  with assms show ?thesis by simp
next
  case (step z)
  then show ?thesis
    by blast
qed

section \<open>First Members\<close>

definition ungrounded :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
  "ungrounded D x \<longleftrightarrow> (\<nexists>y. D y x)"

definition first_member_of :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "first_member_of D x a \<longleftrightarrow> ancestor D x a \<and> ungrounded D x"

definition first_cause :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" where
  "first_cause D x \<longleftrightarrow> (\<exists>y. D x y) \<and> ungrounded D x"

definition first_cause_of :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "first_cause_of D x a \<longleftrightarrow> first_member_of D x a \<and> x \<noteq> a"

lemma first_member_not_target_if_target_has_predecessor:
  assumes "first_member_of D x a" and "D y a"
  shows "x \<noteq> a"
  using assms by (auto simp: first_member_of_def ungrounded_def)

lemma first_cause_of_imp_first_cause:
  assumes "first_cause_of D x a"
  shows "first_cause D x"
proof -
  have "first_member_of D x a" and "x \<noteq> a"
    using assms by (auto simp: first_cause_of_def)
  then have "ancestor D x a" and "ungrounded D x"
    by (auto simp: first_member_of_def)
  from ancestor_nontrivial_has_successor[OF \<open>ancestor D x a\<close> \<open>x \<noteq> a\<close>]
  obtain y where "D x y"
    by auto
  with \<open>ungrounded D x\<close> show ?thesis
    by (auto simp: first_cause_def)
qed

lemma wf_has_first_member:
  assumes "wfP D"
  shows "\<exists>m. first_member_of D m a"
  using assms
proof (induction a rule: wfp_induct_rule)
  case (less a)
  show ?case
  proof (cases "\<exists>b. D b a")
    case False
    then show ?thesis
      by (intro exI[of _ a])
        (auto simp: first_member_of_def ungrounded_def intro: ancestor.refl)
  next
    case True
    then obtain b where Db: "D b a" by blast
    from less.IH[OF Db] obtain m where "first_member_of D m b"
      by blast
    then have "ancestor D m b" and "ungrounded D m"
      by (auto simp: first_member_of_def)
    have "ancestor D b a"
      using Db by (rule ancestor_direct)
    have "ancestor D m a"
      using \<open>ancestor D m b\<close> \<open>ancestor D b a\<close> by (rule ancestor_trans)
    then show ?thesis
      using \<open>ungrounded D m\<close>
      by (auto simp: first_member_of_def)
  qed
qed

lemma wf_has_first_cause_of_if_predecessor:
  assumes "wfP D" and "D b a"
  shows "\<exists>m. first_cause_of D m a"
proof -
  from wf_has_first_member[OF assms(1), of a] obtain m
    where m: "first_member_of D m a"
    by blast
  moreover have "m \<noteq> a"
    using first_member_not_target_if_target_has_predecessor[OF m assms(2)] .
  ultimately show ?thesis
    by (auto simp: first_cause_of_def)
qed

end
