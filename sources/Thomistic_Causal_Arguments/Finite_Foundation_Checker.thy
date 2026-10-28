theory Finite_Foundation_Checker
  imports Foundation_Separations "HOL-Library.Transitive_Closure_Table"
begin

section \<open>Executable Finite Models\<close>

text \<open>
  A finite model is represented by a vertex list and an edge list.  The
  declarative abstraction uses the set of listed vertices and carrier-restricts
  the edge relation.  Duplicated vertices do not change the abstraction, while
  well-formed clients may additionally require @{term "distinct (fst M)"}.
\<close>

type_synonym finite_dependency_model = "nat list \<times> (nat \<times> nat) list"

definition finite_vertices :: "finite_dependency_model \<Rightarrow> nat list"
where
  "finite_vertices M = fst M"

definition finite_edges :: "finite_dependency_model \<Rightarrow> (nat \<times> nat) list"
where
  "finite_edges M = snd M"

definition finite_model_immediate ::
  "finite_dependency_model \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "finite_model_immediate M x y \<longleftrightarrow>
     (x, y) \<in> set (finite_edges M)"

definition finite_model_relation ::
  "finite_dependency_model \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "finite_model_relation M x y \<longleftrightarrow>
     dependency_on (set (finite_vertices M))
       (finite_model_immediate M) x y"

definition finite_model_carrier ::
  "finite_dependency_model \<Rightarrow> nat set"
where
  "finite_model_carrier M = set (finite_vertices M)"

fun finite_list_all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "finite_list_all P [] = True"
| "finite_list_all P (x # xs) = (P x \<and> finite_list_all P xs)"

fun finite_list_ex :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "finite_list_ex P [] = False"
| "finite_list_ex P (x # xs) = (P x \<or> finite_list_ex P xs)"

fun finite_first_failure ::
  "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a option"
where
  "finite_first_failure P [] = None"
| "finite_first_failure P (x # xs) =
     (if P x then Some x else finite_first_failure P xs)"

lemma finite_list_all_iff:
  "finite_list_all P xs \<longleftrightarrow> (\<forall>x \<in> set xs. P x)"
  by (induction xs) simp_all

lemma finite_list_ex_iff:
  "finite_list_ex P xs \<longleftrightarrow> (\<exists>x \<in> set xs. P x)"
  by (induction xs) simp_all

lemma finite_list_exI:
  assumes "x \<in> set xs" and "P x"
  shows "finite_list_ex P xs"
  using assms
  by (induction xs) auto

fun finite_reach ::
  "nat \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   'a \<Rightarrow> 'a \<Rightarrow> bool"
where
  "finite_reach 0 V R x y = (x = y)"
| "finite_reach (Suc n) V R x y =
     (x = y \<or>
       finite_list_ex
         (\<lambda>z. R x z \<and> finite_reach n V R z y) V)"

lemma finite_reach_imp_rtranclp:
  "finite_reach n V R x y \<Longrightarrow> R\<^sup>*\<^sup>* x y"
proof (induction n arbitrary: x y)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  then show ?case
    by (auto simp: finite_list_ex_iff
      intro: r_into_rtranclp converse_rtranclp_into_rtranclp)
qed

lemma finite_reach_mono:
  assumes "n \<le> m" and "finite_reach n V R x y"
  shows "finite_reach m V R x y"
using assms
proof (induction m arbitrary: n x y)
  case 0
  then show ?case
    by simp
next
  case (Suc m)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis
      using Suc.prems(2) by simp
  next
    case (Suc n)
    have "n \<le> m"
      using Suc.prems(1) Suc by simp
    have "x = y \<or>
        finite_list_ex
          (\<lambda>z. R x z \<and> finite_reach n V R z y) V"
      using Suc.prems(2) Suc by simp
    then show ?thesis
    proof
      assume "x = y"
      then show ?thesis by simp
    next
      assume ex:
        "finite_list_ex
          (\<lambda>z. R x z \<and> finite_reach n V R z y) V"
      obtain z where zV: "z \<in> set V"
        and R_xz: "R x z"
        and reach: "finite_reach n V R z y"
        using ex by (auto simp: finite_list_ex_iff)
      have reach_m: "finite_reach m V R z y"
        using Suc.IH[OF \<open>n \<le> m\<close> reach] .
      have ex_m:
          "finite_list_ex
            (\<lambda>w. R x w \<and> finite_reach m V R w y) V"
        using finite_list_exI[of z V
          "\<lambda>w. R x w \<and> finite_reach m V R w y"]
          zV R_xz reach_m
        by blast
      show ?thesis
        using ex_m by (simp add: finite_reach.simps)
    qed
  qed
qed

lemma rtrancl_path_vertices:
  assumes path: "rtrancl_path R x xs y"
    and xV: "x \<in> set V"
    and closed: "\<And>u v. R u v \<Longrightarrow> u \<in> set V \<and> v \<in> set V"
  shows "set xs \<subseteq> set V \<and> y \<in> set V"
  using path xV
proof (induction rule: rtrancl_path.induct)
  case base
  then show ?case by simp
next
  case (step x z ys y)
  have zV: "z \<in> set V"
    using closed step.hyps(1) by blast
  have tail: "set ys \<subseteq> set V \<and> y \<in> set V"
    using step.IH zV by blast
  then show ?case
    using zV by simp
qed

lemma finite_reach_path:
  assumes path: "rtrancl_path R x xs y"
    and xV: "x \<in> set V"
    and closed: "\<And>u v. R u v \<Longrightarrow> u \<in> set V \<and> v \<in> set V"
  shows "finite_reach (length xs) V R x y"
  using path xV
proof (induction rule: rtrancl_path.induct)
  case base
  then show ?case by simp
next
  case (step x z ys y)
  have zV: "z \<in> set V"
    using closed step.hyps(1) by blast
  have tail: "finite_reach (length ys) V R z y"
    using step.IH zV by blast
  have ex:
      "finite_list_ex
        (\<lambda>w. R x w \<and> finite_reach (length ys) V R w y) V"
    using finite_list_exI[of z V
      "\<lambda>w. R x w \<and> finite_reach (length ys) V R w y"]
      zV step.hyps(1) tail
    by blast
  show ?case
    using ex by (simp add: finite_reach.simps)
qed

lemma rtranclp_imp_finite_reach:
  assumes reach: "R\<^sup>*\<^sup>* x y"
    and xV: "x \<in> set V"
    and closed: "\<And>u v. R u v \<Longrightarrow> u \<in> set V \<and> v \<in> set V"
  shows "finite_reach (length V) V R x y"
proof -
  have path_exists: "\<exists>xs. rtrancl_path R x xs y"
    using reach by (simp add: rtranclp_eq_rtrancl_path)
  obtain xs where path: "rtrancl_path R x xs y"
    using path_exists by blast
  obtain xs' where path': "rtrancl_path R x xs' y"
    and distinct: "distinct (x # xs')"
    and subset: "set xs' \<subseteq> set xs"
    using rtrancl_path_distinct[OF path] by blast
  have path_V: "set xs \<subseteq> set V \<and> y \<in> set V"
    using rtrancl_path_vertices[OF path xV closed] .
  have xs_V: "set xs \<subseteq> set V"
    using path_V by blast
  have xs'_V: "set xs' \<subseteq> set V"
    using subset xs_V by blast
  have len_xs': "length xs' \<le> length V"
  proof -
    have card_xs': "card (set xs') = length xs'"
      using distinct by (simp add: distinct_card)
    have "card (set xs') \<le> card (set V)"
      using card_mono xs'_V by blast
    moreover have "card (set V) \<le> length V"
      by (rule card_length)
    ultimately show ?thesis
      using card_xs' by linarith
  qed
  have finite_path: "finite_reach (length xs') V R x y"
    using finite_reach_path[OF path' xV closed] .
  have monotone:
      "finite_reach (length V) V R x y"
    using finite_reach_mono[
      where n = "length xs'" and m = "length V"
        and V = V and R = R and x = x and y = y]
      len_xs' finite_path .
  show "finite_reach (length V) V R x y"
    using monotone by blast
qed

lemma finite_first_failure_sound:
  assumes "finite_first_failure P xs = Some x"
  shows "x \<in> set xs" "P x"
  using assms
  by (induction xs) (auto split: if_splits)

lemma finite_first_failure_complete:
  assumes "\<exists>x \<in> set xs. P x"
  obtains x where "finite_first_failure P xs = Some x"
    and "x \<in> set xs" and "P x"
proof -
  have exists:
      "\<exists>x. finite_first_failure P xs = Some x \<and>
        x \<in> set xs \<and> P x"
    using assms
    by (induction xs) (auto split: if_splits)
  then obtain x where "finite_first_failure P xs = Some x"
    and "x \<in> set xs" and "P x"
    by blast
  then show thesis
    by (rule that)
qed

section \<open>Finite Foundation Predicate and Checker\<close>

definition finite_model_independent ::
  "finite_dependency_model \<Rightarrow> nat \<Rightarrow> bool"
where
  "finite_model_independent M x \<longleftrightarrow>
     x \<in> finite_model_carrier M \<and>
     \<not> finite_list_ex
       (\<lambda>y. dependency_on (finite_model_carrier M)
         (finite_model_immediate M) y x) (finite_vertices M)"

definition finite_model_grounded ::
  "finite_dependency_model \<Rightarrow> nat \<Rightarrow> bool"
where
  "finite_model_grounded M x \<longleftrightarrow>
     finite_list_ex
       (\<lambda>y. dependency_on (finite_model_carrier M)
         (finite_model_immediate M) y x) (finite_vertices M)"

definition finite_model_supports ::
  "finite_dependency_model \<Rightarrow> nat \<Rightarrow> bool"
where
  "finite_model_supports M x \<longleftrightarrow>
     finite_list_ex
       (\<lambda>f. finite_model_independent M f \<and>
         finite_reach (length (finite_vertices M))
           (finite_vertices M)
           (dependency_on (finite_model_carrier M)
             (finite_model_immediate M)) f x)
       (finite_vertices M)"

definition finite_model_bad ::
  "finite_dependency_model \<Rightarrow> nat \<Rightarrow> bool"
where
  "finite_model_bad M x \<longleftrightarrow>
     finite_model_grounded M x \<and> \<not> finite_model_supports M x"

definition finite_foundation_check ::
  "finite_dependency_model \<Rightarrow> bool"
where
  "finite_foundation_check M \<longleftrightarrow>
     finite_list_all (\<lambda>x. \<not> finite_model_bad M x)
       (finite_vertices M)"

definition finite_failure_witness ::
  "finite_dependency_model \<Rightarrow> nat"
where
  "finite_failure_witness M =
     (case finite_first_failure (finite_model_bad M) (finite_vertices M) of
        None \<Rightarrow> 0
      | Some x \<Rightarrow> x)"

text \<open>
  The total executable helper has a harmless default for the impossible
  empty-failure case.  The specification theorem below proves
  that whenever the checker takes its failure branch, the returned natural
  number is a genuine carrier vertex and a genuine bad vertex.
\<close>

datatype finite_foundation_result =
    Foundation_Certificate "nat list"
  | Missing_Foundation_Certificate nat

definition finite_foundation_result ::
  "finite_dependency_model \<Rightarrow> finite_foundation_result"
where
  "finite_foundation_result M =
     (if finite_foundation_check M then
        Foundation_Certificate
          (filter (finite_model_independent M) (finite_vertices M))
      else
        Missing_Foundation_Certificate (finite_failure_witness M))"

lemma finite_model_relation_eq:
  "finite_model_relation M =
    dependency_on (finite_model_carrier M) (finite_model_immediate M)"
  by (rule ext, rule ext)
    (simp add: finite_model_relation_def finite_model_carrier_def)

lemma finite_model_immediate_eq:
  "finite_model_immediate M =
    (\<lambda>x y. (x, y) \<in> set (finite_edges M))"
  by (rule ext, rule ext)
    (simp add: finite_model_immediate_def)

lemma finite_model_grounded_iff:
  assumes "x \<in> finite_model_carrier M"
  shows "finite_model_grounded M x \<longleftrightarrow>
    grounded_in (finite_model_carrier M) (finite_model_immediate M) x"
  using assms
  unfolding finite_model_grounded_def
  by (auto simp: finite_list_ex_iff
    finite_model_relation_def
    finite_model_carrier_def finite_vertices_def
    finite_model_immediate_eq finite_model_immediate_def
    finite_edges_def grounded_in_def
    intro: dependency_onI dest: dependency_onD)

lemma finite_model_independent_iff:
  assumes "x \<in> finite_model_carrier M"
  shows "finite_model_independent M x \<longleftrightarrow>
    independent_in (finite_model_carrier M) (finite_model_immediate M) x"
  using assms
  unfolding finite_model_independent_def
  by (auto simp: finite_list_ex_iff
    finite_model_relation_def
    finite_model_carrier_def finite_vertices_def
    finite_model_immediate_eq finite_model_immediate_def
    finite_edges_def independent_in_def
    intro: dependency_onI dest: dependency_onD)

lemma finite_model_supports_iff:
  assumes "x \<in> finite_model_carrier M"
  shows "finite_model_supports M x \<longleftrightarrow>
    (\<exists>f. first_member_in (finite_model_carrier M)
      (finite_model_immediate M) f x)"
proof -
  have closed:
      "\<And>u v. dependency_on (finite_model_carrier M)
        (finite_model_immediate M) u v \<Longrightarrow>
        u \<in> finite_model_carrier M \<and>
        v \<in> finite_model_carrier M"
    by (auto simp: dependency_on_def)
  have closedV:
      "\<And>u v. dependency_on (finite_model_carrier M)
        (finite_model_immediate M) u v \<Longrightarrow>
        u \<in> set (finite_vertices M) \<and>
        v \<in> set (finite_vertices M)"
    using closed by (auto simp: finite_model_carrier_def)
  have reach_iff:
      "\<And>f. f \<in> finite_model_carrier M \<Longrightarrow>
        finite_reach (length (finite_vertices M))
          (finite_vertices M)
          (dependency_on (finite_model_carrier M)
            (finite_model_immediate M)) f x
        \<longleftrightarrow>
        dependency_ancestor (finite_model_carrier M)
          (finite_model_immediate M) f x"
  proof -
    fix f
    assume fC: "f \<in> finite_model_carrier M"
    show "finite_reach (length (finite_vertices M))
          (finite_vertices M)
          (dependency_on (finite_model_carrier M)
            (finite_model_immediate M)) f x
        \<longleftrightarrow>
        dependency_ancestor (finite_model_carrier M)
          (finite_model_immediate M) f x"
    proof (rule iffI)
      assume bounded:
        "finite_reach (length (finite_vertices M))
          (finite_vertices M)
          (dependency_on (finite_model_carrier M)
            (finite_model_immediate M)) f x"
      have rtrancl:
          "(dependency_on (finite_model_carrier M)
            (finite_model_immediate M))\<^sup>*\<^sup>* f x"
        using finite_reach_imp_rtranclp[OF bounded] .
      show "dependency_ancestor (finite_model_carrier M)
          (finite_model_immediate M) f x"
        using fC assms rtrancl
        by (simp add: dependency_ancestor_def)
    next
      assume ancestor:
        "dependency_ancestor (finite_model_carrier M)
          (finite_model_immediate M) f x"
      obtain rtrancl:
          "(dependency_on (finite_model_carrier M)
            (finite_model_immediate M))\<^sup>*\<^sup>* f x"
        using ancestor by (auto simp: dependency_ancestor_def)
      show "finite_reach (length (finite_vertices M))
          (finite_vertices M)
          (dependency_on (finite_model_carrier M)
            (finite_model_immediate M)) f x"
      proof -
        have fV: "f \<in> set (finite_vertices M)"
          using fC by (simp add: finite_model_carrier_def)
        show "finite_reach (length (finite_vertices M))
            (finite_vertices M)
            (dependency_on (finite_model_carrier M)
              (finite_model_immediate M)) f x"
          using rtranclp_imp_finite_reach[
            where R = "dependency_on (finite_model_carrier M)
              (finite_model_immediate M)"
              and x = f and y = x and V = "finite_vertices M"]
            rtrancl fV closedV .
      qed
    qed
  qed
  show ?thesis
    unfolding finite_model_supports_def
  proof (rule iffI)
    assume support:
      "finite_list_ex
        (\<lambda>f. finite_model_independent M f \<and>
          finite_reach (length (finite_vertices M))
            (finite_vertices M)
            (dependency_on (finite_model_carrier M)
              (finite_model_immediate M)) f x)
        (finite_vertices M)"
    obtain f where fV: "f \<in> set (finite_vertices M)"
        and f_ind: "finite_model_independent M f"
        and bounded:
          "finite_reach (length (finite_vertices M))
            (finite_vertices M)
            (dependency_on (finite_model_carrier M)
              (finite_model_immediate M)) f x"
      using support by (auto simp: finite_list_ex_iff)
    have fC: "f \<in> finite_model_carrier M"
      using fV by (simp add: finite_model_carrier_def)
    have independent:
          "independent_in (finite_model_carrier M)
            (finite_model_immediate M) f"
      using finite_model_independent_iff[OF fC] f_ind by blast
    have ancestor:
          "dependency_ancestor (finite_model_carrier M)
            (finite_model_immediate M) f x"
      using reach_iff[OF fC] bounded by blast
    show "\<exists>f. first_member_in (finite_model_carrier M)
          (finite_model_immediate M) f x"
      using ancestor independent
      by (intro exI) (simp add: first_member_in_def)
  next
    assume first:
      "\<exists>f. first_member_in (finite_model_carrier M)
        (finite_model_immediate M) f x"
    then obtain f where first_f:
        "first_member_in (finite_model_carrier M)
          (finite_model_immediate M) f x"
      by blast
    have ancestor:
          "dependency_ancestor (finite_model_carrier M)
            (finite_model_immediate M) f x"
      using first_f by (rule first_member_inD)
    have independent:
          "independent_in (finite_model_carrier M)
            (finite_model_immediate M) f"
      using first_f by (rule first_member_inD)
    have fC: "f \<in> finite_model_carrier M"
      using independent by (rule independent_inD)
    have f_ind: "finite_model_independent M f"
      using finite_model_independent_iff[OF fC] independent by blast
    have bounded:
          "finite_reach (length (finite_vertices M))
            (finite_vertices M)
            (dependency_on (finite_model_carrier M)
              (finite_model_immediate M)) f x"
      using reach_iff[OF fC] ancestor by blast
    have fV: "f \<in> set (finite_vertices M)"
      using fC by (simp add: finite_model_carrier_def)
    have Pf:
        "finite_model_independent M f \<and>
          finite_reach (length (finite_vertices M))
            (finite_vertices M)
            (dependency_on (finite_model_carrier M)
              (finite_model_immediate M)) f x"
      using f_ind bounded by blast
    show "finite_list_ex
        (\<lambda>f. finite_model_independent M f \<and>
          finite_reach (length (finite_vertices M))
            (finite_vertices M)
            (dependency_on (finite_model_carrier M)
              (finite_model_immediate M)) f x)
        (finite_vertices M)"
      using fV Pf
      by (rule finite_list_exI)
  qed
qed

lemma finite_model_bad_iff:
  assumes "x \<in> finite_model_carrier M"
  shows "finite_model_bad M x \<longleftrightarrow>
    grounded_in (finite_model_carrier M) (finite_model_immediate M) x \<and>
    \<not> (\<exists>f. first_member_in (finite_model_carrier M)
      (finite_model_immediate M) f x)"
  using assms finite_model_grounded_iff[OF assms]
    finite_model_supports_iff[OF assms]
  by (auto simp: finite_model_bad_def)

theorem finite_foundation_check_iff:
  "finite_foundation_check M \<longleftrightarrow>
   local_foundation_on (finite_model_carrier M)
     (finite_model_immediate M) (finite_model_carrier M)"
proof -
  show ?thesis
    unfolding finite_foundation_check_def local_foundation_on_def
  proof (rule iffI)
    assume check:
      "finite_list_all (\<lambda>x. \<not> finite_model_bad M x)
        (finite_vertices M)"
    show "\<forall>a \<in> finite_model_carrier M.
      grounded_in (finite_model_carrier M) (finite_model_immediate M) a
      \<longrightarrow> (\<exists>f. first_member_in (finite_model_carrier M)
        (finite_model_immediate M) f a)"
    proof (intro ballI impI)
      fix a
      assume aC: "a \<in> finite_model_carrier M"
        and grounded:
          "grounded_in (finite_model_carrier M)
            (finite_model_immediate M) a"
      have not_bad: "\<not> finite_model_bad M a"
        using check aC
        by (simp add: finite_list_all_iff finite_model_carrier_def)
      have bad_iff: "finite_model_bad M a \<longleftrightarrow>
          grounded_in (finite_model_carrier M)
            (finite_model_immediate M) a \<and>
          \<not> (\<exists>f. first_member_in (finite_model_carrier M)
            (finite_model_immediate M) f a)"
        by (rule finite_model_bad_iff[OF aC])
      show "\<exists>f. first_member_in (finite_model_carrier M)
        (finite_model_immediate M) f a"
        using not_bad grounded bad_iff by blast
    qed
  next
    assume foundation:
      "\<forall>a \<in> finite_model_carrier M.
        grounded_in (finite_model_carrier M)
          (finite_model_immediate M) a
        \<longrightarrow> (\<exists>f. first_member_in (finite_model_carrier M)
          (finite_model_immediate M) f a)"
    have all_bad:
        "\<forall>a \<in> set (finite_vertices M). \<not> finite_model_bad M a"
    proof (intro ballI)
      fix a
      assume a_list: "a \<in> set (finite_vertices M)"
      have aC: "a \<in> finite_model_carrier M"
        using a_list by (simp add: finite_model_carrier_def)
      have bad_iff: "finite_model_bad M a \<longleftrightarrow>
          grounded_in (finite_model_carrier M)
            (finite_model_immediate M) a \<and>
          \<not> (\<exists>f. first_member_in (finite_model_carrier M)
            (finite_model_immediate M) f a)"
        by (rule finite_model_bad_iff[OF aC])
      show "\<not> finite_model_bad M a"
        using foundation aC bad_iff by blast
    qed
    show "finite_list_all (\<lambda>x. \<not> finite_model_bad M x)
      (finite_vertices M)"
      using all_bad by (simp add: finite_list_all_iff)
  qed
qed

lemma finite_failure_witness_spec:
  assumes "\<not> finite_foundation_check M"
  shows "finite_failure_witness M \<in> finite_model_carrier M"
    and "finite_model_bad M (finite_failure_witness M)"
proof -
  have bad_exists:
      "\<exists>x \<in> set (finite_vertices M). finite_model_bad M x"
    using assms
    by (simp add: finite_foundation_check_def finite_list_all_iff)
  obtain x where failure:
      "finite_first_failure (finite_model_bad M) (finite_vertices M) =
        Some x"
    and x_list: "x \<in> set (finite_vertices M)"
    and bad: "finite_model_bad M x"
    using finite_first_failure_complete[OF bad_exists] .
  have witness_eq: "finite_failure_witness M = x"
    using failure by (simp add: finite_failure_witness_def)
  have xC: "x \<in> finite_model_carrier M"
    using x_list by (simp add: finite_model_carrier_def)
  show "finite_failure_witness M \<in> finite_model_carrier M"
    using witness_eq xC by simp
  show "finite_model_bad M (finite_failure_witness M)"
    using witness_eq bad by simp
qed

lemma finite_foundation_result_success:
  assumes "finite_foundation_result M =
    Foundation_Certificate roots"
  shows "local_foundation_on (finite_model_carrier M)
    (finite_model_immediate M) (finite_model_carrier M)"
proof -
  have "finite_foundation_check M"
    using assms
    by (simp add: finite_foundation_result_def split: if_splits)
  then show ?thesis
    using finite_foundation_check_iff by blast
qed

theorem finite_foundation_result_roots:
  assumes "finite_foundation_result M =
    Foundation_Certificate roots"
  shows "set roots =
    {x \<in> finite_model_carrier M.
      independent_in (finite_model_carrier M)
        (finite_model_immediate M) x}"
proof -
  have check: "finite_foundation_check M"
    using assms
    by (simp add: finite_foundation_result_def split: if_splits)
  have roots_eq:
      "roots = filter (finite_model_independent M) (finite_vertices M)"
    using assms check
    by (simp add: finite_foundation_result_def)
  have model_roots:
      "set roots =
        {x \<in> finite_model_carrier M. finite_model_independent M x}"
    using roots_eq
    by (simp add: finite_model_carrier_def)
  have root_independent:
      "{x \<in> finite_model_carrier M. finite_model_independent M x} =
       {x \<in> finite_model_carrier M.
         independent_in (finite_model_carrier M)
           (finite_model_immediate M) x}"
  proof (rule set_eqI)
    fix x
    show "x \<in> {x \<in> finite_model_carrier M.
          finite_model_independent M x} \<longleftrightarrow>
        x \<in> {x \<in> finite_model_carrier M.
          independent_in (finite_model_carrier M)
            (finite_model_immediate M) x}"
    proof (rule iffI)
      assume left:
        "x \<in> {x \<in> finite_model_carrier M.
          finite_model_independent M x}"
      have xC: "x \<in> finite_model_carrier M"
        using left by simp
      have finite_independent: "finite_model_independent M x"
        using left by simp
      have independent:
          "independent_in (finite_model_carrier M)
            (finite_model_immediate M) x"
        using finite_model_independent_iff[OF xC] finite_independent
        by blast
      show "x \<in> {x \<in> finite_model_carrier M.
          independent_in (finite_model_carrier M)
            (finite_model_immediate M) x}"
        using xC independent by simp
    next
      assume right:
        "x \<in> {x \<in> finite_model_carrier M.
          independent_in (finite_model_carrier M)
            (finite_model_immediate M) x}"
      have xC: "x \<in> finite_model_carrier M"
        using right by simp
      have independent:
          "independent_in (finite_model_carrier M)
            (finite_model_immediate M) x"
        using right by simp
      have finite_independent: "finite_model_independent M x"
        using finite_model_independent_iff[OF xC] independent
        by blast
      show "x \<in> {x \<in> finite_model_carrier M.
          finite_model_independent M x}"
        using xC finite_independent by simp
    qed
  qed
  then show ?thesis
    using model_roots by simp
qed

theorem finite_foundation_result_certificate:
  assumes "finite_foundation_result M =
    Foundation_Certificate roots"
  shows "foundation_set_for (finite_model_carrier M)
      (finite_model_immediate M) (finite_model_carrier M) (set roots)"
proof -
  have root_set:
      "set roots =
        {x \<in> finite_model_carrier M.
          independent_in (finite_model_carrier M)
            (finite_model_immediate M) x}"
    using finite_foundation_result_roots[OF assms] .
  have roots_carrier:
      "set roots \<subseteq> finite_model_carrier M"
    using root_set by auto
  have roots_independent:
      "\<forall>f \<in> set roots.
        independent_in (finite_model_carrier M)
          (finite_model_immediate M) f"
    using root_set by auto
  have local:
      "\<forall>a \<in> finite_model_carrier M.
        grounded_in (finite_model_carrier M)
          (finite_model_immediate M) a \<longrightarrow>
        (\<exists>f. first_member_in (finite_model_carrier M)
          (finite_model_immediate M) f a)"
    using finite_foundation_result_success[OF assms]
    by (simp add: local_foundation_on_def)
  have supports:
      "\<forall>a \<in> finite_model_carrier M.
        grounded_in (finite_model_carrier M)
          (finite_model_immediate M) a \<longrightarrow>
        (\<exists>f \<in> set roots.
          dependency_ancestor (finite_model_carrier M)
            (finite_model_immediate M) f a)"
  proof (intro ballI impI)
    fix a
    assume aC: "a \<in> finite_model_carrier M"
      and grounded:
        "grounded_in (finite_model_carrier M)
          (finite_model_immediate M) a"
    obtain f where first: "first_member_in (finite_model_carrier M)
        (finite_model_immediate M) f a"
      using local aC grounded by blast
    have f_independent:
        "independent_in (finite_model_carrier M)
          (finite_model_immediate M) f"
      using first by (rule first_member_inD)
    have f_ancestor:
        "dependency_ancestor (finite_model_carrier M)
          (finite_model_immediate M) f a"
      using first by (rule first_member_inD)
    have fC: "f \<in> finite_model_carrier M"
      using f_independent by (rule independent_inD)
    have f_root: "f \<in> set roots"
      using root_set fC f_independent by auto
    then show "\<exists>f \<in> set roots.
        dependency_ancestor (finite_model_carrier M)
          (finite_model_immediate M) f a"
      using f_ancestor by blast
  qed
  show ?thesis
    unfolding foundation_set_for_def
    using roots_carrier roots_independent supports by blast
qed

lemma finite_foundation_result_failure:
  assumes "finite_foundation_result M =
    Missing_Foundation_Certificate x"
  shows "x \<in> finite_model_carrier M" and "finite_model_bad M x"
proof -
  have not_check: "\<not> finite_foundation_check M"
    using assms
    by (simp add: finite_foundation_result_def split: if_splits)
  have witness:
      "finite_failure_witness M \<in> finite_model_carrier M"
      "finite_model_bad M (finite_failure_witness M)"
    using finite_failure_witness_spec[OF not_check] .
  have x_eq: "x = finite_failure_witness M"
    using assms not_check
    by (simp add: finite_foundation_result_def)
  show "x \<in> finite_model_carrier M"
    using x_eq witness(1) by simp
  show "finite_model_bad M x"
    using x_eq witness(2) by simp
qed

theorem finite_foundation_result_complete:
  assumes "\<not> local_foundation_on (finite_model_carrier M)
    (finite_model_immediate M) (finite_model_carrier M)"
  obtains x where
    "finite_foundation_result M =
      Missing_Foundation_Certificate x"
    and "x \<in> finite_model_carrier M"
    and "finite_model_bad M x"
proof -
  have not_check: "\<not> finite_foundation_check M"
    using assms finite_foundation_check_iff by blast
  have witness:
      "finite_failure_witness M \<in> finite_model_carrier M"
      "finite_model_bad M (finite_failure_witness M)"
    using finite_failure_witness_spec[OF not_check] .
  have result:
      "finite_foundation_result M =
        Missing_Foundation_Certificate (finite_failure_witness M)"
    using not_check
    by (simp add: finite_foundation_result_def)
  show thesis
    using result witness by (rule that)
qed

theorem finite_foundation_result_correct:
  "(\<exists>roots. finite_foundation_result M =
      Foundation_Certificate roots) \<longleftrightarrow>
   local_foundation_on (finite_model_carrier M)
     (finite_model_immediate M) (finite_model_carrier M)"
proof
  assume "\<exists>roots. finite_foundation_result M =
    Foundation_Certificate roots"
  then obtain roots where result:
      "finite_foundation_result M = Foundation_Certificate roots"
    by blast
  then show "local_foundation_on (finite_model_carrier M)
      (finite_model_immediate M) (finite_model_carrier M)"
    by (rule finite_foundation_result_success)
next
  assume foundation:
    "local_foundation_on (finite_model_carrier M)
      (finite_model_immediate M) (finite_model_carrier M)"
  have "finite_foundation_check M"
    using foundation finite_foundation_check_iff by blast
  then show "\<exists>roots. finite_foundation_result M =
      Foundation_Certificate roots"
    by (auto simp: finite_foundation_result_def)
qed

section \<open>Executable Regression Models\<close>

definition finite_chain_model :: finite_dependency_model
where
  "finite_chain_model = ([0, 1, 2], [(0, 1), (1, 2)])"

definition finite_cycle_model :: finite_dependency_model
where
  "finite_cycle_model = ([0, 1], [(0, 1), (1, 0)])"

value "finite_foundation_result finite_chain_model"
value "finite_foundation_result finite_cycle_model"

end
