theory Finite_Foundation_Analysis
  imports Finite_Foundation_Checker Research_Results
begin

section \<open>Cycle Certificates\<close>

text \<open>
  The existing finite checker certifies the local foundation predicate.  This
  cycle analyzer exposes the other obstruction that matters for the
  binary lattice: a concrete carrier vertex together with a bounded return
  path.  The internal return-segment bound is the length of the supplied
  vertex list; the emitted closed certificate prepends one endpoint and is
  therefore bounded by one greater.  The path lemmas below prove completeness
  for carrier-closed finite relations and expose the resulting payload bound.
\<close>

fun finite_path_to ::
  "nat \<Rightarrow> 'a list \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   'a \<Rightarrow> 'a \<Rightarrow> 'a list option"
where
  "finite_path_to 0 V R x y =
     (if x = y then Some [] else None)"
| "finite_path_to (Suc n) V R x y =
     (if x = y then Some []
      else
        (case List.find
          (\<lambda>z. R x z \<and> finite_reach n V R z y) V of
           None \<Rightarrow> None
         | Some z \<Rightarrow>
             (case finite_path_to n V R z y of
                None \<Rightarrow> None
              | Some ys \<Rightarrow> Some (z # ys))))"

lemma finite_path_to_sound:
  "finite_path_to n V R x y = Some ys \<Longrightarrow>
   rtrancl_path R x ys y"
proof (induction n arbitrary: x y ys)
  case 0
  have base: "x = y \<and> ys = []"
    using \<open>finite_path_to 0 V R x y = Some ys\<close>
    by (simp add: finite_path_to.simps split: if_splits)
  have xy: "x = y"
    using base by simp
  have ys0: "ys = []"
    using base by simp
  show ?case
    unfolding xy ys0
  proof (rule rtrancl_path.base)
  qed
next
  case (Suc n)
  then show ?case
  proof (cases "x = y")
    case True
    have ys0: "ys = []"
      using Suc.prems True by (simp add: finite_path_to.simps)
    show ?thesis
      unfolding True ys0
    proof (rule rtrancl_path.base)
    qed
  next
    case False
    obtain z where find:
        "List.find
          (\<lambda>z. R x z \<and> finite_reach n V R z y) V = Some z"
      and path: "finite_path_to n V R z y = Some (tl ys)"
      using Suc.prems False
      by (auto split: option.splits)
    have pred:
        "R x z \<and> finite_reach n V R z y"
      using find by (auto simp add: List.find_Some_iff)
    have path': "rtrancl_path R z (tl ys) y"
      using Suc.IH[OF path] .
    have z_head: "ys = z # tl ys"
      using Suc.prems False find path by (auto split: option.splits)
    obtain ys' where ys_eq: "ys = z # ys'"
      using z_head by (cases ys) auto
    have tail_eq: "tl ys = ys'"
      using ys_eq by simp
    have path_tail: "rtrancl_path R z ys' y"
      using path' tail_eq by simp
    show ?thesis
      unfolding ys_eq
    proof (rule rtrancl_path.step)
      show "R x z"
        using pred by (rule conjunct1)
      show "rtrancl_path R z ys' y"
        using path_tail .
    qed
  qed
qed

lemma finite_path_to_complete:
  "finite_reach n V R x y \<Longrightarrow>
   (\<exists>ys. finite_path_to n V R x y = Some ys)"
proof (induction n arbitrary: x y)
  case 0
  then show ?case
    by (auto intro: exI[of _ "[]"])
next
  case (Suc n)
  show ?case
  proof (cases "x = y")
    case True
    have eq: "finite_path_to (Suc n) V R x y = Some []"
      using True by (simp add: finite_path_to.simps)
    show ?thesis
      using eq by (rule exI)
  next
    case False
    obtain z where zV: "z \<in> set V" and edge: "R x z"
      and reach: "finite_reach n V R z y"
      using Suc.prems False
      by (auto simp: finite_reach.simps finite_list_ex_iff)
    have find_ne:
        "List.find
          (\<lambda>w. R x w \<and> finite_reach n V R w y) V \<noteq> None"
    proof
      assume none:
        "List.find
          (\<lambda>w. R x w \<and> finite_reach n V R w y) V = None"
      have no_candidate:
          "\<not> (\<exists>w \<in> set V.
            R x w \<and> finite_reach n V R w y)"
        using List.find_None_iff[of "\<lambda>w. R x w \<and>
          finite_reach n V R w y" V] none by blast
      show False
        using no_candidate zV edge reach by blast
    qed
    obtain w where find:
        "List.find
          (\<lambda>w. R x w \<and> finite_reach n V R w y) V = Some w"
      using find_ne by (cases "List.find
          (\<lambda>w. R x w \<and> finite_reach n V R w y) V") auto
    have pred: "R x w \<and> finite_reach n V R w y"
      using find by (auto simp add: List.find_Some_iff)
    have reach_w: "finite_reach n V R w y"
      using pred by (rule conjunct2)
    obtain ys where path: "finite_path_to n V R w y = Some ys"
      using Suc.IH[OF reach_w] by blast
    have result:
        "finite_path_to (Suc n) V R x y = Some (w # ys)"
      using False find path by (simp add: finite_path_to.simps)
    show ?thesis
      using result by (rule exI)
  qed
qed

lemma finite_path_to_obtain:
  assumes "finite_reach n V R x y"
  obtains ys where "finite_path_to n V R x y = Some ys"
  using finite_path_to_complete[OF assms] by blast

lemma finite_path_to_length_le:
  "finite_path_to n V R x y = Some ys \<Longrightarrow> length ys \<le> n"
proof (induction n arbitrary: x y ys)
  case 0
  then show ?case
    by (simp add: finite_path_to.simps split: if_splits)
next
  case (Suc n)
  show ?case
  proof (cases "x = y")
    case True
    then show ?thesis
      using Suc.prems by (simp add: finite_path_to.simps)
  next
    case False
    obtain z where find:
        "List.find
          (\<lambda>z. R x z \<and> finite_reach n V R z y) V = Some z"
      and path: "finite_path_to n V R z y = Some (tl ys)"
      using Suc.prems False
      by (auto split: option.splits)
    have z_head: "ys = z # tl ys"
      using Suc.prems False find path by (auto split: option.splits)
    have tail_bound: "length (tl ys) \<le> n"
      using Suc.IH[OF path] .
    have nonempty: "ys \<noteq> []"
      using z_head by (cases ys) auto
    have "length ys = Suc (length (tl ys))"
      using nonempty by simp
    then show ?thesis
      using tail_bound by simp
  qed
qed

definition finite_cycle_at ::
  "finite_dependency_model \<Rightarrow> nat \<Rightarrow> bool"
where
  "finite_cycle_at M x \<longleftrightarrow>
     x \<in> finite_model_carrier M \<and>
     finite_list_ex
       (\<lambda>y. finite_model_relation M x y \<and>
         finite_reach (length (finite_vertices M))
           (finite_vertices M) (finite_model_relation M) y x)
       (finite_vertices M)"

definition finite_cycle_path_at ::
  "finite_dependency_model \<Rightarrow> nat \<Rightarrow> nat list option"
where
  "finite_cycle_path_at M x =
     (if x \<in> finite_model_carrier M then
        (case List.find
          (\<lambda>y. finite_model_relation M x y \<and>
            finite_reach (length (finite_vertices M))
              (finite_vertices M) (finite_model_relation M) y x)
          (finite_vertices M) of
           None \<Rightarrow> None
         | Some y \<Rightarrow>
             (case finite_path_to (length (finite_vertices M))
                (finite_vertices M) (finite_model_relation M) y x of
                None \<Rightarrow> None
              | Some ys \<Rightarrow> Some (y # ys)))
      else None)"

lemma finite_cycle_path_at_sound:
  assumes "finite_cycle_path_at M x = Some xs"
  shows "x \<in> finite_model_carrier M"
    and "xs \<noteq> []"
    and "rtrancl_path (finite_model_relation M) x xs x"
    and "(finite_model_relation M)\<^sup>+\<^sup>+ x x"
proof -
  have xC: "x \<in> finite_model_carrier M"
    using assms by (auto simp: finite_cycle_path_at_def
      split: if_splits option.splits)
  obtain y where find:
      "List.find
        (\<lambda>y. finite_model_relation M x y \<and>
          finite_reach (length (finite_vertices M))
            (finite_vertices M) (finite_model_relation M) y x)
        (finite_vertices M) = Some y"
    and path:
      "finite_path_to (length (finite_vertices M))
        (finite_vertices M) (finite_model_relation M) y x = Some (tl xs)"
    and xs_head: "xs = y # tl xs"
    using assms xC
    by (auto simp: finite_cycle_path_at_def
      split: if_splits option.splits)
  have pred:
      "finite_model_relation M x y \<and>
       finite_reach (length (finite_vertices M))
         (finite_vertices M) (finite_model_relation M) y x"
    using find by (auto simp add: List.find_Some_iff)
  have edge: "finite_model_relation M x y"
    using pred by (rule conjunct1)
  have bounded:
      "finite_reach (length (finite_vertices M))
        (finite_vertices M) (finite_model_relation M) y x"
    using pred by (rule conjunct2)
  have path_tail:
      "rtrancl_path (finite_model_relation M) y (tl xs) x"
    using finite_path_to_sound[OF path] .
  obtain ys where xs_eq: "xs = y # ys"
    using xs_head by (cases xs) auto
  have tail_eq: "tl xs = ys"
    using xs_eq by simp
  have path_tail':
      "rtrancl_path (finite_model_relation M) y ys x"
    using path_tail tail_eq by simp
  have path_full':
      "rtrancl_path (finite_model_relation M) x (y # ys) x"
  proof (rule rtrancl_path.step)
    show "finite_model_relation M x y"
      using edge .
    show "rtrancl_path (finite_model_relation M) y ys x"
      using path_tail' .
  qed
  have path_full:
      "rtrancl_path (finite_model_relation M) x xs x"
    using path_full' xs_eq by simp
  have rtrancl:
      "(finite_model_relation M)\<^sup>*\<^sup>* y x"
    using finite_reach_imp_rtranclp[OF bounded] .
  have cycle:
      "(finite_model_relation M)\<^sup>+\<^sup>+ x x"
    using rtranclp_into_tranclp2[OF edge rtrancl] .
  show "x \<in> finite_model_carrier M"
    using xC .
  show "xs \<noteq> []"
    using xs_head by (cases xs) auto
  show "rtrancl_path (finite_model_relation M) x xs x"
    using path_full .
  show "(finite_model_relation M)\<^sup>+\<^sup>+ x x"
    using cycle .
qed

lemma finite_cycle_path_at_complete:
  assumes "finite_cycle_at M x"
  obtains xs where "finite_cycle_path_at M x = Some xs"
    and "xs \<noteq> []"
    and "rtrancl_path (finite_model_relation M) x xs x"
proof -
  obtain y where yV: "y \<in> set (finite_vertices M)"
    and pred:
      "finite_model_relation M x y \<and>
       finite_reach (length (finite_vertices M))
         (finite_vertices M) (finite_model_relation M) y x"
    using assms
    by (auto simp: finite_cycle_at_def finite_list_ex_iff)
  have find_ne:
      "List.find
        (\<lambda>z. finite_model_relation M x z \<and>
          finite_reach (length (finite_vertices M))
            (finite_vertices M) (finite_model_relation M) z x)
        (finite_vertices M) \<noteq> None"
  proof
    assume none:
      "List.find
        (\<lambda>z. finite_model_relation M x z \<and>
          finite_reach (length (finite_vertices M))
            (finite_vertices M) (finite_model_relation M) z x)
        (finite_vertices M) = None"
    have no_candidate:
        "\<not> (\<exists>z \<in> set (finite_vertices M).
          finite_model_relation M x z \<and>
          finite_reach (length (finite_vertices M))
            (finite_vertices M) (finite_model_relation M) z x)"
      using List.find_None_iff[of "\<lambda>z. finite_model_relation M x z \<and>
        finite_reach (length (finite_vertices M))
          (finite_vertices M) (finite_model_relation M) z x"
        "finite_vertices M"] none by blast
    show False
      using no_candidate yV pred by blast
  qed
  obtain y' where find:
      "List.find
        (\<lambda>z. finite_model_relation M x z \<and>
          finite_reach (length (finite_vertices M))
            (finite_vertices M) (finite_model_relation M) z x)
        (finite_vertices M) = Some y'"
    using find_ne by (cases "List.find
        (\<lambda>z. finite_model_relation M x z \<and>
          finite_reach (length (finite_vertices M))
            (finite_vertices M) (finite_model_relation M) z x)
        (finite_vertices M)") auto
  have pred':
      "finite_model_relation M x y' \<and>
       finite_reach (length (finite_vertices M))
         (finite_vertices M) (finite_model_relation M) y' x"
    using find by (auto simp add: List.find_Some_iff)
  have reach':
      "finite_reach (length (finite_vertices M))
        (finite_vertices M) (finite_model_relation M) y' x"
    using pred' by blast
  have at_spec: "finite_cycle_at M x"
    using assms .
  have xC: "x \<in> finite_model_carrier M"
    using at_spec by (simp add: finite_cycle_at_def)
  obtain ys where path:
      "finite_path_to (length (finite_vertices M))
        (finite_vertices M) (finite_model_relation M) y' x = Some ys"
    using finite_path_to_obtain[OF reach'] by blast
  have result: "finite_cycle_path_at M x = Some (y' # ys)"
    using xC find path
    by (simp add: finite_cycle_path_at_def)
  have sound:
      "rtrancl_path (finite_model_relation M) x (y' # ys) x"
    using finite_cycle_path_at_sound[OF result] by blast
  have exists_conclusion:
      "\<exists>xs. finite_cycle_path_at M x = Some xs \<and>
        xs \<noteq> [] \<and>
        rtrancl_path (finite_model_relation M) x xs x"
  proof -
    have witness:
        "finite_cycle_path_at M x = Some (y' # ys) \<and>
         (y' # ys) \<noteq> [] \<and>
         rtrancl_path (finite_model_relation M) x (y' # ys) x"
      using result sound by blast
    show ?thesis
      using witness by blast
  qed
  then obtain xs where
      "finite_cycle_path_at M x = Some xs"
    and "xs \<noteq> []"
    and "rtrancl_path (finite_model_relation M) x xs x"
    by blast
  then show thesis
    by (rule that)
qed

lemma finite_cycle_path_at_length_le:
  assumes "finite_cycle_path_at M x = Some xs"
  shows "length xs \<le> Suc (length (finite_vertices M))"
proof -
  have xC: "x \<in> finite_model_carrier M"
    using assms by (auto simp: finite_cycle_path_at_def
      split: if_splits option.splits)
  obtain y where find:
      "List.find
        (\<lambda>y. finite_model_relation M x y \<and>
          finite_reach (length (finite_vertices M))
            (finite_vertices M) (finite_model_relation M) y x)
        (finite_vertices M) = Some y"
    and path:
      "finite_path_to (length (finite_vertices M))
        (finite_vertices M) (finite_model_relation M) y x = Some (tl xs)"
    and xs_head: "xs = y # tl xs"
    using assms xC
    by (auto simp: finite_cycle_path_at_def
      split: if_splits option.splits)
  have tail_bound:
      "length (tl xs) \<le> length (finite_vertices M)"
    using finite_path_to_length_le[OF path] .
  have nonempty: "xs \<noteq> []"
    using xs_head by (cases xs) auto
  have "length xs = Suc (length (tl xs))"
    using nonempty by simp
  then show ?thesis
    using tail_bound by simp
qed

lemma finite_model_relation_closed:
  fixes M :: finite_dependency_model and u v :: nat
  assumes "finite_model_relation M u v"
  shows "u \<in> set (finite_vertices M) \<and>
    v \<in> set (finite_vertices M)"
  using assms
  by (auto simp: finite_model_relation_def finite_model_carrier_def
    dependency_on_def)

definition finite_cycle_witness ::
  "finite_dependency_model \<Rightarrow> nat option"
where
  "finite_cycle_witness M =
     finite_first_failure (finite_cycle_at M) (finite_vertices M)"

definition finite_cycle_check ::
  "finite_dependency_model \<Rightarrow> bool"
where
  "finite_cycle_check M \<longleftrightarrow>
     finite_cycle_witness M = None"

definition finite_cycle_failure_witness ::
  "finite_dependency_model \<Rightarrow> nat"
where
  "finite_cycle_failure_witness M =
     (case finite_cycle_witness M of
        None \<Rightarrow> 0
      | Some x \<Rightarrow> x)"

definition finite_cycle_failure_path ::
  "finite_dependency_model \<Rightarrow> nat list"
where
  "finite_cycle_failure_path M =
     (case finite_cycle_witness M of
        None \<Rightarrow> []
      | Some x \<Rightarrow>
          (case finite_cycle_path_at M x of
             None \<Rightarrow> []
           | Some xs \<Rightarrow> xs))"

datatype finite_cycle_result =
    No_Cycle_Certificate
  | Cycle_Certificate nat "nat list"

definition finite_cycle_result ::
  "finite_dependency_model \<Rightarrow> finite_cycle_result"
where
  "finite_cycle_result M =
     (if finite_cycle_check M then
        No_Cycle_Certificate
      else
        Cycle_Certificate (finite_cycle_failure_witness M)
          (finite_cycle_failure_path M))"

lemma finite_first_failure_none_iff:
  "finite_first_failure P xs = None \<longleftrightarrow>
   (\<forall>x \<in> set xs. \<not> P x)"
  by (induction xs) (auto split: if_splits)

lemma finite_cycle_witness_some:
  assumes "finite_cycle_witness M = Some x"
  shows "x \<in> finite_model_carrier M" "finite_cycle_at M x"
proof -
  have failure:
      "finite_first_failure (finite_cycle_at M) (finite_vertices M) =
        Some x"
    using assms by (simp add: finite_cycle_witness_def)
  have "x \<in> set (finite_vertices M)"
    and "finite_cycle_at M x"
    using finite_first_failure_sound[OF failure] .
  show "x \<in> finite_model_carrier M"
    using \<open>x \<in> set (finite_vertices M)\<close>
    by (simp add: finite_model_carrier_def)
  show "finite_cycle_at M x"
    using \<open>finite_cycle_at M x\<close> .
qed

lemma finite_cycle_at_iff:
  "finite_cycle_at M x \<longleftrightarrow>
   x \<in> finite_model_carrier M \<and>
   (dependency_on (finite_model_carrier M)
      (finite_model_immediate M))\<^sup>+\<^sup>+ x x"
proof
  assume at: "finite_cycle_at M x"
  have xC: "x \<in> finite_model_carrier M"
    using at by (simp add: finite_cycle_at_def)
  obtain y where yV: "y \<in> set (finite_vertices M)"
    and edge: "finite_model_relation M x y"
    and reach:
      "finite_reach (length (finite_vertices M))
        (finite_vertices M) (finite_model_relation M) y x"
    using at
    by (auto simp: finite_cycle_at_def finite_list_ex_iff)
  have rtrancl: "(finite_model_relation M)\<^sup>*\<^sup>* y x"
    using finite_reach_imp_rtranclp[OF reach] .
  have cycle: "(finite_model_relation M)\<^sup>+\<^sup>+ x x"
    using rtranclp_into_tranclp2[OF edge rtrancl] .
  show "x \<in> finite_model_carrier M \<and>
      (dependency_on (finite_model_carrier M)
        (finite_model_immediate M))\<^sup>+\<^sup>+ x x"
    using xC cycle finite_model_relation_eq by simp
next
  assume cycle:
    "x \<in> finite_model_carrier M \<and>
      (dependency_on (finite_model_carrier M)
        (finite_model_immediate M))\<^sup>+\<^sup>+ x x"
  have xC: "x \<in> finite_model_carrier M"
    using cycle by blast
  have relation_eq:
      "finite_model_relation M =
        dependency_on (finite_model_carrier M)
          (finite_model_immediate M)"
    by (rule finite_model_relation_eq)
  have cycle_relation:
      "(finite_model_relation M)\<^sup>+\<^sup>+ x x"
    using cycle relation_eq by simp
  obtain y where edge: "finite_model_relation M x y"
    and tail: "(finite_model_relation M)\<^sup>*\<^sup>* y x"
    using tranclpD[OF cycle_relation] by blast
  have yV: "y \<in> set (finite_vertices M)"
    using edge finite_model_relation_closed by blast
  have relation_closed:
      "\<And>u v. finite_model_relation M u v \<Longrightarrow>
        u \<in> set (finite_vertices M) \<and>
        v \<in> set (finite_vertices M)"
    using finite_model_relation_closed by blast
  have bounded:
      "finite_reach (length (finite_vertices M))
        (finite_vertices M) (finite_model_relation M) y x"
    using rtranclp_imp_finite_reach[
      where R = "finite_model_relation M"
        and V = "finite_vertices M" and x = y and y = x]
      tail yV relation_closed .
  have path:
      "finite_list_ex
        (\<lambda>z. finite_model_relation M x z \<and>
          finite_reach (length (finite_vertices M))
            (finite_vertices M) (finite_model_relation M) z x)
        (finite_vertices M)"
    using finite_list_exI[of y
      "finite_vertices M"
      "\<lambda>z. finite_model_relation M x z \<and>
        finite_reach (length (finite_vertices M))
          (finite_vertices M) (finite_model_relation M) z x"]
      yV edge bounded by blast
  show "finite_cycle_at M x"
    unfolding finite_cycle_at_def
    using xC path by blast
qed

theorem finite_cycle_check_iff:
  "finite_cycle_check M \<longleftrightarrow>
   acyclic_on (finite_model_carrier M) (finite_model_immediate M)"
proof -
  have no_failure:
      "finite_cycle_witness M = None \<longleftrightarrow>
       (\<forall>x \<in> finite_model_carrier M. \<not> finite_cycle_at M x)"
    unfolding finite_cycle_witness_def
    by (simp add: finite_first_failure_none_iff finite_model_carrier_def)
  show ?thesis
    unfolding finite_cycle_check_def acyclic_on_def
    using no_failure finite_cycle_at_iff by simp
qed

theorem finite_cycle_result_no_cycle:
  "finite_cycle_result M = No_Cycle_Certificate \<longleftrightarrow>
   acyclic_on (finite_model_carrier M) (finite_model_immediate M)"
  unfolding finite_cycle_result_def
  using finite_cycle_check_iff by simp

theorem finite_cycle_result_cycle:
  assumes "finite_cycle_result M = Cycle_Certificate x xs"
  shows "x \<in> finite_model_carrier M"
    and "xs \<noteq> []"
    and "rtrancl_path (finite_model_relation M) x xs x"
    and "(dependency_on (finite_model_carrier M)
      (finite_model_immediate M))\<^sup>+\<^sup>+ x x"
proof -
  have not_check: "\<not> finite_cycle_check M"
    using assms by (simp add: finite_cycle_result_def split: if_splits)
  have witness_ne: "finite_cycle_witness M \<noteq> None"
    using not_check by (auto simp: finite_cycle_check_def)
  obtain y where witness_y:
      "finite_cycle_witness M = Some y"
    using witness_ne by (cases "finite_cycle_witness M") auto
  have at: "finite_cycle_at M y"
    using finite_cycle_witness_some[OF witness_y] by blast
  obtain ys where path_at:
      "finite_cycle_path_at M y = Some ys"
    and ys_nonempty: "ys \<noteq> []"
    and path:
      "rtrancl_path (finite_model_relation M) y ys y"
    using finite_cycle_path_at_complete[OF at] .
  have result_expanded:
      "finite_cycle_result M = Cycle_Certificate y ys"
    using not_check witness_y path_at
    by (simp add: finite_cycle_result_def
      finite_cycle_failure_witness_def finite_cycle_failure_path_def)
  have certificate_eq:
      "Cycle_Certificate x xs = Cycle_Certificate y ys"
    using assms result_expanded by simp
  have x_eq: "x = y"
    using certificate_eq by simp
  have xs_eq: "xs = ys"
    using certificate_eq by simp
  have sound_spec:
      "y \<in> finite_model_carrier M \<and>
       ys \<noteq> [] \<and>
       rtrancl_path (finite_model_relation M) y ys y \<and>
       (finite_model_relation M)\<^sup>+\<^sup>+ y y"
    using finite_cycle_path_at_sound[OF path_at] by blast
  show "x \<in> finite_model_carrier M"
    using sound_spec x_eq by blast
  show "xs \<noteq> []"
    using ys_nonempty xs_eq by simp
  show "rtrancl_path (finite_model_relation M) x xs x"
    using path x_eq xs_eq by simp
  have cycle:
      "(finite_model_relation M)\<^sup>+\<^sup>+ x x"
    using sound_spec x_eq by blast
  show "(dependency_on (finite_model_carrier M)
      (finite_model_immediate M))\<^sup>+\<^sup>+ x x"
    using cycle finite_model_relation_eq by simp
qed

lemma finite_cycle_result_cycle_spec:
  assumes "finite_cycle_result M = Cycle_Certificate x xs"
  shows "x \<in> finite_model_carrier M \<and>
    xs \<noteq> [] \<and>
    rtrancl_path (finite_model_relation M) x xs x \<and>
    (dependency_on (finite_model_carrier M)
      (finite_model_immediate M))\<^sup>+\<^sup>+ x x"
  using finite_cycle_result_cycle[OF assms] by blast

lemma finite_cycle_result_cycle_length:
  assumes "finite_cycle_result M = Cycle_Certificate x xs"
  shows "length xs \<le> Suc (length (finite_vertices M))"
proof -
  have not_check: "\<not> finite_cycle_check M"
    using assms by (simp add: finite_cycle_result_def split: if_splits)
  have witness_ne: "finite_cycle_witness M \<noteq> None"
    using not_check by (auto simp: finite_cycle_check_def)
  obtain y where witness_y:
      "finite_cycle_witness M = Some y"
    using witness_ne by (cases "finite_cycle_witness M") auto
  have at: "finite_cycle_at M y"
    using finite_cycle_witness_some[OF witness_y] by blast
  obtain ys where path_at:
      "finite_cycle_path_at M y = Some ys"
    using finite_cycle_path_at_complete[OF at] by blast
  have result_expanded:
      "finite_cycle_result M = Cycle_Certificate y ys"
    using not_check witness_y path_at
    by (simp add: finite_cycle_result_def
      finite_cycle_failure_witness_def finite_cycle_failure_path_def)
  have certificate_eq:
      "Cycle_Certificate x xs = Cycle_Certificate y ys"
    using assms result_expanded by simp
  have x_eq: "x = y"
    using certificate_eq by simp
  have xs_eq: "xs = ys"
    using certificate_eq by simp
  have path_at_xs: "finite_cycle_path_at M x = Some xs"
    using path_at x_eq xs_eq by simp
  show ?thesis
    using finite_cycle_path_at_length_le[OF path_at_xs] .
qed

section \<open>The Finite Foundation Profile\<close>

type_synonym finite_foundation_profile =
  "bool \<times> bool \<times> bool \<times> bool \<times> bool"

definition finite_foundation_profile ::
  "finite_dependency_model \<Rightarrow> finite_foundation_profile"
where
  "finite_foundation_profile M =
     (finite_cycle_check M,
      finite_cycle_check M,
      finite_cycle_check M,
      finite_foundation_check M,
      finite_foundation_check M)"

theorem finite_foundation_profile_correct:
  "finite_foundation_profile M =
   (acyclic_on (finite_model_carrier M) (finite_model_immediate M),
    well_founded_on (finite_model_carrier M) (finite_model_immediate M),
    chain_terminating_on (finite_model_carrier M)
      (finite_model_immediate M),
    local_foundation_on (finite_model_carrier M)
      (finite_model_immediate M) (finite_model_carrier M),
    global_foundation_on (finite_model_carrier M)
      (finite_model_immediate M) (finite_model_carrier M))"
proof -
  have finite_carrier:
      "finite (finite_model_carrier M)"
    by (simp add: finite_model_carrier_def)
  have cycle:
      "finite_cycle_check M =
        acyclic_on (finite_model_carrier M) (finite_model_immediate M)"
    using finite_cycle_check_iff by blast
  have wf_acyclic:
      "well_founded_on (finite_model_carrier M)
        (finite_model_immediate M) =
        acyclic_on (finite_model_carrier M)
          (finite_model_immediate M)"
    using finite_well_founded_iff_acyclic_on[OF finite_carrier]
    by blast
  have wf_chain:
      "well_founded_on (finite_model_carrier M)
        (finite_model_immediate M) =
        chain_terminating_on (finite_model_carrier M)
          (finite_model_immediate M)"
    using well_founded_iff_chain_terminating by blast
  have local_global:
      "local_foundation_on (finite_model_carrier M)
        (finite_model_immediate M) (finite_model_carrier M) =
        global_foundation_on (finite_model_carrier M)
          (finite_model_immediate M) (finite_model_carrier M)"
    using local_foundation_iff_global_foundation[OF subset_refl] by blast
  have local_check:
      "finite_foundation_check M =
        local_foundation_on (finite_model_carrier M)
          (finite_model_immediate M) (finite_model_carrier M)"
    using finite_foundation_check_iff by blast
  show ?thesis
    unfolding finite_foundation_profile_def
    using cycle wf_acyclic wf_chain local_global local_check
    by simp
qed

value "finite_cycle_result finite_chain_model"
value "finite_cycle_result finite_cycle_model"
value "finite_foundation_profile finite_chain_model"
value "finite_foundation_profile finite_cycle_model"

end
