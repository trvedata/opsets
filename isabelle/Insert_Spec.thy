theory Insert_Spec
  imports OpSet
begin

fun insert_spec :: "'oid list \<Rightarrow> ('oid \<times> 'oid option) \<Rightarrow> 'oid list" where
  "insert_spec xs     (oid, None)     = oid#xs" |
  "insert_spec []     (oid, _)        = []" |
  "insert_spec (x#xs) (oid, Some ref) =
     (if x = ref then x # oid # xs
                 else x # (insert_spec xs (oid, Some ref)))"

fun make_insert :: "'oid list \<Rightarrow> 'oid \<Rightarrow> nat \<Rightarrow> ('oid \<times> 'oid option)" where
  "make_insert xs oid 0       = (oid, None)" |
  "make_insert [] oid m       = (oid, None)" |
  "make_insert xs oid (Suc m) = (oid, Some (xs ! min (length xs - 1) m))"

definition interp_list :: "('oid \<times> 'oid option) list \<Rightarrow> 'oid list" where
  "interp_list ops \<equiv> foldl insert_spec [] ops"

locale insert_opset = opset opset set_option
  for opset :: "('oid::{linorder} \<times> 'oid option) set"

definition insert_ops :: "('oid::{linorder} \<times> 'oid option) list \<Rightarrow> bool" where
  "insert_ops list \<equiv> spec_ops set_option list"

lemma insert_ops_NilI [intro!]:
  shows "insert_ops []"
by (auto simp add: insert_ops_def spec_ops_def)

lemma insert_ops_rem_last [dest]:
  assumes "insert_ops (xs @ [x])"
  shows "insert_ops xs"
using assms insert_ops_def spec_ops_rem_last by blast

lemma insert_ops_appendD:
  assumes "insert_ops (xs @ ys)"
  shows "insert_ops xs"
using assms by (induction ys rule: List.rev_induct,
  auto, metis insert_ops_rem_last append_assoc)

lemma insert_ops_rem_prefix:
  assumes "insert_ops (pre @ suf)"
  shows "insert_ops suf"
using assms proof(induction pre)
  case Nil
  then show "insert_ops ([] @ suf) \<Longrightarrow> insert_ops suf"
    by auto
next
  case (Cons a pre)
  have "sorted (map fst suf)"
    using assms by (simp add: insert_ops_def sorted_append spec_ops_def)
  moreover have "distinct (map fst suf)"
    using assms by (simp add: insert_ops_def spec_ops_def)
  ultimately show "insert_ops ((a # pre) @ suf) \<Longrightarrow> insert_ops suf"
    by (simp add: insert_ops_def spec_ops_def)
qed

lemma insert_ops_remove1:
  assumes "insert_ops xs"
  shows "insert_ops (remove1 x xs)"
using assms insert_ops_def spec_ops_remove1 by blast

lemma last_op_greatest:
  assumes "insert_ops (op_list @ [(oid, oper)])"
    and "x \<in> set (map fst op_list)"
  shows "x < oid"
using assms spec_ops_id_inc insert_ops_def by metis

lemma insert_ops_ref_older:
  assumes "insert_ops (pre @ [(oid, Some ref)] @ suf)"
  shows "ref < oid"
using assms by (auto simp add: insert_ops_def spec_ops_def)

lemma insert_ops_memb_ref_older:
  assumes "insert_ops op_list"
    and "(oid, Some ref) \<in> set op_list"
  shows "ref < oid"
using assms insert_ops_ref_older split_list_first by fastforce


subsection \<open>Properties of the insert_spec function\<close>

lemma insert_spec_none [simp]:
  shows "set (insert_spec xs (oid, None)) = set xs \<union> {oid}"
by (induction xs, auto simp add: insert_commute sup_commute)

lemma insert_spec_set [simp]:
  assumes "ref \<in> set xs"
  shows "set (insert_spec xs (oid, Some ref)) = set xs \<union> {oid}"
using assms proof(induction xs)
  assume "ref \<in> set []"
  thus "set (insert_spec [] (oid, Some ref)) = set [] \<union> {oid}"
    by auto
next
  fix a xs
  assume "ref \<in> set xs \<Longrightarrow> set (insert_spec xs (oid, Some ref)) = set xs \<union> {oid}"
    and "ref \<in> set (a#xs)"
  thus "set (insert_spec (a#xs) (oid, Some ref)) = set (a#xs) \<union> {oid}"
    by(cases "a = ref", auto simp add: insert_commute sup_commute)
qed

lemma insert_spec_nonex [simp]:
  assumes "ref \<notin> set xs"
  shows "insert_spec xs (oid, Some ref) = xs"
using assms proof(induction xs)
  show "insert_spec [] (oid, Some ref) = []"
    by simp
next
  fix a xs
  assume "ref \<notin> set xs \<Longrightarrow> insert_spec xs (oid, Some ref) = xs"
    and "ref \<notin> set (a#xs)"
  thus "insert_spec (a#xs) (oid, Some ref) = a#xs"
    by(cases "a = ref", auto simp add: insert_commute sup_commute)
qed

lemma list_greater_non_memb:
  fixes oid :: "'oid::{linorder}"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < oid"
    and "oid \<in> set xs"
  shows "False"
using assms by blast  

lemma inserted_item_ident:
  assumes "a \<in> set (insert_spec xs (e, i))"
    and "a \<notin> set xs"
  shows "a = e"
using assms proof(induction xs)
  case Nil
  then show "a = e" by (cases i, auto)
next
  case (Cons x xs)
  then show "a = e"
  proof(cases i)
    case None
    then show "a = e" using assms by auto
  next
    case (Some ref)
    then show "a = e" using Cons by (case_tac "x = ref", auto)
  qed
qed

lemma insert_spec_distinct [intro]:
  fixes oid :: "'oid::{linorder}"
  assumes 1: "distinct xs"
    and 2: "\<And>x. x \<in> set xs \<Longrightarrow> x < oid"
    and 3: "ref = Some r \<longrightarrow> r < oid"
  shows "distinct (insert_spec xs (oid, ref))"
using 1 2 proof(induction xs)
  show "distinct (insert_spec [] (oid, ref))"
    by(cases ref, auto)
next
  fix a xs
  assume IH: "distinct xs \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> x < oid) \<Longrightarrow> distinct (insert_spec xs (oid, ref))"
    and D: "distinct (a#xs)"
    and L: "\<And>x. x \<in> set (a#xs) \<Longrightarrow> x < oid"
  show "distinct (insert_spec (a#xs) (oid, ref))"
  proof(cases "ref")
    assume "ref = None"
    thus "distinct (insert_spec (a#xs) (oid, ref))"
      using D L by auto
  next
    fix id
    assume S: "ref = Some id"
    {
      assume EQ: "a = id"
      hence "id \<noteq> oid"
        using D L by auto
      moreover have "id \<notin> set xs"
        using D EQ by auto
      moreover have "oid \<notin> set xs"
        using L by auto
      ultimately have "id \<noteq> oid \<and> id \<notin> set xs \<and> oid \<notin> set xs \<and> distinct xs"
        using D by auto
    }
    note T = this
    {
      assume NEQ: "a \<noteq> id"
      have 0: "a \<notin> set (insert_spec xs (oid, Some id))"
        using D L by(metis distinct.simps(2) insert_spec.simps(1) insert_spec_none insert_spec_nonex
            insert_spec_set insert_iff list.set(2) not_less_iff_gr_or_eq)
      have 1: "distinct xs"
        using D by auto
      have "\<And>x. x \<in> set xs \<Longrightarrow> x < oid"
        using L by auto
      hence "distinct (insert_spec xs (oid, Some id))"
        using S IH[OF 1] by blast
      hence "a \<notin> set (insert_spec xs (oid, Some id)) \<and> distinct (insert_spec xs (oid, Some id))"
        using 0 by auto
    }
    from this S T show "distinct (insert_spec (a # xs) (oid, ref))"
      by clarsimp
  qed
qed

lemma insert_after_ref:
  assumes "distinct (xs@ref#ys)"
  shows "insert_spec (xs@ref#ys) (oid, Some ref) = xs@ref#oid#ys"
using assms by (induction xs, auto)

lemma insert_somewhere:
  assumes "ref = None \<or> (ref = Some r \<and> r \<in> set list)"
  shows "\<exists>xs ys. list = xs@ys \<and> insert_spec list (oid, ref) = xs@oid#ys"
using assms proof(induction list)
  assume "ref = None \<or> ref = Some r \<and> r \<in> set []"
  thus "\<exists>xs ys. [] = xs @ ys \<and> insert_spec [] (oid, ref) = xs @ oid # ys"
  proof
    assume "ref = None"
    thus "\<exists>xs ys. [] = xs@ys \<and> insert_spec [] (oid, ref) = xs@oid#ys"
      by auto
  next
    assume "ref = Some r \<and> r \<in> set []"
    thus "\<exists>xs ys. [] = xs@ys \<and> insert_spec [] (oid, ref) = xs@oid#ys"
      by auto
  qed
next
  fix a list
  assume 1: "ref = None \<or> ref = Some r \<and> r \<in> set (a#list)"
    and IH: "ref = None \<or> ref = Some r \<and> r \<in> set list \<Longrightarrow> \<exists>xs ys. list = xs@ys \<and> insert_spec list (oid, ref) = xs@oid#ys"
  show "\<exists>xs ys. a#list = xs@ys \<and> insert_spec (a#list) (oid, ref) = xs@oid#ys"
  proof(rule disjE[OF 1])
    assume "ref = None"
    thus "\<exists>xs ys. a # list = xs @ ys \<and> insert_spec (a # list) (oid, ref) = xs @ oid # ys"
      by force
  next
    assume "ref = Some r \<and> r \<in> set (a # list)"
    hence 2: "r = a \<or> r \<in> set list" and 3: "ref = Some r"
      by auto
    show "\<exists>xs ys. a # list = xs @ ys \<and> insert_spec (a # list) (oid, ref) = xs @ oid # ys"
    proof(rule disjE[OF 2])
      assume "r = a"
      thus "\<exists>xs ys. a # list = xs @ ys \<and> insert_spec (a # list) (oid, ref) = xs @ oid # ys"
        using 3 by(metis append_Cons append_Nil insert_spec.simps(3))
    next
      assume "r \<in> set list"
      from this obtain xs ys where "list = xs@ys \<and> insert_spec list (oid, ref) = xs@oid#ys"
        using IH 3 by auto
      thus "\<exists>xs ys. a # list = xs @ ys \<and> insert_spec (a # list) (oid, ref) = xs @ oid # ys"
        using 3 by clarsimp (metis append_Cons append_Nil)
    qed
  qed
qed

lemma insert_first_part:
  assumes "ref = None \<or> (ref = Some r \<and> r \<in> set xs)"
  shows "insert_spec (xs @ ys) (oid, ref) = (insert_spec xs (oid, ref)) @ ys"
using assms proof(induction ys rule: rev_induct)
  assume "ref = None \<or> ref = Some r \<and> r \<in> set xs"
  thus "insert_spec (xs @ []) (oid, ref) = insert_spec xs (oid, ref) @ []"
    by auto
next
  fix x xsa
  assume IH: "ref = None \<or> ref = Some r \<and> r \<in> set xs \<Longrightarrow> insert_spec (xs @ xsa) (oid, ref) = insert_spec xs (oid, ref) @ xsa"
    and "ref = None \<or> ref = Some r \<and> r \<in> set xs"
  thus "insert_spec (xs @ xsa @ [x]) (oid, ref) = insert_spec xs (oid, ref) @ xsa @ [x]"
  proof(induction xs)
    assume "ref = None \<or> ref = Some r \<and> r \<in> set []"
    thus "insert_spec ([] @ xsa @ [x]) (oid, ref) = insert_spec [] (oid, ref) @ xsa @ [x]"
      by auto
  next
    fix a xs
    assume 1: "ref = None \<or> ref = Some r \<and> r \<in> set (a # xs)"
      and 2: "((ref = None \<or> ref = Some r \<and> r \<in> set xs \<Longrightarrow> insert_spec (xs @ xsa) (oid, ref) = insert_spec xs (oid, ref) @ xsa) \<Longrightarrow>
             ref = None \<or> ref = Some r \<and> r \<in> set xs \<Longrightarrow> insert_spec (xs @ xsa @ [x]) (oid, ref) = insert_spec xs (oid, ref) @ xsa @ [x])"
      and 3: "(ref = None \<or> ref = Some r \<and> r \<in> set (a # xs) \<Longrightarrow> insert_spec ((a # xs) @ xsa) (oid, ref) = insert_spec (a # xs) (oid, ref) @ xsa)"
    show "insert_spec ((a # xs) @ xsa @ [x]) (oid, ref) = insert_spec (a # xs) (oid, ref) @ xsa @ [x]"
    proof(rule disjE[OF 1])
      assume "ref = None"
      thus "insert_spec ((a # xs) @ xsa @ [x]) (oid, ref) = insert_spec (a # xs) (oid, ref) @ xsa @ [x]"
        by auto
    next
      assume "ref = Some r \<and> r \<in> set (a # xs)"
      thus "insert_spec ((a # xs) @ xsa @ [x]) (oid, ref) = insert_spec (a # xs) (oid, ref) @ xsa @ [x]"
        using 2 3 by auto
    qed
  qed
qed

lemma insert_second_part:
  assumes "ref = Some r"
    and "r \<notin> set xs"
    and "r \<in> set ys"
  shows "insert_spec (xs @ ys) (oid, ref) = xs @ (insert_spec ys (oid, ref))"
using assms proof(induction xs)
  assume "ref = Some r"
  thus "insert_spec ([] @ ys) (oid, ref) = [] @ insert_spec ys (oid, ref)"
    by auto
next
  fix a xs
  assume "ref = Some r" and "r \<notin> set (a # xs)" and "r \<in> set ys"
    and "ref = Some r \<Longrightarrow> r \<notin> set xs \<Longrightarrow> r \<in> set ys \<Longrightarrow> insert_spec (xs @ ys) (oid, ref) = xs @ insert_spec ys (oid, ref)"
  thus "insert_spec ((a # xs) @ ys) (oid, ref) = (a # xs) @ insert_spec ys (oid, ref)"
    by auto
qed


subsection \<open>Properties of the interp_list function\<close>

lemma interp_list_empty [simp]:
  shows "interp_list [] = []"
by (simp add: interp_list_def)

lemma interp_list_tail_unfold:
  shows "interp_list (xs @ [x]) = insert_spec (interp_list xs) x"
by (clarsimp simp add: interp_list_def)

lemma interp_list_subset [simp]:
  shows "set (interp_list op_list) \<subseteq> set (map fst op_list)"
proof(induction op_list rule: List.rev_induct)
  case Nil
  then show "set (interp_list []) \<subseteq> set (map fst [])"
    by (simp add: interp_list_def)
next
  case (snoc x xs)
  hence IH: "set (interp_list xs) \<subseteq> set (map fst xs)"
    using interp_list_def by blast
  obtain oid ref where x_pair: "x = (oid, ref)"
    by fastforce
  hence spec: "interp_list (xs @ [x]) = insert_spec (interp_list xs) (oid, ref)"
    by (simp add: interp_list_def)
  then show "set (interp_list (xs @ [x])) \<subseteq> set (map fst (xs @ [x]))"
  proof(cases ref)
    case None
    then show "set (interp_list (xs @ [x])) \<subseteq> set (map fst (xs @ [x]))"
      using IH spec x_pair by auto
  next
    case (Some a)
    then show "set (interp_list (xs @ [x])) \<subseteq> set (map fst (xs @ [x]))"
      using IH spec x_pair by (cases "a \<in> set (interp_list xs)", auto)
  qed
qed

lemma interp_list_distinct:
  assumes "insert_ops op_list"
  shows "distinct (interp_list op_list)"
using assms proof(induction op_list rule: rev_induct)
  case Nil
  then show "distinct (interp_list [])"
    by (simp add: interp_list_def)
next
  case (snoc x xs)
  hence IH: "distinct (interp_list xs)" by blast
  obtain oid ref where x_pair: "x = (oid, ref)" by force
  hence "\<forall>x \<in> set (map fst xs). x < oid"
    using last_op_greatest snoc.prems by blast
  hence "\<forall>x \<in> set (interp_list xs). x < oid"
    using interp_list_subset by fastforce
  hence "distinct (insert_spec (interp_list xs) (oid, ref))"
    using IH insert_spec_distinct insert_spec_nonex by metis
  then show "distinct (interp_list (xs @ [x]))"
    by (simp add: x_pair interp_list_tail_unfold)
qed

lemma distinct_list_split:
  assumes "distinct xs"
    and "xs = xa @ x # ya"
    and "xs = xb @ x # yb"
  shows "xa = xb \<and> ya = yb"
using assms proof(induction xs arbitrary: xa xb x)
  fix xa xb x
  assume "[] = xa @ x # ya"
  thus "xa = xb \<and> ya = yb"
    by auto
next
  fix a xs xa xb x
  assume IH: "\<And>xa xb x. distinct xs \<Longrightarrow> xs = xa @ x # ya \<Longrightarrow> xs = xb @ x # yb \<Longrightarrow> xa = xb \<and> ya = yb"
    and "distinct (a # xs)" and "a # xs = xa @ x # ya" and "a # xs = xb @ x # yb"
  thus "xa = xb \<and> ya = yb"
    by(case_tac xa; case_tac xb) auto
qed


subsection \<open>The list_order predicate\<close>

definition list_order :: "('oid::{linorder} \<times> 'oid option) list \<Rightarrow> 'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "list_order ops x y \<equiv> \<exists>xs ys zs. interp_list ops = xs@[x]@ys@[y]@zs"

lemma list_orderI:
  assumes "interp_list ops = xs@[x]@ys@[y]@zs"
  shows "list_order ops x y"
using assms by (auto simp add: list_order_def)

lemma list_orderE:
  assumes "list_order ops x y"
  shows "\<exists>xs ys zs. interp_list ops = xs@[x]@ys@[y]@zs"
using assms by (auto simp add: list_order_def)

lemma list_order_memb1:
  assumes "list_order ops x y"
  shows "x \<in> set (interp_list ops)"
using assms by (auto simp add: list_order_def)

lemma list_order_memb2:
  assumes "list_order ops x y"
  shows "y \<in> set (interp_list ops)"
using assms by (auto simp add: list_order_def)

lemma list_order_trans:
  assumes "insert_ops op_list"
    and "list_order op_list x y"
    and "list_order op_list y z"
  shows "list_order op_list x z"
proof -
  obtain xxs xys xzs where 1: "interp_list op_list = (xxs@[x]@xys)@(y#xzs)"
    using assms by (auto simp add: list_order_def interp_list_def)
  obtain yxs yys yzs where 2: "interp_list op_list = yxs@y#(yys@[z]@yzs)"
    using assms by (auto simp add: list_order_def interp_list_def)
  have 3: "distinct (interp_list op_list)"
    using assms interp_list_distinct by blast
  hence "xzs = yys@[z]@yzs"
    using distinct_list_split[OF 3, OF 2, OF 1] by auto
  hence "interp_list op_list = xxs@[x]@xys@[y]@yys@[z]@yzs"
    using 1 2 3 by clarsimp
  thus "list_order op_list x z"
    using assms by (metis append.assoc list_orderI)
qed

lemma insert_preserves_order:
  assumes "insert_ops ops" and "insert_ops rest"
    and "rest = before @ after"
    and "ops  = before @ (oid, ref) # after"
  shows "\<exists>xs ys zs. interp_list rest = xs @ zs \<and> interp_list ops = xs @ ys @ zs"
using assms proof(induction after arbitrary: rest ops rule: List.rev_induct)
  case Nil
  then have 1: "interp_list ops = insert_spec (interp_list before) (oid, ref)"
    by (simp add: interp_list_tail_unfold)
  then show "\<exists>xs ys zs. interp_list rest = xs @ zs \<and> interp_list ops = xs @ ys @ zs"
  proof(cases ref)
    case None
    hence "interp_list rest = [] @ (interp_list before) \<and>
           interp_list ops = [] @ [oid] @ (interp_list before)"
      using 1 Nil.prems(3) by simp
    then show ?thesis by blast
  next
    case (Some a)
    then show ?thesis
    proof(cases "a \<in> set (interp_list before)")
      case True
      then obtain xs ys where "interp_list before = xs @ ys \<and>
          insert_spec (interp_list before) (oid, ref) = xs @ oid # ys"
        using insert_somewhere Some by metis
      hence "interp_list rest = xs @ ys \<and> interp_list ops = xs @ [oid] @ ys"
        using 1 Nil.prems(3) by auto
      then show ?thesis by blast
    next
      case False
      hence "interp_list ops = (interp_list rest) @ [] @ []"
        using insert_spec_nonex 1 Nil.prems(3) Some by simp
      then show ?thesis by blast
    qed
  qed
next
  case (snoc oper op_list)
  then have "insert_ops ((before @ (oid, ref) # op_list) @ [oper])"
    and "insert_ops ((before @ op_list) @ [oper])"
    by auto
  then have ops1: "insert_ops (before @ op_list)"
    and ops2: "insert_ops (before @ (oid, ref) # op_list)"
    using insert_ops_appendD by blast+
  then obtain xs ys zs where IH1: "interp_list (before @ op_list) = xs @ zs"
    and IH2: "interp_list (before @ (oid, ref) # op_list) = xs @ ys @ zs"
    using snoc.IH by blast
  obtain i2 r2 where "oper = (i2, r2)" by force
  then show "\<exists>xs ys zs. interp_list rest = xs @ zs \<and> interp_list ops = xs @ ys @ zs"
  proof(cases r2)
    case None
    hence "interp_list (before @ op_list @ [oper]) = (i2 # xs) @ zs"
      by (metis IH1 \<open>oper = (i2, r2)\<close> append.assoc append_Cons insert_spec.simps(1)
          interp_list_tail_unfold)
    moreover have "interp_list (before @ (oid, ref) # op_list @ [oper]) = (i2 # xs) @ ys @ zs"
      by (metis IH2 None \<open>oper = (i2, r2)\<close> append.assoc append_Cons insert_spec.simps(1)
          interp_list_tail_unfold)
    ultimately show ?thesis
      using snoc.prems(3) snoc.prems(4) by blast
  next
    case (Some r)
    then have 1: "interp_list (before @ (oid, ref) # op_list @ [(i2, r2)]) =
                  insert_spec (xs @ ys @ zs) (i2, Some r)"
      by (metis IH2 append.assoc append_Cons interp_list_tail_unfold)
    have 2: "interp_list (before @ op_list @ [(i2, r2)]) = insert_spec (xs @ zs) (i2, Some r)"
      by (metis IH1 append.assoc interp_list_tail_unfold Some)
    consider (r_xs) "r \<in> set xs" | (r_ys) "r \<in> set ys" | (r_zs) "r \<in> set zs" |
             (r_nonex) "r \<notin> set (xs @ ys @ zs)"
      by auto
    then show "\<exists>xs ys zs. interp_list rest = xs @ zs \<and> interp_list ops = xs @ ys @ zs"
    proof(cases)
      case r_xs
      from this have "insert_spec (xs @ ys @ zs) (i2, Some r) =
                      (insert_spec xs (i2, Some r)) @ ys @ zs"
        by (meson insert_first_part)
      moreover have "insert_spec (xs @ zs) (i2, Some r) = (insert_spec xs (i2, Some r)) @ zs"
        by (meson r_xs insert_first_part)
      ultimately show ?thesis
        using 1 2 \<open>oper = (i2, r2)\<close> snoc.prems by auto
    next
      case r_ys
      hence "r \<notin> set xs" and "r \<notin> set zs"
        using IH2 ops2 interp_list_distinct by force+
      moreover from this have "insert_spec (xs @ ys @ zs) (i2, Some r) =
                               xs @ (insert_spec ys (i2, Some r)) @ zs"
        using insert_first_part insert_second_part insert_spec_nonex
        by (metis Some UnE r_ys set_append)
      moreover have "insert_spec (xs @ zs) (i2, Some r) = xs @ zs"
        by (simp add: Some calculation(1) calculation(2))
      ultimately show ?thesis
        using 1 2 \<open>oper = (i2, r2)\<close> snoc.prems by auto
    next
      case r_zs
      hence "r \<notin> set xs" and "r \<notin> set ys"
        using IH2 ops2 interp_list_distinct by force+
      moreover from this have "insert_spec (xs @ ys @ zs) (i2, Some r) =
                               xs @ ys @ (insert_spec zs (i2, Some r))"
        by (metis Some UnE insert_second_part insert_spec_nonex set_append)
      moreover have "insert_spec (xs @ zs) (i2, Some r) = xs @ (insert_spec zs (i2, Some r))"
        by (simp add: r_zs calculation(1) insert_second_part)
      ultimately show ?thesis
        using 1 2 \<open>oper = (i2, r2)\<close> snoc.prems by auto
    next
      case r_nonex
      then have "insert_spec (xs @ ys @ zs) (i2, Some r) = xs @ ys @ zs"
        by simp
      moreover have "insert_spec (xs @ zs) (i2, Some r) = xs @ zs"
        using r_nonex by simp
      ultimately show ?thesis
        using 1 2 \<open>oper = (i2, r2)\<close> snoc.prems by auto
    qed
  qed
qed

lemma distinct_fst:
  assumes "distinct (map fst A)"
  shows "distinct A"
using assms by (induction A) auto

lemma subset_distinct_le:
  assumes "set A \<subseteq> set B" and "distinct A" and "distinct B"
  shows "length A \<le> length B"
using assms proof(induction B arbitrary: A)
  case Nil
  then show "length A \<le> length []" by simp
next
  case (Cons a B)
  then show "length A \<le> length (a # B)"
  proof(cases "a \<in> set A")
    case True
    have "set (remove1 a A) \<subseteq> set B"
      using Cons.prems by auto
    hence "length (remove1 a A) \<le> length B"
      using Cons.IH Cons.prems by auto
    then show "length A \<le> length (a # B)"
      by (simp add: True length_remove1)
  next
    case False
    hence "set A \<subseteq> set B"
      using Cons.prems by auto
    hence "length A \<le> length B"
      using Cons.IH Cons.prems by auto
    then show "length A \<le> length (a # B)"
      by simp
  qed
qed

lemma set_subset_length_eq:
  assumes "set A \<subseteq> set B" and "length B \<le> length A"
    and "distinct A" and "distinct B"
  shows "set A = set B"
proof -
  have "length A \<le> length B"
    using assms by (simp add: subset_distinct_le)
  moreover from this have "card (set A) = card (set B)"
    using assms by (simp add: distinct_card le_antisym)
  ultimately show "set A = set B"
    using assms(1) by (simp add: card_subset_eq)
qed

lemma length_diff_Suc_exists:
  assumes "length xs - length ys = Suc m"
    and "set ys \<subseteq> set xs"
    and "distinct ys" and "distinct xs"
  shows "\<exists>e. e \<in> set xs \<and> e \<notin> set ys"
using assms proof(induction xs arbitrary: ys)
  case Nil
  then show "\<exists>e. e \<in> set [] \<and> e \<notin> set ys"
    by simp
next
  case (Cons a xs)
  then show "\<exists>e. e \<in> set (a # xs) \<and> e \<notin> set ys"
  proof(cases "a \<in> set ys")
    case True
    have IH: "\<exists>e. e \<in> set xs \<and> e \<notin> set (remove1 a ys)"
    proof -
      have "length xs - length (remove1 a ys) = Suc m"
        by (metis Cons.prems(1) One_nat_def Suc_pred True diff_Suc_Suc length_Cons
            length_pos_if_in_set length_remove1)
      moreover have "set (remove1 a ys) \<subseteq> set xs"
        using Cons.prems by auto
      ultimately show ?thesis
        by (meson Cons.IH Cons.prems distinct.simps(2) distinct_remove1)
    qed
    moreover have "set ys - {a} \<subseteq> set xs"
      using Cons.prems(2) by auto
    ultimately show "\<exists>e. e \<in> set (a # xs) \<and> e \<notin> set ys"
      by (metis Cons.prems(4) distinct.simps(2) in_set_remove1 set_subset_Cons subsetCE)
  next
    case False
    then show "\<exists>e. e \<in> set (a # xs) \<and> e \<notin> set ys"
      by auto
  qed
qed

lemma app_length_lt_exists:
  assumes "xsa @ zsa = xs @ ys"
    and "length xsa \<le> length xs"
  shows "xsa @ (drop (length xsa) xs) = xs"
using assms by (induction xsa arbitrary: xs zsa ys, simp,
                metis append_eq_append_conv_if append_take_drop_id)

lemma list_order_monotonic:
  assumes "insert_ops A" and "insert_ops B"
    and "set A \<subseteq> set B"
    and "list_order A x y"
  shows "list_order B x y"
using assms proof(induction rule: measure_induct_rule[where f="\<lambda>x. (length x - length A)"])
  case (less xa)
  have "distinct (map fst A)" and "distinct (map fst xa)" and
    "sorted (map fst A)" and "sorted (map fst xa)"
    using less.prems by (auto simp add: insert_ops_def spec_ops_def)
  hence "distinct A" and "distinct xa"
    by (auto simp add: distinct_fst)
  then show "list_order xa x y"
  proof(cases "length xa - length A")
    case 0
    hence "set A = set xa"
      using set_subset_length_eq less.prems(3) \<open>distinct A\<close> \<open>distinct xa\<close> diff_is_0_eq by blast
    hence "A = xa"
      using \<open>distinct (map fst A)\<close> \<open>distinct (map fst xa)\<close>
        \<open>sorted (map fst A)\<close> \<open>sorted (map fst xa)\<close> map_sorted_distinct_set_unique
      by (metis distinct_map less.prems(3) subset_Un_eq)
    then show "list_order xa x y" 
      using less.prems(4) by blast
  next
    case (Suc nat)
    then obtain e where "e \<in> set xa" and "e \<notin> set A"
      using length_diff_Suc_exists \<open>distinct A\<close> \<open>distinct xa\<close> less.prems(3) by blast
    hence IH: "list_order (remove1 e xa) x y"
    proof -
      have "length (remove1 e xa) - length A < Suc nat"
        using diff_Suc_1 diff_commute length_remove1 less_Suc_eq Suc \<open>e \<in> set xa\<close> by metis
      moreover have "insert_ops (remove1 e xa)"
        by (simp add: insert_ops_remove1 less.prems(2))
      moreover have "set A \<subseteq> set (remove1 e xa)"
        by (metis (no_types, lifting) \<open>e \<notin> set A\<close> in_set_remove1 less.prems(3) set_rev_mp subsetI)
      ultimately show ?thesis
        by (simp add: Suc less.IH less.prems(1) less.prems(4))
    qed
    then obtain xs ys zs where "interp_list (remove1 e xa) = xs @ x # ys @ y # zs"
      using list_order_def by fastforce
    moreover obtain oid ref where e_pair: "e = (oid, ref)"
      by fastforce
    moreover obtain ps ss where xa_split: "xa = ps @ [e] @ ss" and "e \<notin> set ps"
      using split_list_first \<open>e \<in> set xa\<close> by fastforce
    hence "remove1 e (ps @ e # ss) = ps @ ss"
      by (simp add: remove1_append)
    moreover from this have "insert_ops (ps @ ss)" and "insert_ops (ps @ e # ss)"
      using xa_split less.prems(2) by (metis append_Cons append_Nil insert_ops_remove1, auto)
    then obtain xsa ysa zsa where "interp_list (ps @ ss) = xsa @ zsa"
      and interp_xa: "interp_list (ps @ (oid, ref) # ss) = xsa @ ysa @ zsa"
      using insert_preserves_order e_pair by metis
    moreover have xsa_zsa: "xsa @ zsa = xs @ x # ys @ y # zs"
      using interp_list_def remove1_append calculation xa_split by auto
    then show "list_order xa x y"
    proof(cases "length xsa \<le> length xs")
      case True
      then obtain ts where "xsa@ts = xs"
        using app_length_lt_exists xsa_zsa by blast
      hence "interp_list xa = (xsa @ ysa @ ts) @ [x] @ ys @ [y] @ zs"
        using calculation xa_split by auto
      then show "list_order xa x y"
        using list_order_def by blast
    next
      case False
      then show "list_order xa x y"
      proof(cases "length xsa \<le> length (xs @ x # ys)")
        case True
        have xsa_zsa1: "xsa @ zsa = (xs @ x # ys) @ (y # zs)"
          by (simp add: xsa_zsa)
        then obtain us where "xsa @ us = xs @ x # ys"
          using app_length_lt_exists True by blast
        moreover from this have "xs @ x # (drop (Suc (length xs)) xsa) = xsa"
          using append_eq_append_conv_if id_take_nth_drop linorder_not_less
            nth_append nth_append_length False by metis
        moreover have "us @ y # zs = zsa"
          by (metis True xsa_zsa1 append_eq_append_conv_if append_eq_conv_conj calculation(1))
        ultimately have "interp_list xa = xs @ [x] @
              ((drop (Suc (length xs)) xsa) @ ysa @ us) @ [y] @ zs"
          by (simp add: e_pair interp_xa xa_split)
        then show "list_order xa x y"
          using list_order_def by blast
      next
        case False
        hence "length (xs @ x # ys) < length xsa"
          using not_less by blast
        hence "length (xs @ x # ys @ [y]) \<le> length xsa"
          by simp
        moreover have "(xs @ x # ys @ [y]) @ zs = xsa @ zsa"
          by (simp add: xsa_zsa)
        ultimately obtain vs where "(xs @ x # ys @ [y]) @ vs = xsa"
          using app_length_lt_exists by blast
        hence "xsa @ ysa @ zsa = xs @ [x] @ ys @ [y] @ vs @ ysa @ zsa"
          by simp
        hence "interp_list xa = xs @ [x] @ ys @ [y] @ (vs @ ysa @ zsa)"
          using e_pair interp_xa xa_split by auto
        then show "list_order xa x y"
          using list_order_def by blast
      qed
    qed
  qed
qed

lemma list_split_two_elems:
  assumes "distinct xs"
    and "x \<in> set xs" and "y \<in> set xs"
    and "x \<noteq> y"
  shows "\<exists>pre mid suf. xs = pre @ x # mid @ y # suf \<or> xs = pre @ y # mid @ x # suf"
proof -
  obtain as bs where as_bs: "xs = as @ [x] @ bs"
    using assms(2) split_list_first by fastforce
  show ?thesis
  proof(cases "y \<in> set as")
    case True
    then obtain cs ds where "as = cs @ [y] @ ds"
      using assms(3) split_list_first by fastforce
    then show ?thesis
      by (auto simp add: as_bs)
  next
    case False
    then have "y \<in> set bs"
      using as_bs assms(3) assms(4) by auto
    then obtain cs ds where "bs = cs @ [y] @ ds"
      using assms(3) split_list_first by fastforce
    then show ?thesis
      by (auto simp add: as_bs)
  qed
qed

lemma insert_spec_nth_oid:
  assumes "distinct xs"
       and "n < length xs"
     shows "insert_spec xs (oid, Some (xs ! n)) ! Suc n = oid"
using assms proof(induction xs arbitrary: n)
  case Nil
  then show "insert_spec [] (oid, Some ([] ! n)) ! Suc n = oid"
    by simp
next
  case (Cons a xs)
  have "distinct (a # xs)"
    using Cons.prems(1) by auto
  then show "insert_spec (a # xs) (oid, Some ((a # xs) ! n)) ! Suc n = oid"
  proof(cases "a = (a # xs) ! n")
    case True
    then have "n = 0"
      using \<open>distinct (a # xs)\<close> Cons.prems(2) gr_implies_not_zero by force
    then show "insert_spec (a # xs) (oid, Some ((a # xs) ! n)) ! Suc n = oid"
      by auto
  next
    case False
    then have "n > 0"
      using \<open>distinct (a # xs)\<close> Cons.prems(2) gr_implies_not_zero by force
    then obtain m where "n = Suc m"
      using Suc_pred' by blast
    then show "insert_spec (a # xs) (oid, Some ((a # xs) ! n)) ! Suc n = oid"
      using Cons.IH Cons.prems by auto
  qed
qed

lemma correct_position_insert:
  assumes "insert_ops (xs @ [make_insert ys oid m])"
    and "interp_list xs = ys"
  shows "interp_list (xs @ [make_insert ys oid m]) ! min (length ys) m = oid"
proof(cases "m = 0 \<or> ys = []")
  case True
  then have "make_insert ys oid m = (oid, None)" and "min (length ys) m = 0"
    by (cases m, auto)
  then show ?thesis
    by (simp add: interp_list_tail_unfold)
next
  case False
  moreover from this have "m > 0" and "ys \<noteq> []"
    using neq0_conv by blast+
  from this obtain nat where "m = Suc nat"
    using gr0_implies_Suc by blast
  hence "make_insert ys oid m = (oid, Some (ys ! min (length ys - 1) nat))"
    using False by (cases ys, auto)
  hence "interp_list (xs @ [make_insert ys oid m]) =
         insert_spec ys (oid, Some (ys ! min (length ys - 1) nat))"
    by (simp add: assms(2) interp_list_tail_unfold)
  moreover have "min (length ys - 1) nat < length ys"
    by (meson False diff_less length_greater_0_conv min.strict_coboundedI1 zero_less_one)
  ultimately show ?thesis
    using assms insert_spec_nth_oid
    by (metis (no_types, lifting) False Suc_pred' \<open>m = Suc nat\<close> insert_ops_rem_last
        interp_list_distinct length_greater_0_conv min_Suc_Suc)
qed

lemma list_order_transp:
  assumes "insert_ops op_list"
  shows "transp (list_order op_list)"
using assms list_order_trans transpI by metis

lemma list_order_total:
  assumes "insert_ops op_list"
    and "x \<in> set (interp_list op_list)"
    and "y \<in> set (interp_list op_list)"
    and "x \<noteq> y"
  shows "list_order op_list x y \<or> list_order op_list y x"
proof -
  have "distinct (interp_list op_list)"
    using assms(1) by (simp add: interp_list_distinct)
  then obtain pre mid suf
    where "interp_list op_list = pre @ x # mid @ y # suf \<or>
           interp_list op_list = pre @ y # mid @ x # suf"
    using list_split_two_elems assms by metis
  then show "list_order op_list x y \<or> list_order op_list y x"
    by (simp add: list_order_def, blast)
qed

lemma list_order_irrefl:
  assumes 1: "insert_ops op_list"
  shows "\<not> list_order op_list x x"
using assms interp_list_distinct list_orderE by force

lemma interp_list_maybe_grow:
  assumes "insert_ops (xs @ [(oid, ref)])"
  shows "set (interp_list (xs @ [(oid, ref)])) = set (interp_list xs) \<or>
         set (interp_list (xs @ [(oid, ref)])) = (set (interp_list xs) \<union> {oid})"
by (cases ref, simp add: interp_list_tail_unfold,
    metis insert_spec_nonex insert_spec_set interp_list_tail_unfold)

lemma interp_list_maybe_grow2:
  assumes "insert_ops (xs @ [x])"
  shows "set (interp_list (xs @ [x])) = set (interp_list xs) \<or>
         set (interp_list (xs @ [x])) = (set (interp_list xs) \<union> {fst x})"
using assms interp_list_maybe_grow by (cases x, auto)

lemma interp_list_maybe_grow3:
  assumes "insert_ops (xs @ ys)"
  shows "\<exists>A. A \<subseteq> set (map fst ys) \<and> set (interp_list (xs @ ys)) = set (interp_list xs) \<union> A"
using assms proof(induction ys rule: List.rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x ys)
  then have "insert_ops (xs @ ys)"
    by (metis append_assoc insert_ops_rem_last)
  then obtain A where IH: "A \<subseteq> set (map fst ys) \<and>
            set (interp_list (xs @ ys)) = set (interp_list xs) \<union> A"
    using snoc.IH by blast
  then show ?case
  proof(cases "set (interp_list (xs @ ys @ [x])) = set (interp_list (xs @ ys))")
    case True
    moreover have "A \<subseteq> set (map fst (ys @ [x]))"
      using IH by auto
    ultimately show ?thesis
      using IH by auto
  next
    case False
    then have "set (interp_list (xs @ ys @ [x])) = set (interp_list (xs @ ys)) \<union> {fst x}"
      by (metis append_assoc interp_list_maybe_grow2 snoc.prems)
    moreover have "A \<union> {fst x} \<subseteq> set (map fst (ys @ [x]))"
      using IH by auto
    ultimately show ?thesis
      using IH Un_assoc by metis
  qed
qed

lemma interp_list_ref_nonex:
  assumes "insert_ops ops"
    and "ops = xs @ [(oid, Some ref)] @ ys"
    and "ref \<notin> set (interp_list xs)"
  shows "oid \<notin> set (interp_list ops)"
using assms proof(induction ys arbitrary: ops rule: List.rev_induct)
  case Nil
  then have "interp_list ops = insert_spec (interp_list xs) (oid, Some ref)"
    by (simp add: interp_list_tail_unfold)
  moreover have "\<And>i. i \<in> set (map fst xs) \<Longrightarrow> i < oid"
    using Nil.prems last_op_greatest by fastforce
  hence "\<And>i. i \<in> set (interp_list xs) \<Longrightarrow> i < oid"
    by (meson interp_list_subset subsetCE)
  ultimately show "oid \<notin> set (interp_list ops)"
    using assms(3) by auto
next
  case (snoc x ys)
  then have "insert_ops (xs @ (oid, Some ref) # ys)"
    by (metis append.assoc append.simps(1) append_Cons insert_ops_appendD)
  hence IH: "oid \<notin> set (interp_list (xs @ (oid, Some ref) # ys))"
    by (simp add: snoc.IH snoc.prems(3))
  moreover have "distinct (map fst (xs @ (oid, Some ref) # ys @ [x]))"
    using snoc.prems by (metis append_Cons append_self_conv2 insert_ops_def spec_ops_def)
  hence "fst x \<noteq> oid"
    using empty_iff by auto
  moreover have "insert_ops ((xs @ (oid, Some ref) # ys) @ [x])"
    using snoc.prems by auto
  hence "set (interp_list ((xs @ (oid, Some ref) # ys) @ [x])) =
         set (interp_list (xs @ (oid, Some ref) # ys)) \<or> 
         set (interp_list ((xs @ (oid, Some ref) # ys) @ [x])) =
         set (interp_list (xs @ (oid, Some ref) # ys)) \<union> {fst x}"
    using interp_list_maybe_grow2 by blast
  ultimately show "oid \<notin> set (interp_list ops)"
    using snoc.prems(2) by auto
qed

lemma map_fst_append1:
  assumes "\<forall>i \<in> set (map fst xs). P i"
    and "P x"
  shows "\<forall>i \<in> set (map fst (xs @ [(x, y)])). P i"
using assms by (induction xs, auto)

lemma insert_ops_split:
  assumes "insert_ops ops"
    and "(oid, ref) \<in> set ops"
  shows "\<exists>pre suf. ops = pre @ [(oid, ref)] @ suf \<and>
            (\<forall>i \<in> set (map fst pre). i < oid) \<and>
            (\<forall>i \<in> set (map fst suf). oid < i)"
using assms proof(induction ops rule: List.rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  then show ?case
  proof(cases "x = (oid, ref)")
    case True
    moreover from this have "\<forall>i \<in> set (map fst xs). i < oid"
      using last_op_greatest snoc.prems(1) by blast
    ultimately have "xs @ [x] = xs @ [(oid, ref)] @ [] \<and>
            (\<forall>i \<in> set (map fst xs). i < oid) \<and>
            (\<forall>i \<in> set (map fst []). oid < i)"
      by auto
    then show ?thesis by force
  next
    case False
    hence "(oid, ref) \<in> set xs"
      using snoc.prems(2) by auto
    from this obtain pre suf where IH: "xs = pre @ [(oid, ref)] @ suf \<and>
         (\<forall>i \<in> set (map fst pre). i < oid) \<and>
         (\<forall>i \<in> set (map fst suf). oid < i)"
      using snoc.IH snoc.prems(1) by blast
    obtain xi xr where x_pair: "x = (xi, xr)"
      by force
    hence "distinct (map fst (pre @ [(oid, ref)] @ suf @ [(xi, xr)]))"
      by (metis IH append.assoc insert_ops_def spec_ops_def snoc.prems(1))
    hence "xi \<noteq> oid"
      by auto
    have xi_max: "\<forall>x \<in> set (map fst (pre @ [(oid, ref)] @ suf)). x < xi"
      using IH last_op_greatest snoc.prems(1) x_pair by blast
    then show ?thesis
    proof(cases "xi < oid")
      case True
      moreover from this have "\<forall>x \<in> set suf. fst x < oid"
        using xi_max by auto
      hence "suf = []"
        using IH last_in_set by fastforce
      ultimately have "xs @ [x] = (pre @ [(xi, xr)]) @ [] \<and>
              (\<forall>i \<in> set (map fst ((pre @ [(xi, xr)]))). i < oid) \<and>
              (\<forall>i \<in> set (map fst []). oid < i)"
        using dual_order.asym xi_max by auto
      then show ?thesis by (simp add: IH)
    next
      case False
      hence "oid < xi"
        using \<open>xi \<noteq> oid\<close> by auto
      hence "\<forall>i \<in> set (map fst (suf @ [(xi, xr)])). oid < i"
        using IH map_fst_append1 by auto
      hence "xs @ [x] = pre @ [(oid, ref)] @ (suf @ [(xi, xr)]) \<and>
              (\<forall>i \<in> set (map fst pre). i < oid) \<and>
              (\<forall>i \<in> set (map fst (suf @ [(xi, xr)])). oid < i)"
        by (simp add: IH x_pair)
      then show ?thesis by blast
    qed
  qed
qed

lemma insert_ops_split_2:
  assumes "insert_ops ops"
    and "(xid, xr) \<in> set ops"
    and "(yid, yr) \<in> set ops"
    and "xid < yid"
  shows "\<exists>as bs cs. ops = as @ [(xid, xr)] @ bs @ [(yid, yr)] @ cs \<and>
           (\<forall>i \<in> set (map fst as). i < xid) \<and>
           (\<forall>i \<in> set (map fst bs). xid < i \<and> i < yid) \<and>
           (\<forall>i \<in> set (map fst cs). yid < i)"
proof -
  obtain as as1 where x_split: "ops = as @ [(xid, xr)] @ as1 \<and>
      (\<forall>i \<in> set (map fst as). i < xid) \<and> (\<forall>i \<in> set (map fst as1). xid < i)"
    using assms insert_ops_split by blast
  hence "insert_ops ((as @ [(xid, xr)]) @ as1)"
    using assms(1) by auto
  hence "insert_ops as1"
    using assms(1) insert_ops_rem_prefix by blast
  have "(yid, yr) \<in> set as1"
    using x_split assms by auto
  from this obtain bs cs where y_split: "as1 = bs @ [(yid, yr)] @ cs \<and>
      (\<forall>i \<in> set (map fst bs). i < yid) \<and> (\<forall>i \<in> set (map fst cs). yid < i)"
    using assms insert_ops_split \<open>insert_ops as1\<close> by blast
  hence "ops = as @ [(xid, xr)] @ bs @ [(yid, yr)] @ cs"
    using x_split by blast
  moreover have "\<forall>i \<in> set (map fst bs). xid < i \<and> i < yid"
    by (simp add: x_split y_split)
  ultimately show ?thesis
    using x_split y_split by blast
qed

lemma insert_ops_split_3:
  assumes "insert_ops ops"
    and "(xid, xr) \<in> set ops"
    and "(yid, yr) \<in> set ops"
    and "(zid, zr) \<in> set ops"
    and "xid < yid" and "yid < zid"
  shows "\<exists>as bs cs ds. ops = as @ [(xid, xr)] @ bs @ [(yid, yr)] @ cs @ [(zid, zr)] @ ds \<and>
           (\<forall>i \<in> set (map fst as). i < xid) \<and>
           (\<forall>i \<in> set (map fst bs). xid < i \<and> i < yid) \<and>
           (\<forall>i \<in> set (map fst cs). yid < i \<and> i < zid) \<and>
           (\<forall>i \<in> set (map fst ds). zid < i)"
proof -
  obtain as bs cs1 where xy_split: "ops = as @ [(xid, xr)] @ bs @ [(yid, yr)] @ cs1 \<and>
           (\<forall>i \<in> set (map fst as). i < xid) \<and>
           (\<forall>i \<in> set (map fst bs). xid < i \<and> i < yid) \<and>
           (\<forall>i \<in> set (map fst cs1). yid < i)"
    using assms insert_ops_split_2 by blast
  hence "insert_ops ((as @ [(xid, xr)] @ bs @ [(yid, yr)]) @ cs1)"
    using assms(1) by auto
  hence "insert_ops cs1"
    using assms(1) insert_ops_rem_prefix by blast
  have "(zid, zr) \<in> set cs1"
    using assms xy_split by auto
  from this obtain cs ds where z_split: "cs1 = cs @ [(zid, zr)] @ ds \<and>
      (\<forall>i \<in> set (map fst cs). i < zid) \<and> (\<forall>i \<in> set (map fst ds). zid < i)"
    using assms insert_ops_split \<open>insert_ops cs1\<close> by blast
  hence "ops = as @ [(xid, xr)] @ bs @ [(yid, yr)] @ cs @ [(zid, zr)] @ ds"
    using xy_split by blast
  moreover have "\<forall>i \<in> set (map fst cs). yid < i \<and> i < zid"
    by (simp add: xy_split z_split)
  ultimately show ?thesis
    using xy_split z_split by blast
qed

lemma interp_list_last_None:
  shows "oid \<in> set (interp_list (ops @ [(oid, None)]))"
by (simp add: interp_list_tail_unfold)

lemma interp_list_monotonic:
  assumes "insert_ops (pre @ suf)"
    and "oid \<in> set (interp_list pre)"
  shows "oid \<in> set (interp_list (pre @ suf))"
using assms interp_list_maybe_grow3 by auto

lemma insert_ops_sorted_oids:
  assumes "insert_ops (xs @ [(i1, r1)] @ ys @ [(i2, r2)])"
  shows "i1 < i2"
proof -
  have "\<And>i. i \<in> set (map fst (xs @ [(i1, r1)] @ ys)) \<Longrightarrow> i < i2"
    by (metis append.assoc assms last_op_greatest)
  moreover have "i1 \<in> set (map fst (xs @ [(i1, r1)] @ ys))"
    by auto
  ultimately show "i1 < i2"
    by blast
qed

lemma interp_list_append_non_memb:
  assumes "insert_ops (pre @ [(oid, Some ref)] @ suf)"
    and "ref \<notin> set (interp_list pre)"
  shows "ref \<notin> set (interp_list (pre @ [(oid, Some ref)] @ suf))"
using assms proof(induction suf rule: List.rev_induct)
  case Nil
  then show "ref \<notin> set (interp_list (pre @ [(oid, Some ref)] @ []))"
    by (metis append_Nil2 insert_spec_nonex interp_list_tail_unfold)
next
  case (snoc x xs)
  hence IH: "ref \<notin> set (interp_list (pre @ [(oid, Some ref)] @ xs))"
    by (metis append_assoc insert_ops_rem_last)
  moreover have "ref < oid"
    using insert_ops_ref_older snoc.prems(1) by auto
  moreover have "oid < fst x"
    using insert_ops_sorted_oids by (metis prod.collapse snoc.prems(1))
  have "set (interp_list ((pre @ [(oid, Some ref)] @ xs) @ [x])) =
        set (interp_list (pre @ [(oid, Some ref)] @ xs)) \<or>
        set (interp_list ((pre @ [(oid, Some ref)] @ xs) @ [x])) =
        set (interp_list (pre @ [(oid, Some ref)] @ xs)) \<union> {fst x}"
    by (metis (full_types) append.assoc interp_list_maybe_grow2 snoc.prems(1))
  ultimately show "ref \<notin> set (interp_list (pre @ [(oid, Some ref)] @ xs @ [x]))"
    using \<open>oid < fst x\<close> by auto
qed

lemma list_order_append:
  assumes "insert_ops (pre @ suf)"
    and "list_order pre x y"
  shows "list_order (pre @ suf) x y"
by (metis Un_iff assms list_order_monotonic insert_ops_appendD set_append subset_code(1))

lemma list_order_insert_ref:
  assumes "insert_ops (ops @ [(oid, Some ref)])"
    and "ref \<in> set (interp_list ops)"
  shows "list_order (ops @ [(oid, Some ref)]) ref oid"
proof -
  have "interp_list (ops @ [(oid, Some ref)]) = insert_spec (interp_list ops) (oid, Some ref)"
    by (simp add: interp_list_tail_unfold)
  moreover obtain xs ys where "interp_list ops = xs @ [ref] @ ys"
    using assms(2) split_list_first by fastforce
  hence "insert_spec (interp_list ops) (oid, Some ref) = xs @ [ref] @ [] @ [oid] @ ys"
    using assms(1) insert_after_ref interp_list_distinct by fastforce
  ultimately show "list_order (ops @ [(oid, Some ref)]) ref oid"
    using assms(1) list_orderI by metis
qed

lemma list_order_insert_none:
  assumes "insert_ops (ops @ [(oid, None)])"
    and "x \<in> set (interp_list ops)"
  shows "list_order (ops @ [(oid, None)]) oid x"
proof -
  have "interp_list (ops @ [(oid, None)]) = insert_spec (interp_list ops) (oid, None)"
    by (simp add: interp_list_tail_unfold)
  moreover obtain xs ys where "interp_list ops = xs @ [x] @ ys"
    using assms(2) split_list_first by fastforce
  hence "insert_spec (interp_list ops) (oid, None) = [] @ [oid] @ xs @ [x] @ ys"
    by simp
  ultimately show "list_order (ops @ [(oid, None)]) oid x"
    using assms(1) list_orderI by metis
qed

lemma list_order_insert_between:
  assumes "insert_ops (ops @ [(oid, Some ref)])"
    and "list_order ops ref x"
  shows "list_order (ops @ [(oid, Some ref)]) oid x"
proof -
  have "interp_list (ops @ [(oid, Some ref)]) = insert_spec (interp_list ops) (oid, Some ref)"
    by (simp add: interp_list_tail_unfold)
  moreover obtain xs ys zs where "interp_list ops = xs @ [ref] @ ys @ [x] @ zs"
    using assms list_orderE by blast
  moreover have "... = xs @ ref # (ys @ [x] @ zs)"
    by simp
  moreover have "distinct (xs @ ref # (ys @ [x] @ zs))"
    using assms(1) calculation by (metis interp_list_distinct insert_ops_rem_last)
  hence "insert_spec (xs @ ref # (ys @ [x] @ zs)) (oid, Some ref) = xs @ ref # oid # (ys @ [x] @ zs)"
    using assms(1) calculation by (simp add: insert_after_ref)
  moreover have "... = (xs @ [ref]) @ [oid] @ ys @ [x] @ zs"
    by simp
  ultimately show "list_order (ops @ [(oid, Some ref)]) oid x"
    using assms(1) list_orderI by metis
qed

theorem no_interleaving:
  assumes "insert_ops ops"
    and "(xid, ref) \<in> set ops"
    and "(yid, Some xid) \<in> set ops"
    and "(zid, ref) \<in> set ops"
    and "xid \<noteq> yid" and "yid \<noteq> zid" and "zid \<noteq> xid"
  shows "(list_order ops xid yid \<and> list_order ops yid zid) \<or>
         (list_order ops zid xid \<and> list_order ops xid yid) \<or>
         (xid \<notin> set (interp_list ops) \<and> yid \<notin> set (interp_list ops) \<and>
          zid \<notin> set (interp_list ops))"
proof(cases "xid < zid")
  case True
  then show ?thesis
  proof(cases "yid < zid")
    case True
    have "xid < yid"
      using assms insert_ops_memb_ref_older by blast
    then obtain as bs cs ds
      where split: "ops = as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs @ [(zid, ref)] @ ds"
      using assms \<open>yid < zid\<close> insert_ops_split_3 by blast
    then show ?thesis
    proof(cases ref)
      case None
      hence "xid \<in> set (interp_list (as @ [(xid, ref)]))"
        using interp_list_last_None assms(1) split by metis
      hence xid_in: "xid \<in> set (interp_list (as @ [(xid, ref)] @ bs))"
        using interp_list_monotonic assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order (as @ [(xid, ref)] @ bs @ [(yid, Some xid)]) xid yid"
        using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order ops xid yid"
        using list_order_append assms(1) split append.assoc by metis
      moreover have "xid \<in> set (interp_list (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs))"
        using interp_list_monotonic xid_in assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs @ [(zid, ref)]) zid xid"
        using list_order_insert_none assms(1) insert_ops_appendD split append.assoc None by metis
      hence "list_order ops zid xid"
        using list_order_append assms(1) split append.assoc by metis
      ultimately show ?thesis by blast
    next
      case (Some r)
      then show ?thesis
      proof(cases "r \<in> set (interp_list as)")
        case True
        hence r_xid: "list_order (as @ [(xid, ref)]) r xid"
          using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc Some by metis
        hence "xid \<in> set (interp_list (as @ [(xid, ref)]))"
          using list_order_memb2 assms(1) split by metis
        hence xid_in: "xid \<in> set (interp_list (as @ [(xid, ref)] @ bs))"
          using interp_list_monotonic assms(1) insert_ops_appendD split append.assoc by metis
        hence "list_order (as @ [(xid, ref)] @ bs @ [(yid, Some xid)]) xid yid"
          using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc by metis
        hence "list_order ops xid yid"
          using list_order_append assms(1) split append.assoc by metis
        moreover have "list_order (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs) r xid"
          using list_order_append r_xid assms(1) insert_ops_appendD split append.assoc by metis
        hence "list_order (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs @ [(zid, ref)]) zid xid"
          using list_order_insert_between assms(1) insert_ops_appendD split append.assoc Some by metis
        hence "list_order ops zid xid"
          using list_order_append assms(1) split append.assoc by metis
        ultimately show ?thesis by blast
      next
        case False
        hence "xid \<notin> set (interp_list ops)"
          using interp_list_ref_nonex assms(1) split Some by metis
        moreover have "xid \<notin> set (interp_list (as @ [(xid, ref)] @ bs))"
          using interp_list_ref_nonex assms(1) insert_ops_appendD split append.assoc Some False by metis
        hence "yid \<notin> set (interp_list ops)"
          using interp_list_ref_nonex assms(1) split append.assoc by metis
        moreover have "r \<notin> set (interp_list (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs))"
          using interp_list_append_non_memb assms(1) insert_ops_appendD split append.assoc Some False by metis
        hence "zid \<notin> set (interp_list ops)"
          using interp_list_ref_nonex assms(1) split append.assoc Some by metis
        ultimately show ?thesis by blast
      qed
    qed
  next
    case False
    hence "zid < yid"
      using assms(6) by auto
    then obtain as bs cs ds
      where split: "ops = as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs @ [(yid, Some xid)] @ ds"
      using assms \<open>xid < zid\<close> insert_ops_split_3 by blast
    then show ?thesis
    proof(cases ref)
      case None
      hence "xid \<in> set (interp_list (as @ [(xid, ref)]))"
        using interp_list_last_None assms(1) split by metis
      hence xid_in: "xid \<in> set (interp_list (as @ [(xid, ref)] @ bs))"
        using interp_list_monotonic assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order (as @ [(xid, ref)] @ bs @ [(zid, ref)]) zid xid"
        using list_order_insert_none assms(1) insert_ops_appendD split append.assoc None by metis
      hence "list_order ops zid xid"
        using list_order_append assms(1) split append.assoc by metis
      moreover have "xid \<in> set (interp_list (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs))"
        using interp_list_monotonic xid_in assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs @ [(yid, Some xid)]) xid yid"
        using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc None by metis
      hence "list_order ops xid yid"
        using list_order_append assms(1) split append.assoc by metis
      ultimately show ?thesis by blast
    next
      case (Some r)
      then show ?thesis
      proof(cases "r \<in> set (interp_list as)")
        case True
        hence r_xid: "list_order (as @ [(xid, ref)]) r xid"
          using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc Some by metis
        hence "xid \<in> set (interp_list (as @ [(xid, ref)]))"
          using list_order_memb2 assms(1) split by metis
        hence xid_in: "xid \<in> set (interp_list (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs))"
          using interp_list_monotonic assms(1) insert_ops_appendD split append.assoc by metis
        moreover have "list_order (as @ [(xid, ref)] @ bs) r xid"
          using list_order_append r_xid assms(1) insert_ops_appendD split append.assoc by metis
        hence "list_order (as @ [(xid, ref)] @ bs @ [(zid, ref)]) zid xid"
          using list_order_insert_between assms(1) insert_ops_appendD split append.assoc Some by metis
        hence "list_order ops zid xid"
          using list_order_append assms(1) split append.assoc by metis
        moreover have "list_order (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs @ [(yid, Some xid)]) xid yid"
          using list_order_insert_ref xid_in assms(1) insert_ops_appendD split append.assoc Some by metis
        hence "list_order ops xid yid"
          using list_order_append assms(1) split append.assoc by metis
        ultimately show ?thesis by blast
      next
        case False
        hence "xid \<notin> set (interp_list ops)"
          using interp_list_ref_nonex assms(1) split Some by metis
        moreover have "xid \<notin> set (interp_list (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs))"
          using interp_list_ref_nonex assms(1) insert_ops_appendD split append.assoc Some False by metis
        hence "yid \<notin> set (interp_list ops)"
          using interp_list_ref_nonex assms(1) split append.assoc by metis
        moreover have "r \<notin> set (interp_list (as @ [(xid, ref)] @ bs))"
          using interp_list_append_non_memb assms(1) insert_ops_appendD split append.assoc Some False by metis
        hence "zid \<notin> set (interp_list ops)"
          using interp_list_ref_nonex assms(1) split append.assoc Some by metis
        ultimately show ?thesis by blast
      qed
    qed
  qed
next
  case False
  hence "zid < xid" and "xid < yid"
    using assms neq_iff insert_ops_memb_ref_older by blast+
  then obtain as bs cs ds
    where split: "ops = as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)] @ ds"
    using assms insert_ops_split_3 by blast
  then show ?thesis
  proof(cases ref)
    case None
    hence "zid \<in> set (interp_list (as @ [(zid, ref)]))"
      using interp_list_last_None assms(1) split by metis
    hence "zid \<in> set (interp_list (as @ [(zid, ref)] @ bs))"
      using interp_list_monotonic assms(1) insert_ops_appendD split append.assoc by metis
    hence xid_zid: "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)]) xid zid"
      using list_order_insert_none assms(1) insert_ops_appendD split append.assoc None by metis
    hence "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs) xid zid"
      using list_order_append assms(1) insert_ops_appendD split append.assoc by metis
    hence "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)]) yid zid"
      using list_order_insert_between assms(1) insert_ops_appendD split append.assoc by metis
    hence "list_order ops yid zid"
      using list_order_append assms(1) split append.assoc by metis
    moreover have "xid \<in> set (interp_list (as @ [(zid, ref)] @ bs @ [(xid, ref)]))"
      using list_order_memb1 xid_zid assms(1) split by metis
    hence "xid \<in> set (interp_list (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs))"
      using interp_list_monotonic assms(1) insert_ops_appendD split append.assoc by metis
    hence "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)]) xid yid"
      using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc by metis
    hence "list_order ops xid yid"
      using list_order_append assms(1) split append.assoc by metis
    ultimately show ?thesis by blast
  next
    case (Some r)
    then show ?thesis
    proof(cases "r \<in> set (interp_list as)")
      case True
      hence "list_order (as @ [(zid, ref)]) r zid"
        using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc Some by metis
      hence "list_order (as @ [(zid, ref)] @ bs) r zid"
        using list_order_append assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)]) xid zid"
        using list_order_insert_between assms(1) insert_ops_appendD split append.assoc Some by metis
      hence xid_zid: "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs) xid zid"
        using list_order_append assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)]) yid zid"
        using list_order_insert_between assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order ops yid zid"
        using list_order_append assms(1) split append.assoc by metis
      moreover have "xid \<in> set (interp_list (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs))"
        using list_order_memb1 xid_zid assms(1) split by metis
      hence "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)]) xid yid"
        using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order ops xid yid"
        using list_order_append assms(1) split append.assoc by metis
      ultimately show ?thesis by blast
    next
      case False
      hence "zid \<notin> set (interp_list ops)"
        using interp_list_ref_nonex assms(1) split Some by metis
      moreover have r_notin: "r \<notin> set (interp_list (as @ [(zid, ref)] @ bs))"
        using interp_list_append_non_memb assms(1) insert_ops_appendD split append.assoc Some False by metis
      hence "xid \<notin> set (interp_list (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs))"
        using interp_list_ref_nonex assms(1) insert_ops_appendD split append.assoc Some by metis
      hence "yid \<notin> set (interp_list ops)"
        using interp_list_ref_nonex assms(1) split append.assoc by metis
      moreover have "xid \<notin> set (interp_list ops)"
        using interp_list_ref_nonex r_notin assms(1) split append.assoc Some by metis
      ultimately show ?thesis by blast
    qed
  qed
qed

end
