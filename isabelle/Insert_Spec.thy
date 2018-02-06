theory Insert_Spec
  imports Main Util "~~/src/HOL/Library/Product_Lexorder"
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

section\<open>The list specification locale\<close>

locale list_spec =
  fixes op_list :: "('oid::{linorder} \<times> 'oid option) list"
  assumes sorted_oids [simp, intro!]: "sorted (map fst op_list)"
    and distinct_oids [simp, intro!]: "distinct (map fst op_list)"
    and ref_older: "(oid, Some ref) \<in> set op_list \<Longrightarrow> ref < oid"

context list_spec begin
  
definition op_set :: "('oid::{linorder} \<times> 'oid option) set" where
  "op_set \<equiv> set op_list"

definition ins_list :: "'oid list" where
  "ins_list \<equiv> interp_list op_list"

definition list_order :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" (infix "\<sqsubset>" 50) where
  "list_order x y \<equiv> \<exists>xs ys zs. ins_list = xs@[x]@ys@[y]@zs"
  
lemma list_orderI [intro!]:
  assumes "ins_list = xs@[x]@ys@[y] @zs"
  shows "x \<sqsubset> y"
  using assms by(auto simp add: list_order_def)
    
lemma list_orderE [elim]:
  assumes "x \<sqsubset> y"
  shows "\<exists>xs ys zs. ins_list = xs@[x]@ys@[y] @zs"
  using assms by(auto simp add: list_order_def)

lemma list_order_memb1:
  assumes "x \<sqsubset> y"
  shows "x \<in> set (ins_list)"
  using assms by(auto simp add: list_order_def)

lemma list_order_memb2:
  assumes "x \<sqsubset> y"
  shows "y \<in> set (ins_list)"
  using assms by(auto simp add: list_order_def)

end

lemma list_spec_NilI [intro!]:
  shows "list_spec []"
by(clarsimp simp add: list_spec_def)

lemma list_spec_rm_last [dest]:
  assumes "list_spec (xs@[x])"
  shows "list_spec xs"
using assms by(clarsimp simp: list_spec_def) (metis sorted_append)

lemma list_spec_rem_prefix:
  assumes "list_spec (pre @ suf)"
  shows "list_spec suf"
using assms proof(induction pre)
  case Nil
  then show "list_spec ([] @ suf) \<Longrightarrow> list_spec suf"
    by auto
next
  case (Cons a pre)
  have "sorted (map fst suf)"
    using assms list_spec.sorted_oids sorted_append by fastforce
  moreover have "distinct (map fst suf)"
    using assms list_spec.distinct_oids by force
  ultimately show "list_spec ((a # pre) @ suf) \<Longrightarrow> list_spec suf"
    by (simp add: list_spec_def)
qed

lemma insert_spec_none [simp]:
  shows "set (insert_spec xs (oid, None)) = set xs \<union> {oid}"
by(induction xs, auto simp add: insert_commute sup_commute)

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

lemma interp_list_subset [simp]:
  assumes "list_spec op_list"
  shows "set (interp_list op_list) \<subseteq> set (map fst op_list)"
using assms proof(induction op_list rule: List.rev_induct)
  case Nil
  then show "set (interp_list []) \<subseteq> set (map fst [])"
    by (simp add: interp_list_def)
next
  case (snoc x xs)
  hence IH: "set (interp_list xs) \<subseteq> set (map fst xs)"
    by blast
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

lemma list_oid_subset [simp]:
  assumes "list_spec op_list"
  shows "set (list_spec.ins_list op_list) \<subseteq> set (map fst op_list)"
using assms interp_list_subset list_spec.ins_list_def by fastforce

lemma inserted_item_ident:
  assumes "a \<in> set (insert_spec xs (e, i))"
    and "a \<notin> set xs"
  shows "a = e"
  using assms apply(induction xs)
  apply(case_tac i, simp+)
  apply(case_tac i, simp)
  apply(case_tac "aa = aaa", simp+)
  done

lemma interp_list_tail_unfold:
  shows "interp_list (xs@[x]) = insert_spec (interp_list (xs)) x"
by (clarsimp simp add: interp_list_def)

lemma interp_list_op_ids:
  shows "set (interp_list xs) \<subseteq> set (map fst xs)"
  apply(induction xs rule: rev_induct)
  apply(simp add: interp_list_def)
  apply(subgoal_tac "set (interp_list xs) \<subseteq> set (map fst xs)") prefer 2
  apply blast
  apply(simp add: interp_list_def)
  apply(subgoal_tac "\<And>a. a \<in> set (insert_spec (foldl insert_spec [] xs) x) \<Longrightarrow>
                          a \<in> insert (fst x) (set (map fst xs))")
  apply(simp add: subsetI)
  apply(case_tac "a \<in> set (foldl insert_spec [] xs)", force)
  using inserted_item_ident apply fastforce
  done

lemma last_op_greatest:
  assumes "list_spec (op_list @ [(oid, oper)])"
    and "x \<in> set (map fst op_list)"
    shows "x < oid"
using assms proof(induction op_list)
  assume "x \<in> set (map fst [])"
  thus "x < oid"
    by auto
next
  fix a op_list
  assume IH: "list_spec (op_list @ [(oid, oper)]) \<Longrightarrow> x \<in> set (map fst op_list) \<Longrightarrow> x < oid"
    and 2: "list_spec ((a#op_list) @ [(oid, oper)])"
    and 3: "x \<in> set (map fst (a#op_list))"
  hence L: "list_spec (op_list @ [(oid, oper)])"
    by(simp add: list_spec_def sorted_Cons)
  hence S: "sorted (map fst (op_list @ [(oid, oper)]))"
    by(auto simp add: list_spec_def)
  {
    fix x
    assume A: "x \<in> set (map fst op_list @ [oid])"
    hence "fst a < x"
      using S 2 by(cases a, clarsimp simp add: list_spec_def) (metis A le_neq_trans sorted_Cons)
  }
  note T = this
  have "x = fst a \<or> x \<in> set (map fst op_list)"
    using 3 by auto
  thus "x < oid"
  proof
    assume "x = fst a"
    thus "x < oid"
      using T by auto
  next
    assume "x \<in> set (map fst op_list)"
    thus "x < oid"
      using IH L by auto
  qed
qed

lemma interp_list_distinct:
  assumes "list_spec op_list"
  shows "distinct (interp_list op_list)"
using assms proof(induction op_list rule: rev_induct)
  case Nil
  then show "distinct (interp_list [])"
    by (simp add: interp_list_def)
next
  case (snoc x xs)
  hence IH: "distinct (interp_list xs)" by blast
  obtain oid ref where x_pair: "x = (oid, ref)" by force
  hence "\<forall>x\<in>set (list_spec.ins_list xs). x < oid"
    using last_op_greatest list_oid_subset snoc.prems by blast
  hence "distinct (insert_spec (interp_list xs) (oid, ref))"
    using IH insert_spec_distinct
    by (metis insert_spec_nonex list_spec.ins_list_def list_spec_rm_last snoc.prems)
  then show "distinct (interp_list (xs @ [x]))"
    by (simp add: x_pair interp_list_tail_unfold)
qed

lemma list_distinct:
  assumes "list_spec op_list"
  shows "distinct (list_spec.ins_list op_list)"
using assms by (simp add: interp_list_distinct list_spec.ins_list_def)

lemma suffix_eq_distinct_list:
  assumes "ys@suf1 = xs"
      and "ys@suf2 = xs"
    shows "suf1 = suf2"
using assms by(induction xs arbitrary: suf1 suf2 rule: rev_induct, simp) (metis append_eq_append_conv)

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

lemma list_order_trans:
  assumes "list_spec op_list"
    and "list_spec.list_order op_list x y"
    and "list_spec.list_order op_list y z"
  shows "list_spec.list_order op_list x z"
proof -
  obtain xxs xys xzs where 1: "list_spec.ins_list op_list = (xxs@[x]@xys)@(y#xzs)"
    using assms by(auto simp add: list_spec.list_order_def[OF assms(1)])
  obtain yxs yys yzs where 2: "list_spec.ins_list op_list = yxs@y#(yys@[z]@yzs)"
    using assms by(auto simp add: list_spec.list_order_def[OF assms(1)])
  have 3: "distinct (list_spec.ins_list op_list)"
    using assms list_distinct by blast
  hence "xzs = yys@[z]@yzs"
    using distinct_list_split[OF 3, OF 2, OF 1] by auto
  hence "list_spec.ins_list op_list = xxs@[x]@xys@[y]@yys@[z]@yzs"
    using 1 2 3 by clarsimp
  thus  "list_spec.list_order op_list x z"
    using assms by(metis append.assoc list_spec.list_orderI)
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

lemma insert_twice:
  assumes "list_spec (before @ (x1, r1) # after @ [(x2, r2)])"
    and   "list_spec (before @            after @ [(x2, r2)])"
    and "list_spec.ins_list (before @            after) = xs @      zs"
    and "list_spec.ins_list (before @ (x1, r1) # after) = xs @ ys @ zs"
  shows "\<exists>xsa ysa zsa.
    list_spec.ins_list (before @            after @ [(x2, r2)]) = xsa @       zsa \<and>
    list_spec.ins_list (before @ (x1, r1) # after @ [(x2, r2)]) = xsa @ ysa @ zsa"
  using assms apply -
  apply(subgoal_tac "list_spec (before @ after)") prefer 2
  using list_spec_rm_last apply force
  apply(subgoal_tac "list_spec (before @ (x1, r1) # after)") prefer 2
  using list_spec_rm_last apply force
  apply(simp add: list_spec.ins_list_def interp_list_def)
  apply(case_tac r2, simp)
  apply(metis Cons_eq_appendI)
  apply(case_tac "a \<in> set xs", simp)
  apply(meson insert_first_part)
  apply(case_tac "a \<in> set ys", simp)
  apply(rule_tac x=xs in exI)
  apply(rule_tac x="insert_spec ys (x2, r2)" in exI)
  apply(rule_tac x=zs in exI)
  apply(rule conjI)
  apply(subgoal_tac "a \<notin> set zs", simp)
  using assms(4) distinct_append list.simps(15) list_distinct apply force
  apply(simp add: insert_first_part insert_second_part)
  apply(case_tac "a \<in> set zs")
  apply(rule_tac x=xs in exI)
  apply(rule_tac x=ys in exI)
  apply(rule_tac x="insert_spec zs (x2, r2)" in exI)
  apply(simp add: insert_second_part)
  apply force
  done

lemma insert_preserves_order:
  assumes "list_spec op_list" and "list_spec rest"
    and "rest = before @ after"
    and "op_list = before @ (oid, ref) # after"
  shows "\<exists>xs ys zs. list_spec.ins_list rest    = xs @      zs \<and>
                    list_spec.ins_list op_list = xs @ ys @ zs"
  using assms
  apply(induction after arbitrary: rest op_list rule: rev_induct)
   apply clarsimp
   apply(case_tac "ref")
    apply clarsimp
    apply(rule_tac x="[]" in exI, rule_tac x="[oid]" in exI, rule_tac x="list_spec.ins_list before" in exI)
    apply(clarsimp simp add: list_spec.ins_list_def interp_list_def)
    apply(case_tac "a \<in> set (list_spec.ins_list before)")
     apply(simp add: list_spec.ins_list_def interp_list_def)
     apply(frule_tac oid="oid" in insert_somewhere[OF disjI2, OF conjI], assumption)
     apply(erule exE)+
     apply(rule_tac x="xs" in exI, rule_tac x="[oid]" in exI, rule_tac x="ys" in exI)
    apply(clarsimp simp add: list_spec.ins_list_def interp_list_def)
   apply clarsimp
   apply(frule_tac oid="oid" in insert_spec_nonex)
   apply(rule_tac x="list_spec.ins_list before" in exI, rule_tac x="[]" in exI, rule_tac x="[]" in exI)
   apply(clarsimp simp add: list_spec.ins_list_def interp_list_def)
  apply clarsimp
  apply(erule_tac x="before @ xs" in meta_allE)
  apply(erule_tac x="before @ (oid, ref) # xs" in meta_allE)
  apply clarsimp
  apply(subgoal_tac "list_spec (before @ (oid, ref) # xs)") prefer 2
  apply(metis append_Cons append_assoc list_spec_rm_last)
  apply(subgoal_tac "list_spec (before @ xs)") prefer 2
  apply(metis append_assoc list_spec_rm_last)
  apply(clarsimp simp add: insert_twice)
  done

lemma distinct_fst:
  assumes "distinct (map fst A)"
  shows "distinct A"
using assms by(induction A) auto

lemma sorted_fst:
  assumes "sorted (map fst xs)"
    and "distinct (map fst xs)"
  shows "sorted xs"
using assms proof(induction xs)
  show "sorted []"
    by auto
next
  fix a and xs :: "('a \<times> 'b) list"
  assume 1: "sorted (map fst (a # xs))" and 2: "distinct (map fst (a # xs))"
    and IH: "sorted (map fst xs) \<Longrightarrow> distinct (map fst xs) \<Longrightarrow> sorted xs"
  from this obtain x y where 3: "a = (x, y)"
    by force
  have "sorted (map fst xs)" and "distinct (map fst xs)"
    using 1 2 by(auto simp add: sorted_Cons)
  hence "sorted xs"
    using IH by auto
  also have "\<forall>y\<in>set xs. a \<le> y"
    using 1 2 3 by clarsimp (metis antisym_conv1 fst_conv rev_image_eqI set_map sorted_Cons)
  ultimately show "sorted (a # xs)"
    using sorted_Cons by auto
qed

lemma subset_distinct_le:
  assumes "set A \<subseteq> set B" and "distinct A" and "distinct B"
  shows "length A \<le> length B"
  using assms
  apply(induction B arbitrary: A)
   apply clarsimp
  apply clarsimp
  apply(case_tac "a \<in> set A")
   apply(erule_tac x="List.remove1 a A" in meta_allE)
   apply clarsimp
   apply(simp add: length_remove1 subset_insert_iff)
  apply(erule_tac x="A" in meta_allE, clarsimp)
    by(simp add: subset_insert)

lemma set_subset_length_eq:
  assumes "set A \<subseteq> set B" and "length B \<le> length A" and "distinct A" and "distinct B"
  shows "set A = set B"
  using assms
    apply -
  apply(frule subset_distinct_le, assumption, assumption)
  apply(rule card_subset_eq, force, force)
  apply(simp add: distinct_card)
  done

lemma length_diff_Suc_exists:
  assumes "length xs - length ys = Suc m"
    and "set ys \<subseteq> set xs"
    and "distinct ys" and "distinct xs"
  shows "\<exists>e. e \<in> set xs \<and> e \<notin> set ys"
  using assms
  apply(induction xs arbitrary: ys, clarsimp)
  apply clarsimp
  apply(case_tac "a \<in> set ys")
   apply(erule_tac x="List.remove1 a ys" in meta_allE)
   apply(subgoal_tac "length xs - length (remove1 a ys) = Suc m")
    prefer 2
    apply(metis Suc_diff_eq_diff_pred length_pos_if_in_set length_remove1)
   apply clarsimp
   apply(subgoal_tac "set ys - {a} \<subseteq> set xs")
    prefer 2
    apply blast
   apply clarsimp
   apply force
  apply blast
  done

lemma distinct_map_fst_remove1:
  assumes "distinct (map fst xs)"
  shows "distinct (map fst (remove1 x xs))"
  using assms
  apply(induction xs, clarsimp)
  apply(subgoal_tac "distinct (map fst xs)")
   prefer 2
   apply force
  apply clarsimp
  apply(metis fst_conv image_eqI notin_set_remove1)
  done

lemma list_spec_remove1:
  assumes "list_spec xs"
  shows "list_spec (remove1 x xs)"
  using assms apply(clarsimp simp: list_spec_def)
  using sorted_map_remove1 distinct_map_fst_remove1
  apply(metis notin_set_remove1)
  done

lemma app_length_lt_exists:
  assumes "xsa @ zsa = xs @ ys"
    and "length xsa \<le> length xs"
  shows "xsa@(drop (length xsa) xs) = xs"
  using assms
  apply(induction xsa arbitrary: xs zsa ys, clarsimp)
  apply clarsimp
  apply(metis append_Cons append_eq_append_conv_if append_take_drop_id length_Cons)
  done

lemma app_length_lt_exists':
  assumes "xsa @ zsa = xs @ ys"
    and "length xsa \<le> length xs"
  shows "\<exists>zs. xsa@zs = xs"
  using assms app_length_lt_exists by blast

lemma list_order_monotonic:
  assumes "list_spec A" and "list_spec B"
    and "set A \<subseteq> set B"
    and "list_spec.list_order A x y"
  shows "list_spec.list_order B x y"
  using assms
  apply(induction rule: measure_induct_rule[where f="\<lambda>x. (length x - length A)"])
  apply(case_tac "length xa - length A")
   apply(subgoal_tac "set A = set xa")
    apply(clarsimp simp add: list_spec_def)
    apply(metis distinct_map map_sorted_distinct_set_unique sup_idem)
   apply(rule set_subset_length_eq, assumption, force)
  using distinct_fst list_spec_def apply blast
  using distinct_fst list_spec_def apply blast
  apply clarsimp
  apply(subgoal_tac "\<exists>e. e \<in> set xa \<and> e \<notin> set A")
   prefer 2
   apply(rule length_diff_Suc_exists, force, force)
  using distinct_fst list_spec_def apply blast
  using distinct_fst list_spec_def apply blast
  apply(erule exE, erule conjE)
  apply(erule_tac x="List.remove1 e xa" in meta_allE)
  apply(subgoal_tac "length (remove1 e xa) - length A < Suc nat")
   prefer 2
   apply(metis (no_types, lifting) diff_Suc_1 diff_commute length_remove1 less_Suc_eq)
  apply clarsimp
  apply(frule_tac x="(a, b)" in list_spec_remove1) back
  apply clarsimp
  apply(subgoal_tac "set A \<subseteq> set (remove1 (a, b) xa)")
   prefer 2
   apply(metis (no_types, lifting) in_set_remove1 subset_iff)
  apply clarsimp
  apply(clarsimp simp add: list_spec.list_order_def list_spec.ins_list_def)
   apply(subgoal_tac "interp_list (remove1 (a, b) xa) = xs @ x # ys @ y # zs")
    prefer 2 apply simp
   apply clarsimp
   apply(subgoal_tac "\<exists>ps ss. xa = ps@[(a, b)]@ss \<and> (a, b) \<notin> set ps")
    prefer 2 using split_list_first apply fastforce
   apply clarsimp
   apply(subgoal_tac "interp_list (remove1 (a, b) (ps @ (a, b) # ss)) = interp_list (ps @ ss)")
    prefer 2
    apply(simp add: remove1_append)
   apply clarsimp
   apply(frule_tac op_list="ps @ (a, b) # ss" and rest="ps @ ss" in insert_preserves_order)
      apply(simp add: remove1_append)
     apply(rule refl)+
   apply clarsimp
   apply(subgoal_tac "xsa @ zsa = xs @ x # ys @ y # zs")
    prefer 2
    apply(simp add: list_spec.ins_list_def remove1_append)
   apply clarsimp
   apply(case_tac "length xsa \<le> length xs")
    apply(subgoal_tac "\<exists>ts. xsa@ts = xs")
     prefer 2
  using app_length_lt_exists apply blast
    apply clarsimp
    apply(metis append.assoc list_spec.ins_list_def)
   apply(case_tac "length xsa \<le> length (xs@x#ys)")
    apply(subgoal_tac "\<exists>us. xsa@us = xs@x#ys")
     prefer 2
     apply(simp add: app_length_lt_exists')
    apply clarsimp
    apply(rule_tac x="xs" in exI, rule_tac x="(drop (Suc (length xs)) xsa)@ysa@us" in exI, rule_tac x="zs" in exI)
    apply clarsimp
    apply(subgoal_tac "interp_list (ps @ (a, b) # ss) = xsa @ ysa @ zsa")
     prefer 2
     apply(simp add: list_spec.ins_list_def)
    apply clarsimp
    apply(subgoal_tac "xs @ x # drop (Suc (length xs)) xsa = xsa")
     prefer 2
     apply(metis append_eq_append_conv_if id_take_nth_drop linorder_not_less nth_append nth_append_length)
    apply(subgoal_tac "us @ y # zs = zsa")
     apply force
    apply(metis append_Cons append_assoc suffix_eq_distinct_list)
   apply(rule_tac x="xs" in exI, rule_tac x="ys" in exI, rule_tac x="(drop (Suc (Suc (length xs + length ys))) xsa)@ysa@zsa" in exI)
   apply clarsimp
   apply(subgoal_tac "interp_list (ps @ (a, b) # ss) = xsa @ ysa @ zsa")
     prefer 2
    apply(simp add: list_spec.ins_list_def)
   apply(subgoal_tac "xs @ x # ys @ y # drop (Suc (Suc (length xs + length ys))) xsa = xsa")
    prefer 2
    apply(insert app_length_lt_exists)[1]
    apply(erule_tac x="xs @ x # ys @ [y]" in meta_allE)
    apply(erule_tac x="zs" in meta_allE)
    apply(erule_tac x="xsa" in meta_allE)
    apply(erule_tac x="zsa" in meta_allE)
    apply(subgoal_tac "length (xs @ x # ys @ [y]) \<le> length xsa")
     prefer 2
     apply clarsimp
   apply force
  apply force
  done

lemma insert_spec_nth_oid:
  assumes "distinct ys"
       and "n < length ys"
     shows "insert_spec ys (oid, Some (ys ! n)) ! Suc n = oid"
  using assms
  apply(induction ys arbitrary: n)
   apply clarsimp
  apply clarsimp
  apply safe
   apply(subgoal_tac "n = 0")
    prefer 2
    apply(metis distinct.simps(2) length_Cons nth_Cons_0 nth_eq_iff_index_eq zero_less_Suc)
   apply clarsimp
  apply(subgoal_tac "\<exists>m. n = Suc m")
   prefer 2
   apply(metis not0_implies_Suc nth_Cons')
  apply clarsimp
  done

lemma ins_list_correct_position_insert:
  assumes "list_spec (xs@[make_insert ys oid m])"
    and "list_spec.ins_list xs = ys"
  shows "list_spec.ins_list (xs@[make_insert ys oid m]) ! min (length ys) m = oid"
  using assms
  apply -
  apply(clarsimp simp add: list_spec.ins_list_def interp_list_def)
  apply(case_tac "m"; clarsimp)
  apply(case_tac "min (length (list_spec.ins_list xs)) (Suc nat) = Suc nat")
    apply clarsimp
   apply(subgoal_tac "min (length (list_spec.ins_list xs) - Suc 0) nat = nat")
    prefer 2
    apply linarith
    apply(case_tac "(list_spec.ins_list xs)")
    apply clarsimp
    apply clarsimp
     prefer 2
     apply(subgoal_tac "min (length (list_spec.ins_list xs)) (Suc nat) = length (list_spec.ins_list xs)")
    prefer 2
      apply force
     apply(subgoal_tac "min (length (list_spec.ins_list xs) - Suc 0) nat = length (list_spec.ins_list xs) - Suc 0")
      prefer 2
      apply force
     apply clarsimp
   prefer 2
   apply (case_tac "(foldl insert_spec [] xs)")
    apply clarsimp
    apply (metis interp_list_def list.simps(3) list_spec.ins_list_def list_spec_rm_last)
   apply clarsimp
   apply (rule conjI; clarsimp)
  apply (metis distinct_conv_nth interp_list_def length_Cons lessI list_distinct list_spec.ins_list_def list_spec_rm_last min_Suc_Suc min_less_iff_conj nth_Cons' zero_less_Suc)
   apply (metis (no_types, lifting) insert_spec.simps(3) insert_spec_nth_oid interp_list_def length_Cons lessI list_distinct list_spec.ins_list_def list_spec_rm_last min_Suc_Suc min_less_iff_conj nth_Cons_Suc)
  apply (case_tac "(list_spec.ins_list xs)")
   apply clarsimp
  apply clarsimp
  apply (case_tac "(foldl insert_spec [] xs)"; clarsimp)
   apply (metis interp_list_def list.discI list_spec.ins_list_def list_spec_rm_last)
  apply (rule conjI; clarsimp)
   apply (metis distinct_conv_nth interp_list_def length_Cons lessI list_distinct list_spec.ins_list_def list_spec_rm_last nth_Cons_0 zero_less_Suc)
  by (metis (no_types, lifting) insert_spec.simps(3) insert_spec_nth_oid interp_list_def length_Cons lessI list_distinct list_spec.ins_list_def list_spec_rm_last nth_Cons_Suc)

lemma pre_suf_eq_distinct_list_var:
  assumes "distinct (pre2@ys@suf2)"
      and "ys \<noteq> []"
      and "pre1@ys@suf1 = pre2@ys@suf2"
    shows "pre1 = pre2 \<and> suf1 = suf2"
using assms pre_suf_eq_distinct_list by metis

lemma list_order_transp:
  assumes "list_spec op_list"
  shows "transp (list_spec.list_order op_list)"
using assms list_order_trans transpI by metis

lemma list_order_total:
  assumes 1: "list_spec op_list"
    and 2: "x \<in> set (list_spec.ins_list op_list)"
    and 3: "y \<in> set (list_spec.ins_list op_list)"
    and 4: "x \<noteq> y"
  shows "list_spec.list_order op_list x y \<or> list_spec.list_order op_list y x"
  using assms
  apply -
  apply(unfold list_spec.list_order_def[OF 1])
  apply(subgoal_tac "distinct (list_spec.ins_list op_list)")
   apply(drule list_split_two_elems, assumption, assumption, force, force)
  using 1 and list_distinct apply fastforce
  done
    
lemma list_order_irrefl:
  assumes 1: "list_spec op_list"
  shows "\<not> list_spec.list_order op_list x x"
  using assms
  apply -
  apply(unfold list_spec.list_order_def[OF 1])  
  apply(subgoal_tac "distinct (list_spec.ins_list op_list)")
    apply force
  using 1 and list_distinct apply fastforce
  done

lemma ins_list_empty_list [simp]:
  shows "list_spec.ins_list [] = []"
  by(clarsimp simp add: list_spec.ins_list_def[OF list_spec_NilI] interp_list_def)

lemma ins_list_empty [simp]:
  shows "set (list_spec.ins_list []) = {}"
  by(clarsimp simp add: list_spec.ins_list_def[OF list_spec_NilI] interp_list_def)

lemma ins_list_set_eq_disj:
  assumes "list_spec (ys @ [(oid, ref)])"
  shows "set (list_spec.ins_list (ys @ [(oid, ref)])) = set (list_spec.ins_list ys) \<or>
         set (list_spec.ins_list (ys @ [(oid, ref)])) = (set (list_spec.ins_list ys) \<union> {oid})"
  using assms
  apply (subgoal_tac "list_spec ys") prefer 2
  apply auto[1]
  apply(clarsimp simp add: list_spec.ins_list_def interp_list_def)
  apply(cases ref; clarsimp)
  apply(metis insert_spec.simps(1) insert_spec_none insert_spec_nonex insert_spec_set list.simps(15))
  done

lemma ins_list_set_eq_disj2:
  assumes "list_spec (ys @ [x])"
  shows "set (list_spec.ins_list (ys @ [x])) = set (list_spec.ins_list ys) \<or>
         set (list_spec.ins_list (ys @ [x])) = (set (list_spec.ins_list ys) \<union> {fst x})"
  apply (cases x)
  using ins_list_set_eq_disj assms by auto

lemma ins_list_set_eq_disj2_general:
  assumes "list_spec (ys @ xs)"
  shows "\<exists>A. A \<subseteq> set (map fst xs) \<and> set (list_spec.ins_list (ys @ xs)) = (set (list_spec.ins_list ys) \<union> A)"
  using assms
  apply(induction xs rule: List.rev_induct, clarsimp)
  apply clarsimp
  apply(erule meta_impE)
   apply(metis append_assoc list_spec_rm_last)
  apply clarsimp
  apply(subgoal_tac "set (list_spec.ins_list ((ys @ xs) @ [(a, b)])) = set (list_spec.ins_list (ys @ xs)) \<or>
    set (list_spec.ins_list ((ys @ xs) @ [(a, b)])) = set (list_spec.ins_list (ys @ xs)) \<union> {a}")
   apply(erule disjE)
    apply(rule_tac x="A" in exI, force)
   apply(rule_tac x="A \<union> {a}" in exI, force)
  apply(rule ins_list_set_eq_disj, force)
  done

lemma list_spec_irrelevant_operation:
  assumes "list_spec ops"
    and "ops = xs @ [(oid, Some ref)] @ ys"
    and "ref \<notin> set (list_spec.ins_list xs)"
  shows "oid \<notin> set (list_spec.ins_list ops)"
  using assms
  apply(induction ys arbitrary: ops rule: List.rev_induct)
   apply(metis append_Nil2 insert_spec_nonex interp_list_tail_unfold last_op_greatest list_greater_non_memb list_oid_subset list_spec.ins_list_def list_spec_rm_last subsetCE)
  apply clarsimp
  apply(erule_tac x="xs @ (oid, Some ref) # xsa" in meta_allE)
  apply(erule meta_impE)
   apply(metis (no_types, lifting) Nil_is_append_conv append_butlast_last_id butlast.simps(2) butlast_append butlast_snoc list.discI list_spec_rm_last)
  apply clarsimp
  apply(subgoal_tac "distinct (map fst (xs @ (oid, Some ref) # xsa @ [(a, b)]))") prefer 2
  using list_spec.distinct_oids apply blast
  apply(subgoal_tac "a \<noteq> oid") prefer 2
   apply clarsimp
  apply(subgoal_tac "set (list_spec.ins_list ((xs @ (oid, Some ref) # xsa) @ [(a, b)])) = set (list_spec.ins_list (xs @ (oid, Some ref) # xsa)) \<or> 
                      set (list_spec.ins_list ((xs @ (oid, Some ref) # xsa) @ [(a, b)])) = set (list_spec.ins_list (xs @ (oid, Some ref) # xsa)) \<union> {a}")
   apply clarsimp apply force
  apply(rule ins_list_set_eq_disj, force)
  done

lemma list_spec_appendD: "list_spec (xs @ ys) \<Longrightarrow> list_spec xs"
  apply (induct ys rule: rev_induct)
   apply simp
  using list_spec_rm_last by force

lemma map_fst_append1:
  assumes "\<forall>i \<in> set (map fst xs). P i"
    and "P x"
  shows "\<forall>i \<in> set (map fst (xs @ [(x, y)])). P i"
using assms by (induction xs, auto)

lemma list_spec_split:
  assumes "list_spec ops"
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
      by (metis IH append.assoc list_spec.distinct_oids snoc.prems(1))
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

lemma list_spec_split_2:
  assumes "list_spec ops"
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
    using assms list_spec_split by blast
  hence "list_spec ((as @ [(xid, xr)]) @ as1)"
    using assms(1) by auto
  hence "list_spec as1"
    using assms(1) list_spec_rem_prefix by blast
  have "(yid, yr) \<in> set as1"
    using x_split assms by auto
  from this obtain bs cs where y_split: "as1 = bs @ [(yid, yr)] @ cs \<and>
      (\<forall>i \<in> set (map fst bs). i < yid) \<and> (\<forall>i \<in> set (map fst cs). yid < i)"
    using assms list_spec_split \<open>list_spec as1\<close> by blast
  hence "ops = as @ [(xid, xr)] @ bs @ [(yid, yr)] @ cs"
    using x_split by blast
  moreover have "\<forall>i \<in> set (map fst bs). xid < i \<and> i < yid"
    by (simp add: x_split y_split)
  ultimately show ?thesis
    using x_split y_split by blast
qed

lemma list_spec_split_3:
  assumes "list_spec ops"
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
    using assms list_spec_split_2 by blast
  hence "list_spec ((as @ [(xid, xr)] @ bs @ [(yid, yr)]) @ cs1)"
    using assms(1) by auto
  hence "list_spec cs1"
    using assms(1) list_spec_rem_prefix by blast
  have "(zid, zr) \<in> set cs1"
    using assms xy_split by auto
  from this obtain cs ds where z_split: "cs1 = cs @ [(zid, zr)] @ ds \<and>
      (\<forall>i \<in> set (map fst cs). i < zid) \<and> (\<forall>i \<in> set (map fst ds). zid < i)"
    using assms list_spec_split \<open>list_spec cs1\<close> by blast
  hence "ops = as @ [(xid, xr)] @ bs @ [(yid, yr)] @ cs @ [(zid, zr)] @ ds"
    using xy_split by blast
  moreover have "\<forall>i \<in> set (map fst cs). yid < i \<and> i < zid"
    by (simp add: xy_split z_split)
  ultimately show ?thesis
    using xy_split z_split by blast
qed

lemma ins_list_last_None:
  assumes "list_spec (ops @ [(oid, None)])"
  shows "oid \<in> set (list_spec.ins_list (ops @ [(oid, None)]))"
by (simp add: assms interp_list_tail_unfold list_spec.ins_list_def)

lemma ins_list_monotonic:
  assumes "list_spec (pre @ suf)"
    and "oid \<in> set (list_spec.ins_list pre)"
  shows "oid \<in> set (list_spec.ins_list (pre @ suf))"
using assms ins_list_set_eq_disj2_general by auto

lemma list_spec_sorted_oids:
  assumes "list_spec (xs @ [(i1, r1)] @ ys @ [(i2, r2)])"
  shows "i1 < i2"
proof -
  have "\<And>i. i \<in> set (map fst (xs @ [(i1, r1)] @ ys)) \<Longrightarrow> i < i2"
    by (metis append.assoc assms last_op_greatest)
  moreover have "i1 \<in> set (map fst (xs @ [(i1, r1)] @ ys))"
    by auto
  ultimately show "i1 < i2"
    by blast
qed

lemma ins_list_append_non_memb:
  assumes "list_spec (pre @ [(oid, Some ref)] @ suf)"
    and "ref \<notin> set (list_spec.ins_list pre)"
  shows "ref \<notin> set (list_spec.ins_list (pre @ [(oid, Some ref)] @ suf))"
using assms proof(induction suf rule: List.rev_induct)
  case Nil
  then show "ref \<notin> set (list_spec.ins_list (pre @ [(oid, Some ref)] @ []))"
    by (metis append_Nil2 insert_spec_nonex interp_list_tail_unfold
        list_spec.ins_list_def list_spec_appendD)
next
  case (snoc x xs)
  hence IH: "ref \<notin> set (list_spec.ins_list (pre @ [(oid, Some ref)] @ xs))"
    by (metis append_assoc list_spec_rm_last)
  moreover have "ref < oid"
    by (meson list.set_intros(1) list_spec.ref_older list_spec_appendD list_spec_rem_prefix snoc.prems(1))
  moreover have "oid < fst x"
    using list_spec_sorted_oids by (metis prod.collapse snoc.prems(1))
  have "set (list_spec.ins_list ((pre @ [(oid, Some ref)] @ xs) @ [x])) =
        set (list_spec.ins_list (pre @ [(oid, Some ref)] @ xs)) \<or>
        set (list_spec.ins_list ((pre @ [(oid, Some ref)] @ xs) @ [x])) =
        set (list_spec.ins_list (pre @ [(oid, Some ref)] @ xs)) \<union> {fst x}"
    by (metis (full_types) append.assoc ins_list_set_eq_disj2 snoc.prems(1))
  ultimately show "ref \<notin> set (list_spec.ins_list (pre @ [(oid, Some ref)] @ xs @ [x]))"
    using \<open>oid < fst x\<close> by auto
qed

lemma list_order_append:
  assumes "list_spec (pre @ suf)"
    and "list_spec.list_order pre x y"
  shows "list_spec.list_order (pre @ suf) x y"
by (metis Un_iff assms list_order_monotonic list_spec_appendD set_append subset_code(1))

lemma list_order_insert_ref:
  assumes "list_spec (ops @ [(oid, Some ref)])"
    and "ref \<in> set (list_spec.ins_list ops)"
  shows "list_spec.list_order (ops @ [(oid, Some ref)]) ref oid"
proof -
  have "list_spec.ins_list (ops @ [(oid, Some ref)]) =
        insert_spec (list_spec.ins_list ops) (oid, Some ref)"
    by (metis assms(1) interp_list_tail_unfold list_spec.ins_list_def list_spec_appendD)
  moreover obtain xs ys where "list_spec.ins_list ops = xs @ [ref] @ ys"
    by (meson assms(2) list_set_memb)
  hence "insert_spec (list_spec.ins_list ops) (oid, Some ref) = xs @ [ref] @ [] @ [oid] @ ys"
    using assms(1) insert_after_ref list_distinct by fastforce
  ultimately show "list_spec.list_order (ops @ [(oid, Some ref)]) ref oid"
    using assms(1) list_spec.list_orderI by fastforce
qed

lemma list_order_insert_none:
  assumes "list_spec (ops @ [(oid, None)])"
    and "x \<in> set (list_spec.ins_list ops)"
  shows "list_spec.list_order (ops @ [(oid, None)]) oid x"
proof -
  have "list_spec.ins_list (ops @ [(oid, None)]) =
        insert_spec (list_spec.ins_list ops) (oid, None)"
    by (metis assms(1) interp_list_tail_unfold list_spec.ins_list_def list_spec_appendD)
  moreover obtain xs ys where "list_spec.ins_list ops = xs @ [x] @ ys"
    by (meson assms(2) list_set_memb)
  hence "insert_spec (list_spec.ins_list ops) (oid, None) = [] @ [oid] @ xs @ [x] @ ys"
    by simp
  ultimately show "list_spec.list_order (ops @ [(oid, None)]) oid x"
    using assms(1) list_spec.list_orderI by fastforce
qed

lemma list_order_insert_between:
  assumes "list_spec (ops @ [(oid, Some ref)])"
    and "list_spec.list_order ops ref x"
  shows "list_spec.list_order (ops @ [(oid, Some ref)]) oid x"
proof -
  have "list_spec.ins_list (ops @ [(oid, Some ref)]) =
        insert_spec (list_spec.ins_list ops) (oid, Some ref)"
    by (metis assms(1) interp_list_tail_unfold list_spec.ins_list_def list_spec_appendD)
  moreover obtain xs ys zs where "list_spec.ins_list ops = xs @ [ref] @ ys @ [x] @ zs"
    using assms list_spec.list_orderE by blast
  moreover have "... = xs @ ref # (ys @ [x] @ zs)"
    by simp
  moreover have "distinct (xs @ ref # (ys @ [x] @ zs))"
    using assms(1) calculation by (metis list_distinct list_spec_rm_last)
  hence "insert_spec (xs @ ref # (ys @ [x] @ zs)) (oid, Some ref) = xs @ ref # oid # (ys @ [x] @ zs)"
    using assms(1) calculation by (simp add: insert_after_ref)
  moreover have "... = (xs @ [ref]) @ [oid] @ ys @ [x] @ zs"
    by simp
  ultimately show "list_spec.list_order (ops @ [(oid, Some ref)]) oid x"
    using assms(1) list_spec.list_orderI by metis
qed

theorem no_interleaving:
  assumes "list_spec ops"
    and "(xid, ref) \<in> set ops"
    and "(yid, Some xid) \<in> set ops"
    and "(zid, ref) \<in> set ops"
    and "xid \<noteq> yid" and "yid \<noteq> zid" and "zid \<noteq> xid"
  shows "(list_spec.list_order ops xid yid \<and> list_spec.list_order ops yid zid) \<or>
         (list_spec.list_order ops zid xid \<and> list_spec.list_order ops xid yid) \<or>
         (xid \<notin> set (list_spec.ins_list ops) \<and> yid \<notin> set (list_spec.ins_list ops) \<and>
          zid \<notin> set (list_spec.ins_list ops))"
proof(cases "xid < zid")
  case True
  then show ?thesis
  proof(cases "yid < zid")
    case True
    have "xid < yid"
      using assms list_spec.ref_older by blast
    then obtain as bs cs ds
      where split: "ops = as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs @ [(zid, ref)] @ ds"
      using assms \<open>yid < zid\<close> list_spec_split_3 by blast
    then show ?thesis
    proof(cases ref)
      case None
      hence "xid \<in> set (list_spec.ins_list (as @ [(xid, ref)]))"
        using ins_list_last_None assms(1) list_spec_appendD split append.assoc by metis
      hence xid_in: "xid \<in> set (list_spec.ins_list (as @ [(xid, ref)] @ bs))"
        using ins_list_monotonic assms(1) list_spec_appendD split append.assoc by metis
      hence "list_spec.list_order (as @ [(xid, ref)] @ bs @ [(yid, Some xid)]) xid yid"
        using list_order_insert_ref assms(1) list_spec_appendD split append.assoc by metis
      hence "list_spec.list_order ops xid yid"
        using list_order_append assms(1) split append.assoc by metis
      moreover have "xid \<in> set (list_spec.ins_list (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs))"
        using ins_list_monotonic xid_in assms(1) list_spec_appendD split append.assoc by metis
      hence "list_spec.list_order (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs @ [(zid, ref)]) zid xid"
        using list_order_insert_none assms(1) list_spec_appendD split append.assoc None by metis
      hence "list_spec.list_order ops zid xid"
        using list_order_append assms(1) split append.assoc by metis
      ultimately show ?thesis by blast
    next
      case (Some r)
      then show ?thesis
      proof(cases "r \<in> set (list_spec.ins_list as)")
        case True
        hence r_xid: "list_spec.list_order (as @ [(xid, ref)]) r xid"
          using list_order_insert_ref assms(1) list_spec_appendD split append.assoc Some by metis
        hence "xid \<in> set (list_spec.ins_list (as @ [(xid, ref)]))"
          using list_spec.list_order_memb2 assms(1) list_spec_appendD split append.assoc by metis
        hence xid_in: "xid \<in> set (list_spec.ins_list (as @ [(xid, ref)] @ bs))"
          using ins_list_monotonic assms(1) list_spec_appendD split append.assoc by metis
        hence "list_spec.list_order (as @ [(xid, ref)] @ bs @ [(yid, Some xid)]) xid yid"
          using list_order_insert_ref assms(1) list_spec_appendD split append.assoc by metis
        hence "list_spec.list_order ops xid yid"
          using list_order_append assms(1) split append.assoc by metis
        moreover have "list_spec.list_order (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs) r xid"
          using list_order_append r_xid assms(1) list_spec_appendD split append.assoc by metis
        hence "list_spec.list_order (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs @ [(zid, ref)]) zid xid"
          using list_order_insert_between assms(1) list_spec_appendD split append.assoc Some by metis
        hence "list_spec.list_order ops zid xid"
          using list_order_append assms(1) split append.assoc by metis
        ultimately show ?thesis by blast
      next
        case False
        hence "xid \<notin> set (list_spec.ins_list ops)"
          using list_spec_irrelevant_operation assms(1) split Some by metis
        moreover have "xid \<notin> set (list_spec.ins_list (as @ [(xid, ref)] @ bs))"
          using list_spec_irrelevant_operation assms(1) list_spec_appendD split append.assoc Some False by metis
        hence "yid \<notin> set (list_spec.ins_list ops)"
          using list_spec_irrelevant_operation assms(1) split append.assoc by metis
        moreover have "r \<notin> set (list_spec.ins_list (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs))"
          using ins_list_append_non_memb assms(1) list_spec_appendD split append.assoc Some False by metis
        hence "zid \<notin> set (list_spec.ins_list ops)"
          using list_spec_irrelevant_operation assms(1) split append.assoc Some by metis
        ultimately show ?thesis by blast
      qed
    qed
  next
    case False
    hence "zid < yid"
      using assms(6) by auto
    then obtain as bs cs ds
      where split: "ops = as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs @ [(yid, Some xid)] @ ds"
      using assms \<open>xid < zid\<close> list_spec_split_3 by blast
    then show ?thesis
    proof(cases ref)
      case None
      hence "xid \<in> set (list_spec.ins_list (as @ [(xid, ref)]))"
        using ins_list_last_None assms(1) list_spec_appendD split append.assoc by metis
      hence xid_in: "xid \<in> set (list_spec.ins_list (as @ [(xid, ref)] @ bs))"
        using ins_list_monotonic assms(1) list_spec_appendD split append.assoc by metis
      hence "list_spec.list_order (as @ [(xid, ref)] @ bs @ [(zid, ref)]) zid xid"
        using list_order_insert_none assms(1) list_spec_appendD split append.assoc None by metis
      hence "list_spec.list_order ops zid xid"
        using list_order_append assms(1) split append.assoc by metis
      moreover have "xid \<in> set (list_spec.ins_list (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs))"
        using ins_list_monotonic xid_in assms(1) list_spec_appendD split append.assoc by metis
      hence "list_spec.list_order (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs @ [(yid, Some xid)]) xid yid"
        using list_order_insert_ref assms(1) list_spec_appendD split append.assoc None by metis
      hence "list_spec.list_order ops xid yid"
        using list_order_append assms(1) split append.assoc by metis
      ultimately show ?thesis by blast
    next
      case (Some r)
      then show ?thesis
      proof(cases "r \<in> set (list_spec.ins_list as)")
        case True
        hence r_xid: "list_spec.list_order (as @ [(xid, ref)]) r xid"
          using list_order_insert_ref assms(1) list_spec_appendD split append.assoc Some by metis
        hence "xid \<in> set (list_spec.ins_list (as @ [(xid, ref)]))"
          using list_spec.list_order_memb2 assms(1) list_spec_appendD split append.assoc by metis
        hence xid_in: "xid \<in> set (list_spec.ins_list (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs))"
          using ins_list_monotonic assms(1) list_spec_appendD split append.assoc by metis
        moreover have "list_spec.list_order (as @ [(xid, ref)] @ bs) r xid"
          using list_order_append r_xid assms(1) list_spec_appendD split append.assoc by metis
        hence "list_spec.list_order (as @ [(xid, ref)] @ bs @ [(zid, ref)]) zid xid"
          using list_order_insert_between assms(1) list_spec_appendD split append.assoc Some by metis
        hence "list_spec.list_order ops zid xid"
          using list_order_append assms(1) split append.assoc by metis
        moreover have "list_spec.list_order (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs @ [(yid, Some xid)]) xid yid"
          using list_order_insert_ref xid_in assms(1) list_spec_appendD split append.assoc Some by metis
        hence "list_spec.list_order ops xid yid"
          using list_order_append assms(1) split append.assoc by metis
        ultimately show ?thesis by blast
      next
        case False
        hence "xid \<notin> set (list_spec.ins_list ops)"
          using list_spec_irrelevant_operation assms(1) split Some by metis
        moreover have "xid \<notin> set (list_spec.ins_list (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs))"
          using list_spec_irrelevant_operation assms(1) list_spec_appendD split append.assoc Some False by metis
        hence "yid \<notin> set (list_spec.ins_list ops)"
          using list_spec_irrelevant_operation assms(1) split append.assoc by metis
        moreover have "r \<notin> set (list_spec.ins_list (as @ [(xid, ref)] @ bs))"
          using ins_list_append_non_memb assms(1) list_spec_appendD split append.assoc Some False by metis
        hence "zid \<notin> set (list_spec.ins_list ops)"
          using list_spec_irrelevant_operation assms(1) split append.assoc Some by metis
        ultimately show ?thesis by blast
      qed
    qed
  qed
next
  case False
  hence "zid < xid" and "xid < yid"
    using assms neq_iff list_spec.ref_older by blast+
  then obtain as bs cs ds
    where split: "ops = as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)] @ ds"
    using assms list_spec_split_3 by blast
  then show ?thesis
  proof(cases ref)
    case None
    hence "zid \<in> set (list_spec.ins_list (as @ [(zid, ref)]))"
      using ins_list_last_None assms(1) list_spec_appendD split append.assoc by metis
    hence "zid \<in> set (list_spec.ins_list (as @ [(zid, ref)] @ bs))"
      using ins_list_monotonic assms(1) list_spec_appendD split append.assoc by metis
    hence xid_zid: "list_spec.list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)]) xid zid"
      using list_order_insert_none assms(1) list_spec_appendD split append.assoc None by metis
    hence "list_spec.list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs) xid zid"
      using list_order_append assms(1) list_spec_appendD split append.assoc by metis
    hence "list_spec.list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)]) yid zid"
      using list_order_insert_between assms(1) list_spec_appendD split append.assoc by metis
    hence "list_spec.list_order ops yid zid"
      using list_order_append assms(1) split append.assoc by metis
    moreover have "xid \<in> set (list_spec.ins_list (as @ [(zid, ref)] @ bs @ [(xid, ref)]))"
      using list_spec.list_order_memb1 xid_zid assms(1) list_spec_appendD split append.assoc by metis
    hence "xid \<in> set (list_spec.ins_list (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs))"
      using ins_list_monotonic assms(1) list_spec_appendD split append.assoc by metis
    hence "list_spec.list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)]) xid yid"
      using list_order_insert_ref assms(1) list_spec_appendD split append.assoc by metis
    hence "list_spec.list_order ops xid yid"
      using list_order_append assms(1) split append.assoc by metis
    ultimately show ?thesis by blast
  next
    case (Some r)
    then show ?thesis
    proof(cases "r \<in> set (list_spec.ins_list as)")
      case True
      hence "list_spec.list_order (as @ [(zid, ref)]) r zid"
        using list_order_insert_ref assms(1) list_spec_appendD split append.assoc Some by metis
      hence "list_spec.list_order (as @ [(zid, ref)] @ bs) r zid"
        using list_order_append assms(1) list_spec_appendD split append.assoc by metis
      hence "list_spec.list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)]) xid zid"
        using list_order_insert_between assms(1) list_spec_appendD split append.assoc Some by metis
      hence xid_zid: "list_spec.list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs) xid zid"
        using list_order_append assms(1) list_spec_appendD split append.assoc by metis
      hence "list_spec.list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)]) yid zid"
        using list_order_insert_between assms(1) list_spec_appendD split append.assoc by metis
      hence "list_spec.list_order ops yid zid"
        using list_order_append assms(1) split append.assoc by metis
      moreover have "xid \<in> set (list_spec.ins_list (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs))"
        using list_spec.list_order_memb1 xid_zid assms(1) list_spec_appendD split append.assoc by metis
      hence "list_spec.list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)]) xid yid"
        using list_order_insert_ref assms(1) list_spec_appendD split append.assoc by metis
      hence "list_spec.list_order ops xid yid"
        using list_order_append assms(1) split append.assoc by metis
      ultimately show ?thesis by blast
    next
      case False
      hence "zid \<notin> set (list_spec.ins_list ops)"
        using list_spec_irrelevant_operation assms(1) split Some by metis
      moreover have r_notin: "r \<notin> set (list_spec.ins_list (as @ [(zid, ref)] @ bs))"
        using ins_list_append_non_memb assms(1) list_spec_appendD split append.assoc Some False by metis
      hence "xid \<notin> set (list_spec.ins_list (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs))"
        using list_spec_irrelevant_operation assms(1) list_spec_appendD split append.assoc Some by metis
      hence "yid \<notin> set (list_spec.ins_list ops)"
        using list_spec_irrelevant_operation assms(1) split append.assoc by metis
      moreover have "xid \<notin> set (list_spec.ins_list ops)"
        using list_spec_irrelevant_operation r_notin assms(1) split append.assoc Some by metis
      ultimately show ?thesis by blast
    qed
  qed
qed

end
