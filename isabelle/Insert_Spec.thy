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

end

lemma list_spec_NilI [intro!]:
  shows "list_spec []"
by(clarsimp simp add: list_spec_def)

lemma list_spec_rm_last [dest]:
  assumes "list_spec (xs@[x])"
  shows "list_spec xs"
using assms by(clarsimp simp: list_spec_def) (metis sorted_append)

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

lemma list_oid_subset [simp]:
  assumes "list_spec op_list"
  shows "set (list_spec.ins_list op_list) \<subseteq> set (map fst op_list)"
using assms proof(induction op_list rule: List.rev_induct)
  show "set (list_spec.ins_list []) \<subseteq> set (map fst [])"
    by(auto simp add: list_spec.ins_list_def[OF list_spec_NilI] interp_list_def)
next
  fix x and xs :: "('a \<times> 'a option) list"
  assume "list_spec xs \<Longrightarrow> set (list_spec.ins_list xs) \<subseteq> set (map fst xs)"
    and S: "list_spec (xs@[x])"
  hence IH: "set (list_spec.ins_list xs) \<subseteq> set (map fst xs)"
    by blast
  obtain id ref where P: "x = (id, ref)"
    by fastforce
  show "set (list_spec.ins_list (xs@[x])) \<subseteq> set (map fst (xs@[x]))"
  proof -
    {
      fix e
      assume 1: "e \<in> set (list_spec.ins_list (xs @ [(id, ref)]))"
        and 2: "e \<notin> fst ` set xs"
      have 3: "list_spec (xs @ [(id, ref)])"
        using S P by auto
      obtain f where F: "foldl insert_spec [] xs = f"
        by fastforce
      hence 4: "e \<in> set (insert_spec f (id, ref))"
        using 1 2 3 by(clarsimp simp add: list_spec.ins_list_def interp_list_def)
      have "e = id"
      proof(cases ref)
        assume "ref = None"
        thus "e = id"
          using 2 4 F IH S by(metis contra_subsetD  image_set insert_spec.simps(1)
              interp_list_def list_spec.ins_list_def list_spec_rm_last set_ConsD)
      next
        fix a
        assume "ref = Some a"
        show "e = id"
        proof(cases "a \<in> set f")
          assume "a \<in> set f"
          show "e = id"
            using 2 3 4 IH F by(metis \<open>a \<in> set f\<close> \<open>ref = Some a\<close> contra_subsetD image_set
                insert_spec.simps(1) insert_spec_none insert_spec_set interp_list_def
                list_spec.ins_list_def list_spec_rm_last set_ConsD)
        next
          assume "a \<notin> set f"
          show "e = id"
            using 2 3 4 IH F by(metis \<open>a \<notin> set f\<close> \<open>ref = Some a\<close> contra_subsetD image_set
                insert_spec_nonex interp_list_def list_spec.ins_list_def list_spec_rm_last)
        qed
      qed 
    }
    thus "set (list_spec.ins_list (xs@[x])) \<subseteq> set (map fst (xs@[x]))"
      by(clarsimp simp add: P)
  qed
qed

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

lemma list_distinct:
  assumes "list_spec op_list"
  shows "distinct (list_spec.ins_list op_list)"
  using assms apply (induct op_list rule: rev_induct)
  apply(simp add: list_spec.ins_list_def interp_list_def)
  apply(frule list_spec_rm_last, clarsimp)
  apply(subgoal_tac "\<forall>x\<in>set (list_spec.ins_list xs). x < a") prefer 2
  using last_op_greatest list_oid_subset apply blast
  apply(subgoal_tac "distinct (insert_spec (list_spec.ins_list xs) (a, b))") prefer 2
  apply(metis insert_spec.simps(2) insert_spec_distinct last_in_set)
  apply(simp add: list_spec.ins_list_def interp_list_def)
  done

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

lemma distinct_set_length3:
  assumes "distinct xs" "set xs = {x, y, z}" "x \<noteq> y" "y \<noteq> z" "z \<noteq> x" 
  shows   "\<exists>a b c. xs = [a, b, c]"
proof (cases xs)
  assume "xs = []" thus ?thesis using assms by auto 
next
  fix a bs assume 1: "xs = a#bs" thus ?thesis
  proof (cases bs)
    assume "bs = []" thus ?thesis using assms 1 by auto
  next
    fix b cs assume 2: "bs = b#cs" thus ?thesis
    proof (cases cs)
      assume "cs = []" thus ?thesis
        using assms 1 2 by clarsimp (metis all_not_in_conv insertE insert_subset subset_insertI)
    next
      fix c ds assume 3: "cs = c#ds"
      then show ?thesis
      proof (cases ds)
        assume "ds = []" thus ?thesis
          using 1 2 3 by fastforce
      next
        fix d zs assume "ds = d#zs"
        thus ?thesis 
          using 1 2 3 assms by clarsimp (metis all_not_in_conv insertE insert_subset subset_insertI)
      qed
    qed
  qed
qed

lemma set3_injection: "set xs = {x, y, z} \<Longrightarrow> distinct xs \<Longrightarrow> xs = [a, b, c] \<Longrightarrow> distinct [x, y, z] \<Longrightarrow>
  (a = x \<and> b = y \<and> c = z) \<or>
  (a = x \<and> b = z \<and> c = y) \<or>
  (a = y \<and> b = x \<and> c = z) \<or>
  (a = y \<and> b = z \<and> c = x) \<or>
  (a = z \<and> b = x \<and> c = y) \<or>
  (a = z \<and> b = y \<and> c = x)"
  by (metis distinct.simps(2) distinct_length_2_or_more empty_set list.simps(15))

lemma distinct_sorted_set_3_helper:
  assumes "distinct [a, b, c]" and "sorted (map fst [a, b, c])"
    and "set [a, b, c] = {x, y, z}"
    and "fst x < fst y" and "fst y < fst z"
  shows "a = x \<and> b = y \<and> c = z"
  using assms by clarsimp (metis (no_types, lifting) assms(1) distinct.simps(2) empty_set insert_iff less_imp_not_less less_le_trans list.simps(15))

lemma distinct_sorted_set_3:
  assumes "distinct xs" and "sorted (map fst xs)"
    and "set xs = {x, y, z}"
    and "fst x < fst y" and "fst y < fst z"
  shows "xs = [x, y, z]"
  by (metis assms distinct_set_length3 distinct_sorted_set_3_helper leD less_imp_le)
      
lemma no_interleaving_3:
  assumes 1: "list_spec op_list"
    and "x = (xid, None)"
    and "y = (yid, Some xid)"
    and "z = (zid, None)"
    and "set op_list = {x, y, z}"
    and "xid \<noteq> zid"
  shows "(list_spec.list_order op_list xid yid \<and> list_spec.list_order op_list yid zid) \<or>
        (list_spec.list_order op_list zid xid \<and> list_spec.list_order op_list xid yid)"
  using assms
  apply(subgoal_tac "yid > xid")
   prefer 2
  using list_spec.ref_older apply force
  apply(subgoal_tac "op_list = [x,y,z] \<or> op_list = [x,z,y] \<or> op_list = [z,x,y]")
   prefer 2
   apply(subgoal_tac "sorted (map fst op_list)")
    prefer 2
    apply(simp add: list_spec.sorted_oids)
   apply(subgoal_tac "distinct op_list")
  prefer 2
  using list_distinct apply(simp add: distinct_fst list_spec_def)
   apply(case_tac "xid < zid")
    apply(case_tac "yid < zid")
     apply(rule disjI1)
     apply(rule distinct_sorted_set_3; simp)
    apply(rule disjI2, rule disjI1)
    apply(rule distinct_sorted_set_3; simp)
     apply(force)
    apply(metis (no_types, lifting) insertI1 insert_commute less_imp_neq list_spec_def map_of_SomeD map_of_is_SomeI neqE)
   apply(rule disjI2, rule disjI2)
   apply(rule distinct_sorted_set_3; simp)
    apply force
  defer
   apply(erule disjE)
    apply(rule disjI2, rule conjI)
    prefer 2
    apply(unfold list_spec.list_order_def[OF 1])
     apply(rule_tac x="[zid]" in exI, rule_tac x="[]" in exI, rule_tac x="[]" in exI)
    apply(unfold list_spec.ins_list_def[OF 1])
    apply(unfold interp_list_def, clarsimp)
   apply(rule_tac x="[]" in exI, rule_tac x="[]" in exI, rule_tac x="[yid]" in exI)
   apply clarsimp
  apply(erule disjE)
   apply(rule disjI2, rule conjI)
    apply(rule_tac x="[]" in exI, rule_tac x="[]" in exI, rule_tac x="[yid]" in exI)
    apply clarsimp
   apply(rule_tac x="[zid]" in exI, rule_tac x="[]" in exI, rule_tac x="[]" in exI)
   apply clarsimp
  apply(rule disjI1, rule conjI)
   apply(rule_tac x="[]" in exI, rule_tac x="[]" in exI, rule_tac x="[zid]" in exI)
   apply clarsimp
  apply(rule_tac x="[xid]" in exI, rule_tac x="[]" in exI, rule_tac x="[]" in exI)
  apply clarsimp
  done

lemma list_spec_downward_closed:
  assumes "list_spec A"
    and "set B \<subseteq> set A"
    and "sorted (map fst B)" and "distinct B"
  shows "list_spec B"
  using assms
  apply (induct rule: length_induct)
  apply (case_tac xs)
   apply clarsimp
  apply (erule_tac x=list in allE)
  apply clarsimp
  apply (subgoal_tac "sorted (map fst list)")
   apply clarsimp
   apply (clarsimp simp: list_spec_def)
   apply (metis map_of_SomeD map_of_is_SomeI subsetCE)
  using sorted_Cons by blast

lemma distinct_remove1:
  assumes "set xs = set ys \<union> {x}"
    and "distinct (x#ys)" and "distinct xs"
  shows "set (remove1 x xs) = set ys"
  using assms apply (induct xs arbitrary: x ys; clarsimp simp: insert_ident)
  by (metis Diff_insert_absorb insert_Diff_if singletonD)

lemma interp_list_fail:
  assumes "set ops = {(xid, Some a), (yid, Some xid), (zid, Some a)}"
    and "list_spec ops"
    and "xid \<noteq> zid"
    and "yid \<noteq> zid"
  shows "set (interp_list ops) = {}"
  using assms
  apply(clarsimp simp add: interp_list_def)
  apply(subgoal_tac "\<exists>x y z. ops = [x, y, z]")
   apply clarsimp
   apply(subgoal_tac "aa = xid \<or> aa = yid \<or> aa = zid")
    apply(subgoal_tac "aaa = xid \<or> aaa = yid \<or> aaa = zid")
     apply(subgoal_tac "ab = xid \<or> ab = yid \<or> ab = zid")
      apply(erule disjE)+
         apply clarsimp
  using list_spec.distinct_oids apply fastforce
        apply(erule disjE)+
         apply clarsimp
  using list_spec.distinct_oids apply fastforce
  using list_spec.distinct_oids apply fastforce
       apply(erule disjE)+
  using list_spec.distinct_oids apply fastforce
  using list_spec.distinct_oids apply fastforce
       apply(erule disjE)+
  using list_spec.distinct_oids apply fastforce
        apply clarsimp
        apply(subgoal_tac "(xid, b) = (xid, Some a) \<and> (yid, ba) = (yid, Some xid) \<and> (zid, bb) = (zid, Some a)")
         apply clarsimp
        apply(metis empty_set insert_subset list.simps(15) list_spec.distinct_oids map_of_is_SomeI option.inject subsetI)
       apply(erule disjE)+
        apply clarsimp
        apply(subgoal_tac "(xid, b) = (xid, Some a) \<and> (zid, ba) = (zid, Some a) \<and> (yid, bb) = (yid, Some xid)")
             apply clarsimp
        apply(metis assms(1) insert_iff list_spec.distinct_oids map_of_is_SomeI option.inject)
    using list_spec.distinct_oids apply fastforce
        apply(erule disjE)+
    using list_spec.distinct_oids apply fastforce
    using list_spec.distinct_oids apply fastforce
         apply(erule disjE)+
    using list_spec.distinct_oids apply fastforce
      apply clarsimp
                apply(subgoal_tac "(yid, b) = (yid, Some xid) \<and> (zid, bb) = (zid, Some a) \<and> (xid, ba) = (xid, Some a)")
             apply clarsimp
          apply(metis assms(1) insert_iff list_spec.distinct_oids map_of_is_SomeI option.inject)
         apply(erule disjE)
          apply clarsimp
          apply(subgoal_tac "(yid, bb) = (yid, Some xid) \<and> (zid, b) = (zid, Some a) \<and> (xid, ba) = (xid, Some a)")
           apply clarsimp
          apply(metis assms(1) insert_iff list_spec.distinct_oids map_of_is_SomeI option.inject)
    using list_spec.distinct_oids apply fastforce
        apply(erule disjE)+
    using list_spec.distinct_oids apply fastforce
          apply clarsimp
          apply(subgoal_tac "(yid, b) = (yid, Some xid) \<and> (zid, ba) = (zid, Some a) \<and> (xid, bb) = (xid, Some a)")
                 apply clarsimp
          apply(metis assms(1) insert_iff list_spec.distinct_oids map_of_is_SomeI option.inject)
         apply(erule disjE)+
          apply clarsimp
          apply(subgoal_tac "(yid, ba) = (yid, Some xid) \<and> (zid, b) = (zid, Some a) \<and> (xid, bb) = (xid, Some a)")
                       apply clarsimp
          apply(metis assms(1) insert_iff list_spec.distinct_oids map_of_is_SomeI option.inject)
    using list_spec.distinct_oids apply fastforce
        apply(erule disjE)+
    using list_spec.distinct_oids apply fastforce
    using list_spec.distinct_oids apply fastforce
         apply(erule disjE)+
    using list_spec.distinct_oids apply fastforce
    using list_spec.distinct_oids apply fastforce
        apply(erule disjE)+
    using list_spec.distinct_oids apply fastforce
    using list_spec.distinct_oids apply fastforce
    using list_spec.distinct_oids apply fastforce
       apply blast
      apply (smt insert_absorb insert_iff insert_not_empty prod.inject)
     apply (smt doubleton_eq_iff insertI1 insert_absorb insert_iff old.prod.inject)
    apply (rule_tac x="(xid, Some a)" and y="(yid, Some xid)" and z="(zid, Some a)" in distinct_set_length3)
        defer
        apply clarsimp
    using list_spec.distinct_oids apply (simp add: list_spec.ref_older neq_iff)
    using list_spec.distinct_oids apply (simp add: list_spec.ref_older neq_iff)
    using list_spec.distinct_oids apply (simp add: list_spec.ref_older neq_iff)
     apply clarsimp
    using list_spec.distinct_oids distinct_fst by auto


lemma ins_list_empty[simp]:
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

lemma ins_list_missing_ref:
  assumes "list_spec ops"
    and "\<And>r. (a, r) \<notin> set ops"
    and "(xid, Some a) \<in> set ops"
  shows "xid \<notin> set (list_spec.ins_list ops)"
  using assms
  apply(induction ops rule: List.rev_induct)
   apply clarsimp
  apply(case_tac "(xid, Some a) = x")
   apply clarsimp
   apply(subgoal_tac "list_spec.ins_list (xs @ [(xid, Some a)]) = insert_spec (list_spec.ins_list xs) (xid, Some a)") prefer 2
    apply (metis interp_list_tail_unfold list_spec.ins_list_def list_spec_rm_last)
  apply clarsimp
   apply(subgoal_tac "a \<notin> set (map fst xs)") prefer 2
  apply clarsimp
   apply(subgoal_tac "a \<notin> set (list_spec.ins_list xs)") prefer 2
    apply clarsimp
    apply (metis list_oid_subset list_spec_rm_last set_map subsetCE)
   apply(metis insert_spec_nonex interp_list_op_ids last_op_greatest list_greater_non_memb list_spec.ins_list_def list_spec_rm_last subsetCE)
  apply(unfold list_spec.ins_list_def)
  apply(erule meta_impE)
   apply auto[1]
  apply(erule meta_impE)
   apply simp
  apply(erule meta_impE)
   apply clarsimp
  apply (subgoal_tac "list_spec xs") prefer 2
  apply blast
  apply (frule ins_list_set_eq_disj2)
  apply (clarsimp simp: list_spec.ins_list_def)
  by (metis fst_conv image_eqI insert_iff last_op_greatest list_greater_non_memb set_map)

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

lemma no_interleaving:
  assumes "list_spec ops_before" and "list_spec ops_after"
    and "set ops_after = set ops_before \<union> {x,y,z}"
    and "x = (xid, ref)"
    and "y = (yid, Some xid)"
    and "z = (zid, ref)"
    and "xid \<noteq> yid" and "yid \<noteq> zid" and "zid \<noteq> xid"
    and "xid \<notin> set (map fst ops_before)"
    and "yid \<notin> set (map fst ops_before)"
    and "zid \<notin> set (map fst ops_before)"
  shows "((list_spec.list_order ops_after xid yid \<and> list_spec.list_order ops_after yid zid) \<or>
        (list_spec.list_order ops_after zid xid \<and> list_spec.list_order ops_after xid yid)) \<or>
        (xid \<notin> set (list_spec.ins_list ops_after) \<and> yid \<notin> set (list_spec.ins_list ops_after) \<and>
          zid \<notin> set (list_spec.ins_list ops_after))"
  using assms
  apply(cases "ref")
   defer
   apply(case_tac "\<exists>r. (a, r) \<in> set ops_before") prefer 2
    apply(intro disjI2 conjI)
      apply(rule_tac a=a in ins_list_missing_ref)
        apply force
       apply(subgoal_tac "a \<noteq> xid \<and> a \<noteq> yid \<and> a \<noteq> zid")
        apply force
  apply(subgoal_tac "a < xid \<and> a < zid \<and> xid < yid") prefer 2
        apply(simp add: list_spec_def)
       apply force
      apply force
     apply(subgoal_tac "\<exists>pre suf. ops_after = pre@[(yid, Some xid)]@suf")
  apply(elim exE conjE)
     apply(rule_tac xs=pre and ys=suf and ref=xid in list_spec_irrelevant_operation)
        apply force
       apply assumption
      apply(rule_tac a=a in ins_list_missing_ref)
        apply clarsimp
        apply (metis UnI1 distinct_append list_spec_def map_append set_append sorted_append)
  apply(subgoal_tac "a < xid \<and> a < zid \<and> xid < yid") prefer 2
        apply (simp add: list_spec.ref_older)
       apply clarsimp
       apply(subgoal_tac "set pre \<subseteq> set ops_before")
        apply force
  apply(subgoal_tac "set ops_before = set ops_after - {x, y, z}")
        apply clarsimp
        apply fastforce
       apply(metis (no_types, lifting) Diff_cancel Diff_empty Diff_insert0 Un_Diff Un_empty_right assms(3) fst_conv image_eqI)
  apply(subgoal_tac "xid < yid") prefer 2
       apply (simp add: list_spec.ref_older)
      apply(subgoal_tac "\<And>i. i \<in> set (map fst suf) \<Longrightarrow> yid < i")
       apply(metis UnE Un_insert_right append_Cons fst_conv image_eqI insertI1 not_less_iff_gr_or_eq self_append_conv2 set_ConsD set_append set_map)
      apply clarsimp
      apply(subgoal_tac "sorted (map fst ops_after)")
  apply (metis (no_types, lifting) distinct.simps(2) distinct_append fst_conv image_eqI leD list.set_map list.simps(9) list_spec.distinct_oids map_append not_less_iff_gr_or_eq sorted_Cons sorted_append)
  using list_spec.sorted_oids apply blast
     apply (metis Un_insert_right insert_iff list_set_memb)
      apply(rule_tac a=a in ins_list_missing_ref)
        apply force
       apply(subgoal_tac "a \<noteq> xid \<and> a \<noteq> yid \<and> a \<noteq> zid")
        apply force
  apply(subgoal_tac "a < xid \<and> a < zid \<and> xid < yid") prefer 2
        apply(simp add: list_spec_def)
       apply force
    apply force
   apply(elim exE)
   apply(subgoal_tac "\<exists>pre suf. ops_after = pre@[(a, r)]@suf") prefer 2
    apply(metis (no_types, lifting) Un_insert_left Un_insert_right insert_subset list_set_memb mk_disjoint_insert subset_insertI)
   apply(elim exE)
   apply(case_tac "a \<in> set (list_spec.ins_list (pre@[(a, r)]))") prefer 2
    apply(subgoal_tac "x \<in> set suf \<and> y \<in> set suf \<and> z \<in> set suf") prefer 2
     apply(subgoal_tac "a < xid \<and> a < zid \<and> xid < yid") prefer 2
      apply(simp add: list_spec_def)
  using assms(2) list_spec.ref_older apply fastforce
apply(subgoal_tac "sorted (map fst (pre @ [(a, r)] @ suf))")
     apply(subgoal_tac "\<And>i. i \<in> set (map fst pre) \<Longrightarrow> i < a")
      apply(intro conjI)
  apply clarsimp
         apply (metis (no_types, lifting) UnE fst_conv image_eqI insert_iff leD list.set_intros(1) list.set_map sorted_append)
  apply(subgoal_tac "(yid, Some xid) \<notin> set pre")
  apply clarsimp
         apply (metis (no_types, lifting) Un_iff insertI1 insert_commute insert_iff not_less_iff_gr_or_eq prod.inject)
        apply (metis fst_conv image_eqI less_imp_not_less less_trans set_map)
  apply clarsimp
       apply (metis UnE fst_conv image_eqI insert_iff insert_subset not_less_iff_gr_or_eq subset_insertI)
      apply clarsimp
      apply(subst (asm) sorted_append, clarsimp)
      apply(erule_tac x="(aa, b)" in ballE, clarsimp)
       apply(subgoal_tac "aa \<noteq> a")
        apply force
       apply(metis Un_iff Un_insert_right disjoint_insert(1) distinct_append distinct_append distinct_fst insertI1 list.simps(15) list_spec.distinct_oids map_append map_of_SomeD map_of_is_SomeI set_append sup.left_idem)
  apply force
  using list_spec_def apply blast
    apply(elim conjE)
    apply(intro disjI2 conjI)
      apply(subgoal_tac "\<exists>suf1 suf2. suf = suf1 @ [x] @ suf2", erule exE, erule exE)
       apply(subgoal_tac "a \<notin> set (list_spec.ins_list (pre @ [(a, r)] @ suf1))")
        apply(rule_tac xs="pre@[(a, r)]@suf1" and ys="suf2" and ref="a" in list_spec_irrelevant_operation, simp)
         apply clarsimp
        apply simp
       apply clarsimp
       apply(subgoal_tac "list_spec ((pre @ [(a, r)]) @ suf1)")
        apply(frule ins_list_set_eq_disj2_general) back
        apply clarsimp
        apply(subgoal_tac "\<And>i. i \<in> set (map fst suf1) \<Longrightarrow> a < i")
         apply(metis less_irrefl list.set_map subsetCE)
        apply(subgoal_tac "sorted (map fst (pre @ [(a, r)] @ suf1))")
         apply clarsimp
         apply (metis distinct_append distinct_set_notin fst_conv list.set_map list.simps(9) list_spec.distinct_oids map_append subsetCE)
        apply(metis Cons_eq_appendI list_spec.sorted_oids self_append_conv2)
       apply(subgoal_tac "list_spec (((pre @ [(a, r)]) @ suf1) @ ((xid, Some a) # suf2))")
        apply (metis Un_iff distinct_append list_spec_def map_append set_append sorted_append)
       apply force
      apply (meson list_set_memb)
     apply(subgoal_tac "\<exists>suf1 suf2. suf = suf1@[(yid, Some xid)]@suf2") prefer 2
      apply(meson list_set_memb)
  apply(elim exE)
     apply(rule_tac xs="pre@[(a, r)]@suf1" and ys=suf2 and ref=xid in list_spec_irrelevant_operation)
       apply simp
      apply force
  apply (subgoal_tac "x \<in> set suf1")
     apply(subgoal_tac "\<exists>suf1' suf2'. suf1 = suf1'@[(xid, Some a)]@suf2'") prefer 2
  apply (meson list_set_memb)
  apply(elim exE)
     apply(rule_tac xs="pre@[(a, r)]@suf1'" and ys="suf2'" and ref="a" in list_spec_irrelevant_operation)
  apply clarsimp
  apply(subgoal_tac "list_spec ((pre @ (a, r) # suf1' @ (xid, Some a) # suf2') @ ((yid, Some xid) # suf2))")
        apply (metis Un_iff distinct_append list_spec_def map_append set_append sorted_append)
        apply force
       apply force
  apply(subgoal_tac "list_spec ((pre @ [(a, r)]) @ suf1')")
       apply(frule ins_list_set_eq_disj2_general)
       apply (elim exE conjE)
  apply clarsimp
        apply(subgoal_tac "\<And>i. i \<in> set (map fst suf1') \<Longrightarrow> a < i")
         apply(metis less_irrefl list.set_map subsetCE)
        apply(subgoal_tac "sorted (map fst (pre @ [(a, r)] @ suf1'))")
         apply clarsimp
         apply (metis distinct_append distinct_set_notin fst_conv list.set_map list.simps(9) list_spec.distinct_oids map_append subsetCE)
       apply(metis Cons_eq_appendI list_spec.sorted_oids self_append_conv2)
      apply(subgoal_tac "list_spec ((pre @ (a, r) # suf1') @ ((xid, Some a) # suf2') @ ((yid, Some xid) # suf2))")
  using list_spec_appendD apply (metis (full_types) append_Cons append_eq_append_conv2 self_append_conv)
      apply force
     apply (subgoal_tac "xid < yid") prefer 2
      apply (simp add: list_spec_def)
     apply(subgoal_tac "\<And>i. i \<in> set (map fst suf2) \<Longrightarrow> yid < i")
  apply (metis UnE append_Cons fst_conv image_eqI less_imp_not_less list.set_map self_append_conv2 set_ConsD set_append)
        apply(subgoal_tac "sorted (map fst (pre @ [(a, r)] @ suf1 @ [y] @ suf2))")
         apply clarsimp
  apply (metis (no_types, lifting) distinct.simps(2) distinct_append fst_conv image_insert insertI1 leD list.set_map list.simps(9) list_spec.distinct_oids map_append mk_disjoint_insert not_less_iff_gr_or_eq sorted_Cons sorted_append)
  using list_spec_def apply blast
    apply(subgoal_tac "\<exists>suf1 suf2. suf = suf1 @ [z] @ suf2") prefer 2
     apply (meson list_set_memb)
    apply(elim exE)
    apply(rule_tac xs="pre@[(a, r)]@suf1" and ys="suf2" and ref="a" in list_spec_irrelevant_operation)
      apply simp
  apply force
   apply(subgoal_tac "list_spec ((pre @ [(a, r)]) @ suf1)")
       apply(frule ins_list_set_eq_disj2_general)
       apply (elim exE conjE)
  apply clarsimp
        apply(subgoal_tac "\<And>i. i \<in> set (map fst suf1) \<Longrightarrow> a < i")
         apply(metis less_irrefl list.set_map subsetCE)
        apply(subgoal_tac "sorted (map fst (pre @ [(a, r)] @ suf1))")
         apply clarsimp
         apply (metis distinct_append distinct_set_notin fst_conv list.set_map list.simps(9) list_spec.distinct_oids map_append subsetCE)
     apply(metis Cons_eq_appendI list_spec.sorted_oids self_append_conv2)
  using list_spec_appendD apply(metis append_assoc)
  defer
   apply(case_tac "xid < zid")
    apply(rule disjI1, rule disjI2, rule conjI)
     
(*
     prefer 3
     apply(case_tac "xid < zid")
      apply(case_tac "yid < zid")
       apply(subgoal_tac "xid < yid") prefer 2
        apply (metis Un_insert_left insertI1 list_spec_def sup.commute)

       apply(subgoal_tac "\<exists>suf1 suf2 suf3. suf = suf1@[x]@suf2@[z]@suf3", elim exE)


        apply(rule disjI1, rule disjI2, rule conjI)
         apply (subst list_spec.list_order_def)
          apply simp
  apply (subgoal_tac "\<exists>xs ys. list_spec.ins_list (pre @ [(a, r)]) = xs @ [a] @ ys") prefer 2
  apply (meson list_set_memb)
         apply (elim exE)
         apply (rule_tac x="xs@[a]" in exI)
         apply (rule_tac x="[yid]" in exI)
         apply (rule_tac x=ys in exI)
         apply(clarsimp simp add: list_spec.ins_list_def interp_list_def)
  find_theorems "interp_list"




       apply(subgoal_tac "\<exists>suf1 suf2. suf = suf1@[x]@suf2", erule exE, erule exE)
        apply(subgoal_tac "list_spec.list_order (pre @ (a, r) # suf1 @ [(xid, Some a)]) a xid")
*)
end
