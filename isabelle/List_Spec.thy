theory List_Spec
  imports Main
begin

datatype 'oid list_op
  = InsertAfter 'oid
  | Remove 'oid

fun insert_after :: "'oid \<Rightarrow> 'oid \<Rightarrow> 'oid list \<Rightarrow> 'oid list" where
  "insert_after oid ref [] = []" |
  "insert_after oid ref (x#xs) = (if x = ref then x#oid#xs else x # (insert_after oid ref xs))"

fun interp :: "'oid list \<times> 'oid set \<Rightarrow> ('oid \<times> 'oid list_op) \<Rightarrow> 'oid list \<times> 'oid set" where
  "interp (list, tomb) (oid, InsertAfter ref) = (insert_after oid ref list, tomb)" |
  "interp (list, tomb) (oid, Remove      ref) = (list, tomb \<union> {ref})"

definition interp_list :: "('oid \<times> 'oid list_op) list \<Rightarrow> 'oid list \<times> 'oid set" where
  "interp_list ops \<equiv> foldl interp ([], {}) ops"

fun oid_reference :: "'oid list_op \<Rightarrow> 'oid" where
  "oid_reference (InsertAfter ref) = ref" |
  "oid_reference (Remove ref) = ref"
  
locale list_spec =
  fixes op_list :: "('oid::{linorder} \<times> 'oid list_op) list"
  assumes sorted_oids: "sorted (map fst op_list)"
    and distinct_oids: "distinct (map fst op_list)"
    and ref_older: "(oid, oper) \<in> set op_list \<Longrightarrow> oid_reference oper < oid"

context list_spec begin
  
definition op_set :: "('oid::{linorder} \<times> 'oid list_op) set" where
  "op_set \<equiv> set op_list"

definition insertions :: "('oid \<times> 'oid list_op) list" where
  "insertions \<equiv> filter (\<lambda>(_, oper). case oper of InsertAfter x \<Rightarrow> True | _ \<Rightarrow> False ) op_list"

definition ins_list :: "'oid list" where
  "ins_list \<equiv> fst (interp_list op_list)"

definition tombstones :: "'oid set" where
  "tombstones \<equiv> snd (interp_list op_list)"

inductive list_order :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" (infix "\<sqsubset>" 50) where
  "\<lbrakk>ins_list = xs @ [x] @ ys @ [y] @ zs\<rbrakk> \<Longrightarrow> x \<sqsubset> y"

inductive_cases list_order_elim [elim]: "x \<sqsubset> y"

end
  
lemma list_spec_rm_last:
  assumes "list_spec (xs @ [x])"
  shows "list_spec xs"
  using assms apply (clarsimp simp: list_spec_def)
  using sorted_append by blast

lemma insert_after_set:
  assumes "ref \<in> set xs"
  shows "set (insert_after oid ref xs) = set xs \<union> {oid}"
  using assms apply (induct xs, simp)
  by (case_tac "a=ref", simp_all add: insert_commute sup_commute)

lemma insert_after_nonex:
  assumes "ref \<notin> set xs"
  shows "insert_after oid ref xs = xs"
  using assms apply (induct xs, simp)
  by (case_tac "a=ref", simp_all add: insert_commute sup_commute)

lemma list_greater_non_memb:
  fixes oid :: "'oid::{linorder}"
  assumes "\<forall>x \<in> set xs. x < oid"
  shows "oid \<notin> set xs"
  using assms by blast

lemma insert_after_distinct:
  fixes oid :: "'oid::{linorder}"
  assumes "distinct xs"
    and "\<forall>x \<in> set xs. x < oid" and "ref < oid"
  shows "distinct (insert_after oid ref xs)"
  using assms apply (induct xs, simp)
  apply(case_tac "a=ref")
  apply clarsimp
  apply(rule conjI)
  apply(metis list.set_intros(1) list_greater_non_memb set_ConsD)
  using list_greater_non_memb apply blast
  apply(subgoal_tac "a \<noteq> oid")
  apply(subgoal_tac "insert_after oid ref (a # xs) = a # insert_after oid ref xs")
  apply(metis UnE distinct.simps(2) empty_iff insertE insert_after_nonex insert_after_set
    list.set_intros(2))
  apply auto
  done

lemma list_oid_subset:
  assumes "list_spec op_list"
  shows "set (list_spec.ins_list op_list) \<subseteq> set (map fst op_list)"
  using assms apply (induct op_list rule: rev_induct)
  apply(simp add: list_spec.ins_list_def interp_list_def)
  apply(frule list_spec_rm_last, clarsimp)
  apply(case_tac b)
  apply(clarsimp simp add: list_spec.ins_list_def interp_list_def)
  apply(case_tac "x1 \<in> set (list_spec.ins_list xs)")
  apply(metis (no_types, lifting) Pair_inject Un_insert_right contra_subsetD insertE
    insert_after_set interp.simps(1) interp_list_def list_spec.ins_list_def prod.collapse
    sup_bot.comm_neutral)
  apply(simp add: contra_subsetD insert_after_nonex interp_list_def list_spec.ins_list_def)
  apply(metis (no_types, lifting) insert_after_nonex interp.simps(1) prod.collapse subsetCE)
  apply(clarsimp simp add: list_spec.ins_list_def interp_list_def)
  apply(subgoal_tac "x \<in> set (fst (foldl interp ([], {}) xs))", blast)
  apply(metis Pair_inject interp.simps(2) prod.collapse)
  done

lemma last_op_greatest:
  assumes "list_spec (op_list @ [(oid, oper)])"
  shows "\<forall>x \<in> set (map fst op_list). x < oid"
  using assms apply(induct op_list, simp)
  apply(subgoal_tac "sorted (map fst (op_list @ [(oid, oper)]))") prefer 2
  using list_spec.sorted_oids sorted_Cons apply fastforce
  apply(subgoal_tac "list_spec (op_list @ [(oid, oper)])") prefer 2
  apply(simp add: list_spec_def, clarsimp)
  apply(subgoal_tac "\<forall>x \<in> set (map fst op_list @ [oid]). a < x", simp)
  apply(metis (no_types, lifting) distinct.simps(2) dual_order.strict_iff_order
    list.map(1) list.simps(9) list_spec.distinct_oids list_spec.sorted_oids map_append
    prod.sel(1) sorted_Cons)
  done

lemma list_distinct:
  assumes "list_spec op_list"
  shows "distinct (list_spec.ins_list op_list)"
  using assms apply (induct op_list rule: rev_induct)
  apply(simp add: list_spec.ins_list_def interp_list_def)
  apply(frule list_spec_rm_last, clarsimp)
  apply(case_tac b, clarsimp)
  apply(subgoal_tac "\<forall>x\<in>set (list_spec.ins_list xs). x < a") prefer 2
  using last_op_greatest list_oid_subset apply blast
  apply(subgoal_tac "distinct (insert_after a x1 (list_spec.ins_list xs))") prefer 2
  using insert_after_distinct insert_after_nonex apply fastforce
  apply(simp add: list_spec.ins_list_def interp_list_def)
  apply(metis Pair_inject interp.simps(1) prod.collapse)
  apply(simp add: list_spec.ins_list_def interp_list_def)
  apply(metis Pair_inject interp.simps(2) prod.collapse)
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
  using assms apply(induction xs arbitrary: xa xb x, simp)
  apply(case_tac xa; case_tac xb; clarsimp)
  done

lemma list_order_trans:
  assumes "list_spec op_list"
    and "list_spec.list_order op_list x y"
    and "list_spec.list_order op_list y z"
  shows "list_spec.list_order op_list x z"
  using assms apply -
  apply(subgoal_tac "\<exists>ws xs ys zs. list_spec.ins_list op_list = ws@[x]@xs@[y]@ys@[z]@zs")
  apply(metis append.assoc list_spec.list_order.intros)
  apply(erule_tac x=x and y=y in list_spec.list_order_elim, assumption)
  using assms(1) apply -
  apply(erule_tac x=y and y=z in list_spec.list_order_elim, assumption)
  apply(subgoal_tac "distinct (list_spec.ins_list op_list)") prefer 2
  using assms(1) list_distinct apply blast
  apply(subgoal_tac "zs = ysa @ z # zsa") prefer 2
  apply(frule_tac xa="xs @ x # ys" and xb=xsa and x=y and ya=zs
    and yb="ysa @ z # zsa" in distinct_list_split, simp, simp, simp)
  apply(rule_tac x=xs in exI, rule_tac x=ys in exI)
  apply(rule_tac x=ysa in exI, rule_tac x=zsa in exI, simp)
  done

lemma insert_somewhere:
  assumes "ref \<in> set list"
  shows "\<exists>xs ys. list = xs@ys \<and> insert_after oid ref list = xs @ oid # ys"
  using assms apply(induction list, simp)
  apply(case_tac "a=ref")
  apply(rule_tac x="[ref]" in exI, rule_tac x=list in exI, simp)
  apply(subgoal_tac "ref \<in> set list", simp) prefer 2 apply simp
  apply(erule exE)+
  apply(rule_tac x="a#xs" in exI, rule_tac x=ys in exI, force)
  done

lemma insert_first_part:
  assumes "ref \<in> set xs"
  shows "insert_after oid ref (xs @ ys) = (insert_after oid ref xs) @ ys"
  using assms
  apply(induction ys rule: rev_induct, simp, simp)
  apply(induction xs, simp)
  apply(case_tac "a=ref", simp_all)
  done

lemma insert_second_part:
  assumes "ref \<notin> set xs"
    and "ref \<in> set ys"
  shows "insert_after oid ref (xs @ ys) = xs @ (insert_after oid ref ys)"
  using assms
  apply(induction xs, simp, simp)
  apply(subgoal_tac "a \<noteq> ref", blast+)
  done

lemma insert_twice:
  assumes "list_spec (before @ (x1, InsertAfter r1) # after @ [(x2, InsertAfter r2)])"
    and   "list_spec (before @                        after @ [(x2, InsertAfter r2)])"
    and "list_spec.ins_list (before @                        after) = xs @      zs"
    and "list_spec.ins_list (before @ (x1, InsertAfter r1) # after) = xs @ ys @ zs"
  shows "\<exists>xsa ysa zsa.
    list_spec.ins_list (before @                        after @ [(x2, InsertAfter r2)]) = xsa @       zsa \<and>
    list_spec.ins_list (before @ (x1, InsertAfter r1) # after @ [(x2, InsertAfter r2)]) = xsa @ ysa @ zsa"
  using assms apply -
  apply(subgoal_tac "list_spec (before @ after)") prefer 2
  using list_spec_rm_last apply force
  apply(subgoal_tac "list_spec (before @ (x1, InsertAfter r1) # after)") prefer 2
  using list_spec_rm_last apply force
  apply(simp add: list_spec.ins_list_def interp_list_def)
  apply(case_tac "r2 \<in> set xs")
  apply(metis fstI interp.simps(1) prod.collapse insert_first_part)
  apply(case_tac "r2 \<in> set ys")
  apply(rule_tac x=xs in exI)
  apply(rule_tac x="insert_after x2 r2 ys" in exI)
  apply(rule_tac x=zs in exI)
  apply(rule conjI)
  apply(subgoal_tac "r2 \<notin> set zs")
  apply(metis UnE insert_after_nonex interp.simps(1) prod.collapse set_append)
  using assms(4) distinct_append list.simps(15) list_distinct apply force
  apply(metis append_eq_append_conv fstI insert_after_nonex insert_first_part
    insert_second_part insert_somewhere interp.simps(1) not_Cons_self2 prod.collapse)
  apply(case_tac "r2 \<in> set zs")
  apply(rule_tac x=xs in exI)
  apply(rule_tac x=ys in exI)
  apply(rule_tac x="insert_after x2 r2 zs" in exI)
  apply(metis insert_second_part Un_iff fstI interp.simps(1) prod.collapse set_append)
  apply(metis (no_types, lifting) insert_after_nonex UnE interp.simps(1) prod.collapse set_append)
  done

lemma insert_preserves_order:
  assumes "list_spec op_list" and "list_spec rest"
    and "rest = before @ after"
    and "op_list = before @ (oid, InsertAfter ref) # after"
  shows "\<exists>xs ys zs. list_spec.ins_list rest    = xs @      zs \<and>
                    list_spec.ins_list op_list = xs @ ys @ zs"
  using assms
  apply(induction after arbitrary: rest op_list rule: rev_induct)
  apply(case_tac "ref \<in> set (list_spec.ins_list before)")
  apply(subgoal_tac "\<exists>xs zs. list_spec.ins_list rest = xs@zs \<and>
                             list_spec.ins_list op_list = xs@[oid]@zs", blast)
  apply(simp add: list_spec.ins_list_def interp_list_def insert_somewhere)
  (*apply(subgoal_tac "list_spec.ins_list op_list = list_spec.ins_list rest", force)
  apply(simp add: list_spec.ins_list_def interp_list_def insert_after_nonex)
  apply(erule_tac x="before @ xs" in meta_allE)
  apply(erule_tac x="before @ (oid, InsertAfter ref) # xs" in meta_allE)
  apply(subgoal_tac "list_spec (before @ xs)") prefer 2
  apply(metis append_assoc list_spec_rm_last)
  apply(subgoal_tac "list_spec (before @ (oid, InsertAfter ref) # xs)") prefer 2
  apply(metis append_butlast_last_id append_is_Nil_conv butlast.simps(2) butlast_append
    butlast_snoc list.distinct(1) list_spec_rm_last)
  apply clarsimp
  apply(case_tac b, simp add: insert_twice)
  apply clarsimp*)
  oops

lemma
  assumes "list_spec A" and "list_spec B"
    and "set A \<subseteq> set B"
    and "list_spec.list_order A x y"
  shows "list_spec.list_order B x y"
  oops

end
