theory Move
  imports OpSet
begin

datatype 'oid tree_op =
  Assign "'oid" "string" "'oid" "'oid set"

fun tree_op_deps :: "'oid tree_op \<Rightarrow> 'oid set" where
  "tree_op_deps (Assign obj key val prev) = {obj, val} \<union> prev"

definition tree_spec_ops :: "('oid::{linorder} \<times> 'oid tree_op) list \<Rightarrow> bool" where
  "tree_spec_ops list \<equiv> spec_ops list tree_op_deps"

definition tree_ops :: "('oid::{linorder} \<times> 'oid tree_op) list \<Rightarrow> bool" where
  "tree_ops list \<equiv> crdt_ops list tree_op_deps"

locale tree_opset = opset opset tree_op_deps
  for opset :: "('oid::{linorder} \<times> 'oid tree_op) set"

inductive ancestor :: "('oid \<times> 'oid \<times> string \<times> 'oid) set \<Rightarrow> 'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>(oid, obj, key, val) \<in> E\<rbrakk> \<Longrightarrow> ancestor E obj val" |
  "\<lbrakk>(oid, obj, key, val) \<in> E; ancestor E anc obj\<rbrakk> \<Longrightarrow> ancestor E anc val"

fun tree_spec :: "('oid \<times> 'oid \<times> string \<times> 'oid) set \<Rightarrow> ('oid \<times> 'oid tree_op) \<Rightarrow> ('oid \<times> 'oid \<times> string \<times> 'oid) set" where
  "tree_spec E (oid, Assign obj key val prev) = (
     if ancestor E val obj then E else
       { e \<in> E. fst e \<notin> prev \<and> snd (snd (snd e)) \<noteq> val } \<union>
       { (oid, obj, key, val) })"

definition interp_tree :: "('oid \<times> 'oid tree_op) list \<Rightarrow> ('oid \<times> 'oid \<times> string \<times> 'oid) set" where
  "interp_tree ops \<equiv> foldl tree_spec {} ops"

(*fun cmp_pair :: "('oid::{linorder} \<times> 'oid tree_op) \<Rightarrow> ('oid \<times> 'oid tree_op) \<Rightarrow> bool" where
  "cmp_pair (id1, op1) (id2, op2) = (id1 < id2)"

fun sorted_ops :: "('oid::{linorder} \<times> 'oid tree_op) set \<Rightarrow> ('oid \<times> 'oid tree_op) list" where
  "sorted_ops ops = List.linorder.sorted_list_of_set cmp_pair ops"

fun interp_ops :: "('oid::{linorder} \<times> 'oid tree_op) set \<Rightarrow> ('oid \<times> 'oid \<times> string \<times> 'oid) set" where
  "interp_ops ops = foldl tree_spec {} (sorted_ops ops)"*)

fun sorted_oplist :: "('oid::{linorder} \<times> 'oid tree_op) list \<Rightarrow> ('oid \<times> 'oid tree_op) \<Rightarrow> ('oid \<times> 'oid tree_op) list" where
  "sorted_oplist ((i1, op1) # list) (i2, op2) =
     (if i1 < i2
      then (i1, op1) # (sorted_oplist list (i2, op2))
      else (i2, op2) # (i1, op1) # list)" |
  "sorted_oplist [] oper = [oper]"

lemma sorted_oplist_insert:
  shows "\<exists>as bs. xs = as @ bs \<and> sorted_oplist xs oper = as @ [oper] @ bs"
proof(induction xs, simp)
  case (Cons x xs)
  obtain i1 op1 where "x = (i1, op1)" by fastforce
  obtain i2 op2 where "oper = (i2, op2)" by fastforce
  show "\<exists>as bs. x # xs = as @ bs \<and> sorted_oplist (x # xs) oper = as @ [oper] @ bs"
  proof(cases "i1 < i2")
    case True
    hence "sorted_oplist (x # xs) oper = x # (sorted_oplist xs oper)"
      by (simp add: \<open>oper = (i2, op2)\<close> \<open>x = (i1, op1)\<close>)
    moreover obtain as bs where "xs = as @ bs \<and> sorted_oplist xs oper = as @ [oper] @ bs"
      using Cons.IH by blast
    ultimately have "x # xs = (x # as) @ bs \<and> sorted_oplist (x # xs) oper = (x # as) @ [oper] @ bs"
      by auto
    then show ?thesis by blast
  next
    case False
    hence "sorted_oplist (x # xs) oper = oper # x # xs"
      by (simp add: \<open>oper = (i2, op2)\<close> \<open>x = (i1, op1)\<close>)
    hence "x # xs = [] @ (x # xs) \<and> sorted_oplist (x # xs) oper = [] @ [oper] @ (x # xs)"
      by simp
    then show ?thesis by blast
  qed
qed

lemma sorted_oplist_set:
  shows "set (foldl sorted_oplist [] ops) = set ops"
proof(induction ops rule: List.rev_induct, simp)
  case (snoc x xs)
  have "foldl sorted_oplist [] (xs @ [x]) = sorted_oplist (foldl sorted_oplist [] xs) x"
    by simp
  then obtain as bs where "foldl sorted_oplist [] xs = as @ bs \<and>
                           sorted_oplist (as @ bs) x = as @ [x] @ bs"
    by (metis sorted_oplist_insert)
  then show "set (foldl sorted_oplist [] (xs @ [x])) = set (xs @ [x])"
    using snoc.IH by auto
qed

lemma
  assumes "tree_ops ops"
  shows "tree_spec_ops (foldl sorted_oplist [] ops)"
  oops


end
