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

fun sorted_oplist :: "('oid::{linorder} \<times> 'oid tree_op) list \<Rightarrow> ('oid \<times> 'oid tree_op) \<Rightarrow> ('oid \<times> 'oid tree_op) list" where
  "sorted_oplist ((i1, op1) # list) (i2, op2) =
     (if i1 < i2
      then (i1, op1) # (sorted_oplist list (i2, op2))
      else (i2, op2) # (i1, op1) # list)" |
  "sorted_oplist [] oper = [oper]"

lemma sorted_oplist_insert:
  shows "\<exists>as bs. xs = as @ bs \<and> sorted_oplist xs oper = as @ [oper] @ bs \<and>
         (\<forall>a \<in> set as. fst a < fst oper) \<and> (bs \<noteq> [] \<longrightarrow> fst oper \<le> fst (hd bs))"
proof(induction xs, simp)
  case (Cons x xs)
  obtain i1 op1 where "x = (i1, op1)" by fastforce
  obtain i2 op2 where "oper = (i2, op2)" by fastforce
  show "\<exists>as bs. x # xs = as @ bs \<and> sorted_oplist (x # xs) oper = as @ [oper] @ bs \<and>
         (\<forall>a \<in> set as. fst a < fst oper) \<and> (bs \<noteq> [] \<longrightarrow> fst oper \<le> fst (hd bs))"
  proof(cases "i1 < i2")
    case True
    moreover from this have "sorted_oplist (x # xs) oper = x # (sorted_oplist xs oper)"
      by (simp add: \<open>oper = (i2, op2)\<close> \<open>x = (i1, op1)\<close>)
    moreover obtain as bs where "xs = as @ bs \<and> sorted_oplist xs oper = as @ [oper] @ bs \<and>
         (\<forall>a \<in> set as. fst a < fst oper) \<and> (bs \<noteq> [] \<longrightarrow> fst oper \<le> fst (hd bs))"
      using Cons.IH by blast
    ultimately have "x # xs = (x # as) @ bs \<and> sorted_oplist (x # xs) oper = (x # as) @ [oper] @ bs \<and>
         (\<forall>a \<in> set (x # as). fst a < fst oper) \<and> (bs \<noteq> [] \<longrightarrow> fst oper \<le> fst (hd bs))"
      using \<open>oper = (i2, op2)\<close> \<open>x = (i1, op1)\<close> by auto
    then show ?thesis by blast
  next
    case False
    moreover from this have "sorted_oplist (x # xs) oper = oper # x # xs"
      by (simp add: \<open>oper = (i2, op2)\<close> \<open>x = (i1, op1)\<close>)
    ultimately have "x # xs = [] @ (x # xs) \<and> sorted_oplist (x # xs) oper = [] @ [oper] @ (x # xs) \<and>
         (\<forall>a \<in> set []. fst a < fst oper) \<and> (x # xs \<noteq> [] \<longrightarrow> fst oper \<le> fst (hd (x # xs)))"
      using \<open>oper = (i2, op2)\<close> \<open>x = (i1, op1)\<close> by auto
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

lemma sorted_oplist_sorted_1:
  assumes "sorted (map fst xs)"
  shows "sorted (map fst (sorted_oplist xs oper))"
using assms proof(induction xs, simp)
  case (Cons x xs)
  hence IH: "sorted (map fst (sorted_oplist xs oper))"
    by (simp add: sorted_Cons)
  obtain i1 op1 where "x = (i1, op1)" by fastforce
  obtain i2 op2 where "oper = (i2, op2)" by fastforce
  show "sorted (map fst (sorted_oplist (x # xs) oper))"
  proof(cases "i1 < i2")
    case True
    hence "sorted_oplist (x # xs) oper = x # (sorted_oplist xs oper)"
      by (simp add: \<open>oper = (i2, op2)\<close> \<open>x = (i1, op1)\<close>)
    moreover have "\<And>i. i \<in> set (map fst (sorted_oplist xs oper)) \<Longrightarrow> i1 \<le> i"
    proof -
      fix i
      assume i_asm: "i \<in> set (map fst (sorted_oplist xs oper))"
      obtain as bs where "xs = as @ bs \<and> sorted_oplist xs oper = as @ [oper] @ bs"
        using sorted_oplist_insert by blast
      hence "i \<in> set (map fst xs) \<or> i = i2"
        using i_asm \<open>oper = (i2, op2)\<close> by fastforce
      then show "i1 \<le> i"
        by (metis Cons.prems True \<open>x = (i1, op1)\<close> fst_conv leD le_cases list.simps(9) sorted_Cons)
    qed
    ultimately show "sorted (map fst (sorted_oplist (x # xs) oper))"
      by (metis IH \<open>x = (i1, op1)\<close> fst_conv list.simps(9) sorted.simps)
  next
    case False
    moreover from this have "sorted_oplist (x # xs) oper = oper # x # xs"
      by (simp add: \<open>oper = (i2, op2)\<close> \<open>x = (i1, op1)\<close>)
    ultimately show "sorted (map fst (sorted_oplist (x # xs) oper))"
      using Cons.prems \<open>oper = (i2, op2)\<close> \<open>x = (i1, op1)\<close> by auto
  qed
qed

lemma sorted_oplist_sorted:
  shows "sorted (map fst (foldl sorted_oplist [] ops))"
by (induction ops rule: List.rev_induct, auto simp add: sorted_oplist_sorted_1)

lemma sorted_oplist_commute_base:
  assumes "i1 < i2"
  shows "sorted_oplist (sorted_oplist xs (i1, op1)) (i2, op2) =
         sorted_oplist (sorted_oplist xs (i2, op2)) (i1, op1)"
proof(induction xs)
  case Nil
  then show ?case using assms by auto
next
  case (Cons a xs)
  obtain ia opa where "a = (ia, opa)" by fastforce
  consider (lt_i1) "ia < i1" | (i1_i2) "ia \<ge> i1 \<and> ia < i2" | (gt_i2) "ia \<ge> i2"
    using le_less_linear by blast
  then show ?case
  proof(cases)
    case lt_i1
    then show ?thesis using \<open>a = (ia, opa)\<close> Cons.IH by auto
  next
    case i1_i2
    then show ?thesis using \<open>a = (ia, opa)\<close> assms by auto
  next
    case gt_i2
    then show ?thesis using \<open>a = (ia, opa)\<close> assms dual_order.asym by auto
  qed
qed

lemma sorted_oplist_commute:
  assumes "i1 \<noteq> i2"
  shows "sorted_oplist (sorted_oplist xs (i1, op1)) (i2, op2) =
         sorted_oplist (sorted_oplist xs (i2, op2)) (i1, op1)"
by (metis assms neqE sorted_oplist_commute_base)


end
