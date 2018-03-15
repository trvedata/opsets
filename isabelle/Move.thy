theory Move
  imports OpSet
begin

datatype 'oid tree_op =
  Assign "'oid" "string" "'oid" "'oid set"

lemma tree_op_assign:
  assumes "\<And>obj key val prev. x = Assign obj key val prev \<Longrightarrow> P"
  shows "P"
using assms tree_op.exhaust by blast

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
  shows "\<exists>as bs. xs = as @ bs \<and> sorted_oplist xs oper = as @ [oper] @ bs"
proof(induction xs, simp)
  case (Cons x xs)
  obtain i1 op1 where "x = (i1, op1)" by fastforce
  obtain i2 op2 where "oper = (i2, op2)" by fastforce
  show "\<exists>as bs. x # xs = as @ bs \<and> sorted_oplist (x # xs) oper = as @ [oper] @ bs"
  proof(cases "i1 < i2")
    case True
    moreover from this have "sorted_oplist (x # xs) oper = x # (sorted_oplist xs oper)"
      by (simp add: \<open>oper = (i2, op2)\<close> \<open>x = (i1, op1)\<close>)
    moreover obtain as bs where "xs = as @ bs \<and> sorted_oplist xs oper = as @ [oper] @ bs"
      using Cons.IH by blast
    ultimately have "x # xs = (x # as) @ bs \<and> sorted_oplist (x # xs) oper = (x # as) @ [oper] @ bs"
      using \<open>oper = (i2, op2)\<close> \<open>x = (i1, op1)\<close> by auto
    then show ?thesis by blast
  next
    case False
    moreover from this have "sorted_oplist (x # xs) oper = oper # x # xs"
      by (simp add: \<open>oper = (i2, op2)\<close> \<open>x = (i1, op1)\<close>)
    ultimately have "x # xs = [] @ (x # xs) \<and> sorted_oplist (x # xs) oper = [] @ [oper] @ (x # xs)"
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


fun interp_op :: "('oid::{linorder} \<times> 'oid tree_op) list \<times> ('oid \<times> 'oid \<times> string \<times> 'oid) set
   \<Rightarrow> ('oid \<times> 'oid tree_op) \<Rightarrow> ('oid \<times> 'oid tree_op) list \<times> ('oid \<times> 'oid \<times> string \<times> 'oid) set" where
  "interp_op (ops, _) oper = (
      let oplist = sorted_oplist ops oper
      in (oplist, interp_tree oplist))"

lemma interp_op_commute:
  assumes "fst op1 \<noteq> fst op2"
  shows "interp_op (interp_op s op1) op2 = interp_op (interp_op s op2) op1"
proof -
  obtain oplist E where "s = (oplist, E)" by fastforce
  have "fst (interp_op (interp_op s op1) op2) = sorted_oplist (sorted_oplist oplist op1) op2"
    by (metis \<open>s = (oplist, E)\<close> fst_conv interp_op.simps)
  moreover have "fst (interp_op (interp_op s op2) op1) = sorted_oplist (sorted_oplist oplist op2) op1"
    by (metis \<open>s = (oplist, E)\<close> fst_conv interp_op.simps)
  moreover have "sorted_oplist (sorted_oplist oplist op1) op2 = sorted_oplist (sorted_oplist oplist op2) op1"
    by (metis assms prod.collapse sorted_oplist_commute)
  moreover have "snd (interp_op (interp_op s op1) op2) = interp_tree (fst (interp_op (interp_op s op1) op2))"
    by (metis \<open>s = (oplist, E)\<close> calculation(1) interp_op.simps snd_conv)
  ultimately show ?thesis
    by (metis \<open>s = (oplist, E)\<close> interp_op.simps)
qed

(* list of (oid, oper, flag) triples *)

fun tree_spec' :: "('oid \<times> 'oid \<times> string \<times> 'oid) set \<Rightarrow> ('oid \<times> 'oid tree_op \<times> bool) \<Rightarrow> ('oid \<times> 'oid \<times> string \<times> 'oid) set" where
  "tree_spec' E (oid, Assign obj key val prev, valid) = (
     if valid then
       { e \<in> E. fst e \<notin> prev \<and> snd (snd (snd e)) \<noteq> val } \<union>
       { (oid, obj, key, val) }
     else E)"

definition interp_tree' :: "('oid \<times> 'oid tree_op \<times> bool) list \<Rightarrow> ('oid \<times> 'oid \<times> string \<times> 'oid) set" where
  "interp_tree' ops \<equiv> foldl tree_spec' {} ops"

fun append_op :: "('oid::{linorder} \<times> 'oid tree_op) \<Rightarrow> ('oid \<times> 'oid tree_op \<times> bool) list \<Rightarrow>
                  ('oid \<times> 'oid tree_op \<times> bool) list" where
  "append_op (oid, Assign obj key val prev) ops =
     (let valid = \<not> ancestor (interp_tree' ops) val obj
      in ops @ [(oid, Assign obj key val prev, valid)])"

fun reapply_ops :: "('oid::{linorder} \<times> 'oid tree_op \<times> bool) list \<Rightarrow> ('oid \<times> 'oid tree_op \<times> bool) list \<Rightarrow>
                    ('oid \<times> 'oid tree_op \<times> bool) list" where
  "reapply_ops ((oid, oper, flag) # xs) ops = reapply_ops xs (append_op (oid, oper) ops)" |
  "reapply_ops [] ops = ops"

fun add_op :: "('oid::{linorder} \<times> 'oid tree_op) \<Rightarrow> ('oid \<times> 'oid tree_op \<times> bool) list \<Rightarrow>
               ('oid \<times> 'oid tree_op \<times> bool) list \<Rightarrow> ('oid \<times> 'oid tree_op \<times> bool) list" where
  "add_op newop (x # xs) ops =
     (if fst x < fst newop
      then add_op newop xs (ops @ [x])
      else reapply_ops (x # xs) (append_op newop ops))" |
  "add_op newop [] ops = append_op newop ops"

definition add_op1 :: "('oid::{linorder} \<times> 'oid tree_op \<times> bool) list \<Rightarrow> ('oid::{linorder} \<times> 'oid tree_op) \<Rightarrow> ('oid \<times> 'oid tree_op \<times> bool) list" where
  "add_op1 ops newop \<equiv> add_op newop ops []"

lemma add_op_cons:
  shows "map (\<lambda>x. (fst x, fst (snd x))) (add_op (nid, nop) xs [x]) =
    (fst x, fst (snd x)) # map (\<lambda>x. (fst x, fst (snd x))) (add_op (nid, nop) xs [])"
proof(induction xs)
  case Nil
  obtain obj key val prev where "nop = Assign obj key val prev"
    using tree_op.exhaust by blast
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case sorry
qed

lemma append_op_map_fst:
  shows "map fst (append_op (oid, oper) ops) = map fst ops @ [oid]"
proof -
  obtain obj key val prev where "oper = Assign obj key val prev"
    using tree_op.exhaust by blast
  hence "append_op (oid, oper) ops = ops @ [(oid, oper, \<not> ancestor (interp_tree' ops) val obj)]"
    by simp
  thus ?thesis by auto
qed

lemma reapply_ops_last:
  shows "reapply_ops (xs @ [x]) ops = append_op (fst x, fst (snd x)) (reapply_ops xs ops)"
proof(induction xs)
  case Nil
  then show ?case
    by (metis (no_types, lifting) Cons_eq_append_conv prod.collapse reapply_ops.simps(1) reapply_ops.simps(2))
next
  case (Cons a xs)
  hence "reapply_ops ((a # xs) @ [x]) ops =
         reapply_ops (xs @ [x]) (append_op (fst x, fst (snd x)) ops)"
    sorry
  then show ?case sorry
      
qed

lemma reapply_ops_map:
  shows "map fst (reapply_ops xs ops) = map fst (ops @ xs)"
proof(induction xs rule: List.rev_induct, simp)
  case (snoc x xs)
  then show ?case sorry
qed

lemma reapply_ops_map:
  shows "map fst (reapply_ops xs ops) = map fst (ops @ xs)"
proof(induction xs, simp)
  case (Cons a xs)
  have "map fst (reapply_ops (a # xs) ops) =
        map fst (reapply_ops xs (append_op (fst a, fst (snd a)) ops))"
    by (metis prod.collapse reapply_ops.simps(1))
  moreover have "append_op (fst a, fst (snd a)) ops = ops @ [(fst a, fst (snd a), \<not> ancestor (interp_tree' ops) val obj)]"
    sorry
  then show ?case sorry
qed

lemma add_op1_result:
  assumes "ys = map (\<lambda>x. (fst x, fst (snd x))) xs"
  shows "sorted_oplist ys (nid, nop) = map (\<lambda>x. (fst x, fst (snd x))) (add_op1 xs (nid, nop))"
using assms proof(induction xs arbitrary: ys)
  case Nil
  hence "sorted_oplist ys (nid, nop) = [(nid, nop)]"
    by simp
  moreover obtain obj key val prev where "nop = Assign obj key val prev"
    using tree_op.exhaust by blast
  hence "add_op1 [] (nid, nop) = [(nid, nop, \<not> ancestor (interp_tree' []) val obj)]"
    by (simp add: add_op1_def)
  hence "map (\<lambda>x. (fst x, fst (snd x))) (add_op1 [] (nid, nop)) = [(nid, nop)]"
    by simp
  ultimately show ?case by auto
next
  case (Cons x xs)
  obtain xi xo xv where "x = (xi, xo, xv)" by (metis prod.collapse)
  obtain obj key val prev where "nop = Assign obj key val prev"
    using tree_op.exhaust by blast
  show ?case
  proof(cases "xi < nid")
    case True
    then show ?thesis
      by (simp add: Cons.IH Cons.prems \<open>x = (xi, xo, xv)\<close> add_op1_def add_op_cons)
  next
    case False
    hence "sorted_oplist ys (nid, nop) = [(nid, nop)] @ ys"
      using Cons.prems \<open>x = (xi, xo, xv)\<close> by auto
    moreover have "add_op1 (x # xs) (nid, nop) =
         reapply_ops (x # xs) [(nid, nop, \<not> ancestor (interp_tree' []) val obj)]"
      by (simp add: \<open>nop = Assign obj key val prev\<close> \<open>x = (xi, xo, xv)\<close> add_op1_def False)
    then show ?thesis sorry
  qed
qed

lemma add_op1_fold:
  shows "foldl sorted_oplist [] ops = map (\<lambda>x. (fst x, fst (snd x))) (foldl add_op1 [] ops)"
proof(induction ops rule: List.rev_induct, simp)
  case (snoc x xs)
  obtain xid xop where "x = (xid, xop)" by fastforce
  then show ?case
    by (simp add: add_op1_result snoc.IH)
qed

    
lemma interp_equal:
  shows "interp_tree (foldl sorted_oplist [] ops) = interp_tree' (foldl add_op1 [] ops)"
proof(induction ops rule: List.rev_induct)
  case Nil
  then show ?case by (simp add: interp_tree'_def interp_tree_def)
next
  case (snoc x xs)
  obtain oid obj key val prev where "x = (oid, Assign obj key val prev)"
    by (meson prod.simps(1) tree_spec.cases)
  have "foldl sorted_oplist [] (xs @ [x]) = sorted_oplist (foldl sorted_oplist [] xs) x"
    by simp
  have "foldl tree_spec {} (foldl sorted_oplist [] xs) = foldl tree_spec' {} (foldl add_op1 [] xs)"
    using interp_tree'_def interp_tree_def snoc.IH by blast
  then show ?case sorry
qed    

lemma add_op_test:
  assumes "i1 < i2" and "i2 < i3" and "i3 < i4" and "i4 < i5"
    and "o3 = Assign j3 k3 v3 p3"
    and "o4 = Assign j4 k4 v4 p4"
    and "o5 = Assign j5 k5 v5 p5"
  shows "add_op (i3, o3) [(i1, o1, v1), (i2, o2, v2), (i4, o4, v4), (i5, o5, v5)] [] =
         [(i1, o1, v1), (i2, o2, v2), (i3, o3, v3'), (i4, o4, v4'), (i5, o5, v5')] \<and>
         v3' = (\<not> ancestor (interp_tree' [(i1, o1, v1), (i2, o2, v2)]) v3 j3) \<and>
         v4' = (\<not> ancestor (interp_tree' [(i1, o1, v1), (i2, o2, v2), (i3, o3, v3')]) v4 j4) \<and>
         v5' = (\<not> ancestor (interp_tree' [(i1, o1, v1), (i2, o2, v2), (i3, o3, v3'), (i4, o4, v4')]) v5 j5)"
using assms(2) assms(3) by auto

end
