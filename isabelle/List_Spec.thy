theory List_Spec
  imports Main
begin

datatype 'oid list_op
  = InsertAfter 'oid
  | Remove 'oid

definition insert_after :: "'oid \<Rightarrow> 'oid \<Rightarrow> ('oid \<rightharpoonup> 'oid) \<Rightarrow> ('oid \<rightharpoonup> 'oid)" where
  "insert_after oid ref next \<equiv> (next(ref := Some oid))(oid := next ref)"

definition remove :: "'oid \<Rightarrow> ('oid \<rightharpoonup> 'oid) \<Rightarrow> ('oid \<rightharpoonup> 'oid)" where
  "remove ref next \<equiv>
     if \<exists>p. next p = Some ref then
       let p = THE p. next p = Some ref
       in next(p := next ref)
     else next"

fun interp :: "('oid \<rightharpoonup> 'oid) \<Rightarrow> ('oid \<times> 'oid list_op) \<Rightarrow> ('oid \<rightharpoonup> 'oid)" where
  "interp next (oid, InsertAfter ref) = insert_after oid ref next" |
  "interp next (oid, Remove      ref) = remove ref next"

definition interp_list :: "('oid \<times> 'oid list_op) list \<Rightarrow> ('oid \<rightharpoonup> 'oid)" where
  "interp_list ops \<equiv> foldl interp Map.empty ops"

fun oid_reference :: "'oid list_op \<Rightarrow> 'oid" where
  "oid_reference (InsertAfter ref) = ref" |
  "oid_reference (Remove ref) = ref"


locale list_spec =
  fixes op_set :: "'oid::{linorder} \<rightharpoonup> 'oid list_op"
  assumes ref_older: "op_set oid = Some oper \<Longrightarrow> oid_reference oper < oid"

definition (in list_spec) oid_list :: "'oid list" where
  "oid_list \<equiv> sorted_list_of_set (dom op_set)"

definition (in list_spec) op_list :: "('oid \<times> 'oid list_op) list" where
  "op_list \<equiv> map (\<lambda>oid. (oid, the (op_set oid))) oid_list"

definition (in list_spec) next_elem :: "'oid \<rightharpoonup> 'oid" where
  "next_elem \<equiv> interp_list op_list"

lemma (in list_spec) oid_list_sorted:
  assumes "oid_list = xs@x#y#ys"
  shows "x < y"
  using assms apply(simp add: oid_list_def sorted_list_of_set_def)
  apply(induction rule: ) (* TODO... *)

lemma unique_previous:
  assumes "interp_list ops p1 = Some x"
    and "interp_list ops p2 = Some x"
    and "list_spec op_set"
    and "ops = list_spec.op_list op_set"
  shows "p1 = p2"
  using assms 
  apply(induction rule: rev_induct, simp add: interp_list_def)
  apply(simp add: interp_list_def list_spec.op_list_def)
  apply(clarsimp, case_tac b)
  apply(simp add: insert_after_def)

(*
fun insertAfter :: "'oid \<Rightarrow> 'oid \<Rightarrow> 'oid list \<Rightarrow> 'oid list" where
  "insertAfter oid ref [] = []" |
  "insertAfter oid ref (x#xs) =
     (if ref = x then x#oid#xs else x # (insertAfter oid ref xs))"

fun remove :: "'oid \<Rightarrow> 'oid list \<Rightarrow> 'oid list" where
  "remove ref [] = []" |
  "remove ref (x#xs) = (if ref = x then xs else x # (remove ref xs))"

fun interp :: "('oid \<times> 'oid list_op) \<Rightarrow> 'oid list \<Rightarrow> 'oid list" where
  "interp (oid, InsertAfter ref) list = insertAfter oid ref list" |
  "interp (oid, Remove ref) list = remove ref list"
*)

end
