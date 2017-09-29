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
  fixes op_list :: "('oid::{linorder} \<times> 'oid list_op) list"
  assumes op_sorted_list: "sorted (map fst op_list)"
    and distinct_oids: "distinct (map fst op_list)"
    and ref_older: "(oid, oper) \<in> set op_list \<Longrightarrow> oid_reference oper < oid"
context list_spec begin
  
definition op_set :: "_" where
  "op_set \<equiv> set op_list"
  
definition elems :: "('oid \<times> 'oid list_op) list" where
  "elems \<equiv> filter (\<lambda>(_, oper). case oper of InsertAfter x \<Rightarrow> True | _ \<Rightarrow> False ) op_list"
  
definition next_elem :: "'oid \<rightharpoonup> 'oid" where
  "next_elem \<equiv> interp_list op_list"
  
inductive next_elem_tc :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" (infix "\<sqsubset>" 50) where
  next_elem_tcI1: "next_elem a = Some b \<Longrightarrow> a \<sqsubset> b " |
  next_elem_tcI2: "a \<sqsubset> b \<Longrightarrow> next_elem b = Some c \<Longrightarrow> a \<sqsubset> c"
  
inductive_cases next_elem_tcE [elim]: "a \<sqsubset> b"
  thm next_elem_tcE

end
  
lemma list_spec_rm_last: "list_spec (xs @[x]) \<Longrightarrow> list_spec xs"
  apply (clarsimp simp: list_spec_def)
  using sorted_append by blast
    
lemma next_elem_in_opset: "list_spec A \<Longrightarrow> list_spec.next_elem A a = Some b \<Longrightarrow> a \<in> fst ` set A"
  apply (induct A rule: rev_induct)
   apply (simp add: list_spec.next_elem_def interp_list_def insert_after_def)
  apply clarsimp
  apply (frule list_spec_rm_last)
  apply clarsimp
  apply (case_tac ba)
   apply (clarsimp simp add: list_spec.next_elem_def interp_list_def insert_after_def)
   apply (case_tac "a=aa")
    apply force
   apply clarsimp
   apply (case_tac "a=x1")
    apply clarsimp
    
  sorry

lemma "list_spec.next_elem_tc A a b \<Longrightarrow> list_spec A \<Longrightarrow> a \<in> (fst ` set A)"
  apply (erule list_spec.next_elem_tc.induct[rotated])
    prefer 3
    apply simp
  prefer 2
   apply force
    using next_elem_in_opset
  apply (force simp add: list_spec.next_elem_def interp_list_def insert_after_def)
done
    
  
lemma "list_spec.next_elem_tc A a b \<Longrightarrow> list_spec A \<Longrightarrow> list_spec (A@[(oid, InsertAfter ref)]) \<Longrightarrow> list_spec.next_elem_tc (A@[(oid, InsertAfter ref)]) a b" 
  apply (erule list_spec.next_elem_tc.cases)
    apply assumption
   apply clarsimp
   apply (case_tac "a=ref")
    prefer 2
   apply (rule list_spec.next_elem_tcI1)
     apply assumption
    apply (frule list_spec_rm_last)
    apply (simp add: list_spec.next_elem_def interp_list_def)
    apply (unfold insert_after_def)
    apply clarsimp

    apply (subgoal_tac "a \<noteq> oid")
     apply force
  using list_spec.distinct_oids 
oops
  
lemma "list_spec A \<Longrightarrow> list_spec B \<Longrightarrow> (set A) \<subseteq> (set B) \<Longrightarrow> list_spec.next_elem_tc A a b \<Longrightarrow> list_spec.next_elem_tc (list_spec.elems B) a b" 
  apply (induct A rule: rev_induct)
   apply simp
     apply (erule list_spec.next_elem_tcE[rotated])
     apply (simp add: list_spec.next_elem_def interp_list_def)+

   apply clarsimp
  apply (erule list_spec.next_elem_tcE[rotated])
    apply (subgoal_tac "list_spec.next_elem xs a = Some b")
    oops
 
lemma sorted_list_of_set_base:
  assumes "finite A" "sorted_list_of_set A = [x, y]"
  shows "x < y"
    using assms sorted_many_eq sorted_list_of_set
    by (metis distinct_length_2_or_more order.not_eq_order_implies_strict)
    
lemma sorted_list_of_set_sorted:
  assumes "finite A" "sorted_list_of_set A = xs@x#y#ys"
  shows "x < y"
  using assms
  apply (induction ys arbitrary: A rule: rev_induct)
   apply (induction xs arbitrary: A)
    apply (simp add: sorted_list_of_set_base)
   apply clarsimp
   apply (erule_tac x="A-{a}" in meta_allE)
   apply clarsimp
   apply (simp add: sorted_list_of_set_remove)
   apply (erule_tac x="A-{xa}" in meta_allE)
  apply clarsimp
  apply (subgoal_tac "distinct (xs @ x # y # xsa @ [xa])")
   apply (simp add: sorted_list_of_set_remove)
   apply (metis order.not_eq_order_implies_strict sorted_append sorted_list_of_set sorted_many_eq)
  by (metis distinct_sorted_list_of_set)
   
lemma (in list_spec) finite_opset: "finite opset"
  sorry
    
lemma (in list_spec) oid_list_sorted:
  assumes "oid_list = xs@x#y#ys"
  shows "x < y"
  using assms finite_opset  sorted_list_of_set_sorted by fastforce
    
    
lemma (in list_spec) unique_previous:
  assumes "next_elem p1 = Some x"
    and "next_elem p2 = Some x"
  shows "p1 = p2"
  using assms 
    apply (auto simp: next_elem_def)

lemma (in list_spec) oid_list_set_dom:
  shows "set oid_list = dom op_set"
  by (simp add: finite_opset oid_list_def)

lemma (in list_spec) oid_list_dom_member:
  assumes "oid_list = xs@x#ys"
  shows "x \<in> dom op_set"
  using assms oid_list_set_dom by auto

lemma (in list_spec) dom_member_oid_list:
  assumes "x \<in> dom op_set"
  shows "\<exists>xs ys. oid_list = xs@x#ys"
  by (simp add: assms finite_opset oid_list_def split_list)

(*
let A subset opset
  assumes x < y in listA
A subset B subset opset
  then  x < y in listB
*)
    
(*
let A subset opset
  assumes x < y in listA
A subset B subset opset
  then  x < y in listB
*)
    
(*
  exteded xs = xs + extra opers

  assumes x < y in some list
  then  x < y in extended list 
*)

lemma (in list_spec)
  
    
    
lemma oid_list_last_none:
  assumes "list_spec.oid_list op_set = xs @ [x]"
    and "list_spec op_set"
  shows "list_spec.oid_list (op_set(x := None)) = xs"
  using assms apply(induction xs arbitrary: op_set rule: rev_induct)
  apply(subgoal_tac "dom op_set = {x}")
  apply(simp add: list_spec.oid_list_def list_spec_def)
  using list_spec.oid_list_set_dom apply fastforce
  apply(erule_tac x="op_set(xa := None)" in meta_allE)
  sorry

lemma (in list_spec) oid_list_last_greatest:
  assumes "oid_list = xs @ [x]"
    and "y \<in> dom op_set"
  shows "y \<le> x"
  using assms by (metis UnE empty_iff eq_iff finite_opset insertE list.set(1)
    list.set_intros(1) list.simps(15) oid_list_def set_append sorted_append sorted_list_of_set)

lemma (in list_spec) op_list_last_oid:
  assumes "op_list = xs @ [(oid, oper)]"
  shows "oid \<in> dom op_set"
  using assms by (metis Nil_is_map_conv last_in_set last_map oid_list_set_dom op_list_def
    prod.sel(1) snoc_eq_iff_butlast)

lemma (in list_spec) op_list_last_oper:
  assumes "op_list = xs @ [(oid, oper)]"
  shows "op_set oid = Some oper"
  using assms by (metis (mono_tags, lifting) Pair_inject domD last_map map_is_Nil_conv
    op_list_def op_list_last_oid option.sel snoc_eq_iff_butlast)

lemma op_list_remove_last:
  assumes "xs @ [(oid, oper)] = list_spec.op_list op_set"
    and "list_spec op_set"
  shows "xs = list_spec.op_list (op_set(oid := None))"
  using assms apply -
  apply(subgoal_tac "list_spec (op_set(oid := None))") prefer 2
  apply(rule list_spec.intro)
  apply(metis fun_upd_apply list_spec.ref_older option.distinct(1))
  apply(simp add: list_spec.finite_opset)
  apply(subgoal_tac "list_spec.oid_list (op_set(oid := None)) =
                     butlast (list_spec.oid_list op_set)") prefer 2
  sorry

lemma (in list_spec) unique_previous:
  assumes "next_elem p1 = Some x"
    and "next_elem p2 = Some x"
  shows "p1 = p2"
  using assms 
  apply(simp add: next_elem_def interp_list_def list_spec.op_list_def)
  apply(induction op_list arbitrary: op_set rule: rev_induct)
  apply(simp add: interp_list_def)
  apply(clarsimp, case_tac b)
  apply(simp add: interp.elims insert_after_def)

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
