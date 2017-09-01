theory Datalog_Rules
  imports Main
begin

datatype ('oid, 'val) operation
  = MakeList
  | MakeMap
  | MakeVal "'val"
  | InsertAfter "'oid"
  | LinkList "'oid" "'oid"
  | LinkMap "'oid" "string" "'oid"
  | DelList "'oid"
  | DelMap  "'oid" "string"

type_synonym ('oid, 'val) database = "'oid \<rightharpoonup> ('oid, 'val) operation"

definition ref_integrity :: "('oid, 'val) database \<Rightarrow> bool" where
  "ref_integrity \<D> \<equiv> \<forall>oid \<in> dom \<D>. \<forall>x y s.
     (\<D> oid = Some (InsertAfter x) \<longrightarrow> x \<in> dom \<D> \<and> x \<noteq> oid) \<and>
     (\<D> oid = Some (LinkList x y ) \<longrightarrow> x \<in> dom \<D> \<and> x \<noteq> oid \<and> y \<in> dom \<D> \<and> y \<noteq> oid) \<and>
     (\<D> oid = Some (LinkMap x s y) \<longrightarrow> x \<in> dom \<D> \<and> x \<noteq> oid \<and> y \<in> dom \<D> \<and> y \<noteq> oid) \<and>
     (\<D> oid = Some (DelList x    ) \<longrightarrow> x \<in> dom \<D> \<and> x \<noteq> oid) \<and>
     (\<D> oid = Some (DelMap x s   ) \<longrightarrow> x \<in> dom \<D> \<and> x \<noteq> oid)"

locale datalog =
  fixes \<D> :: "('oid::{linorder}, 'val) database"

context datalog begin

(************** List insertion **************)

inductive is_list_elem :: "'oid \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some (InsertAfter parent)\<rbrakk> \<Longrightarrow> is_list_elem oid"

inductive is_list_parent :: "'oid \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some MakeList\<rbrakk> \<Longrightarrow> is_list_parent oid" |
  "\<lbrakk>is_list_elem oid     \<rbrakk> \<Longrightarrow> is_list_parent oid"

inductive parent_child :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>\<D> child = Some (InsertAfter parent); is_list_parent parent\<rbrakk> \<Longrightarrow> parent_child parent child"

inductive has_child :: "'oid \<Rightarrow> bool" where
  "\<lbrakk>parent_child parent child\<rbrakk> \<Longrightarrow> has_child parent"

inductive later_child :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>parent_child parent c;  parent_child parent p; c < p\<rbrakk> \<Longrightarrow> later_child parent c"

inductive sibling :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>parent_child parent c1; parent_child parent c2\<rbrakk> \<Longrightarrow> sibling c1 c2"

inductive later_sibling :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>sibling p l; l < p\<rbrakk> \<Longrightarrow> later_sibling p l"

inductive later_sibling_2 :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>sibling p n; sibling p l; l < n; n < p\<rbrakk> \<Longrightarrow> later_sibling_2 p l"

inductive has_next_sibling :: "'oid \<Rightarrow> bool" where
  "\<lbrakk>later_sibling p n\<rbrakk> \<Longrightarrow> has_next_sibling p"

inductive first_child :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>parent_child parent c; \<not> later_child parent c\<rbrakk> \<Longrightarrow> first_child parent c"

inductive next_sibling :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>later_sibling p n; \<not> later_sibling_2 p n\<rbrakk> \<Longrightarrow> next_sibling p n"

inductive next_sibling_anc :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>next_sibling s n\<rbrakk> \<Longrightarrow> next_sibling_anc s n" |
  "\<lbrakk>\<not> has_next_sibling s; parent_child p s; next_sibling_anc p n\<rbrakk> \<Longrightarrow> next_sibling_anc s n"

inductive has_sibling_anc :: "'oid \<Rightarrow> bool" where
  "\<lbrakk>next_sibling_anc s n\<rbrakk> \<Longrightarrow> has_sibling_anc s"

inductive next_elem :: "'oid \<Rightarrow> 'oid option \<Rightarrow> bool" where
  "\<lbrakk>first_child p n\<rbrakk> \<Longrightarrow> next_elem p (Some n)" |
  "\<lbrakk>is_list_elem p; \<not> has_child p; next_sibling_anc p n\<rbrakk> \<Longrightarrow> next_elem p (Some n)" |  
  "\<lbrakk>is_list_elem p; \<not> has_child p; \<not> has_sibling_anc p\<rbrakk> \<Longrightarrow> next_elem p None"  
  
lemmas [intro] = next_elem.intros
lemmas [intro] = has_sibling_anc.intros
lemmas [intro] = next_sibling_anc.intros
lemmas [intro] = next_sibling.intros
lemmas [intro] = first_child.intros
lemmas [intro] = has_next_sibling.intros
lemmas [intro] = later_sibling_2.intros
lemmas [intro] = later_sibling.intros
lemmas [intro] = sibling.intros
lemmas [intro] = later_child.intros has_child.intros parent_child.intros
lemmas [intro] = is_list_parent.intros is_list_elem.intros

inductive_cases next_elem_elim [elim]: "next_elem oid opt"

inductive_cases has_sibling_anc_elim [elim]: "has_sibling_anc m"
inductive_cases next_sibling_anc_elim [elim]: "next_sibling_anc m n"
inductive_cases next_sibling_elim [elim]: "next_sibling m n"
    
inductive_cases first_child_elim [elim]: "first_child p n"

inductive_cases has_next_sibling_elim [elim]: "has_next_sibling m"
inductive_cases later_sibling_2_elim [elim]: "later_sibling_2 m n"
inductive_cases later_sibling_elim [elim]: "later_sibling m n"
inductive_cases sibling_elim [elim]: "sibling m n"
  
inductive_cases parent_child_elim [elim]: "parent_child p m"
inductive_cases has_child_elim [elim]: "has_child p"
inductive_cases later_child_elim [elim]: "later_child p n"
  
inductive_cases is_list_elem_elim [elim]: "is_list_elem p"
inductive_cases is_list_parent_elim [elim]: "is_list_parent p"
  
end

definition (in datalog) next_elem_rel :: "('oid \<times> 'oid option) set" where
  "next_elem_rel \<equiv> {(x, y). next_elem x y}"

lemma (in datalog) first_child_functional [simp]:
  assumes "first_child p c" and "first_child p d"
  shows "c = d"
  using assms by force
    
lemma (in datalog) first_child_has_child [dest]:
  assumes "first_child m n"
  shows "has_child m"
  using assms by force
    
lemma (in datalog) next_sibling_functional [simp]:
  assumes "next_sibling m n" and "next_sibling m p"
  shows "n = p"
  using assms
  apply -
  apply(erule next_sibling_elim)+
  apply(meson datalog.later_sibling_2.simps later_sibling.cases not_less_iff_gr_or_eq)
  done
    
lemma (in datalog) next_sibling_to_has_next_sibling [dest]:
  assumes "next_sibling m n"
  shows "has_next_sibling m"
using assms by force
    
lemma (in datalog) next_sibling_anc_functional [simp]:
  assumes "next_sibling_anc m n" and "next_sibling_anc m p"
  shows "n = p"
  using assms by(induction rule: next_sibling_anc.induct) force+
    
lemma (in datalog) next_elem_functional [simp]:
  assumes "next_elem m n" and "next_elem m p"
  shows "n = p"
  using assms by - ((erule next_elem_elim)+, auto)
  
lemma (in datalog) next_elem_rel_unique:
  assumes "(x, y) \<in> next_elem_rel" and "(x, z) \<in> next_elem_rel"
  shows "y = z"
  using assms by(clarsimp simp add: next_elem_rel_def)

lemma (in datalog) database_dom_monotonic [intro]:
  assumes "x \<in> dom \<D>"
  shows "x \<in> dom (\<D>(y \<mapsto> z))"
  using assms by auto

lemma (in datalog) next_elem_dom_closed [elim]:
  assumes "next_elem m n"
  shows "m \<in> dom \<D>"
  using assms by - (erule next_elem_elim, (force+))

definition append_op :: "('oid::{linorder}, 'val) database \<Rightarrow> ('oid::{linorder}, 'val) database \<Rightarrow> 'oid \<Rightarrow> ('oid, 'val) operation \<Rightarrow> bool" where
  "append_op \<D> \<D>' oid oper \<equiv>
     (\<D> oid = None \<and> \<D>' = \<D>(oid \<mapsto> oper) \<and>
     ref_integrity \<D> \<and> (\<forall>n \<in> dom \<D>. n < oid))"

lemma is_list_parent_monotonic:
  assumes "datalog.is_list_parent \<D> x"
    and "oid \<notin> dom \<D>"
  shows "datalog.is_list_parent (\<D>(oid \<mapsto> oper)) x"
by(metis (full_types) assms datalog.is_list_elem.simps datalog.is_list_parent.intros
  datalog.is_list_parent_elim domIff fun_upd_other option.simps(3))

lemma is_list_parent_rev:
  assumes "datalog.is_list_parent (\<D>(oid \<mapsto> oper)) x"
    and "x \<noteq> oid"
  shows "datalog.is_list_parent \<D> x"
by (metis (no_types, lifting) assms datalog.is_list_elem.simps
  datalog.is_list_parent.intros(1) datalog.is_list_parent.intros(2)
  datalog.is_list_parent_elim fun_upd_other)

lemma insert_first_child:
  assumes "append_op \<D> \<D>' y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
  shows "datalog.first_child \<D>' x y"
  using assms
  apply(unfold append_op_def, clarsimp)
  apply(subgoal_tac "datalog.parent_child (\<D>(y \<mapsto> InsertAfter x)) x y")
  apply(metis (no_types, lifting) datalog.first_child.intros datalog.later_child_elim
    datalog.parent_child.cases domIff dual_order.asym fun_upd_other option.simps(3))
  apply(simp add: datalog.parent_child.intros domIff is_list_parent_monotonic)
done

lemma insert_has_no_child:
  assumes "append_op \<D> \<D>' y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
  shows "\<not> datalog.has_child \<D>' y"
using assms
  apply(unfold append_op_def, clarsimp)
  apply(erule datalog.has_child_elim)
  apply(erule datalog.parent_child_elim)
  apply(subgoal_tac "x \<in> dom \<D>") prefer 2
  apply(meson datalog.is_list_elem.simps datalog.is_list_parent_elim domI)
  apply(subgoal_tac "x \<noteq> y") prefer 2 apply blast
  apply(subgoal_tac "\<D> child = Some (InsertAfter y)") prefer 2
  apply(meson map_upd_Some_unfold operation.inject(2))
  apply(unfold ref_integrity_def, blast)
  done

lemma first_child_has_no_sibling:
  assumes "append_op \<D> \<D>' y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
    and "\<not> datalog.has_child \<D> x"
  shows "\<not> datalog.has_next_sibling \<D>' y"
  using assms
  apply(unfold append_op_def, clarsimp)
  apply(erule datalog.has_next_sibling_elim)
  apply(erule datalog.later_sibling_elim)
  apply(erule datalog.sibling_elim)
  apply(subgoal_tac "parent = x") prefer 2
  using datalog.parent_child.cases apply fastforce
  apply(subgoal_tac "\<D> n = Some (InsertAfter x)") prefer 2
  apply(metis datalog.parent_child.cases fun_upd_other neq_iff)
  using datalog.has_child.intros datalog.parent_child.intros apply blast
  done

lemma insert_next_sibling:
  assumes "append_op \<D> \<D>' y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
    and "datalog.first_child \<D> x z"
  shows "datalog.next_sibling \<D>' y z"
  using assms
  apply(unfold append_op_def, clarsimp)
  apply(subgoal_tac "datalog.parent_child \<D>' x y") prefer 2
  using insert_first_child datalog.first_child_elim apply blast
  apply(subgoal_tac "datalog.parent_child \<D>' x z") prefer 2
  apply(metis datalog.first_child.cases datalog.parent_child.simps fun_upd_apply)
  apply(subgoal_tac "z < y") prefer 2
  apply(meson datalog.first_child.cases datalog.parent_child_elim domI)
  apply(rule datalog.next_sibling.intros)
  using datalog.later_sibling.intros datalog.sibling.intros apply blast
  apply(clarsimp, erule datalog.later_sibling_2_elim)
  apply(erule datalog.first_child_elim)
  apply(metis datalog.later_child.simps datalog.parent_child.cases
    datalog.parent_child.intros datalog.sibling_elim fun_upd_other neq_iff)
done

lemma insert_unchanged_parent_child:
  assumes "append_op \<D> \<D>' y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
    and "a \<noteq> x"
  shows "datalog.parent_child \<D> a b \<longleftrightarrow> datalog.parent_child \<D>' a b"
  using assms
  apply(unfold append_op_def, clarsimp)
  apply(rule iffI)
   apply(erule datalog.parent_child_elim)
   apply(rule datalog.parent_child.intros, force)
   apply(simp add: domIff is_list_parent_monotonic)
  apply(erule datalog.parent_child_elim)
  apply(rule datalog.parent_child.intros)
   apply(metis (mono_tags, lifting) map_upd_Some_unfold operation.inject(2))
  apply(subgoal_tac "a \<noteq> y")
   apply(meson domIff is_list_parent_rev)
  apply(case_tac "b = y", simp)
  using ref_integrity_def apply fastforce
  done

lemma insert_unchanged_no_child:
  assumes "append_op \<D> \<D>' y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
    and "a \<noteq> x"
    and "\<not> datalog.has_child \<D> a"
  shows "\<not> datalog.has_child \<D>' a"
by(meson assms datalog.has_child.simps insert_unchanged_parent_child)
    
(* I think this is correct because InsertAfter creates a greatest
   sibling, but next_sibling_anc never visits greatest siblings --
   only first_child visits those. *)
lemma insert_unchanged_sibling_anc:
  assumes "append_op \<D> \<D>' y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
    and "a \<noteq> y"
  shows "datalog.next_sibling_anc \<D> a b \<longleftrightarrow> datalog.next_sibling_anc \<D>' a b"
  using assms
  apply(unfold append_op_def, clarsimp)
  sorry (* TODO *)

lemma insert_next_sibling_anc:
  assumes "append_op \<D> \<D>' y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
    and "\<not> datalog.has_child \<D> x"
    and "datalog.next_sibling_anc \<D> x z"
  shows "datalog.next_sibling_anc \<D>' y z"
  using assms
  apply(unfold append_op_def, clarsimp)
  apply(rule_tac p=x in datalog.next_sibling_anc.intros(2))
  using first_child_has_no_sibling apply blast
  using datalog.first_child_elim insert_first_child apply blast
  apply(subgoal_tac "x \<noteq> y")
  apply(simp add: insert_unchanged_sibling_anc)
  using datalog.first_child_has_child insert_first_child insert_has_no_child apply blast
done

lemma insert_end_of_list:
  assumes "append_op \<D> \<D>' y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
    and "\<not> datalog.has_child \<D> x"
    and "\<not> datalog.next_sibling_anc \<D> x z"
  shows "\<not> datalog.next_sibling_anc \<D>' y z"
  using assms
  apply(unfold append_op_def, clarsimp)
  apply(erule datalog.next_sibling_anc_elim)
  using datalog.next_sibling_to_has_next_sibling first_child_has_no_sibling apply blast
  apply(subgoal_tac "p = x", clarsimp) prefer 2
  using datalog.parent_child.cases apply fastforce
  using datalog.has_child.intros insert_has_no_child insert_unchanged_sibling_anc apply fastforce
  done

lemma insert_immediately_after:
  assumes "append_op \<D> \<D>' y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
  shows "datalog.next_elem \<D>' x (Some y)"
using assms datalog.next_elem.intros(1) datalog.next_elem_rel_def insert_first_child by blast

lemma insert_connect_next:
  assumes "append_op \<D> \<D>' y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
    and "datalog.next_elem \<D> x z"
  shows "datalog.next_elem \<D>' y z"
  using assms
  apply(unfold append_op_def, clarsimp)
  apply(erule datalog.next_elem_elim)
  apply(simp add: datalog.is_list_elem.intros datalog.next_elem.intros(2)
    datalog.next_sibling_anc.intros(1) insert_has_no_child insert_next_sibling)
  apply(simp add: datalog.is_list_elem.intros datalog.next_elem.intros(2)
    insert_has_no_child insert_next_sibling_anc)
  apply(simp add: datalog.has_sibling_anc.simps datalog.is_list_elem.intros
    insert_has_no_child datalog.next_elem.intros(3) insert_end_of_list)
  done

lemma insert_unchanged_next_elem:
  assumes "append_op \<D> \<D>' y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
    and "a \<noteq> x"
    and "datalog.next_elem \<D> a b"
  shows "datalog.next_elem \<D>' a b"
  using assms
  apply(unfold append_op_def, clarsimp)
  apply(erule datalog.next_elem_elim)
  apply(subgoal_tac "datalog.first_child \<D>' a n")
  using datalog.next_elem.intros(1) apply blast
  apply(meson datalog.first_child.intros datalog.first_child_elim
    datalog.later_child.simps insert_unchanged_parent_child)
   apply(subgoal_tac "datalog.next_sibling_anc \<D>' a n")
    apply(subgoal_tac "\<not> datalog.has_child \<D>' a")
     apply(simp add: datalog.is_list_elem.simps datalog.next_elem.intros(2))
    apply(simp add: datalog.has_child.simps insert_unchanged_parent_child)
   apply(metis datalog.is_list_elem.cases insert_unchanged_sibling_anc option.simps(3))
  apply(clarsimp, rule datalog.next_elem.intros(3))
    apply (simp add: datalog.is_list_elem.simps)
  using insert_unchanged_no_child apply blast
  apply(metis assms(4) datalog.has_sibling_anc.simps datalog.next_elem_dom_closed
    domIff insert_unchanged_sibling_anc)
  done

lemma insert_serial:
  assumes "append_op \<D> \<D>' y (InsertAfter x)"
    and "(x, z) \<in> datalog.next_elem_rel \<D>"
    and "datalog.is_list_parent \<D> x"
  shows "datalog.next_elem_rel \<D>' = datalog.next_elem_rel \<D> - {(x, z)} \<union> {(x, Some y), (y, z)}"
  using assms
  apply(unfold datalog.next_elem_rel_def append_op_def)
  apply clarsimp
  apply(rule equalityI)
   apply clarify
    apply(subgoal_tac "a \<noteq> x") prefer 2
   apply(case_tac "a = x"; clarsimp)

    apply(subgoal_tac "datalog.next_elem \<D>' y z")

   apply(rule conjI)
    apply(case_tac "a = x"; clarsimp)
     defer
     apply(erule_tac x=a in meta_allE)
    try
     apply(subgoal_tac "a \<in> dom \<D>")
    


(*********** Links between objects and register assignment ***************)

context datalog begin

inductive is_map :: "'oid \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some MakeMap\<rbrakk> \<Longrightarrow> is_map oid"

inductive is_val :: "'oid \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some (MakeVal v)\<rbrakk> \<Longrightarrow> is_val oid"

inductive link_target :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some (LinkList el target); is_list_elem el\<rbrakk> \<Longrightarrow> link_target oid target" |
  "\<lbrakk>\<D> oid = Some (LinkMap m k target); is_map m       \<rbrakk> \<Longrightarrow> link_target oid target"

inductive stolen_link :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>link_target o1 target; link_target o2 target; o1 < o2\<rbrakk> \<Longrightarrow> stolen_link o1 target"

inductive map_write :: "'oid \<Rightarrow> 'oid \<Rightarrow> string \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some (LinkMap m k t); is_map m\<rbrakk> \<Longrightarrow> map_write oid m k" |
  "\<lbrakk>\<D> oid = Some (DelMap m k);    is_map m\<rbrakk> \<Longrightarrow> map_write oid m k"

inductive map_write_old :: "'oid \<Rightarrow> 'oid \<Rightarrow> string \<Rightarrow> bool" where
  "\<lbrakk>map_write o1 m k; map_write o2 m k; o1 < o2\<rbrakk> \<Longrightarrow> map_write_old o1 m k"

inductive list_write :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some (LinkList el t); is_list_elem el\<rbrakk> \<Longrightarrow> list_write oid el" |
  "\<lbrakk>\<D> oid = Some (DelList el);    is_list_elem el\<rbrakk> \<Longrightarrow> list_write oid el"

inductive list_write_old :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>list_write o1 el; list_write o2 el; o1 < o2\<rbrakk> \<Longrightarrow> list_write_old o1 el"

inductive latest_link :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>link_target oid target; \<not> stolen_link oid target\<rbrakk> \<Longrightarrow> latest_link oid target"

inductive latest_map_write :: "'oid \<Rightarrow> 'oid \<Rightarrow> string \<Rightarrow> bool" where
  "\<lbrakk>map_write oid m k; \<not> map_write_old oid m k\<rbrakk> \<Longrightarrow> latest_map_write oid m k"

inductive latest_map_link :: "'oid \<Rightarrow> string \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some (LinkMap m k target); latest_map_write oid m k; latest_link oid target\<rbrakk>
      \<Longrightarrow> latest_map_link m k target"

inductive has_map_val :: "'oid \<Rightarrow> string \<Rightarrow> bool" where
  "\<lbrakk>latest_map_link m k v\<rbrakk> \<Longrightarrow> has_map_val m k"

inductive latest_list_write :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>list_write oid el; \<not> list_write_old oid el\<rbrakk> \<Longrightarrow> latest_list_write oid el"

inductive latest_list_link :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some (LinkList el target); latest_list_write oid el; latest_link oid target\<rbrakk>
      \<Longrightarrow> latest_list_link el target"

inductive has_list_val :: "'oid \<Rightarrow> bool" where
  "\<lbrakk>latest_list_link el v\<rbrakk> \<Longrightarrow> has_list_val el"

end

definition latest_link_rel :: "('oid::{linorder}, 'val) database \<Rightarrow> ('oid \<times> 'oid) set" where
  "latest_link_rel \<D> \<equiv> {(oid, target). datalog.latest_link \<D> oid target}"

definition latest_map_rel :: "('oid::{linorder}, 'val) database \<Rightarrow> ('oid \<times> string \<times> 'oid) set" where
  "latest_map_rel \<D> \<equiv> {(m, k, v). datalog.latest_map_link \<D> m k v}"

lemma map_val_unique:
  assumes "(m, k, v1) \<in> latest_map_rel \<D>"
    and "(m, k, v2) \<in> latest_map_rel \<D>"
  shows "v1 = v2"
  oops

lemma link_map_serial:
  assumes "\<D> oid = None" and "\<D>' = \<D>(oid \<mapsto> LinkMap m k target)"
    and "\<And>n. n \<in> dom \<D> \<Longrightarrow> n < oid"
    and "\<nexists>prev. (prev, target) \<in> latest_link_rel \<D>" (* TODO define semantics for stealing *)
    and "(m, k, v1) \<in> latest_map_rel \<D>" (* TODO case where there's no prior value *)
  shows "latest_map_rel \<D>' = latest_map_rel \<D> - {(m, k, v1)} \<union> {(m, k, target)}"
  oops


(*********** List iteration skipping blank elements ***************)

context datalog begin

inductive next_nonempty :: "'oid \<Rightarrow> 'oid option \<Rightarrow> bool" where
  "\<lbrakk>next_elem el None\<rbrakk> \<Longrightarrow> next_nonempty el None" |
  "\<lbrakk>next_elem el (Some n); has_list_val n\<rbrakk> \<Longrightarrow> next_nonempty el (Some n)" |
  "\<lbrakk>next_elem el (Some n); \<not> has_list_val n; next_nonempty n m\<rbrakk> \<Longrightarrow> next_nonempty el m"

inductive list_elem :: "'oid \<Rightarrow> 'oid \<Rightarrow> 'oid option \<Rightarrow> bool" where
  "\<lbrakk>latest_list_link el v; next_nonempty el next\<rbrakk> \<Longrightarrow> list_elem el v next"

inductive list_suffix :: "'oid \<Rightarrow> ('oid \<times> 'oid) list \<Rightarrow> bool" where
  "\<lbrakk>next_nonempty el None\<rbrakk> \<Longrightarrow> list_suffix el []" |
  "\<lbrakk>next_nonempty el (Some n); latest_list_link n v; list_suffix n suf\<rbrakk> \<Longrightarrow> list_suffix el ((n,v)#suf)"

inductive list_full :: "'oid \<Rightarrow> ('oid \<times> 'oid) list \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some MakeList; list_suffix oid suf\<rbrakk> \<Longrightarrow> list_full oid suf"

end

end
