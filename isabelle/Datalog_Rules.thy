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
    
fun oid_references :: "('o, 'v) operation \<Rightarrow> 'o set" where
  "oid_references (InsertAfter oid) = {oid}" |
  "oid_references (LinkList oid1 oid2) = {oid1, oid2}" |
  "oid_references (LinkMap oid1 _ oid2) = {oid1, oid2}" |
  "oid_references (DelList oid) = {oid}" |
  "oid_references (DelMap oid _) = {oid}" |
  "oid_references _ = {}"

type_synonym ('oid, 'val) database = "'oid \<rightharpoonup> ('oid, 'val) operation"

locale datalog =
  fixes \<D> :: "('oid::{linorder}, 'val) database"
  assumes ref_older: "\<D> oid = Some oper \<Longrightarrow> x \<in> oid_references oper \<Longrightarrow> x < oid"

lemma (in datalog) insert_ref_older:
  assumes "\<D> oid = Some (InsertAfter x)"
  shows "x < oid"
  using assms ref_older by fastforce

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

inductive next_elem :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>first_child p n\<rbrakk> \<Longrightarrow> next_elem p n" |
  "\<lbrakk>is_list_elem p; \<not> has_child p; next_sibling_anc p n\<rbrakk> \<Longrightarrow> next_elem p n"
  
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

definition (in datalog) next_elem_rel :: "('oid \<times> 'oid) set" where
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
  apply(meson later_sibling.cases later_sibling_2.simps not_less_iff_gr_or_eq)
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

locale db_extension = datalog +
  fixes oid and oper
  assumes oid_is_latest [simp]: "n \<in> dom \<D> \<Longrightarrow> n < oid"
    and oid_not_present [simp]: "\<D> oid = None"
    and still_valid_database: "datalog (\<D>(oid \<mapsto> oper))"

lemma db_extension_datalog:
  assumes "db_extension \<D> oid oper"
  shows "datalog \<D>"
  using assms db_extension.axioms(1) by blast

lemma is_list_parent_unchanged:
  assumes "db_extension \<D> oid oper"
    and "x \<noteq> oid"
  shows "datalog.is_list_parent \<D> x \<longleftrightarrow> datalog.is_list_parent (\<D>(oid \<mapsto> oper)) x"
using assms
  by (metis (mono_tags) datalog.is_list_elem.intros datalog.is_list_elem_elim
    datalog.is_list_parent.cases datalog.is_list_parent.intros db_extension.axioms
    db_extension_axioms_def fun_upd_other)

lemma insert_first_child:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
  shows "datalog.first_child (\<D>(y \<mapsto> InsertAfter x)) x y"
  using assms
  apply(subgoal_tac "datalog.parent_child (\<D>(y \<mapsto> InsertAfter x)) x y")
  apply(metis (no_types, lifting) datalog.first_child.intros datalog.later_child_elim
    datalog.parent_child_elim domIff db_extension.oid_is_latest
    db_extension.still_valid_database fun_upd_apply option.distinct(1) order.asym)
  apply(metis datalog.is_list_elem.intros datalog.is_list_parent.intros(2)
    datalog.parent_child.intros db_extension.still_valid_database fun_upd_same
    is_list_parent_unchanged)
  done

lemma insert_has_no_child:
  assumes "db_extension \<D> y (InsertAfter x)"
  shows "\<not> datalog.has_child (\<D>(y \<mapsto> InsertAfter x)) y"
  using assms apply clarsimp
  apply(subgoal_tac "\<exists>child. (\<D>(y \<mapsto> InsertAfter x)) child = Some (InsertAfter y)") prefer 2
  apply(meson datalog.has_child.simps datalog.parent_child.cases db_extension.still_valid_database)
  apply clarify
  apply(subgoal_tac "y < child") prefer 2
  using datalog.insert_ref_older db_extension.still_valid_database apply blast
  apply (metis db_extension.oid_is_latest domI dual_order.asym map_upd_Some_unfold)
  done

lemma first_child_has_no_sibling:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "\<not> datalog.has_child \<D> x"
  shows "\<not> datalog.has_next_sibling (\<D>(y \<mapsto> InsertAfter x)) y"
  using assms apply clarsimp
  apply(case_tac "datalog.is_list_parent \<D> x")
  apply(subgoal_tac "\<exists>sib. datalog.sibling (\<D>(y \<mapsto> InsertAfter x)) y sib \<and> sib < y") prefer 2
  apply(meson datalog.has_next_sibling.cases datalog.later_sibling_elim
    db_extension.still_valid_database)
  apply clarify
  apply(subgoal_tac "datalog.parent_child (\<D>(y \<mapsto> InsertAfter x)) x sib") prefer 2
  apply(metis (no_types, lifting) datalog.first_child_has_child datalog.parent_child.simps
    datalog.sibling_elim db_extension.still_valid_database fun_upd_same insert_first_child
    insert_has_no_child is_list_parent_unchanged)
  apply(subgoal_tac "datalog.parent_child \<D> x sib") prefer 2
  apply(metis (no_types, lifting) datalog.parent_child.cases datalog.parent_child.intros
    db_extension.still_valid_database db_extension_datalog fun_upd_other neq_iff)
  apply(simp add: datalog.has_child.intros db_extension_datalog)
  apply(subgoal_tac "\<exists>s. datalog.sibling (\<D>(y \<mapsto> InsertAfter x)) y s", clarify) prefer 2
  apply(meson datalog.has_next_sibling.cases datalog.later_sibling.cases
    db_extension.still_valid_database)
  apply(subgoal_tac "datalog.parent_child (\<D>(y \<mapsto> InsertAfter x)) x y") prefer 2
  using datalog.parent_child.simps datalog.sibling.cases db_extension.still_valid_database
    apply fastforce
  apply(metis datalog.has_child.intros datalog.parent_child.cases db_extension.still_valid_database
    insert_has_no_child is_list_parent_unchanged)
  done

lemma insert_next_sibling:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
    and "datalog.first_child \<D> x z"
  shows "datalog.next_sibling (\<D>(y \<mapsto> InsertAfter x)) y z"
  using assms apply -
  apply(subgoal_tac "datalog.parent_child (\<D>(y \<mapsto> InsertAfter x)) x y") prefer 2
  using datalog.first_child_elim db_extension.still_valid_database insert_first_child apply blast
  apply(subgoal_tac "datalog.parent_child (\<D>(y \<mapsto> InsertAfter x)) x z") prefer 2
  apply(metis (no_types, lifting) datalog.first_child.cases datalog.parent_child.intros
    datalog.parent_child_elim db_extension.still_valid_database db_extension_datalog fun_upd_apply)
  apply(subgoal_tac "z < y") prefer 2
  apply(metis (no_types, lifting) datalog.first_child_elim datalog.later_child.intros
    datalog.parent_child.cases db_extension.oid_not_present db_extension.still_valid_database
    db_extension_datalog insert_first_child not_less_iff_gr_or_eq option.simps(3))
  apply(subgoal_tac "datalog.later_sibling_2 (\<D>(y \<mapsto> InsertAfter x)) y z \<Longrightarrow> False")
  using datalog.later_sibling.intros datalog.next_sibling.intros datalog.sibling.intros
    db_extension.still_valid_database apply blast
  apply(subgoal_tac "\<exists>mid. datalog.parent_child (\<D>(y \<mapsto> InsertAfter x)) x mid \<and> z < mid \<and> mid < y")
  prefer 2
  apply(metis (no_types, lifting) datalog.later_sibling_2.cases datalog.parent_child.cases
    datalog.parent_child.intros datalog.sibling_elim db_extension.still_valid_database)
  apply clarify
  apply(subgoal_tac "datalog.parent_child \<D> x mid") prefer 2
  apply(metis (no_types, lifting) datalog.parent_child.cases datalog.parent_child.intros
    db_extension.still_valid_database db_extension_datalog fun_upd_other neq_iff)
  apply(meson datalog.first_child_elim datalog.later_child.intros db_extension_datalog)
  done

lemma insert_unchanged_parent_child:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "a \<noteq> x"
  shows "datalog.parent_child \<D> a b \<longleftrightarrow> datalog.parent_child (\<D>(y \<mapsto> InsertAfter x)) a b"
  using assms apply -
  apply(rule iffI)
  apply(subgoal_tac "datalog.is_list_parent (\<D>(y \<mapsto> InsertAfter x)) a") prefer 2
  apply(metis datalog.is_list_elem.intros datalog.is_list_parent.intros(2) datalog.parent_child_elim
    db_extension.still_valid_database db_extension_datalog fun_upd_same is_list_parent_unchanged)
  apply(metis (no_types, lifting) datalog.parent_child.cases datalog.parent_child.intros
    db_extension.oid_not_present db_extension.still_valid_database db_extension_datalog
    map_upd_Some_unfold option.simps(3))
  apply(subgoal_tac "datalog.is_list_parent \<D> a") prefer 2
  apply(metis datalog.has_child.intros datalog.parent_child.cases db_extension.still_valid_database
    insert_has_no_child is_list_parent_unchanged)
  apply(metis (no_types, lifting) datalog.parent_child.intros datalog.parent_child_elim
    db_extension.still_valid_database db_extension_datalog map_upd_Some_unfold operation.inject(2))
  done

lemma insert_unchanged_has_child:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "a \<noteq> x"
  shows "datalog.has_child (\<D>(y \<mapsto> InsertAfter x)) a \<longleftrightarrow> datalog.has_child \<D> a"
  using assms
  by(meson datalog.has_child.intros datalog.has_child_elim db_extension.still_valid_database
    db_extension_datalog insert_unchanged_parent_child)

lemma insert_unchanged_later_child:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "a \<noteq> x"
  shows "datalog.later_child (\<D>(y \<mapsto> InsertAfter x)) a c \<longleftrightarrow> datalog.later_child \<D> a c"
  using assms by(meson datalog.later_child.simps db_extension.still_valid_database
    db_extension_datalog insert_unchanged_parent_child)

lemma insert_unchanged_sibling:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "a \<noteq> y" and "b \<noteq> y"
  shows "datalog.sibling \<D> a b \<longleftrightarrow> datalog.sibling (\<D>(y \<mapsto> InsertAfter x)) a b"
  using assms apply -
  apply(rule iffI)
  apply(subgoal_tac "\<exists>p. \<D> a = Some (InsertAfter p) \<and> \<D> b = Some (InsertAfter p) \<and> datalog.is_list_parent \<D> p")
  prefer 2
  apply(meson datalog.parent_child.cases datalog.sibling_elim db_extension_datalog)
  apply clarify
  apply(subgoal_tac "datalog.is_list_parent (\<D>(y \<mapsto> InsertAfter x)) p") prefer 2
  apply(metis datalog.is_list_elem.intros datalog.is_list_parent.intros(2)
    db_extension.still_valid_database fun_upd_same is_list_parent_unchanged)
  apply(subgoal_tac "datalog.parent_child (\<D>(y \<mapsto> InsertAfter x)) p a") prefer 2
  apply(simp add: datalog.parent_child.intros db_extension.still_valid_database)
  apply(subgoal_tac "datalog.parent_child (\<D>(y \<mapsto> InsertAfter x)) p b") prefer 2
  apply(simp add: datalog.parent_child.intros db_extension.still_valid_database)
  using datalog.sibling.intros db_extension.still_valid_database apply blast
  apply(subgoal_tac "\<exists>p. (\<D>(y \<mapsto> InsertAfter x)) a = Some (InsertAfter p) \<and>
                         (\<D>(y \<mapsto> InsertAfter x)) b = Some (InsertAfter p) \<and>
                         datalog.is_list_parent (\<D>(y \<mapsto> InsertAfter x)) p", clarify)
  prefer 2
  apply(meson datalog.parent_child_elim datalog.sibling.cases db_extension.still_valid_database)
  apply(subgoal_tac "\<D> a = Some (InsertAfter p)")
  apply(subgoal_tac "\<D> b = Some (InsertAfter p)")
  apply(metis datalog.insert_ref_older datalog.parent_child.intros datalog.sibling.intros
    db_extension.oid_is_latest db_extension_datalog domI is_list_parent_unchanged order.asym)
  apply simp_all
  done

lemma insert_unchanged_later_sibling:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "a \<noteq> y"
  shows "datalog.later_sibling \<D> a b \<longleftrightarrow> datalog.later_sibling (\<D>(y \<mapsto> InsertAfter x)) a b"
  using assms by(metis (no_types, hide_lams) datalog.later_sibling.simps datalog.parent_child_elim
      datalog.sibling.simps domIff db_extension.oid_is_latest db_extension.still_valid_database
      db_extension_datalog insert_unchanged_sibling not_less_iff_gr_or_eq option.distinct(1))

lemma (in datalog) later_sibling_2_interpolate:
  assumes "later_sibling_2 x z"
  shows "\<exists>y. sibling x y \<and> sibling x z \<and> z < y \<and> y < x"
  using assms
  apply(induction rule: later_sibling_2.induct)
  apply(rule_tac x=n in exI)
  apply auto
  done

lemma insert_unchanged_later_sibling_2:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "a \<noteq> y"
  shows "datalog.later_sibling_2 \<D> a b \<longleftrightarrow> datalog.later_sibling_2 (\<D>(y \<mapsto> InsertAfter x)) a b"
  using assms apply -
  apply(rule iffI)
  apply(subgoal_tac "\<exists>n. datalog.sibling \<D> a n \<and> datalog.sibling \<D> a b \<and> b < n \<and> n < a") prefer 2
  using datalog.later_sibling_2_interpolate db_extension_datalog apply blast
  apply clarify
  apply(subgoal_tac "datalog.sibling (\<D>(y \<mapsto> InsertAfter x)) a n") prefer 2
  apply(meson datalog.later_sibling.intros datalog.later_sibling_elim
   db_extension.still_valid_database db_extension_datalog insert_unchanged_later_sibling)
  apply(subgoal_tac "datalog.sibling (\<D>(y \<mapsto> InsertAfter x)) a b") prefer 2
  apply(meson datalog.later_sibling.intros datalog.later_sibling_elim less_trans
    db_extension.still_valid_database db_extension_datalog insert_unchanged_later_sibling)
  using datalog.later_sibling_2.intros db_extension.still_valid_database apply blast
  apply(subgoal_tac "\<exists>n. datalog.sibling (\<D>(y \<mapsto> InsertAfter x)) a n \<and>
                         datalog.sibling (\<D>(y \<mapsto> InsertAfter x)) a b \<and>
                         b < n \<and> n < a", clarify) prefer 2
  apply(simp add: datalog.later_sibling_2_interpolate db_extension.still_valid_database)
  apply(subgoal_tac "datalog.sibling \<D> a n") prefer 2
  apply(meson datalog.later_sibling.intros datalog.later_sibling_elim
    db_extension.still_valid_database db_extension_datalog insert_unchanged_later_sibling)
  apply(subgoal_tac "datalog.sibling \<D> a b") prefer 2
  apply(meson datalog.later_sibling.intros datalog.later_sibling_elim less_trans
    db_extension.still_valid_database db_extension_datalog insert_unchanged_later_sibling)
  using datalog.later_sibling_2.intros db_extension_datalog apply blast
  done

lemma insert_unchanged_has_next_sibling:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "a \<noteq> y"
  shows "datalog.has_next_sibling \<D> a \<longleftrightarrow> datalog.has_next_sibling (\<D>(y \<mapsto> InsertAfter x)) a"
  using assms apply -
  apply(rule iffI)
  apply(subgoal_tac "\<exists>b. datalog.sibling \<D> a b \<and> b < a", clarify) prefer 2
  apply(meson datalog.has_next_sibling.cases datalog.later_sibling_elim db_extension_datalog)
  apply(subgoal_tac "datalog.sibling (\<D>(y \<mapsto> InsertAfter x)) a b") prefer 2
  apply(meson datalog.later_sibling.intros datalog.later_sibling_elim
    db_extension.still_valid_database db_extension_datalog insert_unchanged_later_sibling)
  using datalog.has_next_sibling.intros datalog.later_sibling.intros
    db_extension.still_valid_database apply blast
  apply(meson datalog.has_next_sibling.cases datalog.has_next_sibling.intros
    db_extension.still_valid_database db_extension_datalog insert_unchanged_later_sibling)
  done

lemma insert_unchanged_first_child:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "a \<noteq> x"
  shows "datalog.first_child \<D> a b \<longleftrightarrow> datalog.first_child (\<D>(y \<mapsto> InsertAfter x)) a b"
  using assms by (meson datalog.first_child.simps db_extension.still_valid_database
    db_extension_datalog insert_unchanged_later_child insert_unchanged_parent_child)

lemma insert_unchanged_next_sibling:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "a \<noteq> y"
  shows "datalog.next_sibling \<D> a b \<longleftrightarrow> datalog.next_sibling (\<D>(y \<mapsto> InsertAfter x)) a b"
  using assms by (simp add: datalog.next_sibling.simps db_extension.still_valid_database
    db_extension_datalog insert_unchanged_later_sibling insert_unchanged_later_sibling_2)

lemma insert_unchanged_sibling_anc_fwd:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "datalog.next_sibling_anc \<D> a b"
    and "a \<noteq> y"
  shows "datalog.next_sibling_anc (\<D>(y \<mapsto> InsertAfter x)) a b"
  using assms apply(induction rule: datalog.next_sibling_anc.induct[where \<D>=\<D>])
  using assms db_extension_datalog apply force+
  apply(subgoal_tac "datalog.next_sibling (\<D>(y \<mapsto> InsertAfter x)) s n") prefer 2 
  using insert_unchanged_next_sibling apply blast
  using datalog.next_sibling_anc.intros(1) db_extension.still_valid_database apply blast
  apply(subgoal_tac "p \<noteq> y") prefer 2
  apply(metis datalog.first_child_has_child datalog.has_child.intros datalog.parent_child_elim
    db_extension.still_valid_database db_extension_datalog insert_first_child insert_has_no_child
    insert_unchanged_has_child)
  apply clarsimp
  apply(subgoal_tac "datalog.parent_child (\<D>(y \<mapsto> InsertAfter x)) p s") prefer 2
  apply(metis (no_types, lifting) datalog.parent_child.cases datalog.parent_child.intros
    db_extension.still_valid_database db_extension_datalog is_list_parent_unchanged map_upd_Some_unfold)
  using datalog.next_sibling_anc.intros(2) db_extension.still_valid_database
    insert_unchanged_has_next_sibling apply blast
  done

lemma insert_unchanged_sibling_anc_back:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "datalog.next_sibling_anc \<D>' a b"
    and "a \<noteq> y"
    and "\<D>' = \<D>(y \<mapsto> InsertAfter x)"
  shows "datalog.next_sibling_anc \<D> a b"
  using assms apply(induction rule: datalog.next_sibling_anc.induct[where \<D>="\<D>'"])
  using assms apply(simp add: db_extension.still_valid_database, simp)
  using datalog.next_sibling_anc.intros(1) db_extension_datalog insert_unchanged_next_sibling apply blast
  apply(subgoal_tac "p \<noteq> y") prefer 2
  using datalog.has_child.intros db_extension.still_valid_database insert_has_no_child apply blast
  apply clarsimp
  apply(subgoal_tac "datalog.parent_child \<D> p s") prefer 2
  apply(simp add: datalog.parent_child.simps db_extension.still_valid_database
    db_extension_datalog is_list_parent_unchanged)
  using datalog.next_sibling_anc.intros(2) db_extension_datalog
    insert_unchanged_has_next_sibling apply blast
  done

lemma insert_unchanged_next_sibling_anc:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "a \<noteq> y"
  shows "datalog.next_sibling_anc \<D> a b \<longleftrightarrow> datalog.next_sibling_anc (\<D>(y \<mapsto> InsertAfter x)) a b"
  using assms insert_unchanged_sibling_anc_fwd insert_unchanged_sibling_anc_back by blast

lemma insert_unchanged_has_sibling_anc:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "a \<noteq> y"
  shows "datalog.has_sibling_anc \<D> a \<longleftrightarrow> datalog.has_sibling_anc (\<D>(y \<mapsto> InsertAfter x)) a"
  using assms apply -
  apply(rule iffI)
  apply(subgoal_tac "\<exists>b. datalog.next_sibling_anc \<D> a b", clarify) prefer 2
  apply(meson datalog.has_sibling_anc_elim db_extension_datalog)
  apply(subgoal_tac "datalog.next_sibling_anc (\<D>(y \<mapsto> InsertAfter x)) a b") prefer 2
  apply(simp add: insert_unchanged_sibling_anc_fwd)
  using datalog.has_sibling_anc.intros db_extension.still_valid_database apply blast
  apply(meson datalog.has_sibling_anc.cases datalog.has_sibling_anc.intros
    db_extension.still_valid_database db_extension_datalog insert_unchanged_sibling_anc_back)
  done

lemma insert_extend_next_sibling_anc:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
    and "\<not> datalog.has_child \<D> x"
  shows "datalog.next_sibling_anc \<D> x z \<longleftrightarrow> datalog.next_sibling_anc (\<D>(y \<mapsto> InsertAfter x)) y z"
  using assms apply -
  apply(rule iffI)
  apply(subgoal_tac "\<not> datalog.has_next_sibling (\<D>(y \<mapsto> InsertAfter x)) y") prefer 2
  using first_child_has_no_sibling apply blast
  apply(subgoal_tac "datalog.next_sibling_anc (\<D>(y \<mapsto> InsertAfter x)) x z") prefer 2
  using datalog.first_child_has_child db_extension.still_valid_database insert_first_child
    insert_has_no_child insert_unchanged_sibling_anc_fwd apply blast
  using datalog.first_child_elim datalog.next_sibling_anc.intros(2)
    db_extension.still_valid_database insert_first_child apply blast
  apply(subgoal_tac "\<not> datalog.next_sibling (\<D>(y \<mapsto> InsertAfter x)) y z") prefer 2
  using datalog.next_sibling_to_has_next_sibling db_extension.still_valid_database
    first_child_has_no_sibling apply blast
  apply(subgoal_tac "datalog.next_sibling_anc (\<D>(y \<mapsto> InsertAfter x)) x z") prefer 2
  apply (metis (no_types, lifting) datalog.next_sibling_anc_elim datalog.parent_child.cases
    db_extension.still_valid_database fun_upd_same operation.inject(2) option.inject)
  using datalog.first_child_has_child db_extension.still_valid_database insert_first_child
    insert_has_no_child insert_unchanged_sibling_anc_back apply blast
  done

lemma insert_immediately_after:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
  shows "datalog.next_elem (\<D>(y \<mapsto> InsertAfter x)) x y"
  using assms
  by (simp add: datalog.next_elem.intros(1) db_extension.still_valid_database insert_first_child)

lemma insert_connect_next:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
  shows "datalog.next_elem \<D> x z \<longleftrightarrow> datalog.next_elem (\<D>(y \<mapsto> InsertAfter x)) y z"
  using assms apply -
  apply(rule iffI)
  apply(case_tac "datalog.first_child \<D> x z")
  apply(simp add: datalog.is_list_elem.intros datalog.next_elem.intros(2)
    datalog.next_sibling_anc.intros(1) db_extension.still_valid_database insert_has_no_child
    insert_next_sibling)
  apply(subgoal_tac "datalog.next_sibling_anc \<D> x z") prefer 2
  using datalog.next_elem.cases db_extension_datalog apply fastforce
  apply(metis datalog.is_list_elem.intros datalog.next_elem.cases datalog.next_elem.intros(2)
    db_extension.still_valid_database db_extension_datalog fun_upd_same
    insert_extend_next_sibling_anc insert_has_no_child)
  apply(subgoal_tac "datalog (\<D>(y \<mapsto> InsertAfter x))")
   apply(rule datalog.next_elem_elim, assumption, assumption)
  using datalog.first_child_has_child db_extension.still_valid_database insert_has_no_child apply blast
   apply(rule datalog.next_sibling_anc_elim, assumption, assumption)
    apply(subgoal_tac "datalog.first_child \<D> x z")
  using datalog.next_elem.intros(1) db_extension_datalog apply blast
    apply(subgoal_tac "datalog.parent_child (\<D>(y \<mapsto> InsertAfter x)) x z")
     prefer 2
     apply(metis datalog.is_list_parent.intros(2) datalog.later_sibling.cases datalog.next_sibling.cases datalog.parent_child.simps datalog.sibling.cases fun_upd_same is_list_parent_unchanged)
    apply(subgoal_tac "datalog.parent_child \<D> x z")
    prefer 2
    apply(metis datalog.later_sibling.cases datalog.next_sibling.cases datalog.parent_child.simps db_extension_datalog fun_upd_apply order.asym)
    apply(rule datalog.first_child.intros)
  using db_extension_datalog apply blast
     apply force
    apply clarsimp
    defer
  apply(subgoal_tac "datalog.next_sibling_anc (\<D>(y \<mapsto> InsertAfter x)) y z") prefer 2
  using datalog.next_elem_elim db_extension.still_valid_database 
  
  done

lemma insert_unchanged_next_elem:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "a \<noteq> x" and "a \<noteq> y"
  shows "datalog.next_elem \<D> a b \<longleftrightarrow> datalog.next_elem (\<D>(y \<mapsto> InsertAfter x)) a b"
  using assms apply -
  apply(rule iffI)
  apply(case_tac "datalog.first_child \<D> a b")
  apply(simp add: datalog.next_elem.intros(1) db_extension.still_valid_database
    insert_unchanged_first_child)
  apply(subgoal_tac "datalog.next_sibling_anc (\<D>(y \<mapsto> InsertAfter x)) a b") prefer 2
  apply(metis datalog.next_elem.cases db_extension_datalog insert_unchanged_sibling_anc_fwd
    option.sel option.simps(3))
  apply(subgoal_tac "\<not> datalog.has_child (\<D>(y \<mapsto> InsertAfter x)) a") prefer 2
  using datalog.next_elem.cases db_extension_datalog insert_unchanged_has_child apply fastforce
  apply(subgoal_tac "datalog.is_list_elem (\<D>(y \<mapsto> InsertAfter x)) a") prefer 2
  apply(metis (no_types, lifting) datalog.first_child_has_child datalog.is_list_elem.simps
    datalog.next_elem.cases db_extension.still_valid_database db_extension_datalog fun_upd_apply
    insert_unchanged_has_child)
  using datalog.next_elem.intros(2) db_extension.still_valid_database apply blast
  apply(case_tac "datalog.first_child (\<D>(y \<mapsto> InsertAfter x)) a b")
  using datalog.next_elem.intros(1) db_extension_datalog insert_unchanged_first_child apply blast
  apply(simp add: datalog.is_list_elem.simps datalog.next_elem.simps db_extension.still_valid_database
    db_extension_datalog insert_unchanged_has_child insert_unchanged_next_sibling_anc)
  done
    
theorem insert_serial:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
    and "(x, z) \<in> datalog.next_elem_rel \<D>"
  shows "datalog.next_elem_rel (\<D>(y \<mapsto> InsertAfter x)) =
         datalog.next_elem_rel \<D> - {(x, z)} \<union> {(x, y), (y, z)}"
  using assms apply -
  apply(subgoal_tac "datalog \<D>") prefer 2
  apply(simp add: db_extension_datalog)
  apply(subgoal_tac "datalog (\<D>(y \<mapsto> InsertAfter x))") prefer 2
  apply(simp add: db_extension.still_valid_database)
  apply(rule equalityI)
  apply(clarsimp simp add: datalog.next_elem_rel_def)
  apply(metis datalog.next_elem_functional insert_connect_next insert_immediately_after
    insert_unchanged_next_elem)
  apply(subgoal_tac "datalog.next_elem (\<D>(y \<mapsto> InsertAfter x)) x y")
  apply(subgoal_tac "datalog.next_elem (\<D>(y \<mapsto> InsertAfter x)) y z")
  apply(subgoal_tac "datalog.next_elem_rel \<D> \<subseteq> datalog.next_elem_rel (\<D>(y \<mapsto> InsertAfter x)) \<union> {(x, z)}")
  apply(clarsimp simp add: datalog.next_elem_rel_def, blast)
  apply(clarsimp simp add: datalog.next_elem_rel_def)
  apply(metis datalog.next_elem_dom_closed datalog.next_elem_functional db_extension.oid_not_present
    domIff insert_unchanged_next_elem)
  apply(simp add: datalog.next_elem_rel_def insert_connect_next)
  apply(simp add: insert_immediately_after)
  done
    
(************** Groundwork for separation logic ******************)
    
definition (in datalog) pfun_of_next_elem :: "'oid \<rightharpoonup> 'oid" where
  "pfun_of_next_elem x \<equiv>
     if \<not>(\<exists>y. next_elem x y) then
       None
     else Some (THE y. next_elem x y)"
  
lemma (in datalog) pfun_of_next_elem_equality [simp]:
  shows "next_elem x y \<longleftrightarrow> (pfun_of_next_elem x = Some y)"
  apply(unfold pfun_of_next_elem_def)
  apply(clarsimp split!: if_split)
  apply(drule next_elem_functional, assumption)
   apply(simp add: the_equality)+
  done
    
term "f(x := z)"
    
theorem insert_serial_pfun_of_next_elem:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
    and "datalog.pfun_of_next_elem \<D> x = z"
  shows "datalog.pfun_of_next_elem (\<D>(y \<mapsto> InsertAfter x)) =
           (((datalog.pfun_of_next_elem \<D>)(x := Some y))(y := z))"
  using assms
  apply(subgoal_tac "datalog \<D> \<and> datalog (\<D>(y \<mapsto> InsertAfter x))")
   prefer 2
   apply(simp add: db_extension.still_valid_database db_extension_datalog)
  apply clarsimp
  apply(cases z; clarsimp)
   apply(subgoal_tac "\<not>(\<exists>y. datalog.next_elem \<D> x y)")
    prefer 2
  using datalog.pfun_of_next_elem_equality datalog.pfun_of_next_elem_def apply fastforce
   apply clarsimp
   prefer 2
   apply(subgoal_tac "datalog.next_elem \<D> x a")
    prefer 2
    apply(clarsimp simp add: datalog.pfun_of_next_elem_def split!: if_split_asm)
    apply(subst (asm) the_equality, assumption)
     apply(simp add: datalog.next_elem_functional)
    apply(meson datalog.pfun_of_next_elem_def datalog.pfun_of_next_elem_equality)
   apply(subgoal_tac "datalog.next_elem (\<D>(y \<mapsto> InsertAfter x)) x y")
    apply(subgoal_tac "datalog.next_elem (\<D>(y \<mapsto> InsertAfter x)) y a")
     apply(rule ext, clarsimp simp add: datalog.pfun_of_next_elem_def split!: if_split if_split_asm)
         apply(simp add: datalog.next_elem_functional the_equality)
        apply(metis datalog.pfun_of_next_elem_def datalog.pfun_of_next_elem_equality option.sel)
  using insert_unchanged_next_elem apply blast
  using insert_unchanged_next_elem apply blast
     apply(metis datalog.next_elem_functional insert_unchanged_next_elem the_equality)
  using insert_connect_next apply blast
  using insert_immediately_after apply blast
  apply(subgoal_tac "datalog.next_elem (\<D>(y \<mapsto> InsertAfter x)) x y")
   apply(rule ext, clarsimp simp add: datalog.pfun_of_next_elem_def split!: if_split if_split_asm)
       defer
       apply(simp add: datalog.next_elem_functional the_equality)
  using insert_unchanged_next_elem apply blast
  using insert_unchanged_next_elem apply blast
    apply(metis datalog.next_elem_functional insert_unchanged_next_elem the_equality)
  using insert_immediately_after apply blast
    sorry
    

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
