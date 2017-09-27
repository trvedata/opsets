theory List_Insert
  imports Datalog
begin

context datalog begin

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
  "\<lbrakk>parent_child parent child1; parent_child parent child2; child1 > child2\<rbrakk> \<Longrightarrow> later_child parent child2"

inductive first_child :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>parent_child parent child; \<not> later_child parent child\<rbrakk> \<Longrightarrow> first_child parent child"

inductive sibling :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>parent_child parent child1; parent_child parent child2\<rbrakk> \<Longrightarrow> sibling child1 child2"

inductive later_sibling :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>sibling sib1 sib2; sib1 > sib2\<rbrakk> \<Longrightarrow> later_sibling sib1 sib2"

inductive later_sibling_2 :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>sibling sib1 sib2; sibling sib1 sib3; sib1 > sib2; sib2 > sib3\<rbrakk> \<Longrightarrow> later_sibling_2 sib1 sib3"

inductive next_sibling :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>later_sibling sib1 sib2; \<not> later_sibling_2 sib1 sib2\<rbrakk> \<Longrightarrow> next_sibling sib1 sib2"

inductive has_next_sibling :: "'oid \<Rightarrow> bool" where
  "\<lbrakk>later_sibling sib1 sib2\<rbrakk> \<Longrightarrow> has_next_sibling sib1"

inductive next_sibling_anc :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>next_sibling start next\<rbrakk> \<Longrightarrow> next_sibling_anc start next" |
  "\<lbrakk>\<not> has_next_sibling start; parent_child parent start; next_sibling_anc parent next\<rbrakk> \<Longrightarrow> next_sibling_anc start next"

inductive has_sibling_anc :: "'oid \<Rightarrow> bool" where
  "\<lbrakk>next_sibling_anc start next\<rbrakk> \<Longrightarrow> has_sibling_anc start"

inductive next_elem :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>first_child prev next\<rbrakk> \<Longrightarrow> next_elem prev next" |
  "\<lbrakk>is_list_elem prev; \<not> has_child prev; next_sibling_anc prev next\<rbrakk> \<Longrightarrow> next_elem prev next"

(*
  grep '^inductive ' isabelle/List_Insert.thy |
  sed -e 's/^inductive //' -e 's/ .*//' -e 's/^/lemmas [intro] = /' -e 's/$/.intros/'
*)
lemmas [intro] = is_list_elem.intros
lemmas [intro] = is_list_parent.intros
lemmas [intro] = parent_child.intros
lemmas [intro] = has_child.intros
lemmas [intro] = later_child.intros
lemmas [intro] = first_child.intros
lemmas [intro] = sibling.intros
lemmas [intro] = later_sibling.intros
lemmas [intro] = later_sibling_2.intros
lemmas [intro] = next_sibling.intros
lemmas [intro] = has_next_sibling.intros
lemmas [intro] = next_sibling_anc.intros
lemmas [intro] = has_sibling_anc.intros
lemmas [intro] = next_elem.intros

(*
  grep 'lbrakk.*Longrightarrow' isabelle/List_Insert.thy |
  sed -e 's/.*Longrightarrow> //' -e 's/".*//' |
  uniq |
  sed -e 's/^\([^ ]*\)/inductive_cases \1_elim [elim]: "\1/' -e 's/$/"/'
*)
inductive_cases is_list_elem_elim [elim]: "is_list_elem oid"
inductive_cases is_list_parent_elim [elim]: "is_list_parent oid"
inductive_cases parent_child_elim [elim]: "parent_child parent child"
inductive_cases has_child_elim [elim]: "has_child parent"
inductive_cases later_child_elim [elim]: "later_child parent child2"
inductive_cases first_child_elim [elim]: "first_child parent child"
inductive_cases sibling_elim [elim]: "sibling child1 child2"
inductive_cases later_sibling_elim [elim]: "later_sibling sib1 sib2"
inductive_cases later_sibling_2_elim [elim]: "later_sibling_2 sib1 sib3"
inductive_cases next_sibling_elim [elim]: "next_sibling sib1 sib2"
inductive_cases has_next_sibling_elim [elim]: "has_next_sibling sib1"
inductive_cases next_sibling_anc_elim [elim]: "next_sibling_anc start next"
inductive_cases has_sibling_anc_elim [elim]: "has_sibling_anc start"
inductive_cases next_elem_elim [elim]: "next_elem prev next"

end

definition (in datalog) next_elem_rel :: "('oid \<times> 'oid) set" where
  "next_elem_rel \<equiv> {(x, y). next_elem x y}"

lemma (in datalog) insert_ref_older:
  assumes "\<D> oid = Some (InsertAfter x)"
  shows "x < oid"
  using assms ref_older by fastforce

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

lemma is_list_elem_unchanged:
  assumes "db_extension \<D> oid oper"
    and "x \<noteq> oid"
  shows "datalog.is_list_elem \<D> x \<longleftrightarrow> datalog.is_list_elem (\<D>(oid \<mapsto> oper)) x"
  using assms by (metis (mono_tags, lifting) datalog.is_list_elem.simps
    db_extension.still_valid_database db_extension_datalog fun_upd_other)

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

lemma insert_unchanged_parent_child:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "a \<noteq> x \<or> b \<noteq> y"
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
  apply(rule_tac x=sib2 in exI)
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

lemma insert_next_sibling:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
  shows "datalog.first_child \<D> x z \<longleftrightarrow> datalog.next_sibling (\<D>(y \<mapsto> InsertAfter x)) y z"
  using assms apply -
  apply(rule iffI)
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
  apply(subgoal_tac "datalog.parent_child \<D> x z") prefer 2
  apply(metis (no_types, lifting) datalog.later_sibling_elim datalog.next_sibling_elim
    datalog.parent_child.cases datalog.parent_child.intros datalog.sibling_elim
    db_extension.still_valid_database db_extension_datalog fun_upd_apply not_less_iff_gr_or_eq)
  apply(subgoal_tac "z < y") prefer 2
  apply(meson datalog.later_sibling_elim datalog.next_sibling_elim db_extension.still_valid_database)
  apply(subgoal_tac "datalog.later_child \<D> x z \<Longrightarrow> False")
  using datalog.first_child.intros db_extension_def apply blast
  apply(subgoal_tac "\<exists>n. datalog.parent_child \<D> x n \<and> z < n", clarify) prefer 2
  apply(meson datalog.later_child_elim db_extension_datalog)
  apply(subgoal_tac "datalog.parent_child (\<D>(y \<mapsto> InsertAfter x)) x n") prefer 2
  apply(metis datalog.first_child_elim db_extension.still_valid_database insert_first_child
    insert_unchanged_parent_child)
  apply(meson datalog.first_child_elim datalog.later_sibling_2.simps datalog.later_sibling_elim
    datalog.next_sibling_elim datalog.parent_child.cases datalog.sibling.intros
    db_extension.axioms(2) db_extension_axioms_def db_extension_datalog domI insert_first_child)
  done

lemma insert_has_next_sibling:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
  shows "datalog.has_child \<D> x \<longleftrightarrow> datalog.has_next_sibling (\<D>(y \<mapsto> InsertAfter x)) y"
  using assms apply -
  apply(rule iffI)
  apply(subgoal_tac "\<exists>n. datalog.parent_child \<D> x n", clarify) prefer 2
  apply(meson datalog.has_child_elim db_extension_datalog)
  apply(subgoal_tac "datalog.parent_child (\<D>(y \<mapsto> InsertAfter x)) x n") prefer 2
  apply(metis datalog.first_child_elim db_extension.still_valid_database insert_first_child
    insert_unchanged_parent_child)
  apply(meson datalog.first_child_elim datalog.has_next_sibling.intros datalog.later_sibling.intros
    datalog.parent_child.cases datalog.sibling.intros db_extension.axioms(2) db_extension_axioms_def
    db_extension_datalog domI insert_first_child)
  using first_child_has_no_sibling apply blast
  done

lemma insert_unchanged_sibling_anc_fwd:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "datalog.next_sibling_anc \<D> a b"
    and "a \<noteq> y"
  shows "datalog.next_sibling_anc (\<D>(y \<mapsto> InsertAfter x)) a b"
  using assms apply(induction rule: datalog.next_sibling_anc.induct[where \<D>=\<D>])
  using assms db_extension_datalog apply force+
  apply(subgoal_tac "datalog.next_sibling (\<D>(y \<mapsto> InsertAfter x)) start next") prefer 2 
  using insert_unchanged_next_sibling apply blast
  using datalog.next_sibling_anc.intros(1) db_extension.still_valid_database apply blast
  apply(subgoal_tac "parent \<noteq> y") prefer 2
  apply(metis datalog.first_child_has_child datalog.has_child.intros datalog.parent_child_elim
    db_extension.still_valid_database db_extension_datalog insert_first_child insert_has_no_child
    insert_unchanged_has_child)
  apply clarsimp
  apply(subgoal_tac "datalog.parent_child (\<D>(y \<mapsto> InsertAfter x)) parent start") prefer 2
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
  apply(subgoal_tac "parent \<noteq> y") prefer 2
  using datalog.has_child.intros db_extension.still_valid_database insert_has_no_child apply blast
  apply clarsimp
  apply(subgoal_tac "datalog.parent_child \<D> parent start") prefer 2
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
  apply(subgoal_tac "datalog \<D> \<and> datalog (\<D>(y \<mapsto> InsertAfter x))", clarify) prefer 2
  apply(simp add: db_extension.still_valid_database db_extension_datalog)
  apply(rule datalog.next_elem_elim, assumption, assumption)
  using datalog.first_child_has_child db_extension.still_valid_database insert_has_no_child apply blast
  apply(rule datalog.next_sibling_anc_elim, assumption, assumption)
  using datalog.next_elem.intros(1) insert_next_sibling apply blast
  apply(subgoal_tac "parent = x", clarsimp) prefer 2
  using datalog.parent_child.cases apply fastforce
  apply(subgoal_tac "\<not> datalog.has_child \<D> x") prefer 2
  using insert_has_next_sibling apply blast
  apply(subgoal_tac "datalog.next_sibling_anc \<D> x z")
  apply(meson datalog.has_next_sibling.cases datalog.is_list_elem.simps datalog.later_sibling_elim
    datalog.next_elem.intros(2) datalog.next_sibling_anc.cases datalog.next_sibling_to_has_next_sibling
    datalog.parent_child_elim datalog.sibling_elim)
  using insert_extend_next_sibling_anc apply blast
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
  apply(meson datalog.next_elem_elim db_extension_datalog insert_unchanged_sibling_anc_fwd)
  apply(subgoal_tac "\<not> datalog.has_child (\<D>(y \<mapsto> InsertAfter x)) a") prefer 2
  using datalog.next_elem.cases db_extension_datalog insert_unchanged_has_child apply fastforce
  apply(subgoal_tac "datalog.is_list_elem (\<D>(y \<mapsto> InsertAfter x)) a") prefer 2
  apply (metis datalog.is_list_elem.simps datalog.next_elem.cases db_extension.still_valid_database
    db_extension_datalog fun_upd_apply)
  using datalog.next_elem.intros(2) db_extension.still_valid_database apply blast
  apply(case_tac "datalog.first_child (\<D>(y \<mapsto> InsertAfter x)) a b")
  using datalog.next_elem.intros(1) db_extension_datalog insert_unchanged_first_child apply blast
  apply(simp add: datalog.is_list_elem.simps datalog.next_elem.simps db_extension.still_valid_database
    db_extension_datalog insert_unchanged_has_child insert_unchanged_next_sibling_anc)
  done

lemma insert_unrelated_next_elem:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "\<not> datalog.is_list_parent \<D> x"
  shows "datalog.next_elem \<D> a b \<longleftrightarrow> datalog.next_elem (\<D>(y \<mapsto> InsertAfter x)) a b"
  using assms apply -
  apply(rule iffI)
  apply(metis datalog.first_child_elim datalog.is_list_parent.intros(2) datalog.next_elem.simps
    datalog.next_elem_dom_closed datalog.parent_child.cases db_extension.oid_not_present
    db_extension_datalog domIff insert_unchanged_next_elem)
  apply(case_tac "a = y", clarify)
  apply(subgoal_tac "datalog.next_sibling_anc (\<D>(y \<mapsto> InsertAfter x)) y b") prefer 2
  using datalog.first_child_has_child datalog.next_elem_elim db_extension.still_valid_database
    insert_has_no_child apply blast
  apply(subgoal_tac "datalog (\<D>(y \<mapsto> InsertAfter x))") prefer 2
  using db_extension.still_valid_database apply blast
  apply(subgoal_tac "\<exists>p. datalog.parent_child (\<D>(y \<mapsto> InsertAfter x)) p y", clarify) prefer 2
  apply(meson datalog.has_child.simps datalog.next_sibling_anc.simps
    datalog.next_sibling_to_has_next_sibling datalog.parent_child.cases db_extension_datalog
    first_child_has_no_sibling)
  apply(metis (mono_tags) datalog.has_child.intros datalog.parent_child.cases
    db_extension.oid_not_present db_extension_datalog insert_has_no_child
    insert_unchanged_parent_child is_list_parent_unchanged option.simps(3))
  apply(metis datalog.first_child_elim datalog.is_list_parent.simps datalog.next_elem.simps
    datalog.parent_child.cases db_extension.still_valid_database insert_unchanged_next_elem
    is_list_parent_unchanged)
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

definition (in datalog) next_elem_fun :: "'oid \<rightharpoonup> 'oid" where
  "next_elem_fun x \<equiv>
     if \<nexists>y. next_elem x y
     then None
     else Some (THE y. next_elem x y)"

lemma (in datalog) next_elem_fun_equality [simp]:
  shows "next_elem x y \<longleftrightarrow> (next_elem_fun x = Some y)"
  apply(unfold next_elem_fun_def)
  apply(clarsimp split!: if_split)
  apply(drule next_elem_functional, assumption)
  apply(simp add: the_equality)+
  done

theorem insert_serial_fun:
  assumes "db_extension \<D> y (InsertAfter x)"
    and "datalog.is_list_parent \<D> x"
    and "datalog.next_elem_fun \<D> x = z"
  shows "datalog.next_elem_fun (\<D>(y \<mapsto> InsertAfter x)) =
       ((datalog.next_elem_fun \<D>)(x := Some y))(y := z)"
  using assms
  apply(subgoal_tac "datalog \<D> \<and> datalog (\<D>(y \<mapsto> InsertAfter x))") prefer 2
  apply(simp add: db_extension.still_valid_database db_extension_datalog)
  apply clarsimp
  apply(cases z; clarsimp)
  apply(subgoal_tac "\<nexists>y. datalog.next_elem \<D> x y") prefer 2
  using datalog.next_elem_fun_equality datalog.next_elem_fun_def apply fastforce
  apply(subgoal_tac "datalog.next_elem (\<D>(y \<mapsto> InsertAfter x)) x y") prefer 2
  using insert_immediately_after apply blast
  apply(rule ext, clarsimp simp add: datalog.next_elem_fun_def split!: if_split if_split_asm)
  using insert_connect_next apply blast
  using datalog.next_elem_functional apply blast
  using insert_unchanged_next_elem apply blast
  using insert_unchanged_next_elem apply blast
  apply(metis datalog.next_elem_functional insert_unchanged_next_elem theI_unique)
  apply(subgoal_tac "datalog.next_elem \<D> x a") prefer 2
  apply(simp add: datalog.next_elem_fun_equality)
  apply(subgoal_tac "datalog.next_elem (\<D>(y \<mapsto> InsertAfter x)) x y")
  apply(subgoal_tac "datalog.next_elem (\<D>(y \<mapsto> InsertAfter x)) y a")
  apply(rule ext, clarsimp simp add: datalog.next_elem_fun_def split!: if_split if_split_asm)
  apply(simp add: datalog.next_elem_functional the_equality)
  apply(metis datalog.next_elem_fun_def datalog.next_elem_fun_equality option.sel)
  using insert_unchanged_next_elem apply blast
  using insert_unchanged_next_elem apply blast
  apply(metis datalog.next_elem_functional insert_unchanged_next_elem the_equality)
  using insert_connect_next apply blast
  using insert_immediately_after apply blast
  done

end
