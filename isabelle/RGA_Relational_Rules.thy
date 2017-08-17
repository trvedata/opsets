theory RGA_Relational_Rules
  imports Main "~~/src/HOL/Library/Product_Order"
begin

datatype 'eid operation
  = MakeList
  | Insert "'eid"

type_synonym 'eid database = "'eid \<rightharpoonup> 'eid operation"

definition insert :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool" where
  "insert \<D> parent i \<longleftrightarrow> \<D> i = Some (Insert parent)"

inductive list_elem    :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> bool"
  and has_child        :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> bool"
  and child            :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and later_child      :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and sibling          :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and later_sibling    :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and later_sibling_2  :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and has_next_sibling :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> bool"
where
  "\<lbrakk>insert \<D> parent i\<rbrakk> \<Longrightarrow> list_elem \<D> i" |
  "\<lbrakk>insert \<D> parent c\<rbrakk> \<Longrightarrow> has_child \<D> parent" |
  "\<lbrakk>insert \<D> parent c\<rbrakk> \<Longrightarrow> child \<D> parent c" |
  "\<lbrakk>child \<D> parent c;  child \<D> parent p; c < p\<rbrakk> \<Longrightarrow> later_child \<D> parent c" |
  "\<lbrakk>child \<D> parent c1; child \<D> parent c2\<rbrakk> \<Longrightarrow> sibling \<D> c1 c2" |
  "\<lbrakk>sibling \<D> p l; l < p\<rbrakk> \<Longrightarrow> later_sibling \<D> p l" |
  "\<lbrakk>sibling \<D> p n; sibling \<D> p l; l < n; n < p\<rbrakk> \<Longrightarrow> later_sibling_2 \<D> p l" |
  "\<lbrakk>later_sibling \<D> p n\<rbrakk> \<Longrightarrow> has_next_sibling \<D> p"
  
inductive_cases list_elem_ind: "list_elem xs x"
inductive_cases has_child_ind: "has_child xs x"
inductive_cases child_ind: "child xs x y"
inductive_cases later_child_ind: "later_child xs x y"
inductive_cases sibling_ind: "sibling xs x y"
inductive_cases later_sibling_ind: "later_sibling xs x y"
inductive_cases later_sibling_2_ind: "later_sibling_2 xs x y"  
inductive_cases has_next_sibling_ind: "has_next_sibling xs x"

inductive first_child  :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and next_sibling     :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and next_sibling_anc :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and next_elem        :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
where
  "\<lbrakk>child \<D> parent c; \<not> later_child \<D> parent c\<rbrakk> \<Longrightarrow> first_child \<D> parent c" |
  "\<lbrakk>later_sibling \<D> p n; \<not> later_sibling_2 \<D> p n\<rbrakk> \<Longrightarrow> next_sibling \<D> p n" |
  "\<lbrakk>next_sibling \<D> s n\<rbrakk> \<Longrightarrow> next_sibling_anc \<D> s n" |
  "\<lbrakk>\<not> has_next_sibling \<D> s; child \<D> p s; next_sibling_anc \<D> p n\<rbrakk> \<Longrightarrow> next_sibling_anc \<D> s n" |
  "\<lbrakk>first_child \<D> p n\<rbrakk> \<Longrightarrow> next_elem \<D> p n" |
  "\<lbrakk>list_elem \<D> p; \<not> has_child \<D> p; next_sibling_anc \<D> p n\<rbrakk> \<Longrightarrow> next_elem \<D> p n"  

inductive_cases first_child_ind: "first_child xs x y"
inductive_cases next_sibling_ind: "next_sibling \<D> s n"
inductive_cases next_sibling_anc_ind: "next_sibling_anc \<D> s n"
inductive_cases next_elem_ind: "next_elem xs x y"
  
lemmas rga_intros [intro] =
  list_elem_has_child_child_later_child_sibling_later_sibling_later_sibling_2_has_next_sibling.intros
  first_child_next_sibling_next_sibling_anc_next_elem.intros
  
lemmas rga_elims = list_elem_ind has_child_ind child_ind later_child_ind sibling_ind
  later_sibling_ind later_sibling_2_ind has_next_sibling_ind first_child_ind next_sibling_ind
  next_sibling_anc_ind next_elem_ind
  
definition next_elem_rel :: "'eid::{linorder} database \<Rightarrow> ('eid \<times> 'eid) set" where
  "next_elem_rel \<D> \<equiv> {(x, y). next_elem \<D> x y}"

inductive list_suffix :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid list \<Rightarrow> bool"
  and list_full       :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid list \<Rightarrow> bool"
where
  "\<lbrakk>\<not> next_elem \<D> p x\<rbrakk> \<Longrightarrow> list_suffix \<D> p []" |
  "\<lbrakk>next_elem \<D> p x; list_suffix \<D> x xs\<rbrakk> \<Longrightarrow> list_suffix \<D> p (x#xs)" |
  "\<lbrakk>\<D> i = Some MakeList; list_suffix \<D> i xs\<rbrakk> \<Longrightarrow> list_full \<D> i xs"

inductive elem_index :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> nat \<Rightarrow> bool" where
  "\<lbrakk>\<D> head = Some MakeList; next_elem \<D> head x\<rbrakk> \<Longrightarrow> elem_index \<D> x 0" |
  "\<lbrakk>elem_index \<D> x i; next_elem \<D> x y\<rbrakk> \<Longrightarrow> elem_index \<D> y (Suc i)"

lemma first_child_unique:
  assumes "first_child \<D> parent child1"
  and "first_child \<D> parent child2"
  shows "child1 = child2"
by(meson assms rga_intros first_child.cases not_less_iff_gr_or_eq)

lemma next_sibling_unique:
  assumes "next_sibling \<D> prev next1"
  and "next_sibling \<D> prev next2"
  shows "next1 = next2"
  by(meson assms rga_intros later_sibling.cases next_sibling.cases not_less_iff_gr_or_eq)

lemma parent_unique:
  assumes "child \<D> par1 n"
  and "child \<D> par2 n"
  shows "par1 = par2"
  by(metis (no_types, lifting) insert_def assms child.cases operation.inject option.inject)
  
lemma next_elem_unique:
  shows "first_child \<D> parent child1 \<Longrightarrow> first_child \<D> parent child2 \<Longrightarrow> child1 = child2"
    and "next_sibling \<D> prev next1 \<Longrightarrow> next_sibling \<D> prev next2 \<Longrightarrow> next1 = next2"
    and "next_sibling_anc \<D> s n1 \<Longrightarrow> next_sibling_anc \<D> s n2 \<Longrightarrow> n1 = n2"
    and "next_elem \<D> prev next1 \<Longrightarrow> next_elem \<D> prev next2 \<Longrightarrow> next1 = next2"
     apply(induction arbitrary: child2 and next2 and n2 rule: first_child_next_sibling_next_sibling_anc_next_elem.inducts)
  using first_child_unique apply blast
  using next_sibling_unique apply blast
     apply(erule next_sibling_anc_ind)
      apply blast
  using next_sibling_ind apply blast
    apply (metis has_next_sibling.simps next_sibling_anc.simps next_sibling_ind parent_unique)
    apply (meson child.cases first_child.cases next_elem.cases rga_intros(2))
    by (meson child.cases first_child.cases list_elem_has_child_child_later_child_sibling_later_sibling_later_sibling_2_has_next_sibling.intros(2) next_elem.cases)

definition next_elem_fun :: "'a::{linorder} database \<Rightarrow> 'a \<Rightarrow> 'a option" where
  "next_elem_fun \<D> prev \<equiv>
     if \<exists>x. next_elem \<D> prev x then
       Some (THE x. next_elem \<D> prev x)
     else None"
  
definition list_of_database :: "'a::{linorder} database \<Rightarrow> ('a \<times> 'a operation) list" where
  "list_of_database \<D> \<equiv>
    let ss = sorted_list_of_set (dom \<D>) in
      List.map (\<lambda>x. (x, Option.the (\<D> x))) ss"
  
lemma
  assumes "list_of_database \<D> = xs"
  shows "\<D> = map_of xs"
  using assms
  apply(induction xs)
   apply(clarsimp simp add: list_of_database_def)
  sorry
  
lemma not_child_empty [simp]:
  shows "\<not> child Map.empty x y"
  apply(clarsimp)
  apply(erule child_ind, auto simp add: insert_def)
  done
    
lemma not_first_child_empty [simp]:
  shows "\<not> first_child Map.empty x y"
    apply clarsimp
  apply(erule first_child_ind)
  apply auto
  done
    
lemma not_next_sibling_anc_empty [simp]:
  shows "\<not> next_sibling_anc Map.empty x y"
  apply clarsimp
  apply(erule next_sibling_anc_ind)
   apply(erule next_sibling_ind)
   apply(erule later_sibling_ind)
   apply(erule sibling_ind)
   apply simp+
  done
    
lemma not_next_elem_empty [simp]:
  shows "\<not> next_elem Map.empty x y"
  apply clarsimp
  apply(erule next_elem_ind)
   apply simp+
  done

(*    
lemma insert_serial:       
  assumes "(x, z) \<in> next_elem_rel (map_of xs)"
  shows "next_elem_rel (map_of (xs@[(y, Insert x)])) = next_elem_rel (map_of xs) - {(x, z)} \<union> {(x, y), (y, z)}"
  apply(induction xs rule: List.rev_induct)
   apply(clarsimp simp add: next_elem_rel_def)
   apply(rule equalityI, rule subsetI, clarsimp)
    apply(case_tac "a=y"; clarsimp)
    apply(erule rga_elims)+
      apply(clarsimp simp add: insert_def)
      apply(case_tac "b=y"; clarsimp)
     apply(erule rga_elims)+
      apply(clarsimp simp add: insert_def)
      apply(case_tac "b=y"; clarsimp)
     apply(erule child_ind, clarsimp simp add: insert_def)
     apply(erule rga_elims)+
          apply(clarsimp simp add: insert_def)
      apply(case_tac "b=y"; clarsimp)
      apply force
  
lemma
  assumes "list_of_database \<D> = xs @ [x] @ ys"
    and "\<D>(fst y) = None"
    and "\<D>' = \<D>(fst y \<mapsto> Insert (fst x))"
    and "list_of_database \<D>' = xs @ [x] @ ys @ [y]"
    shows "next_elem_rel \<D>' = next_elem_rel \<D> - {(x, z)} \<union> {(x, y), (y, z)}"
  using assms
  apply clarsimp
  apply(induction ys rule: List.rev_induct)
*)
  
    (*
lemma
  shows "next_elem D' a b \<Longrightarrow> D' = (\<D>(y \<mapsto> Insert x)) \<Longrightarrow> \<D> y = None \<Longrightarrow> next_elem \<D> x z \<Longrightarrow> (\<And>n. n \<in> dom \<D> \<Longrightarrow> n < y) \<Longrightarrow> a = x \<longrightarrow> b \<noteq> y \<Longrightarrow> next_elem \<D> a b \<longrightarrow> a = x \<and> b = z \<Longrightarrow> a = y \<and> b = z"
  apply(induction rule: first_child_next_sibling_next_sibling_anc_next_elem.inducts(4))
       prefer 5
       apply(erule rga_elims)+
    apply(clarsimp simp add: insert_def split: if_split_asm)
*)
    
lemma child_D_None_contr:
  assumes "D y = None"
  shows "\<not> child D p y"
  using assms
  apply clarsimp
  apply(erule child_ind)
  apply(clarsimp simp add: insert_def)
  done
    
lemma child_D_dom:
  assumes "child D p y"
  shows "y \<in> dom D"
using child_D_None_contr assms by blast

  (*
list_elem    :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> bool"
  and has_child        :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> bool"
  and child            :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and later_child      :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and sibling          :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and later_sibling    :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and later_sibling_2  :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and has_next_sibling :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> bool"
where
*)
  
lemma later_sibling_insert_invariant_1:
  shows "list_elem D n \<Longrightarrow> D y = None \<Longrightarrow> D' = D(y \<mapsto> Insert z) \<Longrightarrow> list_elem D' n"
    and "has_child D n \<Longrightarrow> D y = None \<Longrightarrow> D' = D(y \<mapsto> Insert z) \<Longrightarrow> has_child D' n"
    and "child D p n \<Longrightarrow> D y = None \<Longrightarrow> D' = D(y \<mapsto> Insert z) \<Longrightarrow> child D' p n"
    and "later_child D p n \<Longrightarrow> D y = None \<Longrightarrow> D' = D(y \<mapsto> Insert z) \<Longrightarrow> later_child D' p n"
    and "sibling D p n \<Longrightarrow> D y = None \<Longrightarrow> D' = D(y \<mapsto> Insert z) \<Longrightarrow>  sibling D' p n"
    and "later_sibling D p n \<Longrightarrow> D y = None \<Longrightarrow> D' = D(y \<mapsto> Insert z) \<Longrightarrow> later_sibling D' p n"
    and "later_sibling_2 D p n \<Longrightarrow> D y = None \<Longrightarrow> D' = D(y \<mapsto> Insert z) \<Longrightarrow> later_sibling_2 D' p n"
    and "has_next_sibling D p \<Longrightarrow> D y = None \<Longrightarrow> D' = D(y \<mapsto> Insert z) \<Longrightarrow> has_next_sibling D' p"
         apply(induction rule: list_elem_has_child_child_later_child_sibling_later_sibling_later_sibling_2_has_next_sibling.inducts)
         apply(clarsimp simp add: insert_def)
         apply(rule_tac parent=parent in rga_intros(1))
         apply(clarsimp simp add: insert_def)
             apply(rule_tac c=c in rga_intros(2))
        apply(clarsimp simp add: insert_def)
       apply(rule rga_intros)
       apply(clarsimp simp add: insert_def)
      apply(rule_tac p=p in rga_intros(4))
        apply force
       apply force
      apply assumption
     apply(rule_tac parent=parent in rga_intros(5))
      apply force
     apply force
    apply(rule rga_intros)
     apply force
    apply assumption
   apply(rule_tac n=n in rga_intros(7))
      apply force
     apply force
    apply assumption
   apply assumption
  apply(rule rga_intros)
    apply force
  done
    
lemma later_sibling_insert_invariant_2:
  shows "list_elem D' n \<Longrightarrow> n \<noteq> y \<Longrightarrow> D y = None \<Longrightarrow> D' = D(y \<mapsto> Insert z) \<Longrightarrow> list_elem D n"
    and "has_child D' n \<Longrightarrow> n \<noteq> z \<Longrightarrow> D y = None \<Longrightarrow> D' = D(y \<mapsto> Insert z) \<Longrightarrow> has_child D n"
    and "child D' p n \<Longrightarrow> n \<noteq> y \<Longrightarrow> D y = None \<Longrightarrow> D' = D(y \<mapsto> Insert z) \<Longrightarrow> child D p n"
    and "later_child D' p n \<Longrightarrow> n \<noteq> y \<Longrightarrow> D y = None \<Longrightarrow> D' = D(y \<mapsto> Insert z) \<Longrightarrow> (z \<noteq> p \<longrightarrow> later_child D p n \<and> z = p \<longrightarrow> True)"
    and "sibling D' p n \<Longrightarrow> n \<noteq> y \<Longrightarrow> D y = None \<Longrightarrow> D' = D(y \<mapsto> Insert z) \<Longrightarrow>  sibling D p n"
    and "later_sibling D' p n \<Longrightarrow> n \<noteq> y \<Longrightarrow> D y = None \<Longrightarrow> D' = D(y \<mapsto> Insert z) \<Longrightarrow> later_sibling D p n"
    and "later_sibling_2 D' p n \<Longrightarrow> n \<noteq> y \<Longrightarrow> D y = None \<Longrightarrow> D' = D(y \<mapsto> Insert z) \<Longrightarrow> later_sibling_2 D p n"
    and "has_next_sibling D' p \<Longrightarrow> D y = None \<Longrightarrow> D' = D(y \<mapsto> Insert z) \<Longrightarrow> has_next_sibling D p"
         apply(induction rule: list_elem_has_child_child_later_child_sibling_later_sibling_later_sibling_2_has_next_sibling.inducts)
         apply(clarsimp simp add: insert_def)
         apply(rule_tac parent=parent in rga_intros(1))
         apply(clarsimp simp add: insert_def split!: if_split_asm)
        apply(rule_tac c=c in rga_intros(2))
        apply(clarsimp simp add: insert_def split!: if_split_asm)
       apply(rule rga_intros)
       apply(clarsimp simp add: insert_def split!: if_split_asm)
      apply(rule_tac p=p in rga_intros(4))
        apply force
    apply force
    
  
lemma insert_serial:
  shows "first_child \<D> x z \<Longrightarrow> (\<And>n. n \<in> dom \<D> \<Longrightarrow> n < y) \<Longrightarrow> \<D> y = None \<Longrightarrow> \<D>' = \<D>(y \<mapsto> Insert x) \<Longrightarrow> \<not> first_child \<D>' x z \<and> first_child \<D>' x y"
    and "next_sibling \<D> x z \<Longrightarrow> \<D> y = None \<Longrightarrow> \<D>' = \<D>(y \<mapsto> Insert x) \<Longrightarrow> next_sibling \<D>' x z"
    and "next_sibling_anc \<D> x z \<Longrightarrow> \<D> y = None \<Longrightarrow> \<D>' = \<D>(y \<mapsto> Insert x) \<Longrightarrow> next_sibling_anc \<D>' x z"
    and "next_elem \<D> x z \<Longrightarrow> (\<And>n. n \<in> dom \<D> \<Longrightarrow> n < y) \<Longrightarrow> \<D> y = None \<Longrightarrow> \<D>' = \<D>(y \<mapsto> Insert x) \<Longrightarrow> \<not> next_elem \<D>' x z \<and> next_elem \<D>' x y \<and> next_elem \<D>' y z"
     apply(induction rule: first_child_next_sibling_next_sibling_anc_next_elem.inducts)
       apply clarsimp
       apply(rule conjI, rule notI)
  apply(erule first_child_ind)
  apply(erule child_ind) back
        apply(clarsimp simp add: insert_def split: if_split_asm)
  using child_D_None_contr apply metis
        apply(subgoal_tac "later_child (\<D>(y \<mapsto> Insert parent)) parent c", force)
        apply(rule rga_intros(4)[where p="y"])
          apply(rule rga_intros, clarsimp simp add: insert_def)+
        apply force
       apply(rule rga_intros)
        apply(rule rga_intros, clarsimp simp add: insert_def)+
       apply(rule notI)
       apply(erule later_child_ind)
       apply(subgoal_tac "p \<in> dom \<D>", force)
  using child_D_dom apply(metis domIff fun_upd_other neq_iff)
    apply(rule rga_intros)
    using later_sibling_insert_invariant apply blast
    using later_sibling_insert_invariant apply metis
       apply(rule rga_intros)
      using later_sibling_insert_invariant apply blast
      defer
       

    
lemma insert_serial:
  assumes "\<D> y = None" and "\<D>' = \<D>(y \<mapsto> Insert x)"
    and "(x, z) \<in> next_elem_rel \<D>"
    and "\<And>n. n \<in> dom \<D> \<Longrightarrow> n < y"
  shows "next_elem_rel \<D>' = next_elem_rel \<D> - {(x, z)} \<union> {(x, y), (y, z)}"
using assms
  apply(clarsimp simp add: next_elem_rel_def)
  apply(rule equalityI, rule subsetI; clarsimp)

end
