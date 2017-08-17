theory RGA_Relational_Rules
  imports Main
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

lemmas rga_intros [intro] =
  list_elem_has_child_child_later_child_sibling_later_sibling_later_sibling_2_has_next_sibling.intros
  first_child_next_sibling_next_sibling_anc_next_elem.intros

definition next_elem_rel :: "'eid::{linorder} database \<Rightarrow> ('eid \<times> 'eid) set" where
  "next_elem_rel \<D> \<equiv> {(x, y). next_elem \<D> x y}"
  
lemma insert_serial:
  assumes "\<D> y = None" and "\<D>' = \<D>(y \<mapsto> Insert x)"
    and "(x, z) \<in> next_elem_rel \<D>"
    and "\<forall>n \<in> dom \<D>. n < y"
  shows "next_elem_rel \<D>' = next_elem_rel \<D> - {(x, z)} \<union> {(x, y), (y, z)}"
  oops

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
    
inductive_cases next_sibling_ind: "next_sibling \<D> s n"
inductive_cases next_sibling_anc_ind: "next_sibling_anc \<D> s n"
  
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
    
    
    

lemma elem_index_biject:
  assumes "elem_index \<D> x i" and "elem_index \<D> y j"
  shows "i = j \<longleftrightarrow> x = y"
  oops


end
