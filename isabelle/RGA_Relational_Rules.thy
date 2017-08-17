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

inductive first_child :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and next_sibling    :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and siblingless_anc :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and next_elem       :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
where
  "\<lbrakk>child \<D> parent c; \<not> later_child \<D> parent c\<rbrakk> \<Longrightarrow> first_child \<D> parent c" |
  "\<lbrakk>later_sibling \<D> p n; \<not> later_sibling_2 \<D> p n\<rbrakk> \<Longrightarrow> next_sibling \<D> p n" |
  "\<lbrakk>list_elem \<D> s; \<not> has_next_sibling \<D> s\<rbrakk> \<Longrightarrow> siblingless_anc \<D> s s" |
  "\<lbrakk>siblingless_anc \<D> s p; child \<D> n p; \<not> has_next_sibling \<D> n\<rbrakk> \<Longrightarrow> siblingless_anc \<D> s n" |
  "\<lbrakk>first_child \<D> p n\<rbrakk> \<Longrightarrow> next_elem \<D> p n" |
  "\<lbrakk>list_elem \<D> p; \<not> has_child \<D> p; next_sibling \<D> p n\<rbrakk> \<Longrightarrow> next_elem \<D> p n" |
  "\<lbrakk>list_elem \<D> p; \<not> has_child \<D> p; siblingless_anc \<D> p a; child \<D> pa a; next_sibling \<D> pa n\<rbrakk> \<Longrightarrow> next_elem \<D> p n"  

lemmas rga_intros [intro] =
  list_elem_has_child_child_later_child_sibling_later_sibling_later_sibling_2_has_next_sibling.intros
  first_child_next_sibling_siblingless_anc_next_elem.intros

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

lemma siblingful_anc_unique:
  assumes "siblingless_anc \<D> prev anc1" and "child \<D> par1 anc1" and "next_sibling \<D> par1 n1"
  assumes "siblingless_anc \<D> prev anc2" and "child \<D> par2 anc2" and "next_sibling \<D> par2 n2"
  shows "n1 = n2"
  using assms apply -
  apply(case_tac "anc1 = anc2")
  using next_sibling_unique parent_unique apply blast
  oops

lemma next_elem_unique:
  assumes "next_elem \<D> prev next1"
  and "next_elem \<D> prev next2"
  shows "next1 = next2"
  oops

lemma elem_index_biject:
  assumes "elem_index \<D> x i" and "elem_index \<D> y j"
  shows "i = j \<longleftrightarrow> x = y"
  oops


end
