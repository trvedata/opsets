theory RGA_Relational_Rules
  imports Main "~~/src/HOL/Library/Cardinality"
begin

datatype 'eid operation
  = MakeList
  | Insert "'eid option" "'eid"

type_synonym 'eid database = "'eid operation set"

definition insert :: "'eid::{linorder, card_UNIV} database \<Rightarrow> 'eid option \<Rightarrow> 'eid \<Rightarrow> bool" where
  "insert \<D> parent i \<longleftrightarrow> Insert parent i \<in> \<D>"

inductive list_elem    :: "'eid::{linorder, card_UNIV} database \<Rightarrow> 'eid \<Rightarrow> bool"
  and has_child        :: "'eid::{linorder, card_UNIV} database \<Rightarrow> 'eid option \<Rightarrow> bool"
  and child            :: "'eid::{linorder, card_UNIV} database \<Rightarrow> 'eid option \<Rightarrow> 'eid \<Rightarrow> bool"
  and later_child      :: "'eid::{linorder, card_UNIV} database \<Rightarrow> 'eid option \<Rightarrow> 'eid \<Rightarrow> bool"
  and sibling          :: "'eid::{linorder, card_UNIV} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and later_sibling    :: "'eid::{linorder, card_UNIV} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and later_sibling_2  :: "'eid::{linorder, card_UNIV} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and has_next_sibling :: "'eid::{linorder, card_UNIV} database \<Rightarrow> 'eid \<Rightarrow> bool"
where
  "\<lbrakk>insert \<D> parent i\<rbrakk> \<Longrightarrow> list_elem \<D> i" |
  "\<lbrakk>insert \<D> parent c\<rbrakk> \<Longrightarrow> has_child \<D> parent" |
  "\<lbrakk>insert \<D> parent c\<rbrakk> \<Longrightarrow> child \<D> parent c" |
  "\<lbrakk>child \<D> parent c;  child \<D> parent p; c < p\<rbrakk> \<Longrightarrow> later_child \<D> parent c" |
  "\<lbrakk>child \<D> parent c1; child \<D> parent c2\<rbrakk> \<Longrightarrow> sibling \<D> c1 c2" |
  "\<lbrakk>sibling \<D> p l; l < p\<rbrakk> \<Longrightarrow> later_sibling \<D> p l" |
  "\<lbrakk>sibling \<D> p n; sibling \<D> p l; l < n; n < p\<rbrakk> \<Longrightarrow> later_sibling_2 \<D> p l" |
  "\<lbrakk>later_sibling \<D> p n\<rbrakk> \<Longrightarrow> has_next_sibling \<D> p"

inductive first_child :: "'eid::{linorder, card_UNIV} database \<Rightarrow> 'eid option \<Rightarrow> 'eid \<Rightarrow> bool"
  and next_sibling    :: "'eid::{linorder, card_UNIV} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and siblingless_anc :: "'eid::{linorder, card_UNIV} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
  and next_elem       :: "'eid::{linorder, card_UNIV} database \<Rightarrow> 'eid \<Rightarrow> 'eid \<Rightarrow> bool"
where
  "\<lbrakk>child \<D> parent c; \<not> later_child \<D> parent c\<rbrakk> \<Longrightarrow> first_child \<D> parent c" |
  "\<lbrakk>later_sibling \<D> p n; \<not> later_sibling_2 \<D> p n\<rbrakk> \<Longrightarrow> next_sibling \<D> p n" |
  "\<lbrakk>list_elem \<D> s; \<not> has_next_sibling \<D> s\<rbrakk> \<Longrightarrow> siblingless_anc \<D> s s" |
  "\<lbrakk>siblingless_anc \<D> s p; child \<D> (Some n) p; \<not> has_next_sibling \<D> n\<rbrakk> \<Longrightarrow> siblingless_anc \<D> s n" |
  "\<lbrakk>first_child \<D> (Some p) n\<rbrakk> \<Longrightarrow> next_elem \<D> p n" |
  "\<lbrakk>list_elem \<D> p; \<not> has_child \<D> (Some p); next_sibling \<D> p n\<rbrakk> \<Longrightarrow> next_elem \<D> p n" |
  "\<lbrakk>list_elem \<D> p; \<not> has_child \<D> (Some p); siblingless_anc \<D> p a; child \<D> (Some p) a; next_sibling \<D> p n\<rbrakk> \<Longrightarrow> next_elem \<D> p n"  

lemmas rga_intros [intro] =
  list_elem_has_child_child_later_child_sibling_later_sibling_later_sibling_2_has_next_sibling.intros
  first_child_next_sibling_siblingless_anc_next_elem.intros


end