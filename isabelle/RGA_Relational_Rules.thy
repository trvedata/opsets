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
  "\<lbrakk>list_elem \<D> p; \<not> has_child \<D> p; siblingless_anc \<D> p a; child \<D> p a; next_sibling \<D> p n\<rbrakk> \<Longrightarrow> next_elem \<D> p n"  

lemmas rga_intros [intro] =
  list_elem_has_child_child_later_child_sibling_later_sibling_later_sibling_2_has_next_sibling.intros
  first_child_next_sibling_siblingless_anc_next_elem.intros
  
inductive list_iter :: "'eid::{linorder} database \<Rightarrow> 'eid \<Rightarrow> 'eid list \<Rightarrow> bool" where
  "list_iter \<D> pa []" |
  "\<lbrakk>first_child \<D> pa e\<rbrakk> \<Longrightarrow> list_iter \<D> pa [e]" |
  "\<lbrakk>list_iter \<D> pa (e'#es); next_elem \<D> e e'\<rbrakk> \<Longrightarrow> list_iter \<D> pa (e#e'#es)"

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

lemma next_elem_unique:
  assumes "next_elem \<D> prev next1"
  and "next_elem \<D> prev next2"
  shows "next1 = next2"
sorry
    
lemma
  shows "insert \<D> pa e \<longleftrightarrow> (\<exists>l. e \<in> set l \<and> list_iter \<D> pa l)"
proof
  assume "insert \<D> pa e"
  show "\<exists>l. e \<in> set l \<and> list_iter \<D> pa l"
    sorry
next
  assume "\<exists>l. e \<in> set l \<and> list_iter \<D> pa l"
  from this obtain l where "list_iter \<D> pa l" and "e \<in> set l"
    by blast
  thus "insert \<D> pa e"
  proof(induction rule: list_iter.induct)
    fix \<D> pa
    assume "e \<in> set []"
    thus "insert \<D> pa e"
      by auto
  next
    fix \<D> pa ea
    assume "first_child \<D> pa ea" and "e \<in> set [ea]"
    hence "e = ea"
      by auto
    also have "child \<D> pa ea"
      using \<open>first_child \<D> pa ea\<close> first_child.cases by blast+
    thus "insert \<D> pa e"
      using insert_def child.cases \<open>e = ea\<close> by blast
  next
    fix \<D> pa e' es ea
    assume "list_iter \<D> pa (e' # es)"
      and "e \<in> set (e' # es) \<Longrightarrow> insert \<D> pa e"
      and "next_elem \<D> ea e'"
      and "e \<in> set (ea # e' # es)"
    hence "e = ea \<or> e \<in> set (e'#es)"
      by auto
    {
      assume "e = ea"
      hence "next_elem \<D> e e'"
        using \<open>next_elem \<D> ea e'\<close> by auto
      have "insert \<D> pa e"
        sorry
    }
    thus "insert \<D> pa e"
      using \<open>e = ea \<or> e \<in> set (e'#es)\<close> \<open>e \<in> set (e' # es) \<Longrightarrow> insert \<D> pa e\<close> by blast
  qed
qed
  


end
