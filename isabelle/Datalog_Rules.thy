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

end

definition next_elem_rel :: "('oid::{linorder}, 'val) database \<Rightarrow> ('oid \<times> 'oid option) set" where
  "next_elem_rel \<D> \<equiv> {(x, y). datalog.next_elem \<D> x y}"

lemma next_elem_unique:
  assumes "(x, y) \<in> next_elem_rel \<D>" and "(x, z) \<in> next_elem_rel \<D>"
  shows "y = z"
  oops

lemma insert_serial:
  assumes "\<D> y = None" and "\<D>' = \<D>(y \<mapsto> InsertAfter x)"
    and "(x, z) \<in> next_elem_rel \<D>"
    and "\<And>n. n \<in> dom \<D> \<Longrightarrow> n < y"
  shows "next_elem_rel \<D>' = next_elem_rel \<D> - {(x, z)} \<union> {(x, Some y), (y, z)}"
  oops


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
