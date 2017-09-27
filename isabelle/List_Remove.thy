theory List_Remove
  imports Assignment
begin

context datalog begin

inductive next_nonempty :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>next_elem el n; has_list_val n\<rbrakk> \<Longrightarrow> next_nonempty el n" |
  "\<lbrakk>next_elem el n; \<not> has_list_val n; next_nonempty n m\<rbrakk> \<Longrightarrow> next_nonempty el m"

inductive has_next_nonempty :: "'oid \<Rightarrow> bool" where
  "\<lbrakk>next_nonempty el n\<rbrakk> \<Longrightarrow> has_next_nonempty el"

inductive list_elem :: "'oid \<Rightarrow> 'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>list_val el v; next_nonempty el next\<rbrakk> \<Longrightarrow> list_elem el v next"

inductive list_suffix :: "'oid \<Rightarrow> ('oid \<times> 'oid) list \<Rightarrow> bool" where
  "\<lbrakk>\<not> has_next_nonempty el\<rbrakk> \<Longrightarrow> list_suffix el []" |
  "\<lbrakk>next_nonempty el n; list_val n v; list_suffix n suf\<rbrakk> \<Longrightarrow> list_suffix el ((n,v)#suf)"

inductive list_full :: "'oid \<Rightarrow> ('oid \<times> 'oid) list \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some MakeList; list_suffix oid suf\<rbrakk> \<Longrightarrow> list_full oid suf"

end

end
