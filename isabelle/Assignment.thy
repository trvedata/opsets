theory Assignment
  imports List_Insert
begin

(*********** Links between objects and register assignment ***************)

context datalog begin

inductive is_map :: "'oid \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some MakeMap\<rbrakk> \<Longrightarrow> is_map oid"

inductive is_val :: "'oid \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some (MakeVal v)\<rbrakk> \<Longrightarrow> is_val oid"

inductive ref_target :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some (ListAssign el v); is_list_elem el\<rbrakk> \<Longrightarrow> ref_target oid v" |
  "\<lbrakk>\<D> oid = Some (MapAssign m k v); is_map m       \<rbrakk> \<Longrightarrow> ref_target oid v"

inductive stolen_ref :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>ref_target o1 v; ref_target o2 v; o1 < o2\<rbrakk> \<Longrightarrow> stolen_ref o1 v"

inductive latest_ref :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>ref_target oid v; \<not> stolen_ref oid v\<rbrakk> \<Longrightarrow> latest_ref oid v"

inductive map_update :: "'oid \<Rightarrow> 'oid \<Rightarrow> string \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some (MapAssign m k v); is_map m\<rbrakk> \<Longrightarrow> map_update oid m k" |
  "\<lbrakk>\<D> oid = Some (MapRemove m k);   is_map m\<rbrakk> \<Longrightarrow> map_update oid m k"

inductive old_map_update :: "'oid \<Rightarrow> 'oid \<Rightarrow> string \<Rightarrow> bool" where
  "\<lbrakk>map_update o1 m k; map_update o2 m k; o1 < o2\<rbrakk> \<Longrightarrow> old_map_update o1 m k"

inductive list_update :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some (ListAssign el t); is_list_elem el\<rbrakk> \<Longrightarrow> list_update oid el" |
  "\<lbrakk>\<D> oid = Some (ListRemove el);   is_list_elem el\<rbrakk> \<Longrightarrow> list_update oid el"

inductive old_list_update :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>list_update o1 el; list_update o2 el; o1 < o2\<rbrakk> \<Longrightarrow> old_list_update o1 el"

inductive latest_map_update :: "'oid \<Rightarrow> 'oid \<Rightarrow> string \<Rightarrow> bool" where
  "\<lbrakk>map_update oid m k; \<not> old_map_update oid m k\<rbrakk> \<Longrightarrow> latest_map_update oid m k"

inductive map_val :: "'oid \<Rightarrow> string \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some (MapAssign m k v); latest_map_update oid m k; latest_ref oid v\<rbrakk> \<Longrightarrow> map_val m k v"

inductive has_map_val :: "'oid \<Rightarrow> string \<Rightarrow> bool" where
  "\<lbrakk>map_val m k v\<rbrakk> \<Longrightarrow> has_map_val m k"

inductive latest_list_update :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>list_update oid el; \<not> old_list_update oid el\<rbrakk> \<Longrightarrow> latest_list_update oid el"

inductive list_val :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>\<D> oid = Some (ListAssign el v); latest_list_update oid el; latest_ref oid v\<rbrakk> \<Longrightarrow> list_val el v"

inductive has_list_val :: "'oid \<Rightarrow> bool" where
  "\<lbrakk>list_val el v\<rbrakk> \<Longrightarrow> has_list_val el"

lemmas [intro] = is_map.intros
lemmas [intro] = is_val.intros
lemmas [intro] = ref_target.intros
lemmas [intro] = stolen_ref.intros
lemmas [intro] = latest_ref.intros
lemmas [intro] = map_update.intros
lemmas [intro] = old_map_update.intros
lemmas [intro] = list_update.intros
lemmas [intro] = old_list_update.intros
lemmas [intro] = latest_map_update.intros
lemmas [intro] = map_val.intros
lemmas [intro] = has_map_val.intros
lemmas [intro] = latest_list_update.intros
lemmas [intro] = list_val.intros
lemmas [intro] = has_list_val.intros

inductive_cases is_map_elim [elim]: "is_map oid"
inductive_cases is_val_elim [elim]: "is_val oid"
inductive_cases ref_target_elim [elim]: "ref_target oid v"
inductive_cases stolen_ref_elim [elim]: "stolen_ref oid v"
inductive_cases latest_ref_elim [elim]: "latest_ref oid v"
inductive_cases map_update_elim [elim]: "map_update oid m k"
inductive_cases old_map_update_elim [elim]: "old_map_update oid m k"
inductive_cases list_update_elim [elim]: "list_update oid el"
inductive_cases old_list_update_elim [elim]: "old_list_update oid el"
inductive_cases latest_map_update_elim [elim]: "latest_map_update oid m k"
inductive_cases map_val_elim [elim]: "map_val m k v"
inductive_cases has_map_val_elim [elim]: "has_map_val m k"
inductive_cases latest_list_update_elim [elim]: "latest_list_update oid el"
inductive_cases list_val_elim [elim]: "list_val el v"
inductive_cases has_list_val_elim [elim]: "has_list_val el"

definition latest_ref_fun :: "'oid \<rightharpoonup> 'oid" where
  "latest_ref_fun v \<equiv>
     if \<nexists>oid. latest_ref oid v
     then None
     else Some (THE oid. latest_ref oid v)"

definition map_val_fun :: "'oid \<Rightarrow> string \<rightharpoonup> 'oid" where
  "map_val_fun m k \<equiv>
     if \<nexists>v. map_val m k v
     then None
     else Some (THE v. map_val m k v)"

definition list_val_fun :: "'oid \<rightharpoonup> 'oid" where
  "list_val_fun el \<equiv>
     if \<nexists>v. list_val el v
     then None
     else Some (THE v. list_val el v)"

lemma latest_ref_functional:
  assumes "latest_ref o1 v"
    and "latest_ref o2 v"
  shows "o1 = o2"
  using assms by (meson latest_ref.cases neqE stolen_ref.intros)

lemma latest_ref_fun_equality [simp]:
  shows "latest_ref oid v \<longleftrightarrow> (latest_ref_fun v = Some oid)"
  apply(unfold latest_ref_fun_def)
  apply(clarsimp split!: if_split)
  apply(drule latest_ref_functional, assumption)
  using latest_ref_functional apply blast
  (* apply(simp add: latest_ref_functional theI) *)
  oops

lemma latest_map_update_functional:
  assumes "latest_map_update o1 m k"
    and "latest_map_update o2 m k"
  shows "o1 = o2"
  using assms by (meson latest_map_update.cases neqE old_map_update.intros)

lemma map_val_functional:
  assumes "map_val m k v1"
    and "map_val m k v2"
  shows "v1 = v2"
  using assms by (metis latest_map_update_functional map_val.cases operation.inject(4) option.sel)

lemma map_val_fun_equality [simp]:
  shows "map_val m k v \<longleftrightarrow> (map_val_fun m k = Some v)"
  apply(unfold map_val_fun_def)
  apply(clarsimp split!: if_split)
  using map_val_functional apply blast
  apply(simp add: map_val_functional theI)
  done

lemma latest_list_update_functional:
  assumes "latest_list_update o1 el"
    and "latest_list_update o2 el"
  shows "o1 = o2"
  using assms by (meson latest_list_update.cases neqE old_list_update.intros)

lemma list_val_functional:
  assumes "list_val el v1"
    and "list_val el v2"
  shows "v1 = v2"
  using assms by (metis latest_list_update_functional list_val.cases operation.inject(3) option.inject)

lemma list_val_fun_equality [simp]:
  shows "list_val el v \<longleftrightarrow> (list_val_fun el = Some v)"
  apply(unfold list_val_fun_def)
  apply(clarsimp split!: if_split)
  using list_val_functional apply blast
  apply(simp add: list_val_functional theI)
  done

end

lemma unchanged_is_map:
  assumes "db_extension \<D> oid oper"
    and "x \<noteq> oid"
  shows "datalog.is_map \<D> x \<longleftrightarrow> datalog.is_map (\<D>(oid \<mapsto> oper)) x"
  by (metis (full_types) assms datalog.is_map.simps db_extension.still_valid_database
    db_extension_datalog fun_upd_other)

lemma map_unchanged_ref_target:
  assumes "db_extension \<D> oid (MapAssign m k v)"
    and "oid \<noteq> x \<or> y \<noteq> v"
  shows "datalog.ref_target \<D> x y \<longleftrightarrow> datalog.ref_target (\<D>(oid \<mapsto> MapAssign m k v)) x y"
  using assms apply -
  apply(rule iffI)
  apply(subgoal_tac "datalog \<D>") prefer 2
  using db_extension_def apply blast
  apply(erule datalog.ref_target_elim, assumption)
  apply(subgoal_tac "datalog.is_list_elem (\<D>(oid \<mapsto> MapAssign m k v)) el") prefer 2
  apply(metis is_list_elem_unchanged datalog.is_list_elem.simps db_extension.oid_not_present
    db_extension_datalog option.simps(3))
  using datalog.ref_target.simps db_extension.oid_not_present db_extension.still_valid_database
    apply fastforce
  apply(subgoal_tac "datalog.is_map (\<D>(oid \<mapsto> MapAssign m k v)) ma") prefer 2
  apply(metis (full_types) datalog.is_map.cases db_extension.oid_not_present db_extension_datalog
    option.simps(3) unchanged_is_map)
  using datalog.ref_target.simps db_extension.oid_not_present db_extension.still_valid_database
    apply fastforce
  apply(subgoal_tac "datalog (\<D>(oid \<mapsto> MapAssign m k v))") prefer 2
  apply(simp add: db_extension.still_valid_database)
  apply(erule datalog.ref_target_elim, assumption)
  apply(subgoal_tac "datalog.is_list_elem \<D> el") prefer 2
  apply(metis (no_types, lifting) datalog.is_list_elem.simps db_extension.still_valid_database
    fun_upd_same is_list_elem_unchanged operation.distinct(39) option.sel)
  apply(metis datalog.ref_target.intros(1) db_extension_datalog map_upd_Some_unfold operation.distinct(45))
  apply(subgoal_tac "datalog.is_map \<D> ma") prefer 2
  apply(metis (mono_tags, lifting) datalog.is_map.cases db_extension.still_valid_database
    map_upd_Some_unfold operation.distinct(21) unchanged_is_map)
  apply(metis datalog.ref_target.intros(2) db_extension_datalog map_upd_Some_unfold operation.inject(4))
  done

lemma list_unchanged_ref_target:
  assumes "db_extension \<D> oid (ListAssign el v)"
    and "x \<noteq> oid \<or> y \<noteq> v"
  shows "datalog.ref_target \<D> x y \<longleftrightarrow> datalog.ref_target (\<D>(oid \<mapsto> ListAssign el v)) x y"
  using assms apply -
  apply(rule iffI)
  apply(subgoal_tac "datalog \<D>") prefer 2
  using db_extension_def apply blast
  apply(erule datalog.ref_target_elim, assumption)
  apply(subgoal_tac "datalog.is_list_elem (\<D>(oid \<mapsto> ListAssign el v)) ela") prefer 2
  apply(metis is_list_elem_unchanged datalog.is_list_elem.simps db_extension.oid_not_present
    db_extension_datalog option.simps(3))
  using datalog.ref_target.simps db_extension.oid_not_present db_extension.still_valid_database
    apply fastforce
  apply(subgoal_tac "datalog.is_map (\<D>(oid \<mapsto> ListAssign el v)) m") prefer 2
  apply(metis (full_types) datalog.is_map.cases db_extension.oid_not_present db_extension_datalog
    option.simps(3) unchanged_is_map)
  using datalog.ref_target.simps db_extension.oid_not_present db_extension.still_valid_database
    apply fastforce
  apply(subgoal_tac "datalog (\<D>(oid \<mapsto> ListAssign el v))") prefer 2
  apply(simp add: db_extension.still_valid_database)
  apply(erule datalog.ref_target_elim, assumption)
  apply(subgoal_tac "datalog.is_list_elem \<D> ela") prefer 2
  apply(metis (no_types, lifting) datalog.is_list_elem.simps db_extension.still_valid_database
    fun_upd_same is_list_elem_unchanged operation.distinct(37) option.sel)
  apply(metis (mono_tags, lifting) datalog.ref_target.intros(1) db_extension_datalog
    map_upd_Some_unfold operation.inject(3))
  apply(subgoal_tac "datalog.is_map \<D> m") prefer 2
  apply(metis datalog.is_map_elim db_extension.still_valid_database fun_upd_same
    operation.distinct(19) option.inject unchanged_is_map)
  apply(metis datalog.ref_target.intros(2) db_extension_datalog map_upd_Some_unfold
    operation.distinct(45))
  done

lemma map_assign_latest_ref:
  assumes "db_extension \<D> oid (MapAssign m k v)"
    and "datalog.is_map \<D> m"
  shows "datalog.latest_ref (\<D>(oid \<mapsto> MapAssign m k v)) oid v"
  using assms apply -
  apply(subgoal_tac "datalog.ref_target (\<D>(oid \<mapsto> MapAssign m k v)) oid v") prefer 2
  apply(metis (no_types, lifting) datalog.is_map.cases datalog.ref_target.intros(2)
    db_extension.oid_not_present db_extension.still_valid_database db_extension_datalog
    fun_upd_same option.simps(3) unchanged_is_map)
  apply(subgoal_tac "datalog.stolen_ref (\<D>(oid \<mapsto> MapAssign m k v)) oid v \<Longrightarrow> False")
  using datalog.latest_ref.intros db_extension.still_valid_database apply blast
  apply(subgoal_tac "datalog (\<D>(oid \<mapsto> MapAssign m k v))") prefer 2
  apply(simp add: db_extension.still_valid_database)
  apply(erule datalog.stolen_ref_elim, assumption)
  apply(subgoal_tac "o2 < oid", force)
  apply(metis (mono_tags, lifting) datalog.ref_target.cases db_extension.axioms(2)
    db_extension_axioms_def domIff fun_upd_other option.simps(3))
  done

lemma list_assign_latest_ref:
  assumes "db_extension \<D> oid (ListAssign el v)"
    and "datalog.is_list_elem \<D> el"
  shows "datalog.latest_ref (\<D>(oid \<mapsto> ListAssign el v)) oid v"
  using assms apply -
  apply(subgoal_tac "datalog.ref_target (\<D>(oid \<mapsto> ListAssign el v)) oid v") prefer 2
  apply(metis (mono_tags, lifting) datalog.is_list_elem.simps datalog.ref_target.intros(1)
    db_extension.oid_not_present db_extension.still_valid_database db_extension_datalog
    fun_upd_apply option.simps(3))
  apply(subgoal_tac "datalog.stolen_ref (\<D>(oid \<mapsto> ListAssign el v)) oid v \<Longrightarrow> False")
  using datalog.latest_ref.intros db_extension.still_valid_database apply blast
  apply(subgoal_tac "datalog (\<D>(oid \<mapsto> ListAssign el v))") prefer 2
  apply(simp add: db_extension.still_valid_database)
  apply(erule datalog.stolen_ref_elim, assumption)
  apply(subgoal_tac "o2 < oid", force)
  apply(metis (mono_tags, lifting) datalog.ref_target.cases db_extension.axioms(2)
    db_extension_axioms_def domIff fun_upd_other option.distinct(1))
  done

lemma map_unchanged_latest_ref:
  assumes "db_extension \<D> oid (MapAssign m k v)"
    and "y \<noteq> v"
  shows "datalog.latest_ref \<D> x y \<longleftrightarrow> datalog.latest_ref (\<D>(oid \<mapsto> MapAssign m k v)) x y"
  using assms by (meson datalog.latest_ref.simps datalog.stolen_ref.simps
    db_extension.still_valid_database db_extension_datalog map_unchanged_ref_target)

lemma list_unchanged_latest_ref:
  assumes "db_extension \<D> oid (ListAssign el v)"
    and "y \<noteq> v"
  shows "datalog.latest_ref \<D> x y \<longleftrightarrow> datalog.latest_ref (\<D>(oid \<mapsto> ListAssign el v)) x y"
  using assms by (meson datalog.latest_ref.simps datalog.stolen_ref.simps
    db_extension.still_valid_database db_extension_datalog list_unchanged_ref_target)

lemma map_assign_unchanged_map_update:
  assumes "db_extension \<D> oid (MapAssign m k v)"
    and "y \<noteq> m \<or> z \<noteq> k"
  shows "datalog.map_update \<D> x y z \<longleftrightarrow> datalog.map_update (\<D>(oid \<mapsto> MapAssign m k v)) x y z"
  using assms apply -
  apply(rule iffI)
  apply(metis (no_types, lifting) datalog.is_map.simps datalog.map_update.simps
    db_extension.oid_not_present db_extension.still_valid_database db_extension_datalog
    fun_upd_other option.simps(3))
  apply(subgoal_tac "datalog.is_map \<D> y") prefer 2
  apply(metis (no_types, lifting) datalog.is_map_elim datalog.map_update.simps
    db_extension.still_valid_database fun_upd_def operation.distinct(21) option.inject
    unchanged_is_map)
  apply(subgoal_tac "datalog (\<D>(oid \<mapsto> MapAssign m k v))") prefer 2
  using db_extension.still_valid_database apply blast
  apply(erule datalog.map_update_elim, assumption)
  apply(metis datalog.map_update.intros(1) db_extension_datalog map_upd_Some_unfold
    operation.inject(4))
  apply(metis datalog.map_update.intros(2) db_extension_datalog map_upd_Some_unfold
    operation.distinct(53))
  done

lemma map_remove_unchanged_map_update:
  assumes "db_extension \<D> oid (MapRemove m k)"
    and "y \<noteq> m \<or> z \<noteq> k"
  shows "datalog.map_update \<D> x y z \<longleftrightarrow> datalog.map_update (\<D>(oid \<mapsto> MapRemove m k)) x y z"
  using assms apply -
  apply(rule iffI)
  apply(metis (no_types, lifting) datalog.is_map.simps datalog.map_update.simps
    db_extension.oid_not_present db_extension.still_valid_database db_extension_datalog
    fun_upd_other option.simps(3))
  apply(subgoal_tac "datalog.is_map \<D> y") prefer 2
  apply(metis (no_types, lifting) datalog.is_map.simps datalog.map_update.simps
    db_extension.still_valid_database map_upd_Some_unfold operation.distinct(25) unchanged_is_map)
  apply(subgoal_tac "datalog (\<D>(oid \<mapsto> MapRemove m k))") prefer 2
  using db_extension.still_valid_database apply blast
  apply(erule datalog.map_update_elim, assumption)
  apply(metis datalog.map_update.intros(1) db_extension_datalog map_upd_Some_unfold
    operation.simps(60))
  apply(metis (no_types, lifting) datalog.map_update.intros(2) db_extension_datalog
    map_upd_Some_unfold operation.inject(6))
  done

lemma list_assign_unchanged_list_update:
  assumes "db_extension \<D> oid (ListAssign el v)"
    and "y \<noteq> el"
  shows "datalog.list_update \<D> x y \<longleftrightarrow> datalog.list_update (\<D>(oid \<mapsto> ListAssign el v)) x y"
  using assms apply -
  apply(rule iffI)
  apply(metis (mono_tags, lifting) datalog.is_list_elem.simps datalog.list_update.simps
    db_extension.oid_not_present db_extension.still_valid_database db_extension_datalog
    fun_upd_other option.simps(3))
  apply(subgoal_tac "datalog.is_list_elem \<D> y") prefer 2
  apply(metis (no_types, lifting) datalog.is_list_elem.cases datalog.list_update.simps
    db_extension.still_valid_database fun_upd_same is_list_elem_unchanged operation.distinct(37)
    option.inject)
  apply(subgoal_tac "datalog (\<D>(oid \<mapsto> ListAssign el v))") prefer 2
  using db_extension.still_valid_database apply blast
  apply(erule datalog.list_update_elim, assumption)
  apply(metis (mono_tags, lifting) datalog.list_update.intros(1) db_extension_datalog
    map_upd_Some_unfold operation.inject(3))
  apply(metis datalog.list_update.intros(2) db_extension_datalog map_upd_Some_unfold
    operation.distinct(47))
  done

lemma list_remove_unchanged_list_update:
  assumes "db_extension \<D> oid (ListRemove el)"
    and "y \<noteq> el"
  shows "datalog.list_update \<D> x y \<longleftrightarrow> datalog.list_update (\<D>(oid \<mapsto> ListRemove el)) x y"
  using assms apply -
  apply(rule iffI)
  apply(metis (mono_tags, lifting) datalog.is_list_elem.simps datalog.list_update.simps
    db_extension.oid_not_present db_extension.still_valid_database db_extension_datalog
    fun_upd_other option.simps(3))
  apply(subgoal_tac "datalog.is_list_elem \<D> y") prefer 2
  apply(metis (no_types, lifting) datalog.is_list_elem.simps datalog.list_update.simps
    db_extension.still_valid_database is_list_elem_unchanged map_upd_Some_unfold
    operation.distinct(41))
  apply(subgoal_tac "datalog (\<D>(oid \<mapsto> ListRemove el))") prefer 2
  using db_extension.still_valid_database apply blast
  apply(erule datalog.list_update_elim, assumption)
  apply(metis datalog.list_update.intros(1) db_extension_datalog map_upd_Some_unfold
    operation.distinct(47))
  apply(metis (no_types, lifting) datalog.list_update.intros(2) db_extension_datalog
    map_upd_Some_unfold operation.inject(5))
  done

lemma map_assign_latest_map_update:
  assumes "db_extension \<D> oid (MapAssign m k v)"
    and "datalog.is_map \<D> m"
  shows "datalog.latest_map_update (\<D>(oid \<mapsto> MapAssign m k v)) oid m k"
  using assms apply -
  apply(subgoal_tac "datalog.map_update (\<D>(oid \<mapsto> MapAssign m k v)) oid m k") prefer 2
  apply(metis (no_types, lifting) datalog.is_map.cases datalog.map_update.intros(1)
    db_extension.oid_not_present db_extension.still_valid_database db_extension_datalog
    fun_upd_same option.simps(3) unchanged_is_map)
  apply(subgoal_tac "datalog.old_map_update (\<D>(oid \<mapsto> MapAssign m k v)) oid m k \<Longrightarrow> False")
  using datalog.latest_map_update.intros db_extension.still_valid_database apply blast
  apply(subgoal_tac "datalog (\<D>(oid \<mapsto> MapAssign m k v))") prefer 2
  apply(simp add: db_extension.still_valid_database)
  apply(erule datalog.old_map_update_elim, assumption)
  apply(subgoal_tac "o2 < oid", force)
  apply(metis (mono_tags, lifting) datalog.map_update_elim db_extension.axioms(2)
    db_extension_axioms_def domIff fun_upd_other option.simps(3))
  done

lemma map_assign_unchanged_latest_map_update:
  assumes "db_extension \<D> oid (MapAssign m k v)"
    and "y \<noteq> m \<or> z \<noteq> k"
  shows "datalog.latest_map_update \<D> x y z \<longleftrightarrow> datalog.latest_map_update (\<D>(oid \<mapsto> MapAssign m k v)) x y z"
  by (metis assms datalog.latest_map_update.simps datalog.old_map_update.simps
    db_extension.still_valid_database db_extension_datalog map_assign_unchanged_map_update)

lemma map_remove_latest_map_update:
  assumes "db_extension \<D> oid (MapRemove m k)"
    and "datalog.is_map \<D> m"
  shows "datalog.latest_map_update (\<D>(oid \<mapsto> MapRemove m k)) oid m k"
  using assms apply -
  apply(subgoal_tac "datalog.map_update (\<D>(oid \<mapsto> MapRemove m k)) oid m k") prefer 2
  apply(metis (no_types, lifting) datalog.is_map.cases datalog.map_update.intros(2)
    db_extension.oid_not_present db_extension.still_valid_database db_extension_datalog
    fun_upd_same option.simps(3) unchanged_is_map)
  apply(subgoal_tac "datalog.old_map_update (\<D>(oid \<mapsto> MapRemove m k)) oid m k \<Longrightarrow> False")
  using datalog.latest_map_update.intros db_extension.still_valid_database apply blast
  apply(subgoal_tac "datalog (\<D>(oid \<mapsto> MapRemove m k))") prefer 2
  apply(simp add: db_extension.still_valid_database)
  apply(erule datalog.old_map_update_elim, assumption)
  apply(subgoal_tac "o2 < oid", force)
  apply(metis (mono_tags, lifting) datalog.map_update_elim db_extension.axioms(2)
    db_extension_axioms_def domIff fun_upd_other option.simps(3))
  done

lemma map_remove_unchanged_latest_map_update:
  assumes "db_extension \<D> oid (MapRemove m k)"
    and "y \<noteq> m \<or> z \<noteq> k"
  shows "datalog.latest_map_update \<D> x y z \<longleftrightarrow> datalog.latest_map_update (\<D>(oid \<mapsto> MapRemove m k)) x y z"
  by (metis assms datalog.latest_map_update.simps datalog.old_map_update.simps
    db_extension.still_valid_database db_extension_datalog map_remove_unchanged_map_update)

lemma list_assign_latest_list_update:
  assumes "db_extension \<D> oid (ListAssign el v)"
    and "datalog.is_list_elem \<D> el"
  shows "datalog.latest_list_update (\<D>(oid \<mapsto> ListAssign el v)) oid el"
  using assms apply -
  apply(subgoal_tac "datalog.list_update (\<D>(oid \<mapsto> ListAssign el v)) oid el") prefer 2
  apply(metis datalog.is_list_elem.simps datalog.list_update.intros(1) db_extension.oid_not_present
    db_extension.still_valid_database db_extension_datalog fun_upd_same is_list_elem_unchanged
    option.simps(3))
  apply(subgoal_tac "datalog.old_list_update (\<D>(oid \<mapsto> ListAssign el v)) oid el \<Longrightarrow> False")
  using datalog.latest_list_update.intros db_extension.still_valid_database apply blast
  apply(subgoal_tac "datalog (\<D>(oid \<mapsto> ListAssign el v))") prefer 2
  apply(simp add: db_extension.still_valid_database)
  apply(erule datalog.old_list_update_elim, assumption)
  apply(subgoal_tac "o2 < oid", force)
  apply(metis (no_types, lifting) datalog.list_update.simps db_extension.axioms(2)
    db_extension_axioms_def domI fun_upd_other)
  done

lemma list_assign_unchanged_latest_list_update:
  assumes "db_extension \<D> oid (ListAssign el v)"
    and "y \<noteq> el"
  shows "datalog.latest_list_update \<D> x y \<longleftrightarrow> datalog.latest_list_update (\<D>(oid \<mapsto> ListAssign el v)) x y"
  by (meson assms datalog.latest_list_update.simps datalog.old_list_update.simps
    db_extension.still_valid_database db_extension_datalog list_assign_unchanged_list_update)

lemma list_remove_latest_list_update:
  assumes "db_extension \<D> oid (ListRemove el)"
    and "datalog.is_list_elem \<D> el"
  shows "datalog.latest_list_update (\<D>(oid \<mapsto> ListRemove el)) oid el"
  using assms apply -
  apply(subgoal_tac "datalog.list_update (\<D>(oid \<mapsto> ListRemove el)) oid el") prefer 2
  apply(metis datalog.is_list_elem.simps datalog.list_update.intros(2) db_extension.oid_not_present
    db_extension.still_valid_database db_extension_datalog fun_upd_same is_list_elem_unchanged
    option.simps(3))
  apply(subgoal_tac "datalog.old_list_update (\<D>(oid \<mapsto> ListRemove el)) oid el \<Longrightarrow> False")
  using datalog.latest_list_update.intros db_extension.still_valid_database apply blast
  apply(subgoal_tac "datalog (\<D>(oid \<mapsto> ListRemove el))") prefer 2
  apply(simp add: db_extension.still_valid_database)
  apply(erule datalog.old_list_update_elim, assumption)
  apply(subgoal_tac "o2 < oid", force)
  apply(metis (no_types, lifting) datalog.list_update.simps db_extension.axioms(2)
    db_extension_axioms_def domI fun_upd_other)
  done

lemma list_remove_unchanged_latest_list_update:
  assumes "db_extension \<D> oid (ListRemove el)"
    and "y \<noteq> el"
  shows "datalog.latest_list_update \<D> x y \<longleftrightarrow> datalog.latest_list_update (\<D>(oid \<mapsto> ListRemove el)) x y"
  by (meson assms datalog.latest_list_update.simps datalog.old_list_update.simps
    db_extension.still_valid_database db_extension_datalog list_remove_unchanged_list_update)

lemma map_assign_map_val:
  assumes "db_extension \<D> oid (MapAssign m k v)"
    and "datalog.is_map \<D> m"
  shows "datalog.map_val (\<D>(oid \<mapsto> MapAssign m k v)) m k v"
  by (meson assms datalog.map_val.simps db_extension.still_valid_database fun_upd_same
    map_assign_latest_map_update map_assign_latest_ref)

lemma map_assign_unchanged_map_val:
  assumes "db_extension \<D> oid (MapAssign m k v)"
    and "x \<noteq> m \<or> y \<noteq> k"
    and "datalog.latest_ref_fun \<D> v = None"
  shows "datalog.map_val \<D> x y z \<longleftrightarrow> datalog.map_val (\<D>(oid \<mapsto> MapAssign m k v)) x y z"
  using assms apply -
  apply(subgoal_tac "datalog \<D> \<and> datalog (\<D>(oid \<mapsto> MapAssign m k v))", clarsimp) prefer 2
  apply(simp add: db_extension.still_valid_database db_extension_datalog)
  apply(rule iffI)
  apply(erule datalog.map_val_elim, assumption)
  apply(subgoal_tac "datalog.latest_map_update (\<D>(oid \<mapsto> MapAssign m k v)) oida x y") prefer 2
  using map_assign_unchanged_latest_map_update apply blast
  apply(subgoal_tac "datalog.latest_ref (\<D>(oid \<mapsto> MapAssign m k v)) oida z") prefer 2
  apply(metis datalog.latest_ref_fun_def db_extension_datalog map_unchanged_latest_ref option.simps(3))
  apply(metis (no_types, lifting) assms(1) datalog.map_val.intros db_extension.oid_not_present
    domI domIff fun_upd_def)
  apply(erule datalog.map_val_elim, assumption)
  apply(subgoal_tac "datalog.latest_map_update \<D> oida x y") prefer 2
  using map_assign_unchanged_latest_map_update apply blast
  apply(subgoal_tac "datalog.latest_ref \<D> oida z") prefer 2
  apply(subgoal_tac "datalog.stolen_ref \<D> oida z \<Longrightarrow> False")
  apply(subgoal_tac "datalog.ref_target \<D> oida z") prefer 2
  apply(metis datalog.latest_map_update.cases datalog.map_update.simps datalog.ref_target.intros(2)
    map_upd_Some_unfold operation.inject(4))
  using datalog.latest_ref.intros apply blast
  apply(erule datalog.stolen_ref_elim, assumption)
  apply(subgoal_tac "datalog.ref_target (\<D>(oid \<mapsto> MapAssign m k v)) o2 z") prefer 2
  apply(metis datalog.ref_target.simps db_extension.oid_not_present db_extension_datalog
    map_unchanged_ref_target option.simps(3))
  apply(meson datalog.latest_ref_elim datalog.stolen_ref.intros db_extension.still_valid_database)
  apply(metis (mono_tags, lifting) datalog.map_val.intros map_upd_Some_unfold operation.inject(4))
  done

lemma map_remove_map_val:
  assumes "db_extension \<D> oid (MapRemove m k)"
  shows "\<nexists>v. datalog.map_val (\<D>(oid \<mapsto> MapRemove m k)) m k v"
  by (metis (no_types, lifting) assms datalog.is_map.simps datalog.latest_map_update.cases
    datalog.latest_map_update_functional datalog.map_update.simps datalog.map_val.cases
    db_extension.still_valid_database fun_upd_same map_remove_latest_map_update
    operation.distinct(25) operation.distinct(53) option.sel unchanged_is_map)

definition set_map_key :: "('oid \<Rightarrow> string \<rightharpoonup> 'oid) \<Rightarrow> 'oid \<Rightarrow> string \<Rightarrow> 'oid option \<Rightarrow> ('oid \<Rightarrow> string \<rightharpoonup> 'oid)"
where "set_map_key view m k v \<equiv> view(m := (view m)(k := v))"

theorem map_assign_serial:
  assumes "db_extension \<D> oid (MapAssign m k v)"
    and "datalog.is_map \<D> m"
    and "datalog.latest_ref_fun \<D> v = None"
  shows "datalog.map_val_fun (\<D>(oid \<mapsto> MapAssign m k v)) =
         set_map_key (datalog.map_val_fun \<D>) m k (Some v)"
  using assms
  apply(subgoal_tac "datalog \<D> \<and> datalog (\<D>(oid \<mapsto> MapAssign m k v))", clarsimp) prefer 2
  apply(simp add: db_extension.still_valid_database db_extension_datalog)
  apply(rule ext, rule ext)
  apply(clarsimp simp: datalog.map_val_fun_def set_map_key_def split!: if_split if_split_asm)
  apply(meson datalog.map_val.intros fun_upd_same map_assign_latest_map_update map_assign_latest_ref)
  using datalog.map_val_functional map_assign_map_val apply blast
  using map_assign_unchanged_map_val apply(blast, blast)
  apply(metis (no_types, lifting) datalog.map_val_fun_def datalog.map_val_fun_equality
    map_assign_unchanged_map_val option.inject)
  using map_assign_unchanged_map_val apply(blast, blast)
  apply(metis datalog.map_val_functional map_assign_unchanged_map_val the_equality)
  done

lemma map_assign_move_from_map:
  assumes "db_extension \<D> oid (MapAssign m k v)"
    and "datalog.is_map \<D> m"
    and "datalog.map_val_fun \<D> m' k' = Some v"
  shows "datalog.map_val_fun (\<D>(oid \<mapsto> MapAssign m k v)) =
         set_map_key (set_map_key (datalog.map_val_fun \<D>) m' k' None) m k (Some v)"
  using assms
  apply(subgoal_tac "datalog \<D> \<and> datalog (\<D>(oid \<mapsto> MapAssign m k v))", clarsimp) prefer 2
  apply(simp add: db_extension.still_valid_database db_extension_datalog)
  apply(rule ext, rule ext)
  apply(clarsimp simp: datalog.map_val_fun_def set_map_key_def split!: if_split if_split_asm)
  using map_assign_map_val apply blast
  using datalog.map_val_functional map_assign_map_val apply blast
(*
  sledgehammer[no_smt_proofs]
*)
  oops

end
