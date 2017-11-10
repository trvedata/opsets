theory RGA_Spec
  imports Main Permute
begin

fun insert_spec :: "'oid list \<Rightarrow> ('oid \<times> 'oid option) \<Rightarrow> 'oid list" where
  "insert_spec list   (oid, None) = oid # list" |
  "insert_spec []     (oid, _   ) = []" |
  "insert_spec (x#xs) (oid, Some ref) = (
     if x = ref then x # oid # xs
                else x # (insert_spec xs (oid, Some ref)))"

definition list_spec :: "('oid \<times> 'oid option) list \<Rightarrow> 'oid list" where
  "list_spec ops \<equiv> foldl insert_spec [] ops"

inductive valid_spec_ops :: "('oid::{linorder} \<times> 'oid option) list \<Rightarrow> bool" where
  "valid_spec_ops []" |
  "\<lbrakk>valid_spec_ops xs;
    \<forall>x \<in> set (map fst xs). x < oid\<rbrakk> \<Longrightarrow> valid_spec_ops (xs@[(oid, None)])" |
  "\<lbrakk>valid_spec_ops xs;
    \<forall>x \<in> set (map fst xs). x < oid; ref < oid\<rbrakk> \<Longrightarrow> valid_spec_ops (xs@[(oid, Some ref)])"

fun insert_body :: "'oid::{linorder} list \<Rightarrow> 'oid \<Rightarrow> 'oid list" where
  "insert_body []     e = [e]" |
  "insert_body (x#xs) e =
     (if x < e then e#x#xs
               else x#insert_body xs e)"

fun insert_rga :: "'oid::{linorder} list \<Rightarrow> ('oid \<times> 'oid option) \<Rightarrow> 'oid list" where
  "insert_rga  xs    (e, None)   = insert_body xs e" |
  "insert_rga  []    (e, Some i) = []" |
  "insert_rga (x#xs) (e, Some i) =
     (if x = i then
        x#insert_body xs e
      else
        x#insert_rga xs (e, Some i))"

definition list_rga :: "('oid::{linorder} \<times> 'oid option) list \<Rightarrow> 'oid list" where
  "list_rga ops \<equiv> foldl insert_rga [] ops"

inductive valid_rga_ops :: "('oid::{linorder} \<times> 'oid option) list \<Rightarrow> bool" where
  "valid_rga_ops []" |
  "\<lbrakk>valid_rga_ops xs;
    oid \<notin> set (map fst xs)\<rbrakk> \<Longrightarrow> valid_rga_ops (xs@[(oid, None)])" |
  "\<lbrakk>valid_rga_ops xs;
    oid \<notin> set (map fst xs);
    ref \<in> set (map fst xs); ref < oid\<rbrakk>  \<Longrightarrow> valid_rga_ops (xs@[(oid, Some ref)])"

lemma spec_ops_distinct:
  assumes "valid_spec_ops xs"
  shows "distinct xs"
  using assms by(induction rule: valid_spec_ops.induct, force+)

lemma spec_ops_ref_less:
  assumes "valid_spec_ops (xs @ [(oid, Some ref)])"
  shows "ref < oid"
  using assms valid_spec_ops.cases by force

lemma spec_ops_rem_last:
  assumes "valid_spec_ops (xs@[x])"
  shows "valid_spec_ops xs"
  using assms valid_spec_ops.cases by fastforce

lemma spec_ops_id_inc:
  assumes "valid_spec_ops (xs@[(oid,ref)])"
    and "x \<in> set (map fst xs)"
  shows "x < oid"
  using assms valid_spec_ops.cases snoc_eq_iff_butlast by auto

lemma spec_ops_rem_any:
  assumes "valid_spec_ops (xs@[x]@ys)"
  shows "valid_spec_ops (xs@ys)"
  using assms apply(induction ys rule: rev_induct)
  using valid_spec_ops.simps apply auto[1]
  apply(subgoal_tac "valid_spec_ops (xs @ [x] @ xsa)") prefer 2
  using spec_ops_rem_last append_assoc apply metis
  apply clarsimp
  apply(subgoal_tac "\<And>xa. xa \<in> set (map fst (xs@xsa)) \<Longrightarrow> xa < a") prefer 2
  apply(subgoal_tac "set (map fst (xs @ xsa)) \<subseteq> set (map fst (xs @ x # xsa))") prefer 2
  apply force
  apply(subgoal_tac "xa \<in> set (map fst (xs @ x # xsa)) \<Longrightarrow> xa < a")
  apply blast
  apply(subgoal_tac "valid_spec_ops ((xs @ x # xsa) @ [(a, b)])")
  using spec_ops_id_inc apply(blast, simp)
  apply(case_tac b)
  apply(metis append_assoc valid_spec_ops.simps)
  apply(subgoal_tac "aa < a")
  apply(metis append_assoc valid_spec_ops.simps)
  apply(subgoal_tac "valid_spec_ops ((xs @ x # xsa) @ [(a, Some aa)])")
  using spec_ops_ref_less apply(blast, simp)
  done

lemma spec_ops_add_any:
  assumes "valid_spec_ops (xs @ ys)"
    and "\<forall>a \<in> set (map fst xs). a < oid"
    and "\<forall>a \<in> set (map fst ys). oid < a"
    and "\<And>r. ref = Some r \<Longrightarrow> r < oid"
  shows "valid_spec_ops (xs @ [(oid, ref)] @ ys)"
  using assms apply(induction ys rule: rev_induct)
  apply(case_tac ref)
  apply(simp add: valid_spec_ops.intros(2))
  apply(simp add: valid_spec_ops.intros(3))
  apply(subgoal_tac "valid_spec_ops (xs @ xsa)") prefer 2
  apply(metis append_assoc spec_ops_rem_last, simp)
  apply(case_tac x, simp)
  apply(subgoal_tac "valid_spec_ops ((xs @ (oid, ref) # xsa) @ [(a, b)])", force)
  apply(subgoal_tac "\<forall>y \<in> set (map fst (xs @ (oid, ref) # xsa)). y < a")
  apply(case_tac b)
  using valid_spec_ops.intros(2) apply blast
  apply(metis append_assoc spec_ops_ref_less valid_spec_ops.intros(3))
  apply(subgoal_tac "\<forall>y\<in>set (map fst xs). y < a") prefer 2
  apply force
  apply(subgoal_tac "\<forall>y\<in>set (map fst xsa). y < a") prefer 2
  apply(metis append.assoc in_set_conv_decomp map_append spec_ops_id_inc)
  apply force
  done

lemma spec_ops_split:
  assumes "valid_spec_ops ys"
    and "oid \<notin> set (map fst ys)"
  shows "\<exists>pre suf. ys = pre @ suf \<and>
            (\<forall>a\<in>set (map fst pre). a < oid) \<and>
            (\<forall>a\<in>set (map fst suf). oid < a)"
  using assms apply(induction ys rule: rev_induct)
  apply force
  apply(subgoal_tac "valid_spec_ops xs") prefer 2
  using spec_ops_rem_last apply blast
  apply(subgoal_tac "oid \<notin> set (map fst xs)") prefer 2
  apply simp
  apply clarsimp
  apply(case_tac "a < oid")
  apply(subgoal_tac "suf=[]") prefer 2
  apply(subgoal_tac "\<forall>x \<in> set (map fst (pre @ suf)). x < a") prefer 2
  apply(metis append.assoc spec_ops_id_inc)
  apply(subgoal_tac "\<forall>x \<in> set suf. fst x < a") prefer 2
  apply simp
  apply(subgoal_tac "\<forall>x \<in> set suf. fst x < oid") prefer 2
  apply fastforce
  using dual_order.asym last_in_set apply blast
  apply(rule_tac x="pre @ [(a, b)]" in exI, rule_tac x="[]" in exI)
  apply force
  apply(subgoal_tac "oid < a") prefer 2
  apply force
  apply(rule_tac x="pre" in exI, rule_tac x="suf @ [(a, b)]" in exI)
  apply force
  done

lemma rga_ops_distinct:
  assumes "valid_rga_ops xs"
  shows "distinct xs"
  using assms by(induction rule: valid_rga_ops.induct, force+)

lemma rga_ops_rem_last:
  assumes "valid_rga_ops (xs@[x])"
  shows "valid_rga_ops xs"
  using assms valid_rga_ops.cases by fastforce

lemma rga_ops_ref_less:
  assumes "valid_rga_ops (xs @ [(oid, Some ref)])"
  shows "ref < oid"
  using assms valid_rga_ops.cases by force

lemma rga_ops_oid_unique:
  assumes "valid_rga_ops (xs @ [(oid, ref)])"
  shows "oid \<notin> set (map fst xs)"
  using assms valid_rga_ops.cases by blast

lemma list_spec_monotonic:
  assumes "valid_spec_ops (xs@[(oid, ref)])"
  shows "set (list_spec xs) \<subseteq> set (list_spec (xs@[(oid, ref)]))"
  oops

lemma list_spec_op_ids:
  assumes "valid_spec_ops xs"
  shows "set (list_spec xs) \<subseteq> set (map fst xs)"
  using assms apply(induction xs rule: rev_induct)
  apply(simp add: list_spec_def)
  apply(subgoal_tac "set (list_spec xs) \<subseteq> set (map fst xs)") prefer 2
  using spec_ops_rem_last apply blast
  apply(simp add: list_spec_def)
  apply(subgoal_tac "\<And>a. a \<in> set (insert_spec (foldl insert_spec [] xs) x) \<Longrightarrow>
                          a \<in> insert (fst x) (fst ` set xs)")
  apply blast
  oops

lemma final_insert:
  assumes "permut (xs @ [x]) (ys @ [x])"
    and "valid_rga_ops (xs @ [x])"
    and "valid_spec_ops (ys @ [x])"
    and "list_rga xs = list_spec ys"
  shows "list_rga (xs @ [x]) = list_spec (ys @ [x])"
  using assms apply(simp add: list_rga_def list_spec_def)
  apply(subgoal_tac "\<exists>oid ref. x = (oid, ref)", (erule exE)+, simp) prefer 2
  apply force
  apply(subgoal_tac "\<And>a. a \<in> set (map fst ys) \<Longrightarrow> a < oid") prefer 2
  using spec_ops_id_inc apply blast
  sorry

lemma append_rga_op:
  assumes "permut (xs @ [x]) (ys @ [x] @ zs)"
    and "valid_rga_ops (xs @ [x])"
    and "valid_spec_ops (ys @ [x] @ zs)"
    and "list_rga xs = list_spec (ys @ zs)"
  shows "list_rga (xs @ [x]) = list_spec (ys @ [x] @ zs)"
  using assms apply(induction zs arbitrary: ys)
  apply(simp add: final_insert)
  sorry

lemma rga_spec_equal:
  assumes "permut xs ys"
    and "valid_rga_ops xs"
    and "valid_spec_ops ys"
  shows "list_rga xs = list_spec ys"
  using assms apply(induction xs arbitrary: ys rule: rev_induct)
  apply(simp add: list_rga_def list_spec_def permut_def)
  apply(subgoal_tac "\<exists>pre suf. ys=pre@[x]@suf") prefer 2
  apply(subgoal_tac "x \<in> set ys") prefer 2
  apply(metis last_in_set permut_def snoc_eq_iff_butlast)
  using list_split_memb apply force
  apply(erule exE, erule exE, erule_tac x="pre@suf" in meta_allE)
  apply(subgoal_tac "list_rga xs = list_spec (pre @ suf)", simp) prefer 2
  apply(meson permut_rem_last rga_ops_rem_last spec_ops_rem_any)
  using append_rga_op apply force
  done

lemma spec_ops_exist:
  assumes "valid_rga_ops xs"
  shows "\<exists>ys. permut xs ys \<and> valid_spec_ops ys"
  using assms apply(induction xs rule: rev_induct)
  apply(simp add: permut_def valid_spec_ops.intros(1))
  apply(subgoal_tac "\<exists>ys. permut xs ys \<and> valid_spec_ops ys") prefer 2
  using rga_ops_rem_last apply blast
  apply(simp, erule exE, erule conjE)
  apply(subgoal_tac "\<exists>oid ref. x = (oid, ref)", (erule exE)+, simp) prefer 2
  apply simp
  apply(subgoal_tac "\<exists>pre suf. ys = pre@suf \<and>
                       (\<forall>a \<in> set (map fst pre). a < oid) \<and>
                       (\<forall>a \<in> set (map fst suf). oid < a)")
  apply((erule exE)+, (erule conjE)+)
  apply(rule_tac x="pre @ [(oid, ref)] @ suf" in exI)
  apply(rule conjI)
  apply(meson permut_append rga_ops_distinct)
  apply(metis rga_ops_ref_less spec_ops_add_any)
  apply(subgoal_tac "oid \<notin> set (map fst ys)") prefer 2
  using permut_pair_fst rga_ops_oid_unique apply blast
  using spec_ops_split apply blast
  done

theorem rga_meets_spec:
  assumes "valid_rga_ops xs"
  shows "\<exists>ys. permut xs ys \<and> valid_spec_ops ys \<and> list_rga xs = list_spec ys"
  using assms rga_spec_equal spec_ops_exist by blast

end
