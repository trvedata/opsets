theory RGA_Spec
  imports Main Permute Insert_Spec RGA
begin

inductive valid_spec_ops :: "('oid::{linorder} \<times> 'oid option) list \<Rightarrow> bool" where
  "valid_spec_ops []" |
  "\<lbrakk>valid_spec_ops xs;
    \<forall>x \<in> set (map fst xs). x < oid\<rbrakk> \<Longrightarrow> valid_spec_ops (xs@[(oid, None)])" |
  "\<lbrakk>valid_spec_ops xs;
    \<forall>x \<in> set (map fst xs). x < oid; ref < oid\<rbrakk> \<Longrightarrow> valid_spec_ops (xs@[(oid, Some ref)])"

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

lemma spec_ops_sorted:
  assumes "valid_spec_ops xs"
  shows "sorted (map fst xs)"
  using assms by (induction rule: valid_spec_ops.induct; auto simp add: order_less_imp_le sorted_append)

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

lemma rga_ops_interp_ids:
  assumes "valid_rga_ops xs"
  shows "set (interp_rga xs) = set (map fst xs)"
  using assms apply(induction xs rule: rev_induct)
  apply(simp add: interp_rga_def)
  apply(subgoal_tac "valid_rga_ops xs") prefer 2
  using rga_ops_rem_last apply blast
  apply(clarsimp simp add: interp_rga_def)
  apply(case_tac b, simp)
  apply(subgoal_tac "aa \<in> set (foldl insert_rga [] xs)") prefer 2
  using valid_rga_ops.cases apply fastforce
  apply(simp add: insert_some_insert_indices)
  done

lemma interp_rga_distinct:
  assumes "valid_rga_ops xs"
  shows "distinct (interp_rga xs)"
  using assms apply(induction xs rule: rev_induct)
  apply(simp add: interp_rga_def)
  apply(subgoal_tac "distinct (foldl insert_rga [] xs)") prefer 2
  apply(metis interp_rga_def rga_ops_rem_last)
  apply(clarsimp simp add: interp_rga_def)
  apply(subgoal_tac "a \<notin> set (foldl insert_rga [] xs)") prefer 2
  apply(metis interp_rga_def rga_ops_interp_ids rga_ops_oid_unique rga_ops_rem_last)
  apply(subgoal_tac "b = None \<or> (\<exists>i. b = Some i \<and> i \<in> set (map fst xs))") prefer 2
  using valid_rga_ops.cases apply fastforce
  apply(subgoal_tac "b = None \<or> (\<exists>i. b = Some i \<and> i \<in> set (foldl insert_rga [] xs))") prefer 2
  apply(metis interp_rga_def rga_ops_interp_ids rga_ops_rem_last)
  apply(subgoal_tac "\<exists>pre suf. foldl insert_rga [] xs = pre@suf \<and>
                     insert_rga (foldl insert_rga [] xs) (a, b) = pre @ a # suf")
  apply force
  using insert_preserves_order apply blast
  done

lemma final_insert:
  assumes "permut (xs @ [x]) (ys @ [x])"
    and "valid_rga_ops (xs @ [x])"
    and "valid_spec_ops (ys @ [x])"
    and "interp_rga xs = interp_list ys"
  shows "interp_rga (xs @ [x]) = interp_list (ys @ [x])"
  using assms apply(simp add: interp_rga_def interp_list_def)
  apply(subgoal_tac "\<exists>oid ref. x = (oid, ref)", (erule exE)+, simp) prefer 2
  apply force
  apply(subgoal_tac "permut xs ys") prefer 2
  using permut_rem_any apply fastforce
  apply(subgoal_tac "\<And>a. a \<in> set (map fst xs) \<Longrightarrow> a < oid") prefer 2
  using spec_ops_id_inc permut_pair_fst apply blast
  apply(subgoal_tac "\<And>a. a \<in> set (interp_rga xs) \<Longrightarrow> a < oid") prefer 2
  apply(metis assms(4) interp_list_op_ids permut_pair_fst subset_code(1))
  apply(case_tac ref)
  apply(subgoal_tac "insert_rga (interp_rga xs) (oid, ref) = oid # interp_rga xs")
  apply(simp add: interp_rga_def)
  apply(metis hd_in_set insert_body.elims insert_body.simps(1) insert_rga.simps(1) list.sel(1))
  apply(subgoal_tac "a \<in> set (map fst xs)") prefer 2
  using valid_rga_ops.cases apply fastforce
  apply(subgoal_tac "a \<in> set (interp_rga xs)") prefer 2
  using rga_ops_interp_ids rga_ops_rem_last apply blast
  apply(subgoal_tac "\<exists>as bs. interp_rga xs = as@a#bs", clarify) prefer 2
  apply(simp add: split_list)
  apply(subgoal_tac "insert_rga (as@a#bs) (oid, Some a) = as@a#oid#bs")
  apply(subgoal_tac "insert_spec (as@a#bs) (oid, Some a) = as@a#oid#bs")
  apply(simp add: interp_rga_def)
  apply(subgoal_tac "distinct (as @ a # bs)") prefer 2
  apply(metis interp_rga_distinct rga_ops_rem_last)
  apply(rule insert_after_ref, assumption)
  apply(metis insert_between_elements interp_rga_distinct rga_ops_rem_last)
  done                   

lemma append_rga_op:
  assumes "permut (xs @ [x]) (ys @ [x] @ zs)"
    and "valid_rga_ops (xs @ [x])"
    and "valid_spec_ops (ys @ [x] @ zs)"
    and "interp_rga xs = interp_list (ys @ zs)"
  shows "interp_rga (xs @ [x]) = interp_list (ys @ [x] @ zs)"
  using assms apply(induction zs arbitrary: xs ys rule: rev_induct)
  apply(simp add: final_insert)
  apply(subgoal_tac "\<And>oper. oper \<in> set(ys @ [x] @ xs) \<Longrightarrow> fst oper < fst xa") prefer 2
  apply(metis append_assoc foo)
  (* xa is biggest op \<Longrightarrow> its insertion happens directly after reference element *)
  apply(subgoal_tac "xa \<in> set xsa") prefer 2
  (* therefore we can split xsa into pre@xa#suf, and commutatively swap xa with every op in suf *)
  sorry

lemma rga_spec_equal:
  assumes "permut xs ys"
    and "valid_rga_ops xs"
    and "valid_spec_ops ys"
  shows "interp_rga xs = interp_list ys"
  using assms apply(induction xs arbitrary: ys rule: rev_induct)
  apply(simp add: interp_rga_def interp_list_def permut_def)
  apply(subgoal_tac "\<exists>pre suf. ys=pre@[x]@suf") prefer 2
  apply(subgoal_tac "x \<in> set ys") prefer 2
  apply(metis last_in_set permut_def snoc_eq_iff_butlast)
  using list_split_memb apply force
  apply(erule exE, erule exE, erule_tac x="pre@suf" in meta_allE)
  apply(subgoal_tac "interp_rga xs = interp_list (pre @ suf)", simp) prefer 2
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
  shows "\<exists>ys. permut xs ys \<and> valid_spec_ops ys \<and> interp_rga xs = interp_list ys"
  using assms rga_spec_equal spec_ops_exist by blast

end
