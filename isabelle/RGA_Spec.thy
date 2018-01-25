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
    
lemma last_element_greatest:
  assumes "valid_spec_ops (xs @ [x])"
    and "y \<in> set xs"
  shows "fst y < fst x"
    sorry

lemma permut_prefix_suffix_exists:
  assumes "permut (xsa @ [x]) (ys @ [x] @ xs @ [xa])"
  shows "\<exists>pre suf. xsa = pre @ [xa] @ suf"
  sorry
    
inductive_cases valid_rga_ops_singleton_middle: "valid_rga_ops (pre @ (a, b) # suf)"
inductive_cases valid_rga_ops_singleton_tail: "valid_rga_ops (pre @ xa # xs @ [(a, b)])"    
  
inductive_cases valid_spec_ops_last: "valid_spec_ops (ys @ [x] @ xs @ [xa])"
  
lemma valid_spec_ops_ref_less:
  shows "valid_spec_ops xs \<Longrightarrow> (oid, Some ref) \<in> set xs \<Longrightarrow> ref < oid"
  by(induction rule: valid_spec_ops.induct, auto)
    
lemma valid_rga_ops_ref_less:
  shows "valid_rga_ops xs \<Longrightarrow> (oid, Some ref) \<in> set xs \<Longrightarrow> ref < oid"
  by(induction rule: valid_rga_ops.induct, auto)

lemma valid_rga_ops_middle_elim:
  shows "(\<And>f r. (f, Some r) \<in> set suf \<Longrightarrow> r \<noteq> fst xa) \<Longrightarrow> valid_rga_ops (pre @ xa # suf) \<Longrightarrow> valid_rga_ops (pre @ suf)"
  apply(induction suf rule: List.rev_induct)
   apply(simp add: rga_ops_rem_last)
  apply(subgoal_tac "(\<And>f r. (f, Some r) \<in> set xs \<Longrightarrow> r \<noteq> fst xa)") prefer 2
   apply force
  apply(subgoal_tac "valid_rga_ops (pre @ xa # xs)") prefer 2
   apply(metis append.assoc append_Cons rga_ops_rem_last)
  apply clarsimp
  apply(erule valid_rga_ops_singleton_tail; clarsimp; subst append_assoc[symmetric]; rule valid_rga_ops.intros)
       apply auto
  done
    
lemma valid_rga_ops_distinct_fst:
  assumes "valid_rga_ops xs"
  shows "distinct (map fst xs)"
  using assms
  apply(induction xs rule: List.rev_induct)
   apply force
  apply clarsimp
  apply(metis list.set_map rga_ops_oid_unique rga_ops_rem_last)
  done
      
lemma valid_rga_ops_ref_integrity:
  assumes "valid_rga_ops (pre @ (oid, Some ref) # suf)"
  shows "ref \<in> fst ` set pre"
  using assms
  apply(induction suf rule: List.rev_induct)
   apply(ind_cases "valid_rga_ops (pre @ [(oid, Some ref)])")
    apply force
  apply(subgoal_tac "valid_rga_ops (pre @ (oid, Some ref) # xs)")
   apply force
  apply(metis surj_pair valid_rga_ops_singleton_tail)
    done

lemma valid_rga_ops_intro:
  assumes "\<And>r. ref = Some r \<Longrightarrow> r \<in> fst ` set xs \<and> r < oid"
    and "oid \<notin> fst ` set xs"
    and "valid_rga_ops xs"
  shows "valid_rga_ops (xs @ [(oid, ref)])"
using assms by (cases ref; auto simp add: valid_rga_ops.intros)

lemma interp_rga_tail_unfold:
  shows "interp_rga (xs@[x]) = insert_rga (interp_rga (xs)) x"
  by(clarsimp simp add: interp_rga_def)

lemma interp_list_tail_unfold:
  shows "interp_list (xs@[x]) = insert_spec (interp_list (xs)) x"
  by(clarsimp simp add: interp_list_def)
    
lemma interp_rga_independent_float_Some:
  assumes "valid_rga_ops(pre@suf@[(oid, Some r)])"
    and "\<And>oid' r. (oid', Some r) \<in> set suf \<Longrightarrow> r \<noteq> oid"
    and "r \<notin> fst ` set suf"
  shows "interp_rga (pre@(oid, Some r)#suf) = interp_rga (pre@suf@[(oid, Some r)])"
  using assms
  apply(induction suf rule: List.rev_induct)
   apply clarsimp
  apply clarsimp
  apply(subgoal_tac "valid_rga_ops (pre @ xs @ [(oid, Some r)])") prefer 2
   apply(subst append_assoc[symmetric], rule valid_rga_ops.intros)
      apply(metis append.left_neutral append_Cons append_assoc rga_ops_rem_last)
     apply(subgoal_tac "distinct (map fst (pre @ xs @ [(a, b), (oid, Some r)]))") prefer 2
  using valid_rga_ops_distinct_fst apply blast
     apply clarsimp
    using valid_rga_ops_ref_integrity
      apply (metis Un_iff append.assoc assms(1) assms(3) list.set_map map_append set_append)
     apply(metis append_assoc assms(1) rga_ops_ref_less)
    apply(subgoal_tac "(\<And>oid' r. (oid', Some r) \<in> set xs \<Longrightarrow> r \<noteq> oid)") prefer 2
     apply blast
    apply clarsimp
    apply(subgoal_tac "interp_rga (pre @ (oid, Some r) # xs @ [(a, b)]) = insert_rga (interp_rga (pre @ xs @ [(oid, Some r)])) (a, b)") prefer 2
      using interp_rga_tail_unfold
       apply(metis append.assoc append_Cons)
      apply(subgoal_tac "insert_rga (interp_rga (pre @ xs @ [(oid, Some r)])) (a, b) = insert_rga (insert_rga (interp_rga (pre @ xs)) (a, b)) (oid, Some r)") prefer 2
        using interp_rga_tail_unfold
         apply(metis append.assoc insert_rga_commutes option.inject)
        apply(metis append.left_neutral append_Cons append_assoc interp_rga_tail_unfold)
        done
    
lemma interp_rga_independent_float_None:
  assumes "valid_rga_ops(pre@suf@[(oid, None)])"
    and "\<And>oid' r. (oid', Some r) \<in> set suf \<Longrightarrow> r \<noteq> oid"
  shows "interp_rga (pre@(oid, None)#suf) = interp_rga (pre@suf@[(oid, None)])"
  using assms
  apply(induction suf rule: List.rev_induct)
   apply clarsimp
  apply clarsimp
  apply(subgoal_tac "valid_rga_ops (pre @ xs @ [(oid, None)])") prefer 2
   apply(subst append_assoc[symmetric], rule valid_rga_ops.intros)
      apply(metis append.left_neutral append_Cons append_assoc rga_ops_rem_last)
     apply(subgoal_tac "distinct (map fst (pre @ xs @ [(a, b), (oid, None)]))") prefer 2
  using valid_rga_ops_distinct_fst apply blast
     apply clarsimp
    apply(subgoal_tac "(\<And>oid' r. (oid', Some r) \<in> set xs \<Longrightarrow> r \<noteq> oid)") prefer 2
     apply blast
    apply clarsimp
    apply(subgoal_tac "interp_rga (pre @ (oid, None) # xs @ [(a, b)]) = insert_rga (interp_rga (pre @ xs @ [(oid, None)])) (a, b)") prefer 2
      using interp_rga_tail_unfold
       apply(metis append.assoc append_Cons)
      apply(subgoal_tac "insert_rga (interp_rga (pre @ xs @ [(oid, None)])) (a, b) = insert_rga (insert_rga (interp_rga (pre @ xs)) (a, b)) (oid, None)") prefer 2
        using interp_rga_tail_unfold
         apply(metis append.assoc insert_rga_None_commutes)
        apply(metis append.left_neutral append_Cons append_assoc interp_rga_tail_unfold)
        done
      
lemma valid_rga_ops_middle_singleton_notin_suffix:
  assumes "valid_rga_ops (pre@[(oid, Some ref)]@suf)"
  shows "ref \<notin> fst ` set suf"
  using assms
  apply -
  apply(subgoal_tac "ref \<in> fst ` set pre")
   apply(subgoal_tac "distinct (map fst (pre @ [(oid, Some ref)] @ suf))") prefer 2
  using valid_rga_ops_distinct_fst apply blast
    apply clarsimp
   apply(metis IntI empty_iff fst_conv image_eqI)
  apply clarsimp
  using valid_rga_ops_ref_integrity apply blast
  done
    
lemma insert_rga_insert_spec_tail_Some_elim:
  assumes "insert_rga list1 (oid, Some ref) = insert_spec list2 (oid, Some ref)"
    and "\<And>i. i \<in> set list1 \<Longrightarrow> i < oid"
    and "ref \<in> set list1"
  shows "list1 = list2"
  using assms
   apply(induction list1 arbitrary: list2)
   apply(case_tac list2; clarsimp split!: if_split_asm)
  apply(erule_tac x="tl list2" in meta_allE)
  apply clarsimp
  apply(erule disjE)
   apply(clarsimp split!: if_split_asm)
   apply(case_tac list2; clarsimp split!: if_split_asm)
   apply(metis insert_body.elims list.inject list.set_intros(1))
  apply(clarsimp split!: if_split_asm)
   apply(case_tac list2; clarsimp split!: if_split_asm)
   apply(metis insert_body.elims list.inject list.set_intros(1))
  apply(case_tac list2; clarsimp split!: if_split_asm)
  done
    
inductive_cases valid_spec_ops_tail_singleton: "valid_spec_ops (xs@[x])"
  
lemma valid_spec_ops_remove1:
  assumes "valid_spec_ops xs"
  shows "valid_spec_ops (remove1 x xs)"
  using assms
  apply(induction xs rule: List.rev_induct)
   apply clarsimp
  apply clarsimp
  apply(erule valid_spec_ops_tail_singleton)
   apply(clarsimp simp add: remove1_append split!: if_split)
    apply(rule valid_spec_ops.intros)
     apply force
    apply force
   apply(rule valid_spec_ops.intros)
    apply force+
  apply(clarsimp simp add: remove1_append split!: if_split)
    apply(rule valid_spec_ops.intros)
     apply force
    apply force
    apply force
   apply(rule valid_spec_ops.intros)
    apply force+
    done

lemma valid_rga_ops_rem_middle:
  assumes "valid_rga_ops (xs @ [(oid, ref)] @ ys)"
    and "\<And>r. Some r \<in> snd ` set ys \<Longrightarrow> r \<noteq> oid"
  shows "valid_rga_ops (xs @ ys)"
using assms proof(induction ys rule: rev_induct)
  case Nil
  then show "valid_rga_ops (xs @ [])"
    using rga_ops_rem_last by auto
next
  case (snoc y ys)
  then obtain yi yr where y_pair: "y = (yi, yr)"
    by force
  hence ref_less: "\<And>r. yr = Some r \<Longrightarrow> r < yi"
    using snoc.prems(1) valid_rga_ops_ref_less by fastforce
  have "valid_rga_ops (xs @ [(oid, ref)] @ ys)"
    by (metis snoc(2) append.assoc rga_ops_rem_last)
  hence IH: "valid_rga_ops (xs @ ys)"
    using snoc.IH snoc.prems(2) by auto
  have "\<And>r. yr = Some r \<Longrightarrow> r \<noteq> oid"
    by (simp add: y_pair snoc.prems(2))
  moreover have "\<And>r. yr = Some r \<Longrightarrow> r \<in> fst ` set (xs @ [(oid, ref)] @ ys)"
    by (metis y_pair append_assoc snoc.prems(1) valid_rga_ops_ref_integrity)
  ultimately have "\<And>r. yr = Some r \<Longrightarrow> r \<in> fst ` set (xs @ ys)"
    by simp
  moreover have "yi \<notin> fst ` set (xs @ [(oid, ref)] @ ys)"
    by (metis y_pair append_assoc rga_ops_oid_unique set_map snoc.prems(1))
  hence "yi \<notin> fst ` set (xs @ ys)"
    by auto
  ultimately show "valid_rga_ops (xs @ ys @ [y])"
    using IH ref_less y_pair valid_rga_ops_intro by (metis append.assoc)
qed

lemma valid_rga_ops_rem_spec:
  assumes "valid_spec_ops (xs @ [(oid, ref)])"
    and "valid_rga_ops (ys @ [(oid, ref)] @ zs)"
    and "permut (xs @ [(oid, ref)]) (ys @ [(oid, ref)] @ zs)"
  shows "valid_rga_ops (ys @ zs)"
proof -
  from assms(1) have "\<And>i. i \<in> fst ` set xs \<Longrightarrow> i < oid"
    by (simp add: last_element_greatest spec_ops_id_inc)
  moreover from assms(1) have "\<And>i r. (i, Some r) \<in> set xs \<Longrightarrow> r < i"
    using spec_ops_rem_last valid_spec_ops_ref_less by blast
  ultimately have "\<And>i r. (i, Some r) \<in> set xs \<Longrightarrow> r < oid"
    by fastforce
  moreover from assms(3) have "set zs \<subseteq> set xs"
    by (metis permut_rem_last permut_subset(2))
  ultimately have "\<And>r. Some r \<in> snd ` set zs \<Longrightarrow> r \<noteq> oid"
    by fastforce
  thus "valid_rga_ops (ys @ zs)"
    using assms(2) valid_rga_ops_rem_middle by blast
qed

lemma interp_rga_interp_list_equal_technical:
  assumes "valid_rga_ops (pre @ x # suf)"
    and "valid_rga_ops (pre @ suf)"
    and "valid_spec_ops (xs@[x])"
    and "permut (pre@[x]@suf) (xs@[x])"
    and "interp_rga (pre @ x # suf) = interp_list (xs @ [x])"
    and "\<And>f r. (f, Some r) \<in> set suf \<Longrightarrow> r \<noteq> fst x"
    and "\<And>r. snd x = Some r \<Longrightarrow> r \<notin> fst ` set suf"
  shows "interp_rga (pre @ suf) = interp_list xs"
  using assms
  apply(induction suf arbitrary: xs rule: List.rev_induct)
   apply clarsimp
   apply(subst (asm) interp_rga_tail_unfold)
   apply(subst (asm) interp_list_tail_unfold)
   apply(ind_cases "valid_rga_ops (pre @ [x])")
    apply(erule valid_spec_ops_tail_singleton)
     apply clarsimp
     apply(subgoal_tac "set pre = set xs") prefer 2
      apply(clarsimp simp add: permut_def)
      apply(simp add: insert_ident)
     apply(subgoal_tac "\<And>x. x \<in> set pre \<Longrightarrow> fst x < oid") prefer 2
      apply clarsimp
     apply(subgoal_tac "set (interp_rga pre) = fst ` set pre") prefer 2
      apply(simp add: rga_ops_interp_ids)
     apply(metis append_Cons append_Nil insert_body_contains_new_elem list.inject list.set_intros(1) neq_Nil_conv)
    apply force
   apply(erule valid_spec_ops_tail_singleton)
    apply force
   apply clarsimp
   apply(drule insert_rga_insert_spec_tail_Some_elim)
     apply(subgoal_tac "i \<in> fst ` set pre") prefer 2
      apply(simp add: rga_ops_interp_ids)
    apply(metis (no_types, lifting) append.right_neutral distinct_set_remove_mid imageE permut_def)
    apply(metis fst_conv image_eqI rga_ops_interp_ids set_map)
   apply force
    apply(erule_tac x="remove1 xa xsa" in meta_allE)
  apply(subgoal_tac "valid_rga_ops (pre @ x # xs)") prefer 2
   apply(metis surj_pair valid_rga_ops_singleton_tail)
  apply(subgoal_tac "valid_rga_ops (pre @ xs)") prefer 2
   apply(metis append.assoc rga_ops_rem_last)
  apply(subgoal_tac "valid_spec_ops (remove1 xa xsa @ [x])") prefer 2
    using valid_spec_ops_remove1 apply(metis remove1_append remove1_idem)
    apply(subgoal_tac "permut (pre @ [x] @ xs) (remove1 xa xsa @ [x])") prefer 2
     apply(clarsimp simp add: permut_def)
     apply auto[1]
    apply(subgoal_tac "interp_rga (pre @ x # xs) = interp_list (remove1 xa xsa @ [x])") prefer 2
     defer
     apply(subgoal_tac "(\<And>f r. (f, Some r) \<in> set xs \<Longrightarrow> r \<noteq> fst x)") prefer 2
      apply auto[1]
     apply(subgoal_tac "(\<And>r. snd x = Some r \<Longrightarrow> r \<notin> fst ` set xs)") prefer 2
      apply auto[1]
     apply clarsimp
     apply(cases x; clarsimp)
     apply(case_tac ba; clarsimp)
      apply(subst (asm) interp_rga_independent_float_None)
        apply(subgoal_tac "valid_rga_ops ((pre @ (xs @ [(a, b)])) @ [(aa, None)])")
         apply force
        apply(rule valid_rga_ops.intros)
         apply force
        apply clarsimp
        apply(rule conjI)
         apply(clarsimp simp add: permut_def)
    using valid_rga_ops_singleton_tail apply fastforce
        apply(rule conjI)
         apply(clarsimp simp add: permut_def)
         apply(metis Un_iff Un_insert_right fst_conv less_irrefl list.set_map list.simps(15) rev_image_eqI set_ConsD spec_ops_id_inc)
        apply(clarsimp simp add: permut_def)
        apply(metis distinct.simps(2) distinct_append fst_conv imageI list.map(2) list.set_map map_append valid_rga_ops_distinct_fst)
       apply clarsimp
      apply(subgoal_tac "interp_rga ((pre @ (xs @ [(a, b)])) @ [(aa, None)]) = interp_list (xsa @ [(aa, None)])") prefer 2
       apply simp
      apply(subst (asm) interp_rga_tail_unfold, subst (asm) interp_list_tail_unfold) back back
      apply(case_tac "interp_rga (pre @ xs @ [(a, b)])"; clarsimp split!: if_split_asm)
      apply(subst (asm) insert_body_head)
       apply(subgoal_tac "fst ` set (pre @ xs @ [(a, b)]) = set (aa # list)") prefer 2
        apply(metis rga_ops_interp_ids set_map)
       apply(subgoal_tac "\<And>x. x \<in> fst ` set xsa \<Longrightarrow> x < aa") prefer 2
        apply(simp add: spec_ops_id_inc)
       apply(subgoal_tac "set xsa = set (pre @ xs @ [(a,b)])") prefer 2
        apply(metis append_Cons append_Nil append_Nil2 permut_def permut_rem_any)
       apply simp
      apply force
      apply(subst (asm) interp_rga_independent_float_Some)
        apply(subgoal_tac "valid_rga_ops ((pre @ (xs @ [(a, b)])) @ [(aa, Some ab)])")
         apply force
        apply(rule valid_rga_ops.intros)
         apply force
        apply clarsimp
        apply(rule conjI)
         apply(clarsimp simp add: permut_def)
    using valid_rga_ops_singleton_tail apply fastforce
        apply(rule conjI)
         apply(clarsimp simp add: permut_def)
         apply(metis Un_iff Un_insert_right fst_conv less_irrefl list.set_map list.simps(15) rev_image_eqI set_ConsD spec_ops_id_inc)
        apply(clarsimp simp add: permut_def)
        apply(metis distinct.simps(2) distinct_append fst_conv imageI list.map(2) list.set_map map_append valid_rga_ops_distinct_fst)
         apply clarsimp
         apply(simp add: valid_rga_ops_ref_integrity)
        apply(simp add: spec_ops_ref_less)
       apply simp
      apply clarsimp
      apply(subgoal_tac "interp_rga ((pre @ (xs @ [(a, b)])) @ [(aa, Some ab)]) = interp_list (xsa @ [(aa, Some ab)])") prefer 2
         apply simp
      apply(subst (asm) interp_rga_tail_unfold, subst (asm) interp_list_tail_unfold) back back
     apply(case_tac "interp_rga (pre @ xs @ [(a, b)])"; clarsimp split!: if_split_asm)
       apply(case_tac "(interp_list xsa)")
        apply clarsimp
      apply(clarsimp split!: if_split_asm)
      apply(subst (asm) insert_body_head)
       apply(subgoal_tac "fst ` set (pre @ xs @ [(a, b)]) = set (ab # list)") prefer 2
        apply(metis rga_ops_interp_ids set_map)
       apply(subgoal_tac "\<And>x. x \<in> fst ` set xsa \<Longrightarrow> x < aa") prefer 2
        apply(simp add: spec_ops_id_inc)
       apply(subgoal_tac "set xsa = set (pre @ xs @ [(a,b)])") prefer 2
        apply(metis append_Cons append_Nil append_Nil2 permut_def permut_rem_any)
       apply simp
      apply(case_tac "(interp_list xsa)"; clarsimp split!: if_split_asm)
     apply(case_tac "(interp_list xsa)"; clarsimp split!: if_split_asm)
     apply(drule insert_rga_insert_spec_tail_Some_elim)
       apply(metis append.left_neutral append_Cons append_Nil2 notin_set_remove1 permut_pair_fst permut_rem_any remove1.simps(2) rga_ops_interp_ids spec_ops_id_inc)
      apply(metis Un_iff list.set_map map_append rga_ops_interp_ids set_ConsD set_append valid_rga_ops_ref_integrity)
     apply force
    apply(case_tac "xa \<in> set xsa") prefer 2
     apply(metis append.assoc append_Nil2 in_set_conv_decomp permut_def permut_rem_any)
    apply(subgoal_tac "\<exists>p s. xsa = p@[xa]@s \<and> xa \<notin> set p \<and> xa \<notin> set s") prefer 2
     apply(metis append_Cons append_Nil distinct.simps(2) distinct_append permut_def split_list_first)
    apply clarsimp
    apply(subgoal_tac "remove1 (a, b) (p @ (a, b) # s) = p@s") prefer 2
     apply (simp add: remove1_append)
      apply clarsimp
      
    
lemma append_rga_op:
  assumes "permut (xs @ [x]) (ys @ [x] @ zs)"
    and "valid_rga_ops (xs @ [x])"
    and "valid_spec_ops (ys @ [x] @ zs)"
    and "interp_rga xs = interp_list (ys @ zs)"
  shows "interp_rga (xs @ [x]) = interp_list (ys @ [x] @ zs)"
  using assms apply(induction zs arbitrary: xs ys rule: rev_induct)
  apply(simp add: final_insert)
  apply(subgoal_tac "\<And>oper. oper \<in> set(ys @ [x] @ xs) \<Longrightarrow> fst oper < fst xa") prefer 2
   apply(metis append_assoc last_element_greatest)
  apply(subgoal_tac "\<exists>pre suf. xsa = pre @ [xa] @ suf") prefer 2
        apply(rule permut_prefix_suffix_exists, assumption)
  (* therefore we can split xsa into pre@xa#suf, and commutatively swap xa with every op in suf *)
  apply(erule exE)+
  apply(subgoal_tac "\<And>oid ref. (oid, Some ref) \<in> set (ys @ [x] @ xs) \<Longrightarrow> ref < oid") prefer 2
    apply(subgoal_tac "valid_spec_ops (ys @ [x] @ xs)") prefer 2
    apply (metis append_Cons append_Nil valid_spec_ops_last)
  using valid_spec_ops_ref_less apply blast
  apply(subgoal_tac "\<And>oid ref. (oid, Some ref) \<in> set (ys @ [x] @ xs) \<Longrightarrow> ref < fst xa") prefer 2
    apply(metis fst_conv less_trans)
  apply(erule_tac x="pre@suf" in meta_allE)
  apply(erule_tac x="ys" in meta_allE)
  apply(subgoal_tac "permut ((pre @ suf) @ [x]) (ys @ [x] @ xs)") prefer 2
   apply(metis append.assoc append_Nil2 permut_rem_any)
  apply(subgoal_tac "\<And>e f r. e \<in> set suf \<Longrightarrow> e = (f, Some r) \<Longrightarrow> r \<noteq> fst xa") prefer 2
    apply(metis append.assoc append_Cons in_set_conv_decomp less_irrefl permut_def)
  apply(subgoal_tac "valid_rga_ops ((pre @ suf) @ [x])") prefer 2
   apply(subgoal_tac "valid_rga_ops (pre @ xa # suf)") prefer 2
    apply(metis append_Cons append_Nil rga_ops_rem_last)
   apply(subst append_assoc)
   apply(rule_tac xa=xa in valid_rga_ops_middle_elim)
    apply(metis Un_iff less_irrefl set_append)
   apply simp
  apply(subgoal_tac "valid_spec_ops (ys @ [x] @ xs)") prefer 2
   apply(metis append_Cons append_Nil valid_spec_ops_last)
  apply(subgoal_tac "interp_rga (pre @ suf) = interp_list (ys @ xs)") prefer 2
   apply clarsimp
   apply(rule_tac x="(a,b)" in interp_rga_interp_list_equal_technical)
       apply(metis append.assoc append_Cons rga_ops_rem_last)
      apply(metis append.assoc rga_ops_rem_last)
     apply force
    apply simp
   apply clarsimp
   apply(drule_tac suf="suf @ [x]" in valid_rga_ops_middle_singleton_notin_suffix[simplified])
    apply clarsimp
   apply(simp add: rev_image_eqI)
  apply clarsimp
  apply(case_tac "b"; clarify)
   apply(subst interp_rga_independent_float_None)
     apply(subst append_assoc[symmetric], rule valid_rga_ops.intros)
      apply force
    apply clarsimp
     apply(rule conjI)
  using prod.collapse apply blast
     apply(subgoal_tac "distinct (map fst (pre @ (a, None) # suf @ [x]))") prefer 2
      using valid_rga_ops_distinct_fst apply blast
         apply(clarsimp simp add: rev_image_eqI)
        apply clarsimp
        apply blast
       apply(subgoal_tac "interp_rga ((pre @ (suf @ [x])) @ [(a, None)]) = interp_list ((ys @ x # xs) @ [(a, None)])")
        apply simp
       apply(rule final_insert)
        apply(clarsimp simp add: permut_def)
          apply auto[1]
         apply(rule valid_rga_ops.intros)
          apply force
         apply clarsimp
        apply(rule conjI)
  using prod.collapse apply blast
     apply(subgoal_tac "distinct (map fst (pre @ (a, None) # suf @ [x]))") prefer 2
      using valid_rga_ops_distinct_fst apply blast
         apply(clarsimp simp add: rev_image_eqI)
        apply force
       apply force
      apply(subst interp_rga_independent_float_Some)
        apply(subst append_assoc[symmetric], rule valid_rga_ops.intros)
      apply force
    apply clarsimp
     apply(rule conjI)
  using prod.collapse apply blast
       apply(subgoal_tac "distinct (map fst (pre @ (a, Some aa) # suf @ [x]))") prefer 2
      using valid_rga_ops_distinct_fst apply blast
         apply(clarsimp simp add: rev_image_eqI)
        apply clarsimp
      using valid_rga_ops_ref_integrity apply blast
         apply(metis append.assoc append_Cons spec_ops_ref_less)
        apply(rule notI)
        apply clarsimp
        apply blast
       apply clarsimp
       apply(rule conjI)
      using valid_rga_ops_middle_singleton_notin_suffix apply fastforce
       apply(metis append_Cons append_Nil old.prod.exhaust valid_rga_ops_middle_singleton_notin_suffix valid_rga_ops_singleton_tail)
      apply(subgoal_tac "interp_rga ((pre @ (suf @ [x])) @ [(a, Some aa)]) = interp_list ((ys @ x # xs) @ [(a, Some aa)])")
       apply simp
        apply(rule final_insert)
        apply(clarsimp simp add: permut_def)
          apply auto[1]
         apply(rule valid_rga_ops.intros)
          apply force
         apply clarsimp
        apply(rule conjI)
      using prod.collapse apply blast
          apply(subgoal_tac "distinct (map fst (pre @ (a, Some aa) # suf @ [x]))") prefer 2
      using valid_rga_ops_distinct_fst apply blast
          apply(clarsimp simp add: rev_image_eqI)
         apply clarsimp
      using valid_rga_ops_ref_integrity apply blast
        apply clarsimp
        apply(metis append.assoc append_Cons spec_ops_ref_less)
       apply clarsimp
      apply blast
      done

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
