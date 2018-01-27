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

subsection\<open>Lemmas about the valid_spec_ops predicate\<close>

inductive_cases spec_ops_last: "valid_spec_ops (xs@[x])"

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

lemma spec_ops_add_any:
  assumes "valid_spec_ops (xs @ ys)"
    and "\<forall>i \<in> set (map fst xs). i < oid"
    and "\<forall>i \<in> set (map fst ys). oid < i"
    and "\<And>r. ref = Some r \<Longrightarrow> r < oid"
  shows "valid_spec_ops (xs @ [(oid, ref)] @ ys)"
using assms proof(induction ys rule: rev_induct)
  case Nil
  then show "valid_spec_ops (xs @ [(oid, ref)] @ [])"
    by (cases ref, auto simp add: valid_spec_ops.intros)
next
  case (snoc y ys)
  have IH: "valid_spec_ops (xs @ [(oid, ref)] @ ys)"
  proof -
    from snoc have "valid_spec_ops (xs @ ys)"
      by (metis append_assoc spec_ops_rem_last)
    thus "valid_spec_ops (xs @ [(oid, ref)] @ ys)"
      using assms(2) snoc by auto
  qed
  obtain yi yr where y_pair: "y = (yi, yr)"
    by force
  have oid_yi: "oid < yi"
    by (simp add: snoc.prems(3) y_pair)
  have yi_biggest: "\<forall>i \<in> set (map fst (xs @ (oid, ref) # ys)). i < yi"
  proof -
    have "\<forall>i \<in> set (map fst xs). i < yi"
      using oid_yi assms(2) less_trans by blast
    moreover have "\<forall>i \<in> set (map fst ys). i < yi"
      by (metis UnCI append_assoc map_append set_append snoc.prems(1) spec_ops_id_inc y_pair)
    ultimately show ?thesis
      using oid_yi by auto
  qed
  thus "valid_spec_ops (xs @ [(oid, ref)] @ ys @ [y])"
  proof(cases yr)
    case None
    then show ?thesis
      using IH yi_biggest valid_spec_ops.intros(2) y_pair by fastforce
  next
    case (Some r)
    moreover have "r < yi"
      by (metis Some append_assoc snoc.prems(1) spec_ops_ref_less y_pair)
    ultimately show ?thesis
      using IH yi_biggest valid_spec_ops.intros(3) y_pair by fastforce
  qed
qed

lemma spec_ops_split:
  assumes "valid_spec_ops xs"
    and "oid \<notin> set (map fst xs)"
  shows "\<exists>pre suf. xs = pre @ suf \<and>
            (\<forall>i \<in> set (map fst pre). i < oid) \<and>
            (\<forall>i \<in> set (map fst suf). oid < i)"
using assms proof(induction xs rule: rev_induct)
  case Nil
  then show ?case by force
next
  case (snoc x xs)
  obtain xi xr where y_pair: "x = (xi, xr)"
    by force
  obtain pre suf where IH: "xs = pre @ suf \<and>
               (\<forall>a\<in>set (map fst pre). a < oid) \<and>
               (\<forall>a\<in>set (map fst suf). oid < a)"
    by (metis UnCI map_append set_append snoc spec_ops_rem_last)
  then show ?case
  proof(cases "xi < oid")
    case xi_less: True
    have "\<forall>x \<in> set (map fst (pre @ suf)). x < xi"
      using IH spec_ops_id_inc snoc.prems(1) y_pair by blast
    hence "\<forall>x \<in> set suf. fst x < xi"
      by simp
    hence "\<forall>x \<in> set suf. fst x < oid"
      using xi_less by auto
    hence "suf = []"
      using IH last_in_set by fastforce
    hence "xs @ [x] = (pre @ [(xi, xr)]) @ [] \<and>
              (\<forall>a\<in>set (map fst ((pre @ [(xi, xr)]))). a < oid) \<and>
              (\<forall>a\<in>set (map fst []). oid < a)"
      by (simp add: IH xi_less y_pair)
    then show ?thesis by force
  next
    case False
    hence "oid < xi" using snoc.prems(2) y_pair by auto
    hence "xs @ [x] = pre @ (suf @ [(xi, xr)]) \<and>
              (\<forall>i \<in> set (map fst pre). i < oid) \<and>
              (\<forall>i \<in> set (map fst (suf @ [(xi, xr)])). oid < i)"
      by (simp add: IH y_pair)
    then show ?thesis by blast
  qed
qed


subsection\<open>Lemmas about the valid_rga_ops predicate\<close>

lemma rga_ops_intro:
  assumes "\<And>r. ref = Some r \<Longrightarrow> r \<in> fst ` set xs \<and> r < oid"
    and "oid \<notin> fst ` set xs"
    and "valid_rga_ops xs"
  shows "valid_rga_ops (xs @ [(oid, ref)])"
using assms by (cases ref; auto simp add: valid_rga_ops.intros)

lemma rga_ops_rem_last:
  assumes "valid_rga_ops (xs@[x])"
  shows "valid_rga_ops xs"
using assms valid_rga_ops.cases by fastforce

lemma rga_ops_ref_less_mid:
  assumes "valid_rga_ops xs"
    and "(oid, Some ref) \<in> set xs"
  shows "ref < oid"
using assms by (induction rule: valid_rga_ops.induct, auto)

lemma rga_ops_ref_less_last:
  assumes "valid_rga_ops (xs @ [(oid, Some ref)])"
  shows "ref < oid"
using assms rga_ops_ref_less_mid by fastforce

lemma rga_ops_distinct:
  assumes "valid_rga_ops xs"
  shows "distinct xs"
using assms by (induction xs, force+)

lemma rga_ops_distinct_fst:
  assumes "valid_rga_ops xs"
  shows "distinct (map fst xs)"
using assms by (induction xs, auto)

lemma rga_ops_unique_last:
  assumes "valid_rga_ops (xs @ [(oid, ref)])"
  shows "oid \<notin> set (map fst xs)"
using assms valid_rga_ops.cases by blast

lemma rga_ops_unique_mid:
  assumes "valid_rga_ops (xs @ [(oid, ref)] @ ys)"
  shows "oid \<notin> set (map fst xs) \<and> oid \<notin> set (map fst ys)"
using assms proof(induction ys rule: rev_induct)  
  case Nil
  then show "oid \<notin> set (map fst xs) \<and> oid \<notin> set (map fst [])"
    using valid_rga_ops.cases snoc_eq_iff_butlast by auto
next
  case (snoc y ys)
  obtain yi yr where y_pair: "y = (yi, yr)"
    by fastforce
  have IH: "oid \<notin> set (map fst xs) \<and> oid \<notin> set (map fst ys)"
    using rga_ops_rem_last snoc by (metis append_assoc)
  have "(xs @ (oid, ref) # ys) @ [(yi, yr)] = xs @ (oid, ref) # ys @ [(yi, yr)]"
    by simp
  hence "yi \<notin> set (map fst (xs @ (oid, ref) # ys))"
    using rga_ops_unique_last by (metis append_Cons append_self_conv2 snoc.prems y_pair)
  thus "oid \<notin> set (map fst xs) \<and> oid \<notin> set (map fst (ys @ [y]))"
    using IH y_pair by auto
qed

lemma rga_ops_ref_exists:
  assumes "valid_rga_ops (pre @ (oid, Some ref) # suf)"
  shows "ref \<in> fst ` set pre"
using assms proof(induction suf rule: List.rev_induct)
  case Nil thus ?case using valid_rga_ops.cases by fastforce
next
  case (snoc x xs) thus ?case using valid_rga_ops.cases by fastforce
qed

lemma rga_ops_no_future_ref:
  assumes "valid_rga_ops (xs @ [(oid, ref)] @ ys)"
  shows "\<And>r. ref = Some r \<Longrightarrow> r \<notin> fst ` set ys"
proof -
  from assms(1) have "\<And>r. ref = Some r \<Longrightarrow> r \<in> set (map fst xs)"
    by (simp add: rga_ops_ref_exists)
  moreover have "distinct (map fst (xs @ [(oid, ref)] @ ys))"
    using assms rga_ops_distinct_fst by blast
  ultimately have "\<And>r. ref = Some r \<Longrightarrow> r \<notin> set (map fst ([(oid, ref)] @ ys))"
    using distinct_pair_list_memb by metis
  thus "\<And>r. ref = Some r \<Longrightarrow> r \<notin> fst ` set ys"
    by simp
qed

lemma rga_ops_reorder:
  assumes "valid_rga_ops (xs @ [(oid, ref)] @ ys)"
    and "\<And>r. Some r \<in> snd ` set ys \<Longrightarrow> r \<noteq> oid"
  shows "valid_rga_ops (xs @ ys @ [(oid, ref)])"
using assms proof(induction ys rule: rev_induct)
  case Nil
  then show "valid_rga_ops (xs @ [] @ [(oid, ref)])"
    using rga_ops_rem_last by auto
next
  case (snoc y ys)
  then obtain yi yr where y_pair: "y = (yi, yr)"
    by force
  have IH: "valid_rga_ops (xs @ ys @ [(oid, ref)])"
  proof -
    have "valid_rga_ops (xs @ [(oid, ref)] @ ys)"
      by (metis snoc(2) append.assoc rga_ops_rem_last)
    thus "valid_rga_ops (xs @ ys @ [(oid, ref)])"
      using snoc.IH snoc.prems(2) by auto
  qed
  have "valid_rga_ops (xs @ ys @ [y])"
  proof -
    have "yi \<notin> fst ` set (xs @ [(oid, ref)] @ ys)"
      by (metis y_pair append_assoc rga_ops_unique_last set_map snoc.prems(1))
    hence "yi \<notin> fst ` set (xs @ ys)"
      by auto
    moreover have "\<And>r. yr = Some r \<Longrightarrow> r \<in> fst ` set (xs @ ys)"
    proof -
      have "\<And>r. yr = Some r \<Longrightarrow> r \<noteq> oid"
        by (simp add: y_pair snoc.prems(2))
      moreover have "\<And>r. yr = Some r \<Longrightarrow> r \<in> fst ` set (xs @ [(oid, ref)] @ ys)"
        by (metis y_pair append_assoc snoc.prems(1) rga_ops_ref_exists)
      ultimately show "\<And>r. yr = Some r \<Longrightarrow> r \<in> fst ` set (xs @ ys)"
        by simp
    qed
    moreover have "\<And>r. yr = Some r \<Longrightarrow> r < yi"
      using snoc.prems(1) rga_ops_ref_less_mid y_pair by fastforce
    moreover from IH have "valid_rga_ops (xs @ ys)"
      using rga_ops_rem_last by force
    ultimately show "valid_rga_ops (xs @ ys @ [y])"
      using y_pair rga_ops_intro by (metis append_assoc)
  qed
  moreover have "oid \<notin> fst ` set (xs @ ys @ [y])"
    using rga_ops_unique_mid by (metis (no_types, lifting) UnE image_Un 
      image_set set_append snoc.prems(1))
  moreover have "\<And>r. ref = Some r \<Longrightarrow> r \<in> fst ` set (xs @ ys @ [y])"
    using rga_ops_ref_exists
    by (metis UnCI append_Cons image_Un set_append snoc.prems(1))
  moreover have "\<And>r. ref = Some r \<Longrightarrow> r < oid"
    using IH by (simp add: rga_ops_ref_less_mid)
  ultimately show "valid_rga_ops (xs @ (ys @ [y]) @ [(oid, ref)])"
    using rga_ops_intro by (metis append_assoc)
qed

lemma rga_ops_rem_middle:
  assumes "valid_rga_ops (xs @ [(oid, ref)] @ ys)"
    and "\<And>r. Some r \<in> snd ` set ys \<Longrightarrow> r \<noteq> oid"
  shows "valid_rga_ops (xs @ ys)"
using assms rga_ops_rem_last rga_ops_reorder append_assoc by metis

lemma rga_ops_independent_suf:
  assumes "valid_spec_ops (xs @ [(oid, ref)])"
    and "valid_rga_ops (ys @ [(oid, ref)] @ zs)"
    and "permut (xs @ [(oid, ref)]) (ys @ [(oid, ref)] @ zs)"
  shows "\<And>i r. (i, Some r) \<in> set zs \<Longrightarrow> r \<noteq> oid"
proof -
  have "\<And>i r. (i, Some r) \<in> set xs \<Longrightarrow> r < oid"
  proof -
    from assms(1) have "\<And>i. i \<in> fst ` set xs \<Longrightarrow> i < oid"
      using spec_ops_id_inc by fastforce
    moreover from assms(1) have "\<And>i r. (i, Some r) \<in> set xs \<Longrightarrow> r < i"
      using assms rga_ops_ref_less_mid by (metis butlast_snoc in_set_butlastD permut_def)
    ultimately show "\<And>i r. (i, Some r) \<in> set xs \<Longrightarrow> r < oid"
      by fastforce
  qed
  moreover from assms(3) have "set zs \<subseteq> set xs"
    by (metis permut_rem_last permut_subset(2))
  ultimately show "\<And>i r. (i, Some r) \<in> set zs \<Longrightarrow> r \<noteq> oid"
    by fastforce
qed

lemma rga_ops_reorder_spec:
  assumes "valid_spec_ops (xs @ [(oid, ref)])"
    and "valid_rga_ops (ys @ [(oid, ref)] @ zs)"
    and "permut (xs @ [(oid, ref)]) (ys @ [(oid, ref)] @ zs)"
  shows "valid_rga_ops (ys @ zs @ [(oid, ref)])"
using assms rga_ops_reorder rga_ops_independent_suf by fastforce

lemma rga_ops_rem_spec:
  assumes "valid_spec_ops (xs @ [(oid, ref)])"
    and "valid_rga_ops (ys @ [(oid, ref)] @ zs)"
    and "permut (xs @ [(oid, ref)]) (ys @ [(oid, ref)] @ zs)"
  shows "valid_rga_ops (ys @ zs)"
using assms rga_ops_rem_last rga_ops_reorder_spec append_assoc by metis


subsection\<open>Lemmas about the interp_rga function\<close>

lemma interp_rga_tail_unfold:
  shows "interp_rga (xs@[x]) = insert_rga (interp_rga (xs)) x"
by (clarsimp simp add: interp_rga_def)

lemma interp_list_tail_unfold:
  shows "interp_list (xs@[x]) = insert_spec (interp_list (xs)) x"
by (clarsimp simp add: interp_list_def)

lemma interp_rga_ids:
  assumes "valid_rga_ops xs"
  shows "set (interp_rga xs) = set (map fst xs)"
using assms proof(induction xs rule: List.rev_induct)
  case Nil
  then show "set (interp_rga []) = set (map fst [])"
    by (simp add: interp_rga_def)
next
  case (snoc x xs)
  hence IH: "set (interp_rga xs) = set (map fst xs)"
    using rga_ops_rem_last by blast
  obtain xi xr where x_pair: "x = (xi, xr)"
    by force
  then show "set (interp_rga (xs @ [x])) = set (map fst (xs @ [x]))"
  proof(cases xr)
    case None
    then show ?thesis
      using IH x_pair by (clarsimp simp add: interp_rga_def)
  next
    case (Some r)
    moreover from this have "r \<in> set (interp_rga xs)"
      using IH rga_ops_ref_exists by (metis x_pair list.set_map snoc.prems)
    ultimately have "set (interp_rga (xs @ [(xi, xr)])) = insert xi (set (interp_rga xs))"
      by (simp add: insert_some_insert_indices interp_rga_tail_unfold)
    then show "set (interp_rga (xs @ [x])) = set (map fst (xs @ [x]))"
      using IH x_pair by auto
  qed
qed

lemma interp_rga_distinct:
  assumes "valid_rga_ops xs"
  shows "distinct (interp_rga xs)"
using assms proof(induction xs rule: List.rev_induct)
  case Nil
  then show "distinct (interp_rga [])" by (simp add: interp_rga_def)
next
  case (snoc x xs)
  hence IH: "distinct (interp_rga xs)"
    using rga_ops_rem_last by blast
  moreover obtain xi xr where x_pair: "x = (xi, xr)"
    by force
  moreover from this have "xi \<notin> set (interp_rga xs)"
    using interp_rga_ids rga_ops_unique_last rga_ops_rem_last by (metis snoc.prems)
  moreover have "xr = None \<or> (\<exists>r. xr = Some r \<and> r \<in> set (map fst xs))"
    using valid_rga_ops.cases snoc.prems snoc_eq_iff_butlast x_pair by auto
  hence "xr = None \<or> (\<exists>r. xr = Some r \<and> r \<in> set (interp_rga xs))"
    using interp_rga_ids rga_ops_rem_last snoc.prems by blast
  hence "\<exists>pre suf. interp_rga xs = pre@suf \<and>
           insert_rga (interp_rga xs) (xi, xr) = pre @ xi # suf"
    using IH insert_preserves_order by blast
  ultimately show "distinct (interp_rga (xs @ [x]))" 
    by (metis Un_iff disjoint_insert(1) distinct.simps(2) distinct_append 
        interp_rga_tail_unfold list.simps(15) set_append)
qed


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
  using interp_rga_ids rga_ops_rem_last apply blast
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

lemma interp_rga_reorder_Some:
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
  using rga_ops_distinct_fst apply blast
     apply clarsimp
    using rga_ops_ref_exists
      apply (metis Un_iff append.assoc assms(1) assms(3) list.set_map map_append set_append)
     apply (simp add: rga_ops_ref_less_mid)
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
    
lemma interp_rga_reorder_None:
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
  using rga_ops_distinct_fst apply blast
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

lemma rga_spec_equal:
  assumes "permut xs ys"
    and "valid_spec_ops xs"
    and "valid_rga_ops ys"
  shows "interp_list xs = interp_rga ys"
using assms proof(induction xs arbitrary: ys rule: rev_induct)
  case Nil
  then show ?case by (simp add: interp_rga_def interp_list_def permut_def)
next
  case (snoc x xs)
  hence "x \<in> set ys"
    by (metis last_in_set permut_def snoc_eq_iff_butlast)
  from this obtain pre suf where ys_split: "ys = pre @ [x] @ suf"
    using list_split_memb by force
  have IH: "interp_list xs = interp_rga (pre @ suf)"
  proof -
    have "valid_rga_ops (pre @ suf)"
      using rga_ops_rem_spec snoc by (metis ys_split spec_ops_last)
    thus ?thesis
      using permut_rem_last spec_ops_rem_last ys_split snoc by metis
  qed
  have valid_rga: "valid_rga_ops (pre @ suf @ [x])"
    using rga_ops_reorder_spec snoc.prems ys_split
    by (metis spec_ops_last)
  have "interp_list (xs @ [x]) = interp_rga (pre @ suf @ [x])"
  proof -
    have "permut (xs @ [x]) (pre @ suf @ [x])"
      using permut_reorder1 snoc.prems(1) ys_split by fastforce
    thus ?thesis
      using valid_rga final_insert IH by (metis append_assoc permut_commute snoc.prems(2))
  qed
  moreover have "interp_rga (pre @ suf @ [x]) = interp_rga (pre @ [x] @ suf)"
  proof -
    obtain oid ref where x_pair: "x = (oid, ref)"
      by force
    have no_ref: "\<And>i r. (i, Some r) \<in> set suf \<Longrightarrow> r \<noteq> oid"
      using rga_ops_independent_suf snoc.prems x_pair ys_split by blast
    show ?thesis
    proof(cases ref)
      case None
      then show "interp_rga (pre @ suf @ [x]) = interp_rga (pre @ [x] @ suf)" 
        using no_ref interp_rga_reorder_None valid_rga x_pair by fastforce
    next
      case (Some a)
      moreover from this have "a \<notin> fst ` set suf"
        using rga_ops_no_future_ref snoc.prems(3) x_pair ys_split by blast
      ultimately show "interp_rga (pre @ suf @ [x]) = interp_rga (pre @ [x] @ suf)"
        using interp_rga_reorder_Some no_ref valid_rga x_pair by force
    qed
  qed
  ultimately show "interp_list (xs @ [x]) = interp_rga ys"
    by (simp add: ys_split)
qed

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
  apply(metis rga_ops_ref_less_last spec_ops_add_any)
  apply(subgoal_tac "oid \<notin> set (map fst ys)") prefer 2
  using permut_pair_fst rga_ops_unique_last apply blast
  using spec_ops_split apply blast
  done

theorem rga_meets_spec:
  assumes "valid_rga_ops xs"
  shows "\<exists>ys. permut ys xs \<and> valid_spec_ops ys \<and> interp_list ys = interp_rga xs"
  using assms rga_spec_equal spec_ops_exist permut_commute by blast

end
