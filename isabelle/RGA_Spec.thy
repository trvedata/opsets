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

subsection\<open>Lemmata about the valid_spec_ops predicate\<close>

inductive_cases spec_ops_last: "valid_spec_ops (xs @ [x])"

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


subsection\<open>Lemmata about the valid_rga_ops predicate\<close>

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

lemma rga_ops_rem_penultimate:
  assumes "valid_rga_ops (xs @ [(i1, r1)] @ [(i2, r2)])"
    and "\<And>r. r2 = Some r \<Longrightarrow> r \<noteq> i1"
  shows "valid_rga_ops (xs @ [(i2, r2)])"
proof -
  have "valid_rga_ops (xs @ [(i1, r1)])"
    using assms(1) rga_ops_rem_last by force
  hence "valid_rga_ops xs"
    using rga_ops_rem_last by force
  moreover have "distinct (map fst (xs @ [(i1, r1)] @ [(i2, r2)]))"
    using assms(1) rga_ops_distinct_fst by blast
  hence "i2 \<notin> set (map fst xs)"
    by auto
  moreover have "\<And>r. r2 = Some r \<Longrightarrow> r \<in> set (map fst (xs @ [(i1, r1)]))"
    using assms(1) by (metis append.assoc list.set_map rga_ops_ref_exists)
  hence "\<And>r. r2 = Some r \<Longrightarrow> r \<in> set (map fst xs)"
    using assms(2) by auto
  moreover have "\<And>r. r2 = Some r \<Longrightarrow> r < i2"
    using assms(1) rga_ops_ref_less_last by (metis append.assoc)
  ultimately show "valid_rga_ops (xs @ [(i2, r2)])"
    by (simp add: rga_ops_intro)
qed


subsection\<open>Lemmata about the interp_rga function\<close>

lemma interp_rga_tail_unfold:
  shows "interp_rga (xs@[x]) = insert_rga (interp_rga (xs)) x"
by (clarsimp simp add: interp_rga_def)

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


subsection\<open>Proof that RGA satisfies the list specification\<close>

lemma final_insert:
  assumes "permut (xs @ [x]) (ys @ [x])"
    and "valid_rga_ops (xs @ [x])"
    and "valid_spec_ops (ys @ [x])"
    and "interp_rga xs = interp_list ys"
  shows "interp_rga (xs @ [x]) = interp_list (ys @ [x])"
proof -
  obtain oid ref where x_pair: "x = (oid, ref)" by force
  have "permut xs ys"
    using assms(1) permut_rem_any by fastforce
  have oid_greatest: "\<And>i. i \<in> set (interp_rga xs) \<Longrightarrow> i < oid"
  proof -
    have "\<And>i. i \<in> set (map fst ys) \<Longrightarrow> i < oid"
      using assms(3) spec_ops_id_inc x_pair by blast
    hence "\<And>i. i \<in> set (map fst xs) \<Longrightarrow> i < oid"
      using \<open>permut xs ys\<close> permut_pair_fst by blast
    thus "\<And>i. i \<in> set (interp_rga xs) \<Longrightarrow> i < oid"
      using assms(2) interp_rga_ids rga_ops_rem_last by blast
  qed
  thus "interp_rga (xs @ [x]) = interp_list (ys @ [x])"
  proof(cases ref)
    case None
    moreover from this have "insert_rga (interp_rga xs) (oid, ref) = oid # interp_rga xs"
      using oid_greatest hd_in_set insert_body.elims insert_body.simps(1)
        insert_rga.simps(1) list.sel(1) by metis
    ultimately show "interp_rga (xs @ [x]) = interp_list (ys @ [x])" 
      using assms(4) by (simp add: interp_list_tail_unfold interp_rga_tail_unfold x_pair)
  next
    case (Some r)
    have "\<exists>as bs. interp_rga xs = as @ r # bs"
    proof -
      have "r \<in> set (map fst xs)"
        using assms(2) valid_rga_ops.cases Some x_pair by blast
      hence "r \<in> set (interp_rga xs)"
        using assms(2) interp_rga_ids rga_ops_rem_last by blast
      thus ?thesis by (simp add: split_list)
    qed
    from this obtain as bs where as_bs: "interp_rga xs = as @ r # bs" by force
    hence "distinct (as @ r # bs)"
      by (metis assms(2) interp_rga_distinct rga_ops_rem_last)
    hence "insert_rga (as @ r # bs) (oid, Some r) = as @ r # oid # bs"
      by (metis as_bs insert_between_elements oid_greatest)
    moreover have "insert_spec (as @ r # bs) (oid, Some r) = as @ r # oid # bs"
      by (meson \<open>distinct (as @ r # bs)\<close> insert_after_ref)
    ultimately show "interp_rga (xs @ [x]) = interp_list (ys @ [x])" 
      by (metis assms(4) Some as_bs interp_list_tail_unfold interp_rga_tail_unfold x_pair)
  qed
qed

lemma interp_rga_reorder:
  assumes "valid_rga_ops (pre @ suf @ [(oid, ref)])"
    and "\<And>i r. (i, Some r) \<in> set suf \<Longrightarrow> r \<noteq> oid"
    and "\<And>r. ref = Some r \<Longrightarrow> r \<notin> fst ` set suf"
  shows "interp_rga (pre @ (oid, ref) # suf) = interp_rga (pre @ suf @ [(oid, ref)])"
using assms proof(induction suf rule: List.rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  have ref_not_x: "\<And>r. ref = Some r \<Longrightarrow> r \<noteq> fst x" using snoc.prems(3) by auto
  have IH: "interp_rga (pre @ (oid, ref) # xs) = interp_rga (pre @ xs @ [(oid, ref)])"
  proof -
    have "valid_rga_ops (pre @ xs @ [(oid, ref)])"
      using rga_ops_rem_penultimate ref_not_x
      by (metis append.assoc prod.collapse snoc.prems(1))
    thus ?thesis using snoc by force
  qed
  obtain xi xr where x_pair: "x = (xi, xr)" by force
  have "interp_rga (pre @ (oid, ref) # xs @ [(xi, xr)]) =
        insert_rga (interp_rga (pre @ xs @ [(oid, ref)])) (xi, xr)"
    using IH interp_rga_tail_unfold by (metis append.assoc append_Cons)
  moreover have "... = insert_rga (insert_rga (interp_rga (pre @ xs)) (oid, ref)) (xi, xr)"
    using interp_rga_tail_unfold by (metis append_assoc)
  moreover have "... = insert_rga (insert_rga (interp_rga (pre @ xs)) (xi, xr)) (oid, ref)"
  proof -
    have "\<And>xrr. xr = Some xrr \<Longrightarrow> xrr \<noteq> oid"
      using x_pair snoc.prems(2) by auto
    thus ?thesis
      using insert_rga_commutes ref_not_x by (metis fst_conv x_pair)
  qed
  moreover have "... = interp_rga (pre @ xs @ [x] @ [(oid, ref)])"
    by (metis append_assoc interp_rga_tail_unfold x_pair)
  ultimately show "interp_rga (pre @ (oid, ref) # xs @ [x]) =
                   interp_rga (pre @ (xs @ [x]) @ [(oid, ref)])"
    by (simp add: x_pair)
qed

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
      using valid_rga final_insert IH
      by (metis append_assoc permut_commute snoc.prems(2))
  qed
  moreover have "... = interp_rga (pre @ [x] @ suf)"
  proof -
    obtain oid ref where x_pair: "x = (oid, ref)"
      by force
    have "\<And>i r. (i, Some r) \<in> set suf \<Longrightarrow> r \<noteq> oid"
      using rga_ops_independent_suf snoc.prems x_pair ys_split by blast
    moreover have "\<And>r. ref = Some r \<Longrightarrow> r \<notin> fst ` set suf"
      using rga_ops_no_future_ref snoc.prems(3) x_pair ys_split by blast
    ultimately show "interp_rga (pre @ suf @ [x]) = interp_rga (pre @ [x] @ suf)"
      using interp_rga_reorder valid_rga x_pair by force
  qed
  ultimately show "interp_list (xs @ [x]) = interp_rga ys"
    by (simp add: ys_split)
qed

lemma spec_ops_exist:
  assumes "valid_rga_ops xs"
  shows "\<exists>ys. permut xs ys \<and> valid_spec_ops ys"
using assms proof(induction xs rule: List.rev_induct)
  case Nil
  then show "\<exists>ys. permut [] ys \<and> valid_spec_ops ys"
    by (simp add: permut_def valid_spec_ops.intros(1))
next
  case (snoc x xs)
  hence IH: "\<exists>ys. permut xs ys \<and> valid_spec_ops ys"
    using rga_ops_rem_last by blast
  then obtain ys oid ref
    where "permut xs ys" and "valid_spec_ops ys" and "x = (oid, ref)"
    by force
  moreover have "\<exists>pre suf. ys = pre@suf \<and>
                       (\<forall>i \<in> set (map fst pre). i < oid) \<and>
                       (\<forall>i \<in> set (map fst suf). oid < i)"
  proof -
    have "oid \<notin> set (map fst ys)"
      using permut_pair_fst rga_ops_unique_last calculation snoc.prems by blast
    thus ?thesis
      using spec_ops_split \<open>valid_spec_ops ys\<close> by blast
  qed
  from this obtain pre suf where "ys = pre @ suf" and
                       "\<forall>i \<in> set (map fst pre). i < oid" and
                       "\<forall>i \<in> set (map fst suf). oid < i" by force
  moreover have "permut (xs @ [(oid, ref)]) (pre @ [(oid, ref)] @ suf)"
    using permut_append rga_ops_distinct calculation snoc.prems by fastforce
  moreover have "valid_spec_ops (pre @ [(oid, ref)] @ suf)"
    using rga_ops_ref_less_last spec_ops_add_any calculation snoc.prems by metis
  ultimately show "\<exists>ys. permut (xs @ [x]) ys \<and> valid_spec_ops ys"
    by blast
qed

theorem rga_meets_spec:
  assumes "valid_rga_ops xs"
  shows "\<exists>ys. permut ys xs \<and> valid_spec_ops ys \<and> interp_list ys = interp_rga xs"
  using assms rga_spec_equal spec_ops_exist permut_commute by blast

end
