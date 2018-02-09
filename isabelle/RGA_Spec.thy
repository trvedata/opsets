theory RGA_Spec
  imports Insert_Spec RGA
begin

locale insert_opset = opset opset set_option
  for opset :: "('oid::{linorder} \<times> 'oid option) set"


subsection\<open>Lemmata about the rga_ops predicate\<close>

definition rga_ops :: "('oid::{linorder} \<times> 'oid option) list \<Rightarrow> bool" where
  "rga_ops list \<equiv> crdt_ops set_option list"

lemma rga_ops_rem_last:
  assumes "rga_ops (xs @ [x])"
  shows "rga_ops xs"
using assms crdt_ops_rem_last rga_ops_def by blast

lemma rga_ops_rem_penultimate:
  assumes "rga_ops (xs @ [(i1, r1), (i2, r2)])"
    and "\<And>r. r2 = Some r \<Longrightarrow> r \<noteq> i1"
  shows "rga_ops (xs @ [(i2, r2)])"
using assms proof -
  have "crdt_ops set_option (xs @ [(i2, r2)])"
    using assms crdt_ops_rem_penultimate rga_ops_def by fastforce
  thus "rga_ops (xs @ [(i2, r2)])"
    by (simp add: rga_ops_def)
qed

lemma rga_ops_ref_exists:
  assumes "rga_ops (pre @ (oid, Some ref) # suf)"
  shows "ref \<in> fst ` set pre"
proof -
  from assms have "crdt_ops set_option (pre @ (oid, Some ref) # suf)"
    by (simp add: rga_ops_def)
  moreover have "set_option (Some ref) = {ref}"
    by simp
  ultimately show "ref \<in> fst ` set pre"
    using crdt_ops_ref_exists by fastforce
qed


subsection\<open>Lemmata about the interp_rga function\<close>

lemma interp_rga_tail_unfold:
  shows "interp_rga (xs@[x]) = insert_rga (interp_rga (xs)) x"
by (clarsimp simp add: interp_rga_def)

lemma interp_rga_ids:
  assumes "rga_ops xs"
  shows "set (interp_rga xs) = set (map fst xs)"
using assms proof(induction xs rule: List.rev_induct)
  case Nil
  then show "set (interp_rga []) = set (map fst [])"
    by (simp add: interp_rga_def)
next
  case (snoc x xs)
  hence IH: "set (interp_rga xs) = set (map fst xs)"
    using rga_ops_rem_last by blast
  obtain xi xr where x_pair: "x = (xi, xr)" by force
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
  assumes "rga_ops xs"
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
    using interp_rga_ids crdt_ops_unique_last rga_ops_rem_last
    by (metis rga_ops_def snoc.prems)
  moreover have "\<exists>pre suf. interp_rga xs = pre@suf \<and>
           insert_rga (interp_rga xs) (xi, xr) = pre @ xi # suf"
  proof -
    have "\<And>r. r \<in> set_option xr \<Longrightarrow> r \<in> set (map fst xs)"
      using crdt_ops_ref_exists rga_ops_def snoc.prems x_pair by fastforce
    hence "xr = None \<or> (\<exists>r. xr = Some r \<and> r \<in> set (map fst xs))"
      using option.set_sel by blast
    hence "xr = None \<or> (\<exists>r. xr = Some r \<and> r \<in> set (interp_rga xs))"
      using interp_rga_ids rga_ops_rem_last snoc.prems by blast
    thus ?thesis
      using IH insert_preserves_order by blast
  qed
  ultimately show "distinct (interp_rga (xs @ [x]))" 
    by (metis Un_iff disjoint_insert(1) distinct.simps(2) distinct_append 
        interp_rga_tail_unfold list.simps(15) set_append)
qed


subsection\<open>Proof that RGA satisfies the list specification\<close>

lemma final_insert:
  assumes "permut (xs @ [x]) (ys @ [x])"
    and "rga_ops (xs @ [x])"
    and "insert_ops (ys @ [x])"
    and "interp_rga xs = interp_list ys"
  shows "interp_rga (xs @ [x]) = interp_list (ys @ [x])"
proof -
  obtain oid ref where x_pair: "x = (oid, ref)" by force
  have "permut xs ys"
    using assms(1) permut_rem_any by fastforce
  have oid_greatest: "\<And>i. i \<in> set (interp_rga xs) \<Longrightarrow> i < oid"
  proof -
    have "\<And>i. i \<in> set (map fst ys) \<Longrightarrow> i < oid"
      using assms(3) by (simp add: spec_ops_id_inc x_pair insert_ops_def)
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
        using assms(2) Some by (simp add: rga_ops_ref_exists x_pair)
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
  assumes "rga_ops (pre @ suf @ [(oid, ref)])"
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
    have "rga_ops ((pre @ xs) @ [x] @ [(oid, ref)])"
      using snoc.prems(1) by auto
    moreover have "\<And>r. ref = Some r \<Longrightarrow> r \<noteq> fst x"
      by (simp add: ref_not_x)
    ultimately have "rga_ops ((pre @ xs) @ [(oid, ref)])"
      using rga_ops_rem_penultimate
      by (metis (no_types, lifting) Cons_eq_append_conv prod.collapse)
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
    and "insert_ops xs"
    and "rga_ops ys"
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
    have "crdt_ops set_option (pre @ suf)"
    proof -
      have "crdt_ops set_option (pre @ [x] @ suf)"
        using rga_ops_def snoc.prems(3) ys_split by blast
      thus "crdt_ops set_option (pre @ suf)"
        using crdt_ops_rem_spec snoc.prems ys_split insert_ops_def by blast
    qed
    hence "rga_ops (pre @ suf)"
      using rga_ops_def by blast
    thus ?thesis
      using permut_rem_last insert_ops_rem_last ys_split snoc by metis
  qed
  have valid_rga: "rga_ops (pre @ suf @ [x])"
  proof -
    have "crdt_ops set_option (pre @ suf @ [x])"
      using snoc.prems ys_split
      by (simp add: crdt_ops_reorder_spec insert_ops_def rga_ops_def)
    thus "rga_ops (pre @ suf @ [x])"
      by (simp add: rga_ops_def)
  qed
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
    have "\<And>op2 r. op2 \<in> snd ` set suf \<Longrightarrow> r \<in> set_option op2 \<Longrightarrow> r \<noteq> oid"
      using snoc.prems
      by (simp add: crdt_ops_independent_suf insert_ops_def rga_ops_def x_pair ys_split)
    hence "\<And>i r. (i, Some r) \<in> set suf \<Longrightarrow> r \<noteq> oid"
      by fastforce 
    moreover have "\<And>r. ref = Some r \<Longrightarrow> r \<notin> fst ` set suf"
      using crdt_ops_no_future_ref snoc.prems(3) x_pair ys_split
      by (metis option.set_intros rga_ops_def)
    ultimately show "interp_rga (pre @ suf @ [x]) = interp_rga (pre @ [x] @ suf)"
      using interp_rga_reorder valid_rga x_pair by force
  qed
  ultimately show "interp_list (xs @ [x]) = interp_rga ys"
    by (simp add: ys_split)
qed

lemma insert_ops_exist:
  assumes "rga_ops xs"
  shows "\<exists>ys. permut xs ys \<and> insert_ops ys"
using assms proof(induction xs rule: List.rev_induct)
  case Nil
  then show "\<exists>ys. permut [] ys \<and> insert_ops ys"
    by (simp add: permut_def spec_ops_empty insert_ops_def)
next
  case (snoc x xs)
  hence IH: "\<exists>ys. permut xs ys \<and> insert_ops ys"
    using rga_ops_rem_last by blast
  then obtain ys oid ref
    where "permut xs ys" and "insert_ops ys" and "x = (oid, ref)"
    by force
  moreover have "\<exists>pre suf. ys = pre@suf \<and>
                       (\<forall>i \<in> set (map fst pre). i < oid) \<and>
                       (\<forall>i \<in> set (map fst suf). oid < i)"
  proof -
    have "oid \<notin> set (map fst xs)"
      using calculation(3) crdt_ops_unique_last rga_ops_def snoc.prems by fastforce
    hence "oid \<notin> set (map fst ys)"
      using calculation(1) permut_pair_fst by blast 
    thus ?thesis
      using spec_ops_split \<open>insert_ops ys\<close> insert_ops_def by blast
  qed
  from this obtain pre suf where "ys = pre @ suf" and
                       "\<forall>i \<in> set (map fst pre). i < oid" and
                       "\<forall>i \<in> set (map fst suf). oid < i" by force
  moreover have "permut (xs @ [(oid, ref)]) (pre @ [(oid, ref)] @ suf)"
    using permut_append crdt_ops_distinct calculation snoc.prems rga_ops_def by metis
  moreover have "insert_ops (pre @ [(oid, ref)] @ suf)"
  proof -
    have "\<forall>r \<in> set_option ref. r < oid"
      using calculation(3) crdt_ops_ref_less_last rga_ops_def snoc.prems by fastforce
    hence "spec_ops set_option (pre @ [(oid, ref)] @ suf)"
      using spec_ops_add_any calculation insert_ops_def by metis
    thus ?thesis by (simp add: insert_ops_def)
  qed
  ultimately show "\<exists>ys. permut (xs @ [x]) ys \<and> insert_ops ys"
    by blast
qed

theorem rga_meets_spec:
  assumes "rga_ops xs"
  shows "\<exists>ys. permut ys xs \<and> insert_ops ys \<and> interp_list ys = interp_rga xs"
  using assms rga_spec_equal insert_ops_exist permut_commute by blast

end
