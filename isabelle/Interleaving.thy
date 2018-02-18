(* Martin Kleppmann, University of Cambridge
   Victor B. F. Gomes, University of Cambridge
   Dominic P. Mulligan, Arm Research, Cambridge
*)

section\<open>Interleaving of concurrent insertions\<close>

text\<open>In this section we prove that our list specification rules out
interleaving of concurrent insertions at the same position.\<close>

theory Interleaving
  imports Insert_Spec
begin

lemma interp_ins_maybe_grow:
  assumes "insert_ops (xs @ [(oid, ref)])"
  shows "set (interp_ins (xs @ [(oid, ref)])) = set (interp_ins xs) \<or>
         set (interp_ins (xs @ [(oid, ref)])) = (set (interp_ins xs) \<union> {oid})"
by (cases ref, simp add: interp_ins_tail_unfold,
    metis insert_spec_nonex insert_spec_set interp_ins_tail_unfold)

lemma interp_ins_maybe_grow2:
  assumes "insert_ops (xs @ [x])"
  shows "set (interp_ins (xs @ [x])) = set (interp_ins xs) \<or>
         set (interp_ins (xs @ [x])) = (set (interp_ins xs) \<union> {fst x})"
using assms interp_ins_maybe_grow by (cases x, auto)

lemma interp_ins_maybe_grow3:
  assumes "insert_ops (xs @ ys)"
  shows "\<exists>A. A \<subseteq> set (map fst ys) \<and> set (interp_ins (xs @ ys)) = set (interp_ins xs) \<union> A"
using assms proof(induction ys rule: List.rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x ys)
  then have "insert_ops (xs @ ys)"
    by (metis append_assoc insert_ops_rem_last)
  then obtain A where IH: "A \<subseteq> set (map fst ys) \<and>
            set (interp_ins (xs @ ys)) = set (interp_ins xs) \<union> A"
    using snoc.IH by blast
  then show ?case
  proof(cases "set (interp_ins (xs @ ys @ [x])) = set (interp_ins (xs @ ys))")
    case True
    moreover have "A \<subseteq> set (map fst (ys @ [x]))"
      using IH by auto
    ultimately show ?thesis
      using IH by auto
  next
    case False
    then have "set (interp_ins (xs @ ys @ [x])) = set (interp_ins (xs @ ys)) \<union> {fst x}"
      by (metis append_assoc interp_ins_maybe_grow2 snoc.prems)
    moreover have "A \<union> {fst x} \<subseteq> set (map fst (ys @ [x]))"
      using IH by auto
    ultimately show ?thesis
      using IH Un_assoc by metis
  qed
qed

lemma interp_ins_ref_nonex:
  assumes "insert_ops ops"
    and "ops = xs @ [(oid, Some ref)] @ ys"
    and "ref \<notin> set (interp_ins xs)"
  shows "oid \<notin> set (interp_ins ops)"
using assms proof(induction ys arbitrary: ops rule: List.rev_induct)
  case Nil
  then have "interp_ins ops = insert_spec (interp_ins xs) (oid, Some ref)"
    by (simp add: interp_ins_tail_unfold)
  moreover have "\<And>i. i \<in> set (map fst xs) \<Longrightarrow> i < oid"
    using Nil.prems last_op_greatest by fastforce
  hence "\<And>i. i \<in> set (interp_ins xs) \<Longrightarrow> i < oid"
    by (meson interp_ins_subset subsetCE)
  ultimately show "oid \<notin> set (interp_ins ops)"
    using assms(3) by auto
next
  case (snoc x ys)
  then have "insert_ops (xs @ (oid, Some ref) # ys)"
    by (metis append.assoc append.simps(1) append_Cons insert_ops_appendD)
  hence IH: "oid \<notin> set (interp_ins (xs @ (oid, Some ref) # ys))"
    by (simp add: snoc.IH snoc.prems(3))
  moreover have "distinct (map fst (xs @ (oid, Some ref) # ys @ [x]))"
    using snoc.prems by (metis append_Cons append_self_conv2 insert_ops_def spec_ops_def)
  hence "fst x \<noteq> oid"
    using empty_iff by auto
  moreover have "insert_ops ((xs @ (oid, Some ref) # ys) @ [x])"
    using snoc.prems by auto
  hence "set (interp_ins ((xs @ (oid, Some ref) # ys) @ [x])) =
         set (interp_ins (xs @ (oid, Some ref) # ys)) \<or> 
         set (interp_ins ((xs @ (oid, Some ref) # ys) @ [x])) =
         set (interp_ins (xs @ (oid, Some ref) # ys)) \<union> {fst x}"
    using interp_ins_maybe_grow2 by blast
  ultimately show "oid \<notin> set (interp_ins ops)"
    using snoc.prems(2) by auto
qed

lemma map_fst_append1:
  assumes "\<forall>i \<in> set (map fst xs). P i"
    and "P x"
  shows "\<forall>i \<in> set (map fst (xs @ [(x, y)])). P i"
using assms by (induction xs, auto)

lemma insert_ops_split:
  assumes "insert_ops ops"
    and "(oid, ref) \<in> set ops"
  shows "\<exists>pre suf. ops = pre @ [(oid, ref)] @ suf \<and>
            (\<forall>i \<in> set (map fst pre). i < oid) \<and>
            (\<forall>i \<in> set (map fst suf). oid < i)"
using assms proof(induction ops rule: List.rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc x xs)
  then show ?case
  proof(cases "x = (oid, ref)")
    case True
    moreover from this have "\<forall>i \<in> set (map fst xs). i < oid"
      using last_op_greatest snoc.prems(1) by blast
    ultimately have "xs @ [x] = xs @ [(oid, ref)] @ [] \<and>
            (\<forall>i \<in> set (map fst xs). i < oid) \<and>
            (\<forall>i \<in> set (map fst []). oid < i)"
      by auto
    then show ?thesis by force
  next
    case False
    hence "(oid, ref) \<in> set xs"
      using snoc.prems(2) by auto
    from this obtain pre suf where IH: "xs = pre @ [(oid, ref)] @ suf \<and>
         (\<forall>i \<in> set (map fst pre). i < oid) \<and>
         (\<forall>i \<in> set (map fst suf). oid < i)"
      using snoc.IH snoc.prems(1) by blast
    obtain xi xr where x_pair: "x = (xi, xr)"
      by force
    hence "distinct (map fst (pre @ [(oid, ref)] @ suf @ [(xi, xr)]))"
      by (metis IH append.assoc insert_ops_def spec_ops_def snoc.prems(1))
    hence "xi \<noteq> oid"
      by auto
    have xi_max: "\<forall>x \<in> set (map fst (pre @ [(oid, ref)] @ suf)). x < xi"
      using IH last_op_greatest snoc.prems(1) x_pair by blast
    then show ?thesis
    proof(cases "xi < oid")
      case True
      moreover from this have "\<forall>x \<in> set suf. fst x < oid"
        using xi_max by auto
      hence "suf = []"
        using IH last_in_set by fastforce
      ultimately have "xs @ [x] = (pre @ [(xi, xr)]) @ [] \<and>
              (\<forall>i \<in> set (map fst ((pre @ [(xi, xr)]))). i < oid) \<and>
              (\<forall>i \<in> set (map fst []). oid < i)"
        using dual_order.asym xi_max by auto
      then show ?thesis by (simp add: IH)
    next
      case False
      hence "oid < xi"
        using \<open>xi \<noteq> oid\<close> by auto
      hence "\<forall>i \<in> set (map fst (suf @ [(xi, xr)])). oid < i"
        using IH map_fst_append1 by auto
      hence "xs @ [x] = pre @ [(oid, ref)] @ (suf @ [(xi, xr)]) \<and>
              (\<forall>i \<in> set (map fst pre). i < oid) \<and>
              (\<forall>i \<in> set (map fst (suf @ [(xi, xr)])). oid < i)"
        by (simp add: IH x_pair)
      then show ?thesis by blast
    qed
  qed
qed

lemma insert_ops_split_2:
  assumes "insert_ops ops"
    and "(xid, xr) \<in> set ops"
    and "(yid, yr) \<in> set ops"
    and "xid < yid"
  shows "\<exists>as bs cs. ops = as @ [(xid, xr)] @ bs @ [(yid, yr)] @ cs \<and>
           (\<forall>i \<in> set (map fst as). i < xid) \<and>
           (\<forall>i \<in> set (map fst bs). xid < i \<and> i < yid) \<and>
           (\<forall>i \<in> set (map fst cs). yid < i)"
proof -
  obtain as as1 where x_split: "ops = as @ [(xid, xr)] @ as1 \<and>
      (\<forall>i \<in> set (map fst as). i < xid) \<and> (\<forall>i \<in> set (map fst as1). xid < i)"
    using assms insert_ops_split by blast
  hence "insert_ops ((as @ [(xid, xr)]) @ as1)"
    using assms(1) by auto
  hence "insert_ops as1"
    using assms(1) insert_ops_rem_prefix by blast
  have "(yid, yr) \<in> set as1"
    using x_split assms by auto
  from this obtain bs cs where y_split: "as1 = bs @ [(yid, yr)] @ cs \<and>
      (\<forall>i \<in> set (map fst bs). i < yid) \<and> (\<forall>i \<in> set (map fst cs). yid < i)"
    using assms insert_ops_split \<open>insert_ops as1\<close> by blast
  hence "ops = as @ [(xid, xr)] @ bs @ [(yid, yr)] @ cs"
    using x_split by blast
  moreover have "\<forall>i \<in> set (map fst bs). xid < i \<and> i < yid"
    by (simp add: x_split y_split)
  ultimately show ?thesis
    using x_split y_split by blast
qed

lemma insert_ops_split_3:
  assumes "insert_ops ops"
    and "(xid, xr) \<in> set ops"
    and "(yid, yr) \<in> set ops"
    and "(zid, zr) \<in> set ops"
    and "xid < yid" and "yid < zid"
  shows "\<exists>as bs cs ds. ops = as @ [(xid, xr)] @ bs @ [(yid, yr)] @ cs @ [(zid, zr)] @ ds \<and>
           (\<forall>i \<in> set (map fst as). i < xid) \<and>
           (\<forall>i \<in> set (map fst bs). xid < i \<and> i < yid) \<and>
           (\<forall>i \<in> set (map fst cs). yid < i \<and> i < zid) \<and>
           (\<forall>i \<in> set (map fst ds). zid < i)"
proof -
  obtain as bs cs1 where xy_split: "ops = as @ [(xid, xr)] @ bs @ [(yid, yr)] @ cs1 \<and>
           (\<forall>i \<in> set (map fst as). i < xid) \<and>
           (\<forall>i \<in> set (map fst bs). xid < i \<and> i < yid) \<and>
           (\<forall>i \<in> set (map fst cs1). yid < i)"
    using assms insert_ops_split_2 by blast
  hence "insert_ops ((as @ [(xid, xr)] @ bs @ [(yid, yr)]) @ cs1)"
    using assms(1) by auto
  hence "insert_ops cs1"
    using assms(1) insert_ops_rem_prefix by blast
  have "(zid, zr) \<in> set cs1"
    using assms xy_split by auto
  from this obtain cs ds where z_split: "cs1 = cs @ [(zid, zr)] @ ds \<and>
      (\<forall>i \<in> set (map fst cs). i < zid) \<and> (\<forall>i \<in> set (map fst ds). zid < i)"
    using assms insert_ops_split \<open>insert_ops cs1\<close> by blast
  hence "ops = as @ [(xid, xr)] @ bs @ [(yid, yr)] @ cs @ [(zid, zr)] @ ds"
    using xy_split by blast
  moreover have "\<forall>i \<in> set (map fst cs). yid < i \<and> i < zid"
    by (simp add: xy_split z_split)
  ultimately show ?thesis
    using xy_split z_split by blast
qed

lemma interp_ins_last_None:
  shows "oid \<in> set (interp_ins (ops @ [(oid, None)]))"
by (simp add: interp_ins_tail_unfold)

lemma interp_ins_monotonic:
  assumes "insert_ops (pre @ suf)"
    and "oid \<in> set (interp_ins pre)"
  shows "oid \<in> set (interp_ins (pre @ suf))"
using assms interp_ins_maybe_grow3 by auto

lemma insert_ops_sorted_oids:
  assumes "insert_ops (xs @ [(i1, r1)] @ ys @ [(i2, r2)])"
  shows "i1 < i2"
proof -
  have "\<And>i. i \<in> set (map fst (xs @ [(i1, r1)] @ ys)) \<Longrightarrow> i < i2"
    by (metis append.assoc assms last_op_greatest)
  moreover have "i1 \<in> set (map fst (xs @ [(i1, r1)] @ ys))"
    by auto
  ultimately show "i1 < i2"
    by blast
qed

lemma interp_ins_append_non_memb:
  assumes "insert_ops (pre @ [(oid, Some ref)] @ suf)"
    and "ref \<notin> set (interp_ins pre)"
  shows "ref \<notin> set (interp_ins (pre @ [(oid, Some ref)] @ suf))"
using assms proof(induction suf rule: List.rev_induct)
  case Nil
  then show "ref \<notin> set (interp_ins (pre @ [(oid, Some ref)] @ []))"
    by (metis append_Nil2 insert_spec_nonex interp_ins_tail_unfold)
next
  case (snoc x xs)
  hence IH: "ref \<notin> set (interp_ins (pre @ [(oid, Some ref)] @ xs))"
    by (metis append_assoc insert_ops_rem_last)
  moreover have "ref < oid"
    using insert_ops_ref_older snoc.prems(1) by auto
  moreover have "oid < fst x"
    using insert_ops_sorted_oids by (metis prod.collapse snoc.prems(1))
  have "set (interp_ins ((pre @ [(oid, Some ref)] @ xs) @ [x])) =
        set (interp_ins (pre @ [(oid, Some ref)] @ xs)) \<or>
        set (interp_ins ((pre @ [(oid, Some ref)] @ xs) @ [x])) =
        set (interp_ins (pre @ [(oid, Some ref)] @ xs)) \<union> {fst x}"
    by (metis (full_types) append.assoc interp_ins_maybe_grow2 snoc.prems(1))
  ultimately show "ref \<notin> set (interp_ins (pre @ [(oid, Some ref)] @ xs @ [x]))"
    using \<open>oid < fst x\<close> by auto
qed

lemma interp_ins_append_memb:
  assumes "insert_ops (pre @ [(oid, Some ref)] @ suf)"
    and "ref \<in> set (interp_ins pre)"
  shows "oid \<in> set (interp_ins (pre @ [(oid, Some ref)] @ suf))"
using assms by (metis UnCI append_assoc insert_spec_set interp_ins_monotonic
  interp_ins_tail_unfold singletonI)

lemma interp_ins_append_forward:
  assumes "insert_ops (xs @ ys)"
    and "oid \<in> set (interp_ins (xs @ ys))"
    and "oid \<in> set (map fst xs)"
  shows "oid \<in> set (interp_ins xs)"
using assms proof(induction ys rule: List.rev_induct, simp)
  case (snoc y ys)
  obtain cs ds ref where "xs = cs @ (oid, ref) # ds"
    by (metis (no_types, lifting) imageE prod.collapse set_map snoc.prems(3) split_list_last)
  hence "insert_ops (cs @ [(oid, ref)] @ (ds @ ys) @ [y])"
    using snoc.prems(1) by auto
  hence "oid < fst y"
    using insert_ops_sorted_oids by (metis prod.collapse)
  hence "oid \<noteq> fst y"
    by blast
  then show ?case
    using snoc.IH snoc.prems(1) snoc.prems(2) assms(3) inserted_item_ident
    by (metis append_assoc insert_ops_appendD interp_ins_tail_unfold prod.collapse)
qed

lemma interp_ins_nonex_forward:
  assumes "insert_ops (xs @ ys)"
    and "oid \<notin> set (interp_ins (xs @ ys))"
  shows "oid \<notin> set (interp_ins xs)"
using assms interp_ins_monotonic by blast

lemma interp_ins_find_ref:
  assumes "insert_ops (xs @ [(oid, Some ref)] @ ys)"
    and "ref \<in> set (interp_ins (xs @ [(oid, Some ref)] @ ys))"
  shows "\<exists>r. (ref, r) \<in> set xs"
proof -
  have "ref < oid"
    using assms(1) insert_ops_ref_older by blast
  have "ref \<in> set (map fst (xs @ [(oid, Some ref)] @ ys))"
    by (meson assms(2) interp_ins_subset subsetCE)
  then obtain x where x_prop: "x \<in> set (xs @ [(oid, Some ref)] @ ys) \<and> fst x = ref"
    by fastforce
  obtain xr where x_pair: "x = (ref, xr)"
    using prod.exhaust_sel x_prop by blast
  show "\<exists>r. (ref, r) \<in> set xs"
  proof(cases "x \<in> set xs")
    case True
    then show "\<exists>r. (ref, r) \<in> set xs"
      by (metis x_prop prod.collapse)
  next
    case False
    hence "(ref, xr) \<in> set ([(oid, Some ref)] @ ys)"
      using x_prop x_pair by auto
    hence "(ref, xr) \<in> set ys"
      using \<open>ref < oid\<close> x_prop
      by (metis append_Cons append_self_conv2 fst_conv min.strict_order_iff set_ConsD)
    then obtain as bs where "ys = as @ (ref, xr) # bs"
      by (meson split_list)
    hence "insert_ops ((xs @ [(oid, Some ref)] @ as @ [(ref, xr)]) @ bs)"
      using assms(1) by auto
    hence "insert_ops (xs @ [(oid, Some ref)] @ as @ [(ref, xr)])"
      using insert_ops_appendD by blast
    hence "oid < ref" (* contradiction *)
      using insert_ops_sorted_oids by auto
    then show ?thesis
      using \<open>ref < oid\<close> by force
  qed
qed

lemma list_order_append:
  assumes "insert_ops (pre @ suf)"
    and "list_order pre x y"
  shows "list_order (pre @ suf) x y"
by (metis Un_iff assms list_order_monotonic insert_ops_appendD set_append subset_code(1))

lemma list_order_insert_ref:
  assumes "insert_ops (ops @ [(oid, Some ref)])"
    and "ref \<in> set (interp_ins ops)"
  shows "list_order (ops @ [(oid, Some ref)]) ref oid"
proof -
  have "interp_ins (ops @ [(oid, Some ref)]) = insert_spec (interp_ins ops) (oid, Some ref)"
    by (simp add: interp_ins_tail_unfold)
  moreover obtain xs ys where "interp_ins ops = xs @ [ref] @ ys"
    using assms(2) split_list_first by fastforce
  hence "insert_spec (interp_ins ops) (oid, Some ref) = xs @ [ref] @ [] @ [oid] @ ys"
    using assms(1) insert_after_ref interp_ins_distinct by fastforce
  ultimately show "list_order (ops @ [(oid, Some ref)]) ref oid"
    using assms(1) list_orderI by metis
qed

lemma list_order_insert_none:
  assumes "insert_ops (ops @ [(oid, None)])"
    and "x \<in> set (interp_ins ops)"
  shows "list_order (ops @ [(oid, None)]) oid x"
proof -
  have "interp_ins (ops @ [(oid, None)]) = insert_spec (interp_ins ops) (oid, None)"
    by (simp add: interp_ins_tail_unfold)
  moreover obtain xs ys where "interp_ins ops = xs @ [x] @ ys"
    using assms(2) split_list_first by fastforce
  hence "insert_spec (interp_ins ops) (oid, None) = [] @ [oid] @ xs @ [x] @ ys"
    by simp
  ultimately show "list_order (ops @ [(oid, None)]) oid x"
    using assms(1) list_orderI by metis
qed

lemma list_order_insert_between:
  assumes "insert_ops (ops @ [(oid, Some ref)])"
    and "list_order ops ref x"
  shows "list_order (ops @ [(oid, Some ref)]) oid x"
proof -
  have "interp_ins (ops @ [(oid, Some ref)]) = insert_spec (interp_ins ops) (oid, Some ref)"
    by (simp add: interp_ins_tail_unfold)
  moreover obtain xs ys zs where "interp_ins ops = xs @ [ref] @ ys @ [x] @ zs"
    using assms list_orderE by blast
  moreover have "... = xs @ ref # (ys @ [x] @ zs)"
    by simp
  moreover have "distinct (xs @ ref # (ys @ [x] @ zs))"
    using assms(1) calculation by (metis interp_ins_distinct insert_ops_rem_last)
  hence "insert_spec (xs @ ref # (ys @ [x] @ zs)) (oid, Some ref) = xs @ ref # oid # (ys @ [x] @ zs)"
    using assms(1) calculation by (simp add: insert_after_ref)
  moreover have "... = (xs @ [ref]) @ [oid] @ ys @ [x] @ zs"
    by simp
  ultimately show "list_order (ops @ [(oid, Some ref)]) oid x"
    using assms(1) list_orderI by metis
qed

inductive insert_seq :: "'oid option \<Rightarrow> ('oid \<times> 'oid option) list \<Rightarrow> bool" where
  "insert_seq start [(oid, start)]" |
  "\<lbrakk>insert_seq start (list @ [(prev, ref)])\<rbrakk>
      \<Longrightarrow> insert_seq start (list @ [(prev, ref), (oid, Some prev)])"

lemma insert_seq_nonempty:
  assumes "insert_seq start xs"
  shows "xs \<noteq> []"
using assms by (induction rule: insert_seq.induct, auto)

lemma insert_seq_hd:
  assumes "insert_seq start xs"
  shows "\<exists>oid. hd xs = (oid, start)"
using assms by (induction rule: insert_seq.induct, simp,
  metis append_self_conv2 hd_append2 list.sel(1))

lemma insert_seq_rem_last:
  assumes "insert_seq start (xs @ [x])"
    and "xs \<noteq> []"
  shows "insert_seq start xs"
using assms insert_seq.cases by fastforce

lemma insert_seq_butlast:
  assumes "insert_seq start xs"
    and "xs \<noteq> []" and "xs \<noteq> [last xs]"
  shows "insert_seq start (butlast xs)"
proof -
  have "length xs > 1"
    by (metis One_nat_def Suc_lessI add_0_left append_butlast_last_id append_eq_append_conv
        append_self_conv2 assms(2) assms(3) length_greater_0_conv list.size(3) list.size(4))
  hence "butlast xs \<noteq> []"
    by (metis length_butlast less_numeral_extra(3) list.size(3) zero_less_diff)
  then show "insert_seq start (butlast xs)"
    using assms by (metis append_butlast_last_id insert_seq_rem_last)
qed

lemma insert_seq_last_ref:
  assumes "insert_seq start (xs @ [(xi, xr), (yi, yr)])"
  shows "yr = Some xi"
using assms insert_seq.cases by fastforce

lemma insert_seq_ref_missing:
  assumes "insert_seq (Some r) xs"
    and "insert_ops ops" and "insert_ops xs"
    and "set xs \<subseteq> set ops"
    and "ops = as @ [hd xs] @ bs"
    and "r \<notin> set (interp_ins as)"
  shows "\<forall>x \<in> set (map fst xs). x \<notin> set (interp_ins ops)"
using assms proof(induction xs rule: List.rev_induct, simp)
  case snoc_x: (snoc x xs)
  then show "\<forall>x \<in> set (map fst (xs @ [x])). x \<notin> set (interp_ins ops)"
  proof(cases "xs = []")
    case True
    moreover from this have "fst x \<notin> set (interp_ins ops)"
      using interp_ins_ref_nonex insert_seq_hd snoc_x.prems by fastforce
    ultimately show "\<forall>x \<in> set (map fst (xs @ [x])). x \<notin> set (interp_ins ops)"
      by auto 
  next
    case xs_nonempty: False
    then obtain rest y where snoc_y: "xs = rest @ [y]"
      using append_butlast_last_id by metis
    obtain yi yr xi xr where yx_pairs: "y = (yi, yr) \<and> x = (xi, xr)"
      by force
    then have "xr = Some yi"
      using insert_seq_last_ref snoc_x.prems(1) snoc_y by force
    have IH: "\<forall>x \<in> set (map fst xs). x \<notin> set (interp_ins ops)"
    proof -
      have "insert_seq (Some r) xs"
        using snoc_x.prems(1) insert_seq_rem_last xs_nonempty by blast
      moreover have "insert_ops xs"
        using snoc_x.prems(3) insert_ops_rem_last by blast
      moreover have "set xs \<subseteq> set ops"
        using snoc_x.prems(4) by auto
      ultimately show ?thesis
        using snoc_x.IH snoc_x.prems snoc_y hd_append2 by blast
    qed
    moreover have "x \<in> set ops"
      using snoc_x.prems(4) by auto
    then obtain as bs where "ops = as @ x # bs"
      by (meson split_list)
    have "yi \<notin> set (interp_ins ops)"
      using IH by (simp add: yx_pairs snoc_y)
    hence "yi \<notin> set (interp_ins as)"
      using \<open>ops = as @ x # bs\<close> interp_ins_monotonic snoc_x.prems(2) by blast
    hence "xi \<notin> set (interp_ins ops)"
      using interp_ins_ref_nonex \<open>ops = as @ x # bs\<close> \<open>xr = Some yi\<close>
        append.simps(2) snoc_x.prems(2) yx_pairs by fastforce
    moreover have "set (map fst (xs @ [x])) = set (map fst xs) \<union> {xi}"
      using yx_pairs by auto
    ultimately show "\<forall>x \<in> set (map fst (xs @ [x])). x \<notin> set (interp_ins ops)"
      by simp
  qed
qed

(*lemma insert_seq_at_start:
  assumes "insert_ops (ops @ [(oid, start)])"
    and "insert_seq start xs" and "insert_ops xs"
    and "set xs \<subseteq> set ops"
    and "start = None \<or> (\<exists>r. start = Some r \<and> r \<in> set (interp_ins ops))"
  shows "\<forall>x \<in> set (map fst xs). list_order (ops @ [(oid, start)]) oid x"
using assms proof(induction xs rule: List.rev_induct, simp)
  case (snoc x xs)
  then have IH: "\<forall>i \<in> set (map fst xs). list_order (ops @ [(oid, start)]) oid i"
    by (metis append_is_Nil_conv insert_ops_rem_last insert_seq_rem_last le_sup_iff
        list.distinct(1) list.map_disc_iff set_append split_list_last)
  obtain as bs where x_split: "ops = as @ x # bs"
    using Un_insert_right snoc.prems(4) split_list by fastforce
  moreover have "list_order (ops @ [(oid, start)]) oid (fst x)"
  proof(cases "xs = []")
    case True
    then have "snd x = start"
      using snoc.prems(2) insert_seq_hd by fastforce
    hence "fst x \<in> set (interp_ins ops)"
    proof(cases start)
      case None
      hence "fst x \<in> set (interp_ins (as @ [x]))"
        by (metis \<open>snd x = start\<close> interp_ins_last_None prod.collapse)
      moreover have "ops = (as @ [x]) @ bs"
        using x_split by simp
      ultimately show ?thesis
        using snoc.prems(1) interp_ins_monotonic by blast
    next
      case (Some a)
      then show ?thesis sorry
    qed
    then show ?thesis
      sorry
  next
    case False
    then show ?thesis sorry
  qed
  ultimately show "\<forall>i \<in> set (map fst (xs @ [x])). list_order (ops @ [(oid, start)]) oid i"
    using IH by auto
qed*)

lemma insert_seq_start_none:
  assumes "insert_ops ops"
    and "insert_seq None xs" and "insert_ops xs"
    and "set xs \<subseteq> set ops"
  shows "\<forall>i \<in> set (map fst xs). i \<in> set (interp_ins ops)"
using assms proof(induction xs rule: List.rev_induct, simp)
  case (snoc x xs)
  then have IH: "\<forall>i \<in> set (map fst xs). i \<in> set (interp_ins ops)"
    by (metis Nil_is_map_conv append_is_Nil_conv insert_ops_appendD insert_seq_rem_last
        le_supE list.simps(3) set_append split_list)
  then show "\<forall>i \<in> set (map fst (xs @ [x])). i \<in> set (interp_ins ops)"
  proof(cases "xs = []")
    case True
    then obtain oid where "xs @ [x] = [(oid, None)]"
      using insert_seq_hd snoc.prems(2) by fastforce
    hence "(oid, None) \<in> set ops"
      using snoc.prems(4) by auto
    then obtain as bs where "ops = as @ (oid, None) # bs"
      by (meson split_list)
    hence "ops = (as @ [(oid, None)]) @ bs"
      by (simp add: \<open>ops = as @ (oid, None) # bs\<close>)
    moreover have "oid \<in> set (interp_ins (as @ [(oid, None)]))"
      by (simp add: interp_ins_last_None)
    ultimately have "oid \<in> set (interp_ins ops)"
      using interp_ins_monotonic snoc.prems(1) by blast
    then show "\<forall>i \<in> set (map fst (xs @ [x])). i \<in> set (interp_ins ops)" 
      using \<open>xs @ [x] = [(oid, None)]\<close> by auto
  next
    case False
    then obtain rest y where snoc_y: "xs = rest @ [y]"
      using append_butlast_last_id by metis
    obtain yi yr xi xr where yx_pairs: "y = (yi, yr) \<and> x = (xi, xr)"
      by force
    then have "xr = Some yi"
      using insert_seq_last_ref snoc.prems(2) snoc_y by fastforce
    have "yi < xi"
      using insert_ops_sorted_oids snoc_y yx_pairs snoc.prems(3)
      by (metis (no_types, lifting) append_eq_append_conv2)
    have "(yi, yr) \<in> set ops" and "(xi, Some yi) \<in> set ops"
      using snoc.prems(4) snoc_y yx_pairs \<open>xr = Some yi\<close> by auto
    then obtain as bs cs where ops_split: "ops = as @ [(yi, yr)] @ bs @ [(xi, Some yi)] @ cs"
      using insert_ops_split_2 \<open>yi < xi\<close> snoc.prems(1) by blast
    hence "yi \<in> set (interp_ins (as @ [(yi, yr)] @ bs))"
    proof -
      have "yi \<in> set (interp_ins ops)"
        by (simp add: IH snoc_y yx_pairs)
      moreover have "ops = (as @ [(yi, yr)] @ bs) @ ([(xi, Some yi)] @ cs)"
        using ops_split by simp
      moreover have "yi \<in> set (map fst (as @ [(yi, yr)] @ bs))"
        by simp
      ultimately show ?thesis
        using snoc.prems(1) interp_ins_append_forward by blast
    qed
    hence "xi \<in> set (interp_ins ((as @ [(yi, yr)] @ bs) @ [(xi, Some yi)] @ cs))"
      using snoc.prems(1) interp_ins_append_memb ops_split by force
    hence "xi \<in> set (interp_ins ops)"
      by (simp add: ops_split)
    then show "\<forall>i \<in> set (map fst (xs @ [x])). i \<in> set (interp_ins ops)"
      using IH yx_pairs by auto
  qed
qed

lemma insert_seq_after_start:
  assumes "insert_ops ops"
    and "insert_seq (Some ref) xs" and "insert_ops xs"
    and "set xs \<subseteq> set ops"
    and "ref \<in> set (interp_ins ops)"
  shows "\<forall>i \<in> set (map fst xs). list_order ops ref i"
using assms proof(induction xs rule: List.rev_induct, simp)
  case (snoc x xs)
  have IH: "\<forall>i \<in> set (map fst xs). list_order ops ref i"
    using snoc.IH snoc.prems insert_seq_rem_last insert_ops_appendD
    by (metis Nil_is_map_conv Un_subset_iff empty_set equals0D set_append)
  moreover have "list_order ops ref (fst x)"
  proof(cases "xs = []")
    case True
    hence "snd x = Some ref"
      using insert_seq_hd snoc.prems(2) by fastforce
    moreover have "x \<in> set ops"
      using snoc.prems(4) by auto
    then obtain cs ds where x_split: "ops = cs @ x # ds"
      by (meson split_list)
    have "list_order (cs @ [(fst x, Some ref)]) ref (fst x)"
    proof -
      have "insert_ops (cs @ [(fst x, Some ref)] @ ds)"
        using x_split \<open>snd x = Some ref\<close>
        by (metis append_Cons append_self_conv2 prod.collapse snoc.prems(1))
      moreover from this obtain rr where "(ref, rr) \<in> set cs"
        using interp_ins_find_ref x_split \<open>snd x = Some ref\<close> assms(5)
        by (metis (no_types, lifting) append_Cons append_self_conv2 prod.collapse)
      hence "ref \<in> set (interp_ins cs)"
      proof -
        have "ops = cs @ ([(fst x, Some ref)] @ ds)"
          by (metis x_split \<open>snd x = Some ref\<close> append_Cons append_self_conv2 prod.collapse)
        thus "ref \<in> set (interp_ins cs)"
          using assms(5) calculation interp_ins_append_forward interp_ins_append_non_memb by blast
      qed
      ultimately show "list_order (cs @ [(fst x, Some ref)]) ref (fst x)"
        using list_order_insert_ref by (metis append.assoc insert_ops_appendD)
    qed
    moreover have "ops = (cs @ [(fst x, Some ref)]) @ ds"
      using calculation x_split
      by (metis append_eq_Cons_conv append_eq_append_conv2 append_self_conv2 prod.collapse)
    ultimately show "list_order ops ref (fst x)"
      using list_order_append snoc.prems(1) by blast
  next
    case False
    then obtain rest y where snoc_y: "xs = rest @ [y]"
      using append_butlast_last_id by metis
    obtain yi yr xi xr where yx_pairs: "y = (yi, yr) \<and> x = (xi, xr)"
      by force
    then have "xr = Some yi"
      using insert_seq_last_ref snoc.prems(2) snoc_y by fastforce
    have "yi < xi"
      using insert_ops_sorted_oids snoc_y yx_pairs snoc.prems(3)
      by (metis (no_types, lifting) append_eq_append_conv2)
    have "(yi, yr) \<in> set ops" and "(xi, Some yi) \<in> set ops"
      using snoc.prems(4) snoc_y yx_pairs \<open>xr = Some yi\<close> by auto
    then obtain as bs cs where ops_split: "ops = as @ [(yi, yr)] @ bs @ [(xi, Some yi)] @ cs"
      using insert_ops_split_2 \<open>yi < xi\<close> snoc.prems(1) by blast
    have "list_order ops ref yi"
      by (simp add: IH snoc_y yx_pairs)
    moreover have "list_order (as @ [(yi, yr)] @ bs @ [(xi, Some yi)]) yi xi"
    proof -
      have "insert_ops ((as @ [(yi, yr)] @ bs @ [(xi, Some yi)]) @ cs)"
        using ops_split snoc.prems(1) by auto
      hence "insert_ops ((as @ [(yi, yr)] @ bs) @ [(xi, Some yi)])"
        using insert_ops_appendD by fastforce
      moreover have "yi \<in> set (interp_ins ops)"
        using \<open>list_order ops ref yi\<close> list_order_memb2 by auto
      hence "yi \<in> set (interp_ins (as @ [(yi, yr)] @ bs))"
        using interp_ins_append_non_memb ops_split snoc.prems(1) by force
      ultimately show ?thesis
        using list_order_insert_ref by force
    qed
    hence "list_order ops yi xi"
      by (metis append_assoc list_order_append ops_split snoc.prems(1))
    ultimately show "list_order ops ref (fst x)"
      using list_order_trans snoc.prems(1) yx_pairs by auto
  qed
  ultimately show "\<forall>i \<in> set (map fst (xs @ [x])). list_order ops ref i"
    by auto
qed

(*lemma insert_seq_no_start:
  assumes "insert_ops ops"
    and "insert_seq (Some ref) xs" and "insert_ops xs"
    and "set xs \<subseteq> set ops"
    and "ref \<notin> set (interp_ins ops)"
  shows "\<forall>i \<in> set (map fst xs). i \<notin> set (interp_ins ops)"
using assms proof(induction xs rule: List.rev_induct, simp)
  case (snoc x xs)
  have IH: "\<forall>i \<in> set (map fst xs). i \<notin> set (interp_ins ops)"
    using snoc.IH snoc.prems insert_seq_rem_last insert_ops_appendD
    by (metis append_is_Nil_conv le_sup_iff list.map_disc_iff set_append split_list_first)
  moreover have "fst x \<notin> set (interp_ins ops)"
    sorry
  ultimately show "\<forall>i \<in> set (map fst (xs @ [x])). i \<notin> set (interp_ins ops)"
    by auto
qed*)


(*lemma insert_seq_after_start:
  assumes "insert_ops ops"
    and "insert_seq (Some ref) xs" and "insert_ops xs"
    and "set xs \<subseteq> set ops"
  shows "(\<forall>i \<in> set (map fst xs). list_order ops ref i) \<or>
         (\<forall>i \<in> set (map fst xs). i \<notin> set (interp_ins ops))"
proof -
  have "hd xs \<in> set ops"
    using assms(2) assms(4) hd_in_set insert_seq_nonempty by blast
  then obtain as bs where "ops = as @ (hd xs) # bs"
    by (meson split_list)
  show ?thesis
  proof(cases "ref \<in> set (interp_ins ops)")
    case ref_exist: True
    have "\<forall>i \<in> set (map fst xs). list_order ops ref i"
      using assms proof(induction xs rule: List.rev_induct, simp)
      case (snoc x xs)
      have IH: "\<forall>i \<in> set (map fst xs). list_order ops ref i"
        using snoc.IH snoc.prems insert_seq_rem_last insert_ops_appendD
        by (metis Nil_is_map_conv Un_subset_iff empty_set equals0D set_append)
      moreover have "list_order ops ref (fst x)"
      proof(cases "xs = []")
        case True
        hence "snd x = Some ref"
          using insert_seq_hd snoc.prems(2) by fastforce
        have "x \<in> set ops"
          using snoc.prems(4) by auto
        then obtain cs ds where "ops = cs @ x # ds"
          by (meson split_list)
        hence "insert_ops (cs @ [(fst x, Some ref)] @ ds)"
          by (metis \<open>snd x = Some ref\<close> append_Cons append_self_conv2 prod.collapse snoc.prems(1))
        then obtain rr where "(ref, rr) \<in> set cs"
          using interp_ins_find_ref \<open>ops = cs @ x # ds\<close> \<open>snd x = Some ref\<close> ref_exist
          by (metis (no_types, lifting) append_Cons append_self_conv2 prod.collapse)
        hence "ref \<in> set (interp_ins cs)"
          (* why not use interp_ins_append_forward? *)
          using interp_ins_append_non_memb \<open>ops = cs @ x # ds\<close> \<open>snd x = Some ref\<close>
          by (metis append_Cons prod.collapse ref_exist self_append_conv2 snoc.prems(1))
        hence "list_order (cs @ [(fst x, Some ref)]) ref (fst x)"
          using list_order_insert_ref \<open>insert_ops (cs @ [(fst x, Some ref)] @ ds)\<close>
          by (metis append.assoc insert_ops_appendD)
        moreover have "ops = (cs @ [(fst x, Some ref)]) @ ds"
          by (metis \<open>ops = cs @ x # ds\<close> \<open>snd x = Some ref\<close> append_eq_Cons_conv append_eq_append_conv2 append_self_conv2 prod.collapse)
        ultimately show "list_order ops ref (fst x)"
          using list_order_append snoc.prems(1) by blast
      next
        case False
        then show ?thesis sorry
      qed
      ultimately show "\<forall>i \<in> set (map fst (xs @ [x])). list_order ops ref i"
        by auto
    qed
    then show ?thesis by blast
  next
    case ref_nexist: False
    have "\<forall>i \<in> set (map fst xs). i \<notin> set (interp_ins ops)"
      using assms proof(induction xs rule: List.rev_induct, simp)
      case (snoc x xs)
      have IH: "\<forall>i \<in> set (map fst xs). i \<notin> set (interp_ins ops)"
        using snoc.IH snoc.prems insert_seq_rem_last insert_ops_appendD
        by (metis append_is_Nil_conv le_sup_iff list.map_disc_iff set_append split_list_first)
      moreover have "fst x \<notin> set (interp_ins ops)"
        sorry
      ultimately show "\<forall>i \<in> set (map fst (xs @ [x])). i \<notin> set (interp_ins ops)"
        by auto
    qed
    then show ?thesis by blast
  qed
qed*)


lemma insert_ops_hd_less:
  assumes "insert_ops ((id1, ref1) # (id2, ref2) # ops)"
  shows "id1 < id2"
using assms by (auto simp add: insert_ops_def spec_ops_def)

lemma insert_ops_subset_last:
  assumes "insert_ops (xs @ [x])"
    and "insert_ops ys"
    and "set ys \<subseteq> set (xs @ [x])"
    and "x \<in> set ys"
  shows "x = last ys"
using assms proof(induction ys, simp)
  case (Cons y ys)
  then show "x = last (y # ys)"
  proof(cases "ys = []")
    case True
    then show "x = last (y # ys)"
      using Cons.prems(4) by auto
  next
    case ys_nonempty: False
    have "x \<noteq> y"
    proof -
      obtain mid l where "ys = mid @ [l]"
        using append_butlast_last_id ys_nonempty by metis
      moreover obtain li lr where "l = (li, lr)"
        by force
      moreover have "\<And>i. i \<in> set (map fst (y # mid)) \<Longrightarrow> i < li"
        by (metis last_op_greatest Cons.prems(2) calculation append_Cons)
      hence "fst y < li"
        by simp
      moreover have "\<And>i. i \<in> set (map fst xs) \<Longrightarrow> i < fst x"
        using assms(1) last_op_greatest by (metis prod.collapse)
      hence "\<And>i. i \<in> set (map fst (y # ys)) \<Longrightarrow> i \<le> fst x"
        using Cons.prems(3) by fastforce
      ultimately show "x \<noteq> y"
        by fastforce
    qed
    then show "x = last (y # ys)"
      using Cons.IH Cons.prems insert_ops_rem_cons ys_nonempty
      by (metis dual_order.trans last_ConsR set_ConsD set_subset_Cons)
  qed
qed

lemma subset_butlast:
  assumes "set xs \<subseteq> set (ys @ [y])"
    and "last xs = y"
    and "distinct xs"
  shows "set (butlast xs) \<subseteq> set ys"
using assms by (induction xs, auto)

lemma distinct_append_butlast1:
  assumes "distinct (map fst xs @ map fst ys)"
  shows "distinct (map fst (butlast xs) @ map fst ys)"
using assms proof(induction xs, simp)
  case (Cons a xs)
  have "fst a \<notin> set (map fst xs @ map fst ys)"
    using Cons.prems by auto
  moreover have "set (map fst (butlast xs)) \<subseteq> set (map fst xs)"
    by (metis in_set_butlastD map_butlast subsetI)
  hence "set (map fst (butlast xs) @ map fst ys) \<subseteq> set (map fst xs @ map fst ys)"
    by auto
  ultimately have "fst a \<notin> set (map fst (butlast xs) @ map fst ys)"
    by blast
  then show "distinct (map fst (butlast (a # xs)) @ map fst ys)"
    using Cons.IH Cons.prems by auto
qed

lemma distinct_append_butlast2:
  assumes "distinct (map fst xs @ map fst ys)"
  shows "distinct (map fst xs @ map fst (butlast ys))"
using assms proof(induction xs)
  case Nil
  then show "distinct (map fst [] @ map fst (butlast ys))"
    by (simp add: distinct_butlast map_butlast)
next
  case (Cons a xs)
  have "fst a \<notin> set (map fst xs @ map fst ys)"
    using Cons.prems by auto
  moreover have "set (map fst (butlast ys)) \<subseteq> set (map fst ys)"
    by (metis in_set_butlastD map_butlast subsetI)
  hence "set (map fst xs @ map fst (butlast ys)) \<subseteq> set (map fst xs @ map fst ys)"
    by auto
  ultimately have "fst a \<notin> set (map fst xs @ map fst (butlast ys))"
    by blast
  then show ?case
    using Cons.IH Cons.prems by auto
qed

(*theorem no_interleaving_general:
  assumes "insert_ops ops"
    and "insert_seq start xs" and "insert_ops xs"
    and "insert_seq start ys" and "insert_ops ys"
    and "set xs \<subseteq> set ops" and "set ys \<subseteq> set ops"
    and "distinct (map fst xs @ map fst ys)"
  shows "(((\<forall>x \<in> set (map fst xs). \<forall>y \<in> set (map fst ys). list_order ops x y) \<or>
           (\<forall>x \<in> set (map fst xs). \<forall>y \<in> set (map fst ys). list_order ops y x)) \<and>
          (\<forall>r. start = Some r \<longrightarrow> (\<forall>x \<in> set (map fst xs). list_order ops r x) \<and>
                                  (\<forall>y \<in> set (map fst ys). list_order ops r y))) \<or>
         (\<forall>x \<in> set (map fst xs) \<union> set (map fst ys). x \<notin> set (interp_ins ops))"
using assms proof(induction ops arbitrary: xs ys rule: List.rev_induct, simp)
  case (snoc a ops)
  then have "insert_ops ops"
    by blast
  consider (a_in_xs) "a \<in> set xs" | (a_in_ys) "a \<in> set ys" | (neither) "a \<notin> set xs \<and> a \<notin> set ys"
    by blast
  then show ?case
  proof(cases)
    case a_in_xs
    then have "a \<notin> set ys"
      using snoc.prems(8) by auto
    hence "set ys \<subseteq> set ops"
      using snoc.prems(7) DiffE by auto
    from a_in_xs have "a = last xs"
      using insert_ops_subset_last snoc.prems by blast
    have IH: "(((\<forall>x \<in> set (map fst (butlast xs)). \<forall>y \<in> set (map fst ys). list_order ops x y) \<or>
                (\<forall>x \<in> set (map fst (butlast xs)). \<forall>y \<in> set (map fst ys). list_order ops y x)) \<and>
               (\<forall>r. start = Some r \<longrightarrow> (\<forall>x \<in> set (map fst (butlast xs)). list_order ops r x) \<and>
                                       (\<forall>y \<in> set (map fst ys).           list_order ops r y))) \<or>
              (\<forall>x \<in> set (map fst (butlast xs)) \<union> set (map fst ys). x \<notin> set (interp_ins ops))"
    proof(cases "xs = [a]")
      case True
      moreover have "(\<forall>r. start = Some r \<longrightarrow> (\<forall>y \<in> set (map fst ys). list_order ops r y)) \<or>
            (\<forall>y \<in> set (map fst ys). y \<notin> set (interp_ins ops))"
        using insert_seq_after_start insert_seq_no_start \<open>insert_ops ops\<close> \<open>set ys \<subseteq> set ops\<close>
          snoc.prems(4) snoc.prems(5) by blast
      ultimately show ?thesis by auto
    next
      case xs_longer: False
      from \<open>a = last xs\<close> have "set (butlast xs) \<subseteq> set ops"
        using distinct_fst snoc.prems subset_butlast by fastforce
      moreover have "insert_seq start (butlast xs)"
        using insert_seq_butlast insert_seq_nonempty xs_longer \<open>a = last xs\<close> snoc.prems(2) by blast
      moreover have "insert_ops (butlast xs)"
        by (metis append_butlast_last_id insert_ops_appendD insert_seq_nonempty
            snoc.prems(2) snoc.prems(3))
      moreover have "distinct (map fst (butlast xs) @ map fst ys)"
        using distinct_append_butlast1 snoc.prems(8) by blast
      moreover have "set ys \<subseteq> set ops"
        using \<open>a \<notin> set ys\<close> DiffE snoc.prems(7) by auto
      ultimately show ?thesis
        using \<open>insert_ops ops\<close> snoc.IH snoc.prems(4) snoc.prems(5) by auto
    qed
    consider
      (x_first) "(\<forall>x \<in> set (map fst (butlast xs)). \<forall>y \<in> set (map fst ys). list_order ops x y) \<and>
                 (\<forall>r. start = Some r \<longrightarrow> (\<forall>x \<in> set (map fst (butlast xs)). list_order ops r x) \<and>
                                         (\<forall>y \<in> set (map fst ys).           list_order ops r y))" |
      (y_first) "(\<forall>x \<in> set (map fst (butlast xs)). \<forall>y \<in> set (map fst ys). list_order ops y x) \<and>
                 (\<forall>r. start = Some r \<longrightarrow> (\<forall>x \<in> set (map fst (butlast xs)). list_order ops r x) \<and>
                                         (\<forall>y \<in> set (map fst ys).           list_order ops r y))" |
      (neither) "\<forall>x \<in> set (map fst (butlast xs)) \<union> set (map fst ys). x \<notin> set (interp_ins ops)"
      using IH by blast
    then show ?thesis
    proof(cases)
      case x_first
      moreover have y_exists: "\<forall>y \<in> set (map fst ys). y \<in> set (interp_ins ops)"
      proof(cases start)
        case None
        then show ?thesis
          using insert_seq_start_none \<open>insert_ops ops\<close> \<open>set ys \<subseteq> set ops\<close> snoc.prems by blast
      next
        case (Some r)
        then show ?thesis
          using list_order_memb2 x_first by blast
      qed
      moreover have "\<forall>y \<in> set (map fst ys). list_order (ops @ [a]) (fst a) y"
      proof(cases "xs = [a]")
        case True
        then have "snd a = start"
          using snoc.prems(2) insert_seq_hd by force
        then show "\<forall>y \<in> set (map fst ys). list_order (ops @ [a]) (fst a) y"
        proof(cases start)
          case None
          then show ?thesis
            using list_order_insert_none snoc.prems(1)
            by (metis y_exists \<open>snd a = start\<close> prod.collapse)
        next
          case (Some r)
          then show ?thesis
            using list_order_insert_between snoc.prems(1)
            by (metis x_first \<open>snd a = start\<close> prod.collapse)
        qed
      next
        case xs_longer: False
        hence "butlast xs = (butlast (butlast xs)) @ [last (butlast xs)]"
          using \<open>a = last xs\<close> insert_seq_butlast insert_seq_nonempty snoc.prems(2) by fastforce
        moreover from this have "xs = (butlast (butlast xs)) @ [last (butlast xs), a]"
          by (metis \<open>a = last xs\<close> append.assoc append_butlast_last_id butlast.simps(2)
              insert_seq_nonempty last_ConsL last_ConsR list.simps(3) snoc.prems(2))
        hence "snd a = Some (fst (last (butlast xs)))"
          using snoc.prems(2) insert_seq_last_ref by (metis prod.collapse)
        moreover have "\<forall>y \<in> set (map fst ys). list_order ops (fst (last (butlast xs))) y"
          using x_first calculation by (metis last_in_set last_map map_is_Nil_conv snoc_eq_iff_butlast)
        ultimately show "\<forall>y \<in> set (map fst ys). list_order (ops @ [a]) (fst a) y"
          using snoc.prems(1) list_order_insert_between by (metis prod.collapse)
      qed
      moreover have map_fst_xs: "map fst xs = map fst (butlast xs) @ map fst [last xs]"
        by (metis append_butlast_last_id insert_seq_nonempty map_append snoc.prems(2))
      hence "set (map fst xs) = set (map fst (butlast xs)) \<union> {fst a}"
        by (simp add: \<open>a = last xs\<close>)
      moreover have "\<forall>r. start = Some r \<longrightarrow> list_order (ops @ [a]) r (fst a)"
      proof(cases start, simp)
        case (Some r)
        moreover have "r \<in> set (interp_ins (ops @ [a]))"
          using list_order_memb1 x_first snoc.prems(1) snoc.prems(4) interp_ins_monotonic
          by (metis calculation insert_seq_nonempty last_in_set list.map_disc_iff)
        ultimately show ?thesis
          using snoc.prems by (simp add: insert_seq_after_start \<open>a = last xs\<close> map_fst_xs)
      qed
      ultimately have "(\<forall>x \<in> set (map fst xs). \<forall>y \<in> set (map fst ys). list_order (ops @ [a]) x y) \<and>
          (\<forall>r. start = Some r \<longrightarrow> (\<forall>x \<in> set (map fst xs). list_order (ops @ [a]) r x) \<and>
                                  (\<forall>y \<in> set (map fst ys). list_order (ops @ [a]) r y))"
        using snoc.prems(1) by (simp add: list_order_append)
      then show ?thesis by blast
    next
      case y_first
      moreover have y_exists: "\<forall>y \<in> set (map fst ys). y \<in> set (interp_ins ops)"
      proof(cases start)
        case None
        then show ?thesis
          using insert_seq_start_none \<open>insert_ops ops\<close> \<open>set ys \<subseteq> set ops\<close> snoc.prems by blast
      next
        case (Some r)
        then show ?thesis
          using list_order_memb2 y_first by blast
      qed
      moreover have "\<forall>y \<in> set (map fst ys). list_order (ops @ [a]) y (fst a)"
      proof(cases "xs = [a]")
        case True
        then have "snd a = start"
          using snoc.prems(2) insert_seq_hd by force
        then show "\<forall>y \<in> set (map fst ys). list_order (ops @ [a]) y (fst a)"
        proof(cases "ys", simp)
          case (Cons y ysa)
          then show ?thesis sorry
        qed
          
      next
        case xs_longer: False
        hence "butlast xs = (butlast (butlast xs)) @ [last (butlast xs)]"
          using \<open>a = last xs\<close> insert_seq_butlast insert_seq_nonempty snoc.prems(2) by fastforce
        moreover from this have "xs = (butlast (butlast xs)) @ [last (butlast xs), a]"
          by (metis \<open>a = last xs\<close> append.assoc append_butlast_last_id butlast.simps(2)
              insert_seq_nonempty last_ConsL last_ConsR list.simps(3) snoc.prems(2))
        hence "snd a = Some (fst (last (butlast xs)))"
          using snoc.prems(2) insert_seq_last_ref by (metis prod.collapse)
        moreover have "\<forall>y \<in> set (map fst ys). list_order ops y (fst (last (butlast xs)))"
          using y_first calculation by (metis last_in_set last_map map_is_Nil_conv snoc_eq_iff_butlast)
        ultimately show "\<forall>y \<in> set (map fst ys). list_order (ops @ [a]) y (fst a)"
          using snoc.prems(1) list_order_insert_between sorry
      qed
      moreover have map_fst_xs: "map fst xs = map fst (butlast xs) @ map fst [last xs]"
        by (metis append_butlast_last_id insert_seq_nonempty map_append snoc.prems(2))
      hence "set (map fst xs) = set (map fst (butlast xs)) \<union> {fst a}"
        by (simp add: \<open>a = last xs\<close>)
      moreover have "\<forall>r. start = Some r \<longrightarrow> list_order (ops @ [a]) r (fst a)"
      proof(cases start, simp)
        case (Some r)
        moreover have "r \<in> set (interp_ins (ops @ [a]))"
          using list_order_memb1 y_first snoc.prems(1) snoc.prems(4) interp_ins_monotonic
          by (metis calculation insert_seq_nonempty last_in_set list.map_disc_iff)
        ultimately show ?thesis
          using snoc.prems by (simp add: insert_seq_after_start \<open>a = last xs\<close> map_fst_xs)
      qed
      ultimately have "(\<forall>x \<in> set (map fst xs). \<forall>y \<in> set (map fst ys). list_order (ops @ [a]) y x) \<and>
          (\<forall>r. start = Some r \<longrightarrow> (\<forall>x \<in> set (map fst xs). list_order (ops @ [a]) r x) \<and>
                                  (\<forall>y \<in> set (map fst ys). list_order (ops @ [a]) r y))"
        using snoc.prems(1) by (simp add: list_order_append)
      then show ?thesis by blast
    next
      case neither
      have "\<forall>x \<in> set (map fst xs) \<union> set (map fst ys). x \<notin> set (interp_ins (ops @ [a]))"
        sorry
      then show ?thesis sorry
    qed
  next
    case a_in_ys
    then have "a \<notin> set xs"
      using snoc.prems(8) by auto
    hence "set xs \<subseteq> set ops"
      using snoc.prems(6) DiffE by auto
    from a_in_ys have "a = last ys"
      using insert_ops_subset_last snoc.prems by blast
    have IH: "(\<forall>x \<in> set (map fst xs). \<forall>y \<in> set (map fst (butlast ys)). list_order ops x y) \<or>
              (\<forall>x \<in> set (map fst xs). \<forall>y \<in> set (map fst (butlast ys)). list_order ops y x) \<or>
              (\<forall>x \<in> set (map fst xs) \<union> set (map fst (butlast ys)). x \<notin> set (interp_ins ops))"
    proof(cases "ys = [a]")
      case True
      then show ?thesis by simp
    next
      case ys_longer: False
      from a_in_ys have "a = last ys"
        using insert_ops_subset_last snoc.prems by blast
      hence "set (butlast ys) \<subseteq> set ops"
        using snoc.prems by (simp add: distinct_fst subset_butlast)
      moreover have "insert_seq start (butlast ys)"
        using insert_seq_butlast insert_seq_nonempty ys_longer \<open>a = last ys\<close> snoc.prems(4) by blast
      moreover have "insert_ops (butlast ys)"
        by (metis append_butlast_last_id insert_ops_appendD insert_seq_nonempty
            snoc.prems(4) snoc.prems(5))
      moreover have "distinct (map fst xs @ map fst (butlast ys))"
        using distinct_append_butlast2 snoc.prems(8) by blast
      moreover have "set xs \<subseteq> set ops"
        using \<open>a \<notin> set xs\<close> DiffE snoc.prems(6) by auto
      ultimately show ?thesis
        using \<open>insert_ops ops\<close> snoc.IH snoc.prems(2) snoc.prems(3) by auto
    qed
    then show ?thesis sorry
  next
    case neither
    then show ?thesis sorry
  qed
qed*)
(*
  obtain x1 y1 where x1_def: "(x1, start) = hd xs" and y1_def: "(y1, start) = hd ys"
    by (metis insert_seq_hd snoc.prems(2) snoc.prems(4))
  hence x1_memb: "x1 \<in> set (map fst xs)" and y1_memb: "y1 \<in> set (map fst ys)"
    using insert_seq_nonempty snoc.prems(2) snoc.prems(4)
    by (metis fst_conv hd_map list.set_sel(1) map_is_Nil_conv)+
  hence "x1 \<noteq> y1"
    using snoc.prems(8) by auto
  have oid_greatest: "\<And>i. i \<in> set (map fst ops) \<Longrightarrow> i < oid"
    using snoc.prems(1) a_pair last_op_greatest by blast
  then show ?case
  proof(cases "x1 < y1")
    case True
    consider (before_y1) "oid < y1" | (is_y1) "oid = y1" | (after_y1) "y1 < oid"
      using linorder_cases by blast
    then show ?thesis
    proof(cases)
      case before_y1
      moreover from this have "y1 < oid"
        using y1_memb oid_greatest snoc.prems(7) a_pair hd_in_set by fastforce
      ultimately show ?thesis
        by force
    next
      case is_y1
      then have "(x1, start) \<in> set (ops @ [a])"
        using snoc.prems(2) snoc.prems(6) x1_def insert_seq_nonempty list.set_sel(1) by auto
      hence "(x1, start) \<in> set ops"
        by (simp add: \<open>x1 \<noteq> y1\<close> a_pair is_y1)
      then obtain as bs where "ops = as @ [(x1, start)] @ bs"
        using insert_ops_split snoc.prems(1) by blast
      consider (ref_missing) "\<exists>r. start = Some r \<and> r \<notin> set (interp_ins as)"
        | (ref_exists) "start = None \<or> (\<exists>r. start = Some r \<and> r \<in> set (interp_ins as))"
        by fastforce
      then show ?thesis
      proof(cases)
        case ref_missing
        then obtain r where "start = Some r"
          by force
        then have "\<forall>x \<in> set (map fst xs). x \<notin> set (interp_ins ops)"
        proof -
          have "insert_seq (Some r) xs"
            using snoc.prems(2) \<open>start = Some r\<close> by blast
          moreover have "insert_ops xs"
            by (simp add: snoc.prems(3))
          moreover have "ops = as @ [hd xs] @ bs"
            by (simp add: \<open>ops = as @ [(x1, start)] @ bs\<close> x1_def)
          moreover have "r \<notin> set (interp_ins as)"
            using \<open>start = Some r\<close> ref_missing by blast
          ultimately show ?thesis
            using insert_seq_ref_missing sorry
        qed
        then show ?thesis sorry
      next
        case ref_exists
        then show ?thesis sorry
      qed
    next
      case after_y1
      then show ?thesis sorry
    qed
  next
    case False
    then have "y1 < x1"
      using \<open>x1 \<noteq> y1\<close> by auto
    consider (before_x1) "oid < x1" | (is_x1) "oid = x1" | (after_x1) "x1 < oid"
      using linorder_cases by blast
    then show ?thesis
    proof(cases)
      case before_x1
      moreover from this have "x1 < oid"
        using x1_memb oid_greatest snoc.prems(6) a_pair hd_in_set by fastforce
      ultimately show ?thesis
        by force
    next
      case is_x1
      then show ?thesis sorry
    next
      case after_x1
      then show ?thesis sorry
    qed
  qed
qed *)

theorem no_interleaving:
  assumes "insert_ops ops"
    and "(xid, ref) \<in> set ops"
    and "(yid, Some xid) \<in> set ops"
    and "(zid, ref) \<in> set ops"
    and "xid \<noteq> yid" and "yid \<noteq> zid" and "zid \<noteq> xid"
  shows "(list_order ops xid yid \<and> list_order ops yid zid) \<or>
         (list_order ops zid xid \<and> list_order ops xid yid) \<or>
         (xid \<notin> set (interp_ins ops) \<and> yid \<notin> set (interp_ins ops) \<and>
          zid \<notin> set (interp_ins ops))"
proof(cases "xid < zid")
  case True
  then show ?thesis
  proof(cases "yid < zid")
    case True
    have "xid < yid"
      using assms insert_ops_memb_ref_older by blast
    then obtain as bs cs ds
      where split: "ops = as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs @ [(zid, ref)] @ ds"
      using assms \<open>yid < zid\<close> insert_ops_split_3 by blast
    then show ?thesis
    proof(cases ref)
      case None
      hence "xid \<in> set (interp_ins (as @ [(xid, ref)]))"
        using interp_ins_last_None assms(1) split by metis
      hence xid_in: "xid \<in> set (interp_ins (as @ [(xid, ref)] @ bs))"
        using interp_ins_monotonic assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order (as @ [(xid, ref)] @ bs @ [(yid, Some xid)]) xid yid"
        using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order ops xid yid"
        using list_order_append assms(1) split append.assoc by metis
      moreover have "xid \<in> set (interp_ins (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs))"
        using interp_ins_monotonic xid_in assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs @ [(zid, ref)]) zid xid"
        using list_order_insert_none assms(1) insert_ops_appendD split append.assoc None by metis
      hence "list_order ops zid xid"
        using list_order_append assms(1) split append.assoc by metis
      ultimately show ?thesis by blast
    next
      case (Some r)
      then show ?thesis
      proof(cases "r \<in> set (interp_ins as)")
        case True
        hence r_xid: "list_order (as @ [(xid, ref)]) r xid"
          using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc Some by metis
        hence "xid \<in> set (interp_ins (as @ [(xid, ref)]))"
          using list_order_memb2 assms(1) split by metis
        hence xid_in: "xid \<in> set (interp_ins (as @ [(xid, ref)] @ bs))"
          using interp_ins_monotonic assms(1) insert_ops_appendD split append.assoc by metis
        hence "list_order (as @ [(xid, ref)] @ bs @ [(yid, Some xid)]) xid yid"
          using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc by metis
        hence "list_order ops xid yid"
          using list_order_append assms(1) split append.assoc by metis
        moreover have "list_order (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs) r xid"
          using list_order_append r_xid assms(1) insert_ops_appendD split append.assoc by metis
        hence "list_order (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs @ [(zid, ref)]) zid xid"
          using list_order_insert_between assms(1) insert_ops_appendD split append.assoc Some by metis
        hence "list_order ops zid xid"
          using list_order_append assms(1) split append.assoc by metis
        ultimately show ?thesis by blast
      next
        case False
        hence "xid \<notin> set (interp_ins ops)"
          using interp_ins_ref_nonex assms(1) split Some by metis
        moreover have "xid \<notin> set (interp_ins (as @ [(xid, ref)] @ bs))"
          using interp_ins_ref_nonex assms(1) insert_ops_appendD split append.assoc Some False by metis
        hence "yid \<notin> set (interp_ins ops)"
          using interp_ins_ref_nonex assms(1) split append.assoc by metis
        moreover have "r \<notin> set (interp_ins (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs))"
          using interp_ins_append_non_memb assms(1) insert_ops_appendD split append.assoc Some False by metis
        hence "zid \<notin> set (interp_ins ops)"
          using interp_ins_ref_nonex assms(1) split append.assoc Some by metis
        ultimately show ?thesis by blast
      qed
    qed
  next
    case False
    hence "zid < yid"
      using assms(6) by auto
    then obtain as bs cs ds
      where split: "ops = as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs @ [(yid, Some xid)] @ ds"
      using assms \<open>xid < zid\<close> insert_ops_split_3 by blast
    then show ?thesis
    proof(cases ref)
      case None
      hence "xid \<in> set (interp_ins (as @ [(xid, ref)]))"
        using interp_ins_last_None assms(1) split by metis
      hence xid_in: "xid \<in> set (interp_ins (as @ [(xid, ref)] @ bs))"
        using interp_ins_monotonic assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order (as @ [(xid, ref)] @ bs @ [(zid, ref)]) zid xid"
        using list_order_insert_none assms(1) insert_ops_appendD split append.assoc None by metis
      hence "list_order ops zid xid"
        using list_order_append assms(1) split append.assoc by metis
      moreover have "xid \<in> set (interp_ins (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs))"
        using interp_ins_monotonic xid_in assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs @ [(yid, Some xid)]) xid yid"
        using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc None by metis
      hence "list_order ops xid yid"
        using list_order_append assms(1) split append.assoc by metis
      ultimately show ?thesis by blast
    next
      case (Some r)
      then show ?thesis
      proof(cases "r \<in> set (interp_ins as)")
        case True
        hence r_xid: "list_order (as @ [(xid, ref)]) r xid"
          using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc Some by metis
        hence "xid \<in> set (interp_ins (as @ [(xid, ref)]))"
          using list_order_memb2 assms(1) split by metis
        hence xid_in: "xid \<in> set (interp_ins (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs))"
          using interp_ins_monotonic assms(1) insert_ops_appendD split append.assoc by metis
        moreover have "list_order (as @ [(xid, ref)] @ bs) r xid"
          using list_order_append r_xid assms(1) insert_ops_appendD split append.assoc by metis
        hence "list_order (as @ [(xid, ref)] @ bs @ [(zid, ref)]) zid xid"
          using list_order_insert_between assms(1) insert_ops_appendD split append.assoc Some by metis
        hence "list_order ops zid xid"
          using list_order_append assms(1) split append.assoc by metis
        moreover have "list_order (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs @ [(yid, Some xid)]) xid yid"
          using list_order_insert_ref xid_in assms(1) insert_ops_appendD split append.assoc Some by metis
        hence "list_order ops xid yid"
          using list_order_append assms(1) split append.assoc by metis
        ultimately show ?thesis by blast
      next
        case False
        hence "xid \<notin> set (interp_ins ops)"
          using interp_ins_ref_nonex assms(1) split Some by metis
        moreover have "xid \<notin> set (interp_ins (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs))"
          using interp_ins_ref_nonex assms(1) insert_ops_appendD split append.assoc Some False by metis
        hence "yid \<notin> set (interp_ins ops)"
          using interp_ins_ref_nonex assms(1) split append.assoc by metis
        moreover have "r \<notin> set (interp_ins (as @ [(xid, ref)] @ bs))"
          using interp_ins_append_non_memb assms(1) insert_ops_appendD split append.assoc Some False by metis
        hence "zid \<notin> set (interp_ins ops)"
          using interp_ins_ref_nonex assms(1) split append.assoc Some by metis
        ultimately show ?thesis by blast
      qed
    qed
  qed
next
  case False
  hence "zid < xid" and "xid < yid"
    using assms neq_iff insert_ops_memb_ref_older by blast+
  then obtain as bs cs ds
    where split: "ops = as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)] @ ds"
    using assms insert_ops_split_3 by blast
  then show ?thesis
  proof(cases ref)
    case None
    hence "zid \<in> set (interp_ins (as @ [(zid, ref)]))"
      using interp_ins_last_None assms(1) split by metis
    hence "zid \<in> set (interp_ins (as @ [(zid, ref)] @ bs))"
      using interp_ins_monotonic assms(1) insert_ops_appendD split append.assoc by metis
    hence xid_zid: "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)]) xid zid"
      using list_order_insert_none assms(1) insert_ops_appendD split append.assoc None by metis
    hence "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs) xid zid"
      using list_order_append assms(1) insert_ops_appendD split append.assoc by metis
    hence "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)]) yid zid"
      using list_order_insert_between assms(1) insert_ops_appendD split append.assoc by metis
    hence "list_order ops yid zid"
      using list_order_append assms(1) split append.assoc by metis
    moreover have "xid \<in> set (interp_ins (as @ [(zid, ref)] @ bs @ [(xid, ref)]))"
      using list_order_memb1 xid_zid assms(1) split by metis
    hence "xid \<in> set (interp_ins (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs))"
      using interp_ins_monotonic assms(1) insert_ops_appendD split append.assoc by metis
    hence "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)]) xid yid"
      using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc by metis
    hence "list_order ops xid yid"
      using list_order_append assms(1) split append.assoc by metis
    ultimately show ?thesis by blast
  next
    case (Some r)
    then show ?thesis
    proof(cases "r \<in> set (interp_ins as)")
      case True
      hence "list_order (as @ [(zid, ref)]) r zid"
        using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc Some by metis
      hence "list_order (as @ [(zid, ref)] @ bs) r zid"
        using list_order_append assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)]) xid zid"
        using list_order_insert_between assms(1) insert_ops_appendD split append.assoc Some by metis
      hence xid_zid: "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs) xid zid"
        using list_order_append assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)]) yid zid"
        using list_order_insert_between assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order ops yid zid"
        using list_order_append assms(1) split append.assoc by metis
      moreover have "xid \<in> set (interp_ins (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs))"
        using list_order_memb1 xid_zid assms(1) split by metis
      hence "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)]) xid yid"
        using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order ops xid yid"
        using list_order_append assms(1) split append.assoc by metis
      ultimately show ?thesis by blast
    next
      case False
      hence "zid \<notin> set (interp_ins ops)"
        using interp_ins_ref_nonex assms(1) split Some by metis
      moreover have r_notin: "r \<notin> set (interp_ins (as @ [(zid, ref)] @ bs))"
        using interp_ins_append_non_memb assms(1) insert_ops_appendD split append.assoc Some False by metis
      hence "xid \<notin> set (interp_ins (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs))"
        using interp_ins_ref_nonex assms(1) insert_ops_appendD split append.assoc Some by metis
      hence "yid \<notin> set (interp_ins ops)"
        using interp_ins_ref_nonex assms(1) split append.assoc by metis
      moreover have "xid \<notin> set (interp_ins ops)"
        using interp_ins_ref_nonex r_notin assms(1) split append.assoc Some by metis
      ultimately show ?thesis by blast
    qed
  qed
qed

end
