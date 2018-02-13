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

lemma interp_list_maybe_grow:
  assumes "insert_ops (xs @ [(oid, ref)])"
  shows "set (interp_list (xs @ [(oid, ref)])) = set (interp_list xs) \<or>
         set (interp_list (xs @ [(oid, ref)])) = (set (interp_list xs) \<union> {oid})"
by (cases ref, simp add: interp_list_tail_unfold,
    metis insert_spec_nonex insert_spec_set interp_list_tail_unfold)

lemma interp_list_maybe_grow2:
  assumes "insert_ops (xs @ [x])"
  shows "set (interp_list (xs @ [x])) = set (interp_list xs) \<or>
         set (interp_list (xs @ [x])) = (set (interp_list xs) \<union> {fst x})"
using assms interp_list_maybe_grow by (cases x, auto)

lemma interp_list_maybe_grow3:
  assumes "insert_ops (xs @ ys)"
  shows "\<exists>A. A \<subseteq> set (map fst ys) \<and> set (interp_list (xs @ ys)) = set (interp_list xs) \<union> A"
using assms proof(induction ys rule: List.rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x ys)
  then have "insert_ops (xs @ ys)"
    by (metis append_assoc insert_ops_rem_last)
  then obtain A where IH: "A \<subseteq> set (map fst ys) \<and>
            set (interp_list (xs @ ys)) = set (interp_list xs) \<union> A"
    using snoc.IH by blast
  then show ?case
  proof(cases "set (interp_list (xs @ ys @ [x])) = set (interp_list (xs @ ys))")
    case True
    moreover have "A \<subseteq> set (map fst (ys @ [x]))"
      using IH by auto
    ultimately show ?thesis
      using IH by auto
  next
    case False
    then have "set (interp_list (xs @ ys @ [x])) = set (interp_list (xs @ ys)) \<union> {fst x}"
      by (metis append_assoc interp_list_maybe_grow2 snoc.prems)
    moreover have "A \<union> {fst x} \<subseteq> set (map fst (ys @ [x]))"
      using IH by auto
    ultimately show ?thesis
      using IH Un_assoc by metis
  qed
qed

lemma interp_list_ref_nonex:
  assumes "insert_ops ops"
    and "ops = xs @ [(oid, Some ref)] @ ys"
    and "ref \<notin> set (interp_list xs)"
  shows "oid \<notin> set (interp_list ops)"
using assms proof(induction ys arbitrary: ops rule: List.rev_induct)
  case Nil
  then have "interp_list ops = insert_spec (interp_list xs) (oid, Some ref)"
    by (simp add: interp_list_tail_unfold)
  moreover have "\<And>i. i \<in> set (map fst xs) \<Longrightarrow> i < oid"
    using Nil.prems last_op_greatest by fastforce
  hence "\<And>i. i \<in> set (interp_list xs) \<Longrightarrow> i < oid"
    by (meson interp_list_subset subsetCE)
  ultimately show "oid \<notin> set (interp_list ops)"
    using assms(3) by auto
next
  case (snoc x ys)
  then have "insert_ops (xs @ (oid, Some ref) # ys)"
    by (metis append.assoc append.simps(1) append_Cons insert_ops_appendD)
  hence IH: "oid \<notin> set (interp_list (xs @ (oid, Some ref) # ys))"
    by (simp add: snoc.IH snoc.prems(3))
  moreover have "distinct (map fst (xs @ (oid, Some ref) # ys @ [x]))"
    using snoc.prems by (metis append_Cons append_self_conv2 insert_ops_def spec_ops_def)
  hence "fst x \<noteq> oid"
    using empty_iff by auto
  moreover have "insert_ops ((xs @ (oid, Some ref) # ys) @ [x])"
    using snoc.prems by auto
  hence "set (interp_list ((xs @ (oid, Some ref) # ys) @ [x])) =
         set (interp_list (xs @ (oid, Some ref) # ys)) \<or> 
         set (interp_list ((xs @ (oid, Some ref) # ys) @ [x])) =
         set (interp_list (xs @ (oid, Some ref) # ys)) \<union> {fst x}"
    using interp_list_maybe_grow2 by blast
  ultimately show "oid \<notin> set (interp_list ops)"
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

lemma interp_list_last_None:
  shows "oid \<in> set (interp_list (ops @ [(oid, None)]))"
by (simp add: interp_list_tail_unfold)

lemma interp_list_monotonic:
  assumes "insert_ops (pre @ suf)"
    and "oid \<in> set (interp_list pre)"
  shows "oid \<in> set (interp_list (pre @ suf))"
using assms interp_list_maybe_grow3 by auto

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

lemma interp_list_append_non_memb:
  assumes "insert_ops (pre @ [(oid, Some ref)] @ suf)"
    and "ref \<notin> set (interp_list pre)"
  shows "ref \<notin> set (interp_list (pre @ [(oid, Some ref)] @ suf))"
using assms proof(induction suf rule: List.rev_induct)
  case Nil
  then show "ref \<notin> set (interp_list (pre @ [(oid, Some ref)] @ []))"
    by (metis append_Nil2 insert_spec_nonex interp_list_tail_unfold)
next
  case (snoc x xs)
  hence IH: "ref \<notin> set (interp_list (pre @ [(oid, Some ref)] @ xs))"
    by (metis append_assoc insert_ops_rem_last)
  moreover have "ref < oid"
    using insert_ops_ref_older snoc.prems(1) by auto
  moreover have "oid < fst x"
    using insert_ops_sorted_oids by (metis prod.collapse snoc.prems(1))
  have "set (interp_list ((pre @ [(oid, Some ref)] @ xs) @ [x])) =
        set (interp_list (pre @ [(oid, Some ref)] @ xs)) \<or>
        set (interp_list ((pre @ [(oid, Some ref)] @ xs) @ [x])) =
        set (interp_list (pre @ [(oid, Some ref)] @ xs)) \<union> {fst x}"
    by (metis (full_types) append.assoc interp_list_maybe_grow2 snoc.prems(1))
  ultimately show "ref \<notin> set (interp_list (pre @ [(oid, Some ref)] @ xs @ [x]))"
    using \<open>oid < fst x\<close> by auto
qed

lemma list_order_append:
  assumes "insert_ops (pre @ suf)"
    and "list_order pre x y"
  shows "list_order (pre @ suf) x y"
by (metis Un_iff assms list_order_monotonic insert_ops_appendD set_append subset_code(1))

lemma list_order_insert_ref:
  assumes "insert_ops (ops @ [(oid, Some ref)])"
    and "ref \<in> set (interp_list ops)"
  shows "list_order (ops @ [(oid, Some ref)]) ref oid"
proof -
  have "interp_list (ops @ [(oid, Some ref)]) = insert_spec (interp_list ops) (oid, Some ref)"
    by (simp add: interp_list_tail_unfold)
  moreover obtain xs ys where "interp_list ops = xs @ [ref] @ ys"
    using assms(2) split_list_first by fastforce
  hence "insert_spec (interp_list ops) (oid, Some ref) = xs @ [ref] @ [] @ [oid] @ ys"
    using assms(1) insert_after_ref interp_list_distinct by fastforce
  ultimately show "list_order (ops @ [(oid, Some ref)]) ref oid"
    using assms(1) list_orderI by metis
qed

lemma list_order_insert_none:
  assumes "insert_ops (ops @ [(oid, None)])"
    and "x \<in> set (interp_list ops)"
  shows "list_order (ops @ [(oid, None)]) oid x"
proof -
  have "interp_list (ops @ [(oid, None)]) = insert_spec (interp_list ops) (oid, None)"
    by (simp add: interp_list_tail_unfold)
  moreover obtain xs ys where "interp_list ops = xs @ [x] @ ys"
    using assms(2) split_list_first by fastforce
  hence "insert_spec (interp_list ops) (oid, None) = [] @ [oid] @ xs @ [x] @ ys"
    by simp
  ultimately show "list_order (ops @ [(oid, None)]) oid x"
    using assms(1) list_orderI by metis
qed

lemma list_order_insert_between:
  assumes "insert_ops (ops @ [(oid, Some ref)])"
    and "list_order ops ref x"
  shows "list_order (ops @ [(oid, Some ref)]) oid x"
proof -
  have "interp_list (ops @ [(oid, Some ref)]) = insert_spec (interp_list ops) (oid, Some ref)"
    by (simp add: interp_list_tail_unfold)
  moreover obtain xs ys zs where "interp_list ops = xs @ [ref] @ ys @ [x] @ zs"
    using assms list_orderE by blast
  moreover have "... = xs @ ref # (ys @ [x] @ zs)"
    by simp
  moreover have "distinct (xs @ ref # (ys @ [x] @ zs))"
    using assms(1) calculation by (metis interp_list_distinct insert_ops_rem_last)
  hence "insert_spec (xs @ ref # (ys @ [x] @ zs)) (oid, Some ref) = xs @ ref # oid # (ys @ [x] @ zs)"
    using assms(1) calculation by (simp add: insert_after_ref)
  moreover have "... = (xs @ [ref]) @ [oid] @ ys @ [x] @ zs"
    by simp
  ultimately show "list_order (ops @ [(oid, Some ref)]) oid x"
    using assms(1) list_orderI by metis
qed

theorem no_interleaving:
  assumes "insert_ops ops"
    and "(xid, ref) \<in> set ops"
    and "(yid, Some xid) \<in> set ops"
    and "(zid, ref) \<in> set ops"
    and "xid \<noteq> yid" and "yid \<noteq> zid" and "zid \<noteq> xid"
  shows "(list_order ops xid yid \<and> list_order ops yid zid) \<or>
         (list_order ops zid xid \<and> list_order ops xid yid) \<or>
         (xid \<notin> set (interp_list ops) \<and> yid \<notin> set (interp_list ops) \<and>
          zid \<notin> set (interp_list ops))"
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
      hence "xid \<in> set (interp_list (as @ [(xid, ref)]))"
        using interp_list_last_None assms(1) split by metis
      hence xid_in: "xid \<in> set (interp_list (as @ [(xid, ref)] @ bs))"
        using interp_list_monotonic assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order (as @ [(xid, ref)] @ bs @ [(yid, Some xid)]) xid yid"
        using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order ops xid yid"
        using list_order_append assms(1) split append.assoc by metis
      moreover have "xid \<in> set (interp_list (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs))"
        using interp_list_monotonic xid_in assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs @ [(zid, ref)]) zid xid"
        using list_order_insert_none assms(1) insert_ops_appendD split append.assoc None by metis
      hence "list_order ops zid xid"
        using list_order_append assms(1) split append.assoc by metis
      ultimately show ?thesis by blast
    next
      case (Some r)
      then show ?thesis
      proof(cases "r \<in> set (interp_list as)")
        case True
        hence r_xid: "list_order (as @ [(xid, ref)]) r xid"
          using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc Some by metis
        hence "xid \<in> set (interp_list (as @ [(xid, ref)]))"
          using list_order_memb2 assms(1) split by metis
        hence xid_in: "xid \<in> set (interp_list (as @ [(xid, ref)] @ bs))"
          using interp_list_monotonic assms(1) insert_ops_appendD split append.assoc by metis
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
        hence "xid \<notin> set (interp_list ops)"
          using interp_list_ref_nonex assms(1) split Some by metis
        moreover have "xid \<notin> set (interp_list (as @ [(xid, ref)] @ bs))"
          using interp_list_ref_nonex assms(1) insert_ops_appendD split append.assoc Some False by metis
        hence "yid \<notin> set (interp_list ops)"
          using interp_list_ref_nonex assms(1) split append.assoc by metis
        moreover have "r \<notin> set (interp_list (as @ [(xid, ref)] @ bs @ [(yid, Some xid)] @ cs))"
          using interp_list_append_non_memb assms(1) insert_ops_appendD split append.assoc Some False by metis
        hence "zid \<notin> set (interp_list ops)"
          using interp_list_ref_nonex assms(1) split append.assoc Some by metis
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
      hence "xid \<in> set (interp_list (as @ [(xid, ref)]))"
        using interp_list_last_None assms(1) split by metis
      hence xid_in: "xid \<in> set (interp_list (as @ [(xid, ref)] @ bs))"
        using interp_list_monotonic assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order (as @ [(xid, ref)] @ bs @ [(zid, ref)]) zid xid"
        using list_order_insert_none assms(1) insert_ops_appendD split append.assoc None by metis
      hence "list_order ops zid xid"
        using list_order_append assms(1) split append.assoc by metis
      moreover have "xid \<in> set (interp_list (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs))"
        using interp_list_monotonic xid_in assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs @ [(yid, Some xid)]) xid yid"
        using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc None by metis
      hence "list_order ops xid yid"
        using list_order_append assms(1) split append.assoc by metis
      ultimately show ?thesis by blast
    next
      case (Some r)
      then show ?thesis
      proof(cases "r \<in> set (interp_list as)")
        case True
        hence r_xid: "list_order (as @ [(xid, ref)]) r xid"
          using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc Some by metis
        hence "xid \<in> set (interp_list (as @ [(xid, ref)]))"
          using list_order_memb2 assms(1) split by metis
        hence xid_in: "xid \<in> set (interp_list (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs))"
          using interp_list_monotonic assms(1) insert_ops_appendD split append.assoc by metis
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
        hence "xid \<notin> set (interp_list ops)"
          using interp_list_ref_nonex assms(1) split Some by metis
        moreover have "xid \<notin> set (interp_list (as @ [(xid, ref)] @ bs @ [(zid, ref)] @ cs))"
          using interp_list_ref_nonex assms(1) insert_ops_appendD split append.assoc Some False by metis
        hence "yid \<notin> set (interp_list ops)"
          using interp_list_ref_nonex assms(1) split append.assoc by metis
        moreover have "r \<notin> set (interp_list (as @ [(xid, ref)] @ bs))"
          using interp_list_append_non_memb assms(1) insert_ops_appendD split append.assoc Some False by metis
        hence "zid \<notin> set (interp_list ops)"
          using interp_list_ref_nonex assms(1) split append.assoc Some by metis
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
    hence "zid \<in> set (interp_list (as @ [(zid, ref)]))"
      using interp_list_last_None assms(1) split by metis
    hence "zid \<in> set (interp_list (as @ [(zid, ref)] @ bs))"
      using interp_list_monotonic assms(1) insert_ops_appendD split append.assoc by metis
    hence xid_zid: "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)]) xid zid"
      using list_order_insert_none assms(1) insert_ops_appendD split append.assoc None by metis
    hence "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs) xid zid"
      using list_order_append assms(1) insert_ops_appendD split append.assoc by metis
    hence "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)]) yid zid"
      using list_order_insert_between assms(1) insert_ops_appendD split append.assoc by metis
    hence "list_order ops yid zid"
      using list_order_append assms(1) split append.assoc by metis
    moreover have "xid \<in> set (interp_list (as @ [(zid, ref)] @ bs @ [(xid, ref)]))"
      using list_order_memb1 xid_zid assms(1) split by metis
    hence "xid \<in> set (interp_list (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs))"
      using interp_list_monotonic assms(1) insert_ops_appendD split append.assoc by metis
    hence "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)]) xid yid"
      using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc by metis
    hence "list_order ops xid yid"
      using list_order_append assms(1) split append.assoc by metis
    ultimately show ?thesis by blast
  next
    case (Some r)
    then show ?thesis
    proof(cases "r \<in> set (interp_list as)")
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
      moreover have "xid \<in> set (interp_list (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs))"
        using list_order_memb1 xid_zid assms(1) split by metis
      hence "list_order (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs @ [(yid, Some xid)]) xid yid"
        using list_order_insert_ref assms(1) insert_ops_appendD split append.assoc by metis
      hence "list_order ops xid yid"
        using list_order_append assms(1) split append.assoc by metis
      ultimately show ?thesis by blast
    next
      case False
      hence "zid \<notin> set (interp_list ops)"
        using interp_list_ref_nonex assms(1) split Some by metis
      moreover have r_notin: "r \<notin> set (interp_list (as @ [(zid, ref)] @ bs))"
        using interp_list_append_non_memb assms(1) insert_ops_appendD split append.assoc Some False by metis
      hence "xid \<notin> set (interp_list (as @ [(zid, ref)] @ bs @ [(xid, ref)] @ cs))"
        using interp_list_ref_nonex assms(1) insert_ops_appendD split append.assoc Some by metis
      hence "yid \<notin> set (interp_list ops)"
        using interp_list_ref_nonex assms(1) split append.assoc by metis
      moreover have "xid \<notin> set (interp_list ops)"
        using interp_list_ref_nonex r_notin assms(1) split append.assoc Some by metis
      ultimately show ?thesis by blast
    qed
  qed
qed

end
