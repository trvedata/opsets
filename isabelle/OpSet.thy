theory OpSet
  imports Main Permute Util
begin

definition spec_ops :: "('oper \<Rightarrow> 'oid set) \<Rightarrow> ('oid::{linorder} \<times> 'oper) list \<Rightarrow> bool" where
  "spec_ops deps ops \<equiv> (sorted (map fst ops) \<and> distinct (map fst ops) \<and>
           (\<forall>oid oper ref. (oid, oper) \<in> set ops \<and> ref \<in> deps oper \<longrightarrow> ref < oid))"

inductive crdt_ops :: "('oper \<Rightarrow> 'oid set) \<Rightarrow> ('oid::{linorder} \<times> 'oper) list \<Rightarrow> bool" where
  "crdt_ops deps []" |
  "\<lbrakk>crdt_ops deps xs;
    oid \<notin> set (map fst xs);
    \<forall>ref \<in> deps oper. ref \<in> set (map fst xs) \<and> ref < oid
   \<rbrakk> \<Longrightarrow> crdt_ops deps (xs @ [(oid, oper)])"

locale opset =
  fixes opset :: "('oid::{linorder} \<times> 'oper) set"
    and deps  :: "'oper \<Rightarrow> 'oid set"
  assumes unique_oid: "(i1, op1) \<in> opset \<Longrightarrow> (i2, op2) \<in> opset \<Longrightarrow> op1 = op2"
    and ref_older: "(oid, oper) \<in> opset \<Longrightarrow> ref \<in> deps oper \<Longrightarrow> ref < oid"
    and finite_opset: "finite opset"

lemma opset_subset:
  assumes "opset Y deps"
    and "X \<subseteq> Y"
  shows "opset X deps"
proof
  fix i1 op1 i2 op2
  assume "(i1, op1) \<in> X" and "(i2, op2) \<in> X"
  thus "op1 = op2"
    using assms by (meson opset.unique_oid set_mp)
next
  fix oid oper ref
  assume "(oid, oper) \<in> X" and "ref \<in> deps oper"
  thus "ref < oid"
    using assms by (meson opset.ref_older set_rev_mp)
next
  show "finite X"
    using assms opset.finite_opset finite_subset by blast
qed

lemma opset_insert:
  assumes "opset (insert x ops) deps"
  shows "opset ops deps"
using assms opset_subset by blast

lemma opset_sublist:
  assumes "opset (set (xs @ ys @ zs)) deps"
  shows "opset (set (xs @ zs)) deps"
proof -
  have "set (xs @ zs) \<subseteq> set (xs @ ys @ zs)"
    by auto
  thus "opset (set (xs @ zs)) deps"
    using assms opset_subset by blast
qed


subsection\<open>Lemmata about the spec_ops predicate\<close>

lemma spec_ops_empty:
  shows "spec_ops deps []"
by (simp add: spec_ops_def)

lemma spec_ops_rem_last:
  assumes "spec_ops deps (xs @ [x])"
  shows "spec_ops deps xs"
proof -
  have "sorted (map fst (xs @ [x]))" and "distinct (map fst (xs @ [x]))"
    using assms spec_ops_def by blast+
  moreover from this have "sorted (map fst xs)" and "distinct xs"
    by (auto simp add: sorted_append distinct_butlast distinct_map)
  moreover have "\<forall>oid oper ref. (oid, oper) \<in> set xs \<and> ref \<in> deps oper \<longrightarrow> ref < oid"
    by (metis assms butlast_snoc in_set_butlastD spec_ops_def)
  ultimately show "spec_ops deps xs"
    by (simp add: spec_ops_def)
qed

lemma spec_ops_ref_less:
  assumes "spec_ops deps xs"
    and "(oid, oper) \<in> set xs"
    and "r \<in> deps oper"
  shows "r < oid"
using assms spec_ops_def by force

lemma spec_ops_ref_less_last:
  assumes "spec_ops deps (xs @ [(oid, oper)])"
    and "r \<in> deps oper"
  shows "r < oid"
using assms spec_ops_ref_less by fastforce

lemma spec_ops_id_inc:
  assumes "spec_ops deps (xs @ [(oid, oper)])"
    and "x \<in> set (map fst xs)"
  shows "x < oid"
proof -
  have "sorted ((map fst xs) @ (map fst [(oid, oper)]))"
    using assms(1) by (simp add: spec_ops_def)
  hence "\<forall>i \<in> set (map fst xs). i \<le> oid"
    by (simp add: sorted_append)
  moreover have "distinct ((map fst xs) @ (map fst [(oid, oper)]))"
    using assms(1) by (simp add: spec_ops_def)
  hence "\<forall>i \<in> set (map fst xs). i \<noteq> oid"
    by auto
  ultimately show "x < oid"
    using assms(2) le_neq_trans by auto
qed

lemma spec_ops_add_any:
  assumes "spec_ops deps (xs @ ys)"
    and "\<forall>i \<in> set (map fst xs). i < oid"
    and "\<forall>i \<in> set (map fst ys). oid < i"
    and "\<forall>ref \<in> deps oper. ref < oid"
  shows "spec_ops deps (xs @ [(oid, oper)] @ ys)"
using assms proof(induction ys rule: rev_induct)
  case empty_ys: Nil
  hence "sorted ((map fst xs) @ [oid])"
    using assms(2) sorted_append spec_ops_def by fastforce
  moreover have "distinct ((map fst xs) @ [oid])"
    using empty_ys spec_ops_def by auto
  moreover have "\<forall>oid oper ref. (oid, oper) \<in> set xs \<and> ref \<in> deps oper \<longrightarrow> ref < oid"
    using empty_ys.prems(1) spec_ops_def by fastforce
  hence "\<forall>i opr r. (i, opr) \<in> set (xs @ [(oid, oper)]) \<and> r \<in> deps opr \<longrightarrow> r < i"
    using empty_ys.prems(4) by auto
  ultimately show "spec_ops deps (xs @ [(oid, oper)] @ [])"
    by (simp add: spec_ops_def)
next
  case (snoc y ys)
  have IH: "spec_ops deps (xs @ [(oid, oper)] @ ys)"
  proof -
    from snoc have "spec_ops deps (xs @ ys)"
      by (metis append_assoc spec_ops_rem_last)
    thus "spec_ops deps (xs @ [(oid, oper)] @ ys)"
      using assms(2) snoc by auto
  qed
  obtain yi yo where y_pair: "y = (yi, yo)"
    by force
  have oid_yi: "oid < yi"
    by (simp add: snoc.prems(3) y_pair)
  have yi_biggest: "\<forall>i \<in> set (map fst (xs @ [(oid, oper)] @ ys)). i < yi"
  proof -
    have "\<forall>i \<in> set (map fst xs). i < yi"
      using oid_yi assms(2) less_trans by blast
    moreover have "\<forall>i \<in> set (map fst ys). i < yi"
      by (metis UnCI append_assoc map_append set_append snoc.prems(1) spec_ops_id_inc y_pair)
    ultimately show ?thesis
      using oid_yi by auto
  qed
  have "sorted (map fst (xs @ [(oid, oper)] @ ys @ [y]))"
  proof -
    from IH have "sorted (map fst (xs @ [(oid, oper)] @ ys))"
      using spec_ops_def by blast
    hence "sorted (map fst (xs @ [(oid, oper)] @ ys) @ [yi])"
      using yi_biggest sorted_append
      by (metis (no_types, lifting) append_Nil2 order_less_imp_le set_ConsD sorted_single)
    thus "sorted (map fst (xs @ [(oid, oper)] @ ys @ [y]))"
      by (simp add: y_pair)
  qed
  moreover have "distinct (map fst (xs @ [(oid, oper)] @ ys @ [y]))"
  proof -
    have "distinct (map fst (xs @ [(oid, oper)] @ ys) @ [yi])"
      using IH yi_biggest spec_ops_def
      by (metis distinct.simps(2) distinct1_rotate order_less_irrefl rotate1.simps(2))
    thus "distinct (map fst (xs @ [(oid, oper)] @ ys @ [y]))"
      by (simp add: y_pair)
  qed
  moreover have "\<forall>i opr r. (i, opr) \<in> set (xs @ [(oid, oper)] @ ys @ [y])
                     \<and> r \<in> deps opr \<longrightarrow> r < i"
  proof -
    have "\<forall>i opr r. (i, opr) \<in> set (xs @ [(oid, oper)] @ ys) \<and> r \<in> deps opr \<longrightarrow> r < i"
      by (meson IH spec_ops_def)
    moreover have "\<forall>ref. ref \<in> deps yo \<longrightarrow> ref < yi"
      by (metis spec_ops_ref_less append_is_Nil_conv last_appendR last_in_set last_snoc
          list.simps(3) snoc.prems(1) y_pair)
    ultimately show ?thesis
      using y_pair by auto
  qed
  ultimately show "spec_ops deps (xs @ [(oid, oper)] @ ys @ [y])"
    using spec_ops_def by blast
qed

lemma spec_ops_split:
  assumes "spec_ops deps xs"
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
      using IH spec_ops_id_inc snoc.prems(1) y_pair by metis
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

lemma spec_ops_exists_base:
  assumes "finite ops"
    and "\<And>i1 i2 op1 op2. (i1, op1) \<in> ops \<Longrightarrow> (i2, op2) \<in> ops \<Longrightarrow> op1 = op2"
    and "\<And>oid oper ref. (oid, oper) \<in> ops \<Longrightarrow> ref \<in> deps oper \<Longrightarrow> ref < oid"
  shows "\<exists>op_list. set op_list = ops \<and> spec_ops deps op_list"
using assms proof(induct ops rule: Finite_Set.finite_induct_select)
  case empty
  then show "\<exists>op_list. set op_list = {} \<and> spec_ops deps op_list"
    by (simp add: spec_ops_empty)
next
  case (select subset)
  from this obtain op_list where "set op_list = subset" and "spec_ops deps op_list"
    using assms by blast
  moreover obtain oid oper where select: "(oid, oper) \<in> ops - subset"
    using select.hyps(1) by auto
  moreover from this have "\<And>op2. (oid, op2) \<in> ops \<Longrightarrow> op2 = oper"
    using assms(2) by auto
  hence "oid \<notin> fst ` subset"
    by (metis (no_types, lifting) DiffD2 select image_iff prod.collapse psubsetD select.hyps(1))
  from this obtain pre suf
    where "op_list = pre @ suf"
      and "\<forall>i \<in> set (map fst pre). i < oid"
      and "\<forall>i \<in> set (map fst suf). oid < i"
    using spec_ops_split calculation by (metis (no_types, lifting) set_map)
  moreover have "set (pre @ [(oid, oper)] @ suf) = insert (oid, oper) subset"
    using calculation by auto
  moreover have "spec_ops deps (pre @ [(oid, oper)] @ suf)"
    using calculation spec_ops_add_any assms(3) by (metis DiffD1)
  ultimately show ?case by blast
qed

lemma spec_ops_exists:
  assumes "opset ops deps"
  shows "\<exists>op_list. set op_list = ops \<and> spec_ops deps op_list"
proof -
  have "finite ops"
    using assms opset.finite_opset by force
  moreover have "\<And>i1 i2 op1 op2. (i1, op1) \<in> ops \<Longrightarrow> (i2, op2) \<in> ops \<Longrightarrow> op1 = op2"
    using assms opset.unique_oid by force
  moreover have "\<And>oid oper ref. (oid, oper) \<in> ops \<Longrightarrow> ref \<in> deps oper \<Longrightarrow> ref < oid"
    using assms opset.ref_older by force
  ultimately show "\<exists>op_list. set op_list = ops \<and> spec_ops deps op_list"
    by (simp add: spec_ops_exists_base)
qed


subsection\<open>Lemmata about the crdt_ops predicate\<close>

inductive_cases crdt_ops_last: "crdt_ops deps (xs @ [x])"

lemma crdt_ops_intro:
  assumes "\<And>r. r \<in> deps oper \<Longrightarrow> r \<in> fst ` set xs \<and> r < oid"
    and "oid \<notin> fst ` set xs"
    and "crdt_ops deps xs"
  shows "crdt_ops deps (xs @ [(oid, oper)])"
using assms crdt_ops.simps by force

lemma crdt_ops_rem_last:
  assumes "crdt_ops deps (xs @ [x])"
  shows "crdt_ops deps xs"
using assms crdt_ops.cases snoc_eq_iff_butlast by blast

lemma crdt_ops_ref_less:
  assumes "crdt_ops deps xs"
    and "(oid, oper) \<in> set xs"
    and "r \<in> deps oper"
  shows "r < oid"
using assms by (induction rule: crdt_ops.induct, auto)

lemma crdt_ops_ref_less_last:
  assumes "crdt_ops deps (xs @ [(oid, oper)])"
    and "r \<in> deps oper"
  shows "r < oid"
using assms crdt_ops_ref_less by fastforce

lemma crdt_ops_distinct:
  assumes "crdt_ops deps xs"
  shows "distinct xs"
using assms by (induction xs, force+)

lemma crdt_ops_distinct_fst:
  assumes "crdt_ops deps xs"
  shows "distinct (map fst xs)"
using assms by (induction xs, auto)

lemma crdt_ops_unique_last:
  assumes "crdt_ops deps (xs @ [(oid, oper)])"
  shows "oid \<notin> set (map fst xs)"
using assms crdt_ops.cases by blast

lemma crdt_ops_unique_mid:
  assumes "crdt_ops deps (xs @ [(oid, oper)] @ ys)"
  shows "oid \<notin> set (map fst xs) \<and> oid \<notin> set (map fst ys)"
using assms proof(induction ys rule: rev_induct)  
  case Nil
  then show "oid \<notin> set (map fst xs) \<and> oid \<notin> set (map fst [])"
    by (metis crdt_ops_unique_last Nil_is_map_conv append_Nil2 empty_iff empty_set)
next
  case (snoc y ys)
  obtain yi yr where y_pair: "y = (yi, yr)"
    by fastforce
  have IH: "oid \<notin> set (map fst xs) \<and> oid \<notin> set (map fst ys)"
    using crdt_ops_rem_last snoc by (metis append_assoc)
  have "(xs @ (oid, oper) # ys) @ [(yi, yr)] = xs @ (oid, oper) # ys @ [(yi, yr)]"
    by simp
  hence "yi \<notin> set (map fst (xs @ (oid, oper) # ys))"
    using crdt_ops_unique_last by (metis append_Cons append_self_conv2 snoc.prems y_pair)
  thus "oid \<notin> set (map fst xs) \<and> oid \<notin> set (map fst (ys @ [y]))"
    using IH y_pair by auto
qed

lemma crdt_ops_ref_exists:
  assumes "crdt_ops deps (pre @ (oid, oper) # suf)"
    and "ref \<in> deps oper"
  shows "ref \<in> fst ` set pre"
using assms proof(induction suf rule: List.rev_induct)
  case Nil thus ?case
    by (metis crdt_ops_last prod.sel(2))
next
  case (snoc x xs) thus ?case
    using crdt_ops.cases by force
qed

lemma crdt_ops_no_future_ref:
  assumes "crdt_ops deps (xs @ [(oid, oper)] @ ys)"
  shows "\<And>ref. ref \<in> deps oper \<Longrightarrow> ref \<notin> fst ` set ys"
proof -
  from assms(1) have "\<And>ref. ref \<in> deps oper \<Longrightarrow> ref \<in> set (map fst xs)"
    by (simp add: crdt_ops_ref_exists)
  moreover have "distinct (map fst (xs @ [(oid, oper)] @ ys))"
    using assms crdt_ops_distinct_fst by blast
  ultimately have "\<And>ref. ref \<in> deps oper \<Longrightarrow> ref \<notin> set (map fst ([(oid, oper)] @ ys))"
    using distinct_pair_list_memb by metis
  thus "\<And>ref. ref \<in> deps oper \<Longrightarrow> ref \<notin> fst ` set ys"
    by simp
qed

lemma crdt_ops_reorder:
  assumes "crdt_ops deps (xs @ [(oid, oper)] @ ys)"
    and "\<And>op2 r. op2 \<in> snd ` set ys \<Longrightarrow> r \<in> deps op2 \<Longrightarrow> r \<noteq> oid"
  shows "crdt_ops deps (xs @ ys @ [(oid, oper)])"
using assms proof(induction ys rule: rev_induct)
  case Nil
  then show "crdt_ops deps (xs @ [] @ [(oid, oper)])"
    using crdt_ops_rem_last by auto
next
  case (snoc y ys)
  then obtain yi yo where y_pair: "y = (yi, yo)"
    by fastforce
  have IH: "crdt_ops deps (xs @ ys @ [(oid, oper)])"
  proof -
    have "crdt_ops deps (xs @ [(oid, oper)] @ ys)"
      by (metis snoc(2) append.assoc crdt_ops_rem_last)
    thus "crdt_ops deps (xs @ ys @ [(oid, oper)])"
      using snoc.IH snoc.prems(2) by auto
  qed
  have "crdt_ops deps (xs @ ys @ [y])"
  proof -
    have "yi \<notin> fst ` set (xs @ [(oid, oper)] @ ys)"
      by (metis y_pair append_assoc crdt_ops_unique_last set_map snoc.prems(1))
    hence "yi \<notin> fst ` set (xs @ ys)"
      by auto
    moreover have "\<And>r. r \<in> deps yo \<Longrightarrow> r \<in> fst ` set (xs @ ys) \<and> r < yi"
    proof -
      have "\<And>r. r \<in> deps yo \<Longrightarrow> r \<noteq> oid"
        using snoc.prems(2) y_pair by fastforce
      moreover have "\<And>r. r \<in> deps yo \<Longrightarrow> r \<in> fst ` set (xs @ [(oid, oper)] @ ys)"
        by (metis y_pair append_assoc snoc.prems(1) crdt_ops_ref_exists)
      moreover have "\<And>r. r \<in> deps yo \<Longrightarrow> r < yi"
        using crdt_ops_ref_less snoc.prems(1) y_pair by fastforce
      ultimately show "\<And>r. r \<in> deps yo \<Longrightarrow> r \<in> fst ` set (xs @ ys) \<and> r < yi"
        by simp
    qed
    moreover from IH have "crdt_ops deps (xs @ ys)"
      using crdt_ops_rem_last by force
    ultimately show "crdt_ops deps (xs @ ys @ [y])"
      using y_pair crdt_ops_intro by (metis append.assoc)
  qed
  moreover have "oid \<notin> fst ` set (xs @ ys @ [y])"
    using crdt_ops_unique_mid by (metis (no_types, lifting) UnE image_Un 
      image_set set_append snoc.prems(1))
  moreover have "\<And>r. r \<in> deps oper \<Longrightarrow> r \<in> fst ` set (xs @ ys @ [y])"
    using crdt_ops_ref_exists
    by (metis UnCI append_Cons image_Un set_append snoc.prems(1))
  moreover have "\<And>r. r \<in> deps oper \<Longrightarrow> r < oid"
    using IH crdt_ops_ref_less by fastforce
  ultimately show "crdt_ops deps (xs @ (ys @ [y]) @ [(oid, oper)])"
    using crdt_ops_intro by (metis append_assoc)
qed

lemma crdt_ops_rem_middle:
  assumes "crdt_ops deps (xs @ [(oid, ref)] @ ys)"
    and "\<And>op2 r. op2 \<in> snd ` set ys \<Longrightarrow> r \<in> deps op2 \<Longrightarrow> r \<noteq> oid"
  shows "crdt_ops deps (xs @ ys)"
using assms crdt_ops_rem_last crdt_ops_reorder append_assoc by metis

lemma crdt_ops_independent_suf:
  assumes "spec_ops deps (xs @ [(oid, oper)])"
    and "crdt_ops deps (ys @ [(oid, oper)] @ zs)"
    and "permut (xs @ [(oid, oper)]) (ys @ [(oid, oper)] @ zs)"
  shows "\<And>op2 r. op2 \<in> snd ` set zs \<Longrightarrow> r \<in> deps op2 \<Longrightarrow> r \<noteq> oid"
proof -
  have "\<And>op2 r. op2 \<in> snd ` set xs \<Longrightarrow> r \<in> deps op2 \<Longrightarrow> r < oid"
  proof -
    from assms(1) have "\<And>i. i \<in> fst ` set xs \<Longrightarrow> i < oid"
      using spec_ops_id_inc by fastforce
    moreover have "\<And>i2 op2 r. (i2, op2) \<in> set xs \<Longrightarrow> r \<in> deps op2 \<Longrightarrow> r < i2"
      using assms(1) spec_ops_ref_less spec_ops_rem_last by fastforce
    ultimately show "\<And>op2 r. op2 \<in> snd ` set xs \<Longrightarrow> r \<in> deps op2 \<Longrightarrow> r < oid"
      by fastforce
  qed
  moreover from assms(3) have "set zs \<subseteq> set xs"
    by (metis permut_rem_last permut_subset(2))
  ultimately show "\<And>op2 r. op2 \<in> snd ` set zs \<Longrightarrow> r \<in> deps op2 \<Longrightarrow> r \<noteq> oid"
    by fastforce
qed

lemma crdt_ops_reorder_spec:
  assumes "spec_ops deps (xs @ [x])"
    and "crdt_ops deps (ys @ [x] @ zs)"
    and "permut (xs @ [x]) (ys @ [x] @ zs)"
  shows "crdt_ops deps (ys @ zs @ [x])"
using assms proof -
  obtain oid oper where x_pair: "x = (oid, oper)" by force
  hence "\<And>op2 r. op2 \<in> snd ` set zs \<Longrightarrow> r \<in> deps op2 \<Longrightarrow> r \<noteq> oid"
    using assms crdt_ops_independent_suf by fastforce
  thus "crdt_ops deps (ys @ zs @ [x])"
    using assms(2) crdt_ops_reorder x_pair by metis
qed

lemma crdt_ops_rem_spec:
  assumes "spec_ops deps (xs @ [x])"
    and "crdt_ops deps (ys @ [x] @ zs)"
    and "permut (xs @ [x]) (ys @ [x] @ zs)"
  shows "crdt_ops deps (ys @ zs)"
using assms crdt_ops_rem_last crdt_ops_reorder_spec append_assoc by metis

lemma crdt_ops_rem_penultimate:
  assumes "crdt_ops deps (xs @ [(i1, r1)] @ [(i2, r2)])"
    and "\<And>r. r \<in> deps r2 \<Longrightarrow> r \<noteq> i1"
  shows "crdt_ops deps (xs @ [(i2, r2)])"
proof -
  have "crdt_ops deps (xs @ [(i1, r1)])"
    using assms(1) crdt_ops_rem_last by force
  hence "crdt_ops deps xs"
    using crdt_ops_rem_last by force
  moreover have "distinct (map fst (xs @ [(i1, r1)] @ [(i2, r2)]))"
    using assms(1) crdt_ops_distinct_fst by blast
  hence "i2 \<notin> set (map fst xs)"
    by auto
  moreover have "crdt_ops deps ((xs @ [(i1, r1)]) @ [(i2, r2)])"
    using assms(1) by auto
  hence "\<And>r. r \<in> deps r2 \<Longrightarrow> r \<in> fst ` set (xs @ [(i1, r1)])"
    using crdt_ops_ref_exists by metis
  hence "\<And>r. r \<in> deps r2 \<Longrightarrow> r \<in> set (map fst xs)"
    using assms(2) by auto
  moreover have "\<And>r. r \<in> deps r2 \<Longrightarrow> r < i2"
    using assms(1) crdt_ops_ref_less by fastforce
  ultimately show "crdt_ops deps (xs @ [(i2, r2)])"
    by (simp add: crdt_ops_intro)
qed

end
