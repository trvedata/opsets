theory RGA
  imports Main
begin

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

definition interp_rga :: "('oid::{linorder} \<times> 'oid option) list \<Rightarrow> 'oid list" where
  "interp_rga ops \<equiv> foldl insert_rga [] ops"


subsection\<open>Commutativity of insert_rga\<close>

lemma insert_body_set_ins [simp]:
  shows  "set (insert_body xs e) = insert e (set xs)"
by (induction xs, auto)

lemma insert_rga_set_ins:
  assumes "i \<in> set xs"
  shows "set (insert_rga xs (oid, Some i)) = insert oid (set xs)"
using assms by (induction xs, auto)

lemma insert_body_commutes:
  shows "insert_body (insert_body xs e1) e2 = insert_body (insert_body xs e2) e1"
by (induction xs, auto)

lemma insert_rga_insert_body_commute:
  assumes "i2 \<noteq> Some e1"
  shows "insert_rga (insert_body xs e1) (e2, i2) = insert_body (insert_rga xs (e2, i2)) e1"
using assms by (induction xs; cases i2) (auto simp add: insert_body_commutes)

lemma insert_rga_None_commutes:
  assumes "i2 \<noteq> Some e1"
  shows "insert_rga (insert_rga xs (e1, None)) (e2, i2  ) =
         insert_rga (insert_rga xs (e2, i2  )) (e1, None)"
using assms by (induction xs; cases i2) (auto simp add: insert_body_commutes)

lemma insert_rga_nonexistent:
  assumes "i \<notin> set xs"
  shows "insert_rga xs (e, Some i) = xs"
using assms by (induction xs, auto)

lemma insert_rga_Some_commutes:
  assumes "i1 \<in> set xs" and "i2 \<in> set xs"
    and "e1 \<noteq> i2" and "e2 \<noteq> i1"
  shows "insert_rga (insert_rga xs (e1, Some i1)) (e2, Some i2) =
         insert_rga (insert_rga xs (e2, Some i2)) (e1, Some i1)"
using assms proof (induction xs, simp)
  case (Cons a xs)
  then show ?case
    by (cases "a = i1"; cases "a = i2";
        auto simp add: insert_body_commutes insert_rga_insert_body_commute)
qed

lemma insert_rga_commutes:
  assumes "i2 \<noteq> Some e1" and "i1 \<noteq> Some e2"
  shows "insert_rga (insert_rga xs (e1, i1)) (e2, i2) =
         insert_rga (insert_rga xs (e2, i2)) (e1, i1)"
proof(cases i1)
  case None
  then show ?thesis
  using assms(1) insert_rga_None_commutes by (cases i2, fastforce, blast)
next
  case some_r1: (Some r1)
  then show ?thesis
  proof(cases i2)
    case None
    then show ?thesis 
      using assms(2) insert_rga_None_commutes by fastforce
  next
    case some_r2: (Some r2)
    then show ?thesis
    proof(cases "r1 \<in> set xs \<and> r2 \<in> set xs")
      case True
      then show ?thesis
        using assms some_r1 some_r2 by (simp add: insert_rga_Some_commutes)
    next
      case False
      then show ?thesis
        using assms some_r1 some_r2
        by (metis insert_iff insert_rga_nonexistent insert_rga_set_ins)
    qed
  qed
qed

lemma insert_body_split:
  shows "\<exists>p s. xs = p @ s \<and> insert_body xs e = p @ e # s"
proof(induction xs, force)
  case (Cons a xs)
  then obtain p s where IH: "xs = p @ s \<and> insert_body xs e = p @ e # s"
    by blast
  then show "\<exists>p s. a # xs = p @ s \<and> insert_body (a # xs) e = p @ e # s"
  proof(cases "a < e")
    case True
    then have "a # xs = [] @ (a # p @ s) \<and> insert_body (a # xs) e = [] @ e # (a # p @ s)"
      by (simp add: IH)
    then show ?thesis by blast
  next
    case False
    then have "a # xs = (a # p) @ s \<and> insert_body (a # xs) e = (a # p) @ e # s"
      using IH by auto
    then show ?thesis by blast
  qed
qed

lemma insert_between_elements:
  assumes "xs = pre @ ref # suf"
    and "distinct xs"
    and "\<And>i. i \<in> set xs \<Longrightarrow> i < e"
  shows "insert_rga xs (e, Some ref) = pre @ ref # e # suf"
using assms proof(induction xs arbitrary: pre, force)
  case (Cons a xs)
  then show "insert_rga (a # xs) (e, Some ref) = pre @ ref # e # suf"
  proof(cases pre)
    case pre_nil: Nil
    then have "a = ref"
      using Cons.prems(1) by auto
    then show ?thesis
      using Cons.prems pre_nil by (cases suf, auto)
  next
    case (Cons b pre')
    then have "insert_rga xs (e, Some ref) = pre' @ ref # e # suf"
      using Cons.IH Cons.prems by auto
    then show ?thesis
      using Cons.prems(1) Cons.prems(2) local.Cons by auto
  qed
qed

lemma insert_rga_after_ref:
  assumes "\<forall>x\<in>set as. a \<noteq> x"
    and "insert_body (cs @ ds) e = cs @ e # ds"
  shows "insert_rga (as @ a # cs @ ds) (e, Some a) = as @ a # cs @ e # ds"
using assms by (induction as; auto)

lemma insert_rga_preserves_order:
  assumes "i = None \<or> (\<exists>i'. i = Some i' \<and> i' \<in> set xs)"
    and "distinct xs"
  shows "\<exists>pre suf. xs = pre @ suf \<and> insert_rga xs (e, i) = pre @ e # suf"
proof(cases i)
  case None
  then show "\<exists>pre suf. xs = pre @ suf \<and> insert_rga xs (e, i) = pre @ e # suf"
    using insert_body_split by auto
next
  case (Some r)
  moreover from this obtain as bs where "xs = as @ r # bs \<and> (\<forall>x \<in> set as. x \<noteq> r)"
    using assms(1) split_list_first by fastforce
  moreover have "\<exists>cs ds. bs = cs @ ds \<and> insert_body bs e = cs @ e # ds"
    by (simp add: insert_body_split)
  then obtain cs ds where "bs = cs @ ds \<and> insert_body bs e = cs @ e # ds"
    by blast
  ultimately have "xs = (as @ r # cs) @ ds \<and> insert_rga xs (e, i) = (as @ r # cs) @ e # ds"
    using insert_rga_after_ref by fastforce
  then show ?thesis by blast
qed

end
