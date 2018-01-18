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

subsection\<open>Preservation of element indices\<close>

lemma insert_body_preserve_indices [simp]:
  shows  "set (insert_body xs e) = set xs \<union> {e}"
by(induction xs, auto)

lemma insert_none_preserve_indices:
  shows "set (insert_rga xs (oid, None)) = set xs \<union> {oid}"
by(induction xs, auto)

lemma insert_some_preserve_indices:
  assumes "i \<in> set xs"
  shows "set (insert_rga xs (oid, Some i)) = set xs \<union> {oid}"
using assms by(induction xs, auto)

subsection\<open>Commutativity of concurrent operations\<close>

lemma insert_body_commutes:
  shows "insert_body (insert_body xs e1) e2 = insert_body (insert_body xs e2) e1"
by(induction xs, auto)

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
    by (cases "a = i1"; cases "a = i2"; auto simp add: insert_body_commutes insert_rga_insert_body_commute)
qed

lemma insert_rga_commutes:
  assumes "i2 \<noteq> Some e1" and "i1 \<noteq> Some e2"
  shows "insert_rga (insert_rga xs (e1, i1)) (e2, i2) =
         insert_rga (insert_rga xs (e2, i2)) (e1, i1)"
  using assms apply(cases i1; cases i2)
  using insert_rga_None_commutes apply(blast, blast, force)
  apply clarsimp
  apply(case_tac "a \<in> set xs"; case_tac "aa \<in> set xs")
  apply(simp add: insert_rga_Some_commutes)
  apply(simp_all add: insert_rga_nonexistent insert_some_preserve_indices)
  done

lemma insert_body_stop_iteration:
  assumes "e > x"
  shows "insert_body (x#xs) e = e#x#xs"
using assms by simp

lemma insert_body_contains_new_elem:
  shows "\<exists>p s. xs = p @ s \<and> insert_body xs e = p @ e # s"
  apply (induction xs)
  apply force
  apply clarsimp
  apply (rule conjI)
  apply clarsimp
  apply (rule_tac x="[]" in exI)
  apply fastforce
  apply clarsimp
  apply (rename_tac a p s)
  apply (rule_tac x="a # p" in exI)
  apply clarsimp
  done

lemma insert_between_elements:
  assumes "xs = pre@ref#suf"
      and "distinct xs"
      and "\<And>i'. i' \<in> set xs \<Longrightarrow> i' < e"
    shows "insert_rga xs (e, Some ref) = pre @ ref # e # suf"
  using assms
  apply(induction xs arbitrary: pre)
  apply force
  apply(clarsimp)
  apply(case_tac pre)
  apply(clarsimp)
  apply(case_tac suf)
  apply force
  apply force
  apply clarsimp
  done

lemma insert_position_element_technical:
  assumes "\<forall>x\<in>set as. a \<noteq> x"
    and "insert_body (cs @ ds) e = cs @ e # ds"
  shows "insert_rga (as @ a # cs @ ds) (e, Some a) = as @ a # cs @ e # ds"
using assms by (induction as; auto)

lemma insert_preserves_order:
  assumes "i = None \<or> (\<exists>i'. i = Some i' \<and> i' \<in> set xs)"
      and "distinct xs"
    shows "\<exists>pre suf. xs = pre@suf \<and> insert_rga xs (e, i) = pre @ e # suf"
  using assms
  apply -
  apply(erule disjE)
  apply clarsimp
  using insert_body_contains_new_elem apply metis
  apply(erule exE, clarsimp)
  apply(rename_tac a)
  apply(subgoal_tac "\<exists>as bs. xs = as@a#bs \<and> (\<forall>x \<in> set as. x \<noteq> a)")
  apply clarsimp
  apply(rename_tac as bs)
  apply(subgoal_tac "\<exists>cs ds. insert_body bs e = cs@e#ds \<and> cs@ds = bs")
  apply clarsimp
  apply(rename_tac cs ds) 
  apply(rule_tac x="as@a#cs" in exI)
  apply(rule_tac x="ds" in exI)
  apply clarsimp
  apply(metis insert_position_element_technical)
  apply(metis insert_body_contains_new_elem)
  using split_list_first apply fastforce
done

end
