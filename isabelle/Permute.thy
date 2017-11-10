theory Permute
  imports Main (*"../../crdt-isabelle/src/Util"*)
begin

definition permut :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "permut xs ys \<equiv> distinct xs \<and> distinct ys \<and> set xs = set ys"

lemma list_split_memb:
  assumes "x \<in> set xs"
  shows "\<exists>ys zs. xs = ys @ [x] @ zs"
  using assms by(induction xs rule: rev_induct, simp, case_tac "x=xa", force+)

lemma permut_single:
  assumes "permut [x] (ys @ [x] @ zs)"
  shows "ys = [] \<and> zs = []"
  using assms by(clarsimp simp: permut_def subset_insert)

lemma distinct_rem_mid:
  assumes "distinct (xs @ [x] @ ys)"
  shows "distinct (xs @ ys)"
  using assms by(induction ys rule: rev_induct, simp_all)

lemma distinct_append_non_memb:
  assumes "distinct (xs @ [x])"
  shows "x \<notin> set xs"
  using assms by force

lemma distinct_set_remove_last:
  assumes "distinct (xs @ [x])"
  shows "set xs = set (xs @ [x]) - {x}"
  using assms by force

lemma distinct_set_remove_mid:
  assumes "distinct (xs @ [x] @ ys)"
  shows "set (xs @ ys) = set (xs @ [x] @ ys) - {x}"
  using assms by force

lemma permut_rem_last:
  assumes "permut (xs @ [x]) (ys @ [x] @ zs)"
  shows "permut xs (ys @ zs)"
  apply(subgoal_tac "distinct xs") prefer 2
  using assms distinct_append permut_def apply blast
  apply(subgoal_tac "distinct (ys @ zs)") prefer 2
  using assms distinct_rem_mid apply(simp add: permut_def)
  apply(subgoal_tac "set xs = set (xs @ [x]) - {x}") prefer 2
  apply(meson assms distinct_set_remove_last permut_def)
  using assms distinct_set_remove_mid permut_def apply metis
  done

lemma permut_rem_any:
  assumes "permut (as @ [x] @ bs) (ys @ [x] @ zs)"
  shows "permut (as @ bs) (ys @ zs)"
  apply(subgoal_tac "distinct (as @ bs)") prefer 2
  apply(meson assms distinct_rem_mid permut_def)
  apply(subgoal_tac "distinct (ys @ zs)") prefer 2
  apply(meson assms distinct_rem_mid permut_def)
  apply(subgoal_tac "set (as @ bs) = set (as @ [x] @ bs) - {x}") prefer 2
  apply(metis assms distinct_set_remove_mid permut_def)+
  done

end
