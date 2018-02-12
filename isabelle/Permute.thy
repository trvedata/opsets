(* Martin Kleppmann, University of Cambridge
   Victor B. F. Gomes, University of Cambridge
   Dominic P. Mulligan, Arm Research, Cambridge
*)

section\<open>Permutation predicate\<close>

text\<open>This section defines the "permut" predicate that indicates two
lists are permutations of each other, and proves various lemmas to
facilitate working with this predicate.\<close>

theory Permute
  imports Main
begin

text\<open>We say that two lists xs and ys are permutations of each other
if the two lists contain the same set of elements, and the elements
in each of the list are distinct (i.e. the lists do not contain any
duplicate elements).\<close>

definition permut :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "permut xs ys \<equiv> distinct xs \<and> distinct ys \<and> set xs = set ys"

lemma permut_single:
  assumes "permut [x] (ys @ [x] @ zs)"
  shows "ys = [] \<and> zs = []"
using assms by (auto simp: permut_def subset_insert)

lemma permut_commute:
  shows "permut xs ys \<longleftrightarrow> permut ys xs"
using permut_def by blast

lemma distinct_rem_mid:
  assumes "distinct (xs @ [x] @ ys)"
  shows "distinct (xs @ ys)"
using assms by (induction ys rule: rev_induct, simp_all)

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
proof -
  have "distinct xs"
    using assms distinct_append permut_def by blast
  moreover from this have "set xs = set (xs @ [x]) - {x}"
    by (meson assms distinct_set_remove_last permut_def)
  moreover have "distinct (ys @ zs)"
    using assms distinct_rem_mid by (simp add: permut_def)
  ultimately show "permut xs (ys @ zs)"
    using assms distinct_set_remove_mid permut_def by metis
qed

lemma permut_rem_any:
  assumes "permut (as @ [x] @ bs) (ys @ [x] @ zs)"
  shows "permut (as @ bs) (ys @ zs)"
proof -
  have "distinct (as @ bs)"
    by (meson assms distinct_rem_mid permut_def)
  moreover have "distinct (ys @ zs)"
    by (meson assms distinct_rem_mid permut_def)
  moreover have "set (as @ bs) = set (as @ [x] @ bs) - {x}"
    by (metis assms distinct_set_remove_mid permut_def)
  ultimately show "permut (as @ bs) (ys @ zs)"
    by (metis assms distinct_set_remove_mid permut_def)
qed

lemma permut_subset:
  assumes "permut xs (ys @ zs)"
  shows "set ys \<subseteq> set xs" and "set zs \<subseteq> set xs"
by (metis Un_iff assms permut_def set_append subsetI)+

lemma permut_append:
  assumes "permut xs (ys @ zs)"
    and "distinct (xs @ [x])"
  shows "permut (xs @ [x]) (ys @ [x] @ zs)"
using assms by (simp add: permut_def)

lemma permut_reorder1:
  assumes "permut (xs @ [x]) (ys @ [x] @ zs)"
  shows "permut (xs @ [x]) (ys @ zs @ [x])"
by (metis append.right_neutral append_assoc assms permut_append permut_def permut_rem_last)

lemma permut_trans:
  assumes "permut xs ys"
    and "permut ys zs"
  shows "permut xs zs"
using assms permut_def by blast

lemma permut_pair_fst:
  assumes "permut xs ys"
  shows "set (map fst xs) = set (map fst ys)"
using assms by (simp add: permut_def)

lemma permut_pair_snd:
  assumes "permut xs ys"
  shows "set (map snd xs) = set (map snd ys)"
using assms by (simp add: permut_def)

lemma permut_find_append:
  assumes "permut (xs @ [y]) (ys @ zs)"
  shows "y \<in> set ys \<or> y \<in> set zs"
using assms proof(induction xs arbitrary: ys zs rule: rev_induct)
  case Nil
  hence "set (ys @ zs) = {y}"
    by (metis append_self_conv2 empty_set list.simps(15) permut_def)
  thus "y \<in> set ys \<or> y \<in> set zs" by auto
next
  case (snoc a xs)
  then show "y \<in> set ys \<or> y \<in> set zs"
    by (metis UnE last_in_set last_snoc permut_def set_append snoc_eq_iff_butlast)
qed

end
