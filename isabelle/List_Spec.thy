theory List_Spec
  imports Insert_Spec
begin

fun succ_rel :: "'oid list \<Rightarrow> ('oid \<times> 'oid option) set" where
  "succ_rel [] = {}" |
  "succ_rel [head] = {(head, None)}" |
  "succ_rel (head#x#xs) = {(head, Some x)} \<union> succ_rel (x#xs)"

fun insert_alt :: "('oid \<times> 'oid option) set \<Rightarrow> ('oid \<times> 'oid) \<Rightarrow> ('oid \<times> 'oid option) set" where
  "insert_alt list_rel (oid, ref) = (
      if \<exists>n. (ref, n) \<in> list_rel
      then {(p, n) \<in> list_rel. p \<noteq> ref} \<union> {(ref, Some oid)} \<union>
           {(i, n). i = oid \<and> (ref, n) \<in> list_rel}
      else list_rel)"

lemma succ_rel_set_fst:
  shows "fst ` (succ_rel xs) = set xs"
by (induction xs rule: succ_rel.induct, auto)

lemma succ_rel_functional:
  assumes "(a, b1) \<in> succ_rel xs"
    and "(a, b2) \<in> succ_rel xs"
    and "distinct xs"
  shows "b1 = b2"
using assms proof(induction xs rule: succ_rel.induct)
  case 1
  then show ?case by simp
next
  case (2 head)
  then show ?case by simp
next
  case (3 head x xs)
  then show ?case
  proof(cases "a = head")
    case True
    hence "a \<notin> set (x#xs)"
      using 3 by auto
    hence "a \<notin> fst ` (succ_rel (x#xs))"
      using succ_rel_set_fst by metis
    then show "b1 = b2"
      using 3 image_iff by fastforce
  next
    case False
    hence "{(a, b1), (a, b2)} \<subseteq> succ_rel (x#xs)"
      using 3 by auto
    moreover have "distinct (x#xs)"
      using 3 by auto
    ultimately show "b1 = b2"
      using "3.IH" by auto
  qed
qed

lemma succ_rel_rem_head:
  assumes "distinct (x # xs)"
  shows "{(p, n) \<in> succ_rel (x # xs). p \<noteq> x} = succ_rel xs"
proof -
  have head_notin: "x \<notin> fst ` succ_rel xs"
    using assms by (simp add: succ_rel_set_fst)
  moreover obtain y where "(x, y) \<in> succ_rel (x # xs)"
    by (cases xs, auto)
  moreover have "succ_rel (x # xs) = {(x, y)} \<union> succ_rel xs"
    using calculation head_notin image_iff by (cases xs, fastforce+)
  moreover from this have "\<And>n. (x, n) \<in> succ_rel (x # xs) \<Longrightarrow> n = y"
    by (metis Pair_inject fst_conv head_notin image_eqI insertE insert_is_Un)
  hence "{(p, n) \<in> succ_rel (x # xs). p \<noteq> x} = succ_rel (x # xs) - {(x, y)}"
    by blast
  moreover have "succ_rel (x # xs) - {(x, y)} = succ_rel xs"
    using image_iff calculation by fastforce
  ultimately show "{(p, n) \<in> succ_rel (x # xs). p \<noteq> x} = succ_rel xs"
    by simp
qed

lemma succ_rel_swap_head:
  assumes "distinct (ref # list)"
    and "(ref, n) \<in> succ_rel (ref # list)"
  shows "succ_rel (oid # list) = {(oid, n)} \<union> succ_rel list"
proof(cases list)
  case Nil
  then show ?thesis using assms by auto
next
  case (Cons a list)
  moreover from this have "n = Some a"
    by (metis Un_iff assms singletonI succ_rel.simps(3) succ_rel_functional)
  ultimately show ?thesis by simp
qed

lemma succ_rel_insert_alt:
  assumes "a \<noteq> ref"
    and "distinct (oid # a # b # list)"
  shows "insert_alt (succ_rel (a # b # list)) (oid, ref) =
         {(a, Some b)} \<union> insert_alt (succ_rel (b # list)) (oid, ref)"
proof(cases "\<exists>n. (ref, n) \<in> succ_rel (a # b # list)")
  case True
  hence "insert_alt (succ_rel (a # b # list)) (oid, ref) =
           {(p, n) \<in> succ_rel (a # b # list). p \<noteq> ref} \<union> {(ref, Some oid)} \<union>
           {(i, n). i = oid \<and> (ref, n) \<in> succ_rel (a # b # list)}"
    by simp
  moreover have "{(p, n) \<in> succ_rel (a # b # list). p \<noteq> ref} =
                 {(a, Some b)} \<union> {(p, n) \<in> succ_rel (b # list). p \<noteq> ref}"
    using assms(1) by auto
  moreover have "insert_alt (succ_rel (b # list)) (oid, ref) =
           {(p, n) \<in> succ_rel (b # list). p \<noteq> ref} \<union> {(ref, Some oid)} \<union>
           {(i, n). i = oid \<and> (ref, n) \<in> succ_rel (b # list)}"
  proof -
    have "\<exists>n. (ref, n) \<in> succ_rel (b # list)"
      using assms(1) True by auto
    thus ?thesis by simp
  qed
  moreover have "{(i, n). i = oid \<and> (ref, n) \<in> succ_rel (a # b # list)} =
                 {(i, n). i = oid \<and> (ref, n) \<in> succ_rel (b # list)}"
    using assms(1) by auto
  ultimately show ?thesis by simp
next
  case False
  then show ?thesis by auto
qed

lemma succ_rel_insert_head:
  assumes "distinct (ref # list)"
  shows "succ_rel (insert_spec (ref # list) (oid, Some ref)) =
         insert_alt (succ_rel (ref # list)) (oid, ref)"
proof -
  obtain n where ref_in_rel: "(ref, n) \<in> succ_rel (ref # list)"
    by (cases list, auto)
  moreover from this have "{(p, n) \<in> succ_rel (ref # list). p \<noteq> ref} = succ_rel list"
    using assms succ_rel_rem_head by (metis (mono_tags, lifting))
  moreover have "{(i, n). i = oid \<and> (ref, n) \<in> succ_rel (ref # list)} = {(oid, n)}"
  proof -
    have "\<And>nx. (ref, nx) \<in> succ_rel (ref # list) \<Longrightarrow> nx = n"
      using assms by (simp add: succ_rel_functional ref_in_rel)
    hence "{(i, n) \<in> succ_rel (ref # list). i = ref} \<subseteq> {(ref, n)}"
      by blast
    moreover have "{(ref, n)} \<subseteq> {(i, n) \<in> succ_rel (ref # list). i = ref}"
      by (simp add: ref_in_rel)
    ultimately show ?thesis by blast
  qed
  moreover have "insert_alt (succ_rel (ref # list)) (oid, ref) =
                   {(p, n) \<in> succ_rel (ref # list). p \<noteq> ref} \<union> {(ref, Some oid)} \<union>
                   {(i, n). i = oid \<and> (ref, n) \<in> succ_rel (ref # list)}"
  proof -
    have "\<exists>n. (ref, n) \<in> succ_rel (ref # list)"
      using ref_in_rel by blast
    thus ?thesis by simp
  qed
  ultimately have "insert_alt (succ_rel (ref # list)) (oid, ref) =
                   succ_rel list \<union> {(ref, Some oid)} \<union> {(oid, n)}"
    by simp
  moreover have "succ_rel (oid # list) = {(oid, n)} \<union> succ_rel list"
    using assms ref_in_rel succ_rel_swap_head by metis
  hence "succ_rel (ref # oid # list) = {(ref, Some oid), (oid, n)} \<union> succ_rel list"
    by auto
  ultimately show "succ_rel (insert_spec (ref # list) (oid, Some ref)) =
                   insert_alt (succ_rel (ref # list)) (oid, ref)"
    by auto
qed

lemma succ_rel_insert_later:
  assumes "succ_rel (insert_spec (b # list) (oid, Some ref)) =
           insert_alt (succ_rel (b # list)) (oid, ref)"
    and "a \<noteq> ref"
    and "distinct (a # b # list)"
  shows "succ_rel (insert_spec (a # b # list) (oid, Some ref)) =
         insert_alt (succ_rel (a # b # list)) (oid, ref)"
proof -
  have "succ_rel (a # b # list) = {(a, Some b)} \<union> succ_rel (b # list)"
    by simp
  moreover have "insert_spec (a # b # list) (oid, Some ref) =
                 a # (insert_spec (b # list) (oid, Some ref))"
    using assms(2) by simp
  hence "succ_rel (insert_spec (a # b # list) (oid, Some ref)) =
         {(a, Some b)} \<union> succ_rel (insert_spec (b # list) (oid, Some ref))"
    by auto
  hence "succ_rel (insert_spec (a # b # list) (oid, Some ref)) =
         {(a, Some b)} \<union> insert_alt (succ_rel (b # list)) (oid, ref)"
    using assms(1) by auto
  moreover have "insert_alt (succ_rel (a # b # list)) (oid, ref) =
                 {(a, Some b)} \<union> insert_alt (succ_rel (b # list)) (oid, ref)"
    using succ_rel_insert_alt assms(2) by auto
  ultimately show ?thesis by blast
qed

lemma succ_rel_insert_Some:
  assumes "distinct list"
  shows "succ_rel (insert_spec list (oid, Some ref)) = insert_alt (succ_rel list) (oid, ref)"
using assms proof(induction list)
  case Nil
  then show "succ_rel (insert_spec [] (oid, Some ref)) = insert_alt (succ_rel []) (oid, ref)"
    by simp
next
  case (Cons a list)
  hence "distinct (a # list)"
    by simp
  then show "succ_rel (insert_spec (a # list) (oid, Some ref)) =
             insert_alt (succ_rel (a # list)) (oid, ref)"
  proof(cases "a = ref")
    case True
    then show ?thesis
      using succ_rel_insert_head \<open>distinct (a # list)\<close> by metis
  next
    case False
    hence "a \<noteq> ref" by simp
    moreover have "succ_rel (insert_spec list (oid, Some ref)) =
                   insert_alt (succ_rel list) (oid, ref)"
      using Cons.IH Cons.prems by auto
    ultimately show "succ_rel (insert_spec (a # list) (oid, Some ref)) =
                     insert_alt (succ_rel (a # list)) (oid, ref)"
      by (cases list, force, metis Cons.prems succ_rel_insert_later)
  qed
qed

definition interp_alt :: "'oid \<Rightarrow> ('oid \<times> 'oid option) list \<Rightarrow> ('oid \<times> 'oid option) set" where
  "interp_alt head ops \<equiv> foldl insert_alt {(head, None)}
     (map (\<lambda>x. case x of
            (oid, None)     \<Rightarrow> (oid, head) |
            (oid, Some ref) \<Rightarrow> (oid, ref)) 
      ops)"

theorem insert_alt_equivalent:
  assumes "insert_ops ops"
    and "head \<notin> fst ` set ops"
    and "\<And>r. Some r \<in> snd ` set ops \<Longrightarrow> r \<noteq> head"
  shows "succ_rel (head # interp_list ops) = interp_alt head ops"
using assms proof(induction ops rule: List.rev_induct)
  case Nil
  then show "succ_rel (head # interp_list []) = interp_alt head []"
    by (simp add: interp_list_def interp_alt_def)
next
  case (snoc x xs)
  have IH: "succ_rel (head # interp_list xs) = interp_alt head xs"
    using snoc by auto
  have distinct_list: "distinct (head # interp_list xs)"
  proof -
    have "distinct (interp_list xs)"
      using interp_list_distinct snoc.prems(1) by blast
    moreover have "set (interp_list xs) \<subseteq> fst ` set xs"
      using interp_list_subset snoc.prems(1) by fastforce
    ultimately show "distinct (head # interp_list xs)"
      using snoc.prems(2) by auto
  qed
  obtain oid r where x_pair: "x = (oid, r)" by force
  then show "succ_rel (head # interp_list (xs @ [x])) = interp_alt head (xs @ [x])"
  proof(cases r)
    case None
    have "interp_alt head (xs @ [x]) = insert_alt (interp_alt head xs) (oid, head)"
      by (simp add: interp_alt_def None x_pair)
    moreover have "... = insert_alt (succ_rel (head # interp_list xs)) (oid, head)"
      by (simp add: IH)
    moreover have "... = succ_rel (insert_spec (head # interp_list xs) (oid, Some head))"
      using distinct_list succ_rel_insert_Some by metis
    moreover have "... = succ_rel (head # (insert_spec (interp_list xs) (oid, None)))"
      by auto
    moreover have "... = succ_rel (head # (interp_list (xs @ [x])))"
      by (simp add: interp_list_tail_unfold None x_pair)
    ultimately show ?thesis by simp
  next
    case (Some ref)
    have "ref \<noteq> head"
      by (simp add: Some snoc.prems(3) x_pair)
    have "interp_alt head (xs @ [x]) = insert_alt (interp_alt head xs) (oid, ref)"
      by (simp add: interp_alt_def Some x_pair)
    moreover have "... = insert_alt (succ_rel (head # interp_list xs)) (oid, ref)"
      by (simp add: IH)
    moreover have "... = succ_rel (insert_spec (head # interp_list xs) (oid, Some ref))"
      using distinct_list succ_rel_insert_Some by metis
    moreover have "... = succ_rel (head # (insert_spec (interp_list xs) (oid, Some ref)))"
      using \<open>ref \<noteq> head\<close> by auto
    moreover have "... = succ_rel (head # (interp_list (xs @ [x])))"
      by (simp add: interp_list_tail_unfold Some x_pair)
    ultimately show ?thesis by simp
  qed
qed

end
