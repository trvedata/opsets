theory List_Spec
  imports Insert_Spec
begin

fun succ_rel :: "'oid list \<Rightarrow> ('oid \<times> 'oid) set" where
  "succ_rel [] = {}" |
  "succ_rel [head] = {}" |
  "succ_rel (head#x#xs) = {(head, x)} \<union> succ_rel (x#xs)"

fun insert_spec_alt :: "('oid \<times> 'oid) set \<Rightarrow> ('oid \<times> 'oid) \<Rightarrow> ('oid \<times> 'oid) set" where
  "insert_spec_alt list_rel (oid, ref) = (
      {(p, n) \<in> list_rel. p \<noteq> ref} \<union> {(ref, oid)} \<union>
      {(i, n). i = oid \<and> (ref, n) \<in> list_rel})"

lemma succ_rel_set_fst:
  shows "fst ` (succ_rel xs) = set (butlast xs)"
by (induction xs rule: succ_rel.induct, auto)

lemma succ_rel_set_snd:
  shows "snd ` (succ_rel xs) = set (tl xs)"
by (induction xs rule: succ_rel.induct, auto)

lemma succ_rel_functional:
  assumes "{(a, b1), (a, b2)} \<subseteq> succ_rel xs"
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
      using 3 by blast
    hence "a \<notin> fst ` (succ_rel (x#xs))"
      using succ_rel_set_fst in_set_butlastD by metis
    then show "b1 = b2"
      using 3 image_iff by fastforce
  next
    case False
    hence "{(a, b1), (a, b2)} \<subseteq> succ_rel (x#xs)"
      using 3 by auto
    moreover have "distinct (x#xs)"
      using 3 by auto
    ultimately show "b1 = b2"
      using "3.IH" by linarith
  qed
qed

lemma succ_rel_rem_head:
  assumes "distinct (x#y#xs)"
  shows "{(p, n) \<in> succ_rel (x#y#xs). p \<noteq> x} = succ_rel (y#xs)"
proof -
  have head_notin: "x \<notin> fst ` succ_rel (y#xs)"
    using assms succ_rel_set_fst by (metis distinct_set_notin in_set_butlastD)
  moreover have "succ_rel (x#y#xs) = {(x, y)} \<union> succ_rel (y#xs)"
    by simp
  moreover from this have "\<And>n. (x, n) \<in> succ_rel (x#y#xs) \<Longrightarrow> n = y"
    by (metis Pair_inject fst_conv head_notin image_eqI insertE insert_is_Un)
  hence "{(p, n) \<in> succ_rel (x#y#xs). p \<noteq> x} = succ_rel (x#y#xs) - {(x, y)}"
    by blast
  moreover have "succ_rel (x#y#xs) - {(x, y)} = succ_rel (y#xs)"
    using head_notin image_iff by fastforce
  ultimately show "{(p, n) \<in> succ_rel (x#y#xs). p \<noteq> x} = succ_rel (y#xs)"
    by simp
qed


lemma insert_spec_succ_rel:
  assumes "after = insert_spec before (oid, if ref = head then None else Some ref)"
    and "distinct (head # oid # before)"
  shows "succ_rel (head # after) = insert_spec_alt (succ_rel (head # before)) (oid, ref)"
proof(cases "ref = head")
  case ref_head: True
  hence "after = oid # before"
    using assms by simp
  then show ?thesis
  proof(cases before)
    case before_empty: Nil
    moreover from this have "succ_rel (head # before) = {}"
      by simp
    moreover from this have "succ_rel (head # after) = {(head, oid)}"
      using \<open>after = oid # before\<close> before_empty by auto
    ultimately show ?thesis 
      using ref_head by auto
  next
    case (Cons a list)
    moreover from this have head_in_rel: "(head, a) \<in> succ_rel (head # before)"
      by (cases list, auto)
    moreover have "distinct (head#a#list)"
      using assms(2) calculation by auto
    hence "{(p, n) \<in> succ_rel (head#a#list). p \<noteq> head} = succ_rel (a#list)"
      using succ_rel_rem_head by fastforce
    hence "{(p, n) \<in> succ_rel (head#before). p \<noteq> ref} = succ_rel before"
      using local.Cons ref_head by auto
    moreover have "{(i, n). i = oid \<and> (ref, n) \<in> succ_rel (head # before)} = {(oid, a)}"
    proof -
      have "\<And>n. (head, n) \<in> succ_rel (head # before) \<Longrightarrow> n = a"
        using calculation succ_rel_rem_head ref_head by fastforce
      hence "{(i, n) \<in> succ_rel (head # before). i = head} \<subseteq> {(head, a)}"
        by blast
      moreover have "{(head, a)} \<subseteq> {(i, n) \<in> succ_rel (head # before). i = head}"
        by (simp add: head_in_rel)
      ultimately show ?thesis
        using ref_head by blast
    qed
    moreover have "succ_rel before = succ_rel (tl after)"
      by (simp add: \<open>after = oid # before\<close>)
    moreover have "insert_spec_alt (succ_rel (head # before)) (oid, ref) =
                     {(p, n) \<in> succ_rel (head # before). p \<noteq> ref} \<union> {(ref, oid)} \<union>
                     {(i, n). i = oid \<and> (ref, n) \<in> succ_rel (head # before)}"
      by simp
    ultimately have "insert_spec_alt (succ_rel (head # before)) (oid, ref) =
             succ_rel (a#list) \<union> {(ref, oid)} \<union> {(oid, a)}"
      by simp
    moreover have "succ_rel (head # after) = {(head, oid), (oid, a)} \<union> succ_rel before"
      using \<open>after = oid # before\<close> local.Cons by auto
    ultimately show ?thesis
      using local.Cons ref_head by auto
  qed
next
  case False
  then show ?thesis sorry
qed
  

end
