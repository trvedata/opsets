theory List_Spec
  imports Insert_Spec
begin

fun successor_rel :: "'oid list \<Rightarrow> ('oid \<times> 'oid) set" where
  "successor_rel [] = {}" |
  "successor_rel [head] = {}" |
  "successor_rel (head#x#xs) = {(head, x)} \<union> successor_rel (x#xs)"

fun insert_spec_alt :: "('oid \<times> 'oid) set \<Rightarrow> ('oid \<times> 'oid) \<Rightarrow> ('oid \<times> 'oid) set" where
  "insert_spec_alt list_rel (oid, ref) = (
      {(p, n) \<in> list_rel. p \<noteq> ref} \<union> {(ref, oid)} \<union>
      {(i, n). i = oid \<and> (ref, n) \<in> list_rel})"

lemma successor_rel_set_fst:
  shows "fst ` (successor_rel xs) = set (butlast xs)"
by (induction xs rule: successor_rel.induct, auto)

lemma successor_rel_set_snd:
  shows "snd ` (successor_rel xs) = set (tl xs)"
by (induction xs rule: successor_rel.induct, auto)

lemma successor_rel_functional:
  assumes "{(a, b1), (a, b2)} \<subseteq> successor_rel xs"
    and "distinct xs"
  shows "b1 = b2"
using assms proof(induction xs rule: successor_rel.induct)
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
    hence "a \<notin> fst ` (successor_rel (x#xs))"
      using successor_rel_set_fst in_set_butlastD by metis
    then show "b1 = b2"
      using 3 image_iff by fastforce
  next
    case False
    hence "{(a, b1), (a, b2)} \<subseteq> successor_rel (x#xs)"
      using 3 by auto
    moreover have "distinct (x#xs)"
      using 3 by auto
    ultimately show "b1 = b2"
      using "3.IH" by linarith
  qed
qed


lemma insert_spec_successor_rel:
  assumes "after = insert_spec before (oid, if ref = head then None else Some ref)"
  shows "successor_rel (head # after) = insert_spec_alt (successor_rel (head # before)) (oid, ref)"
proof(cases "ref = head")
  case ref_head: True
  hence "after = oid # before"
    using assms by simp
  then show ?thesis
  proof(cases before)
    case before_empty: Nil
    moreover from this have "successor_rel (head # before) = {}"
      by simp
    moreover from this have "successor_rel (head # after) = {(head, oid)}"
      using \<open>after = oid # before\<close> before_empty by auto
    ultimately show ?thesis 
      using ref_head by auto
  next
    case (Cons a list)
    moreover from this have "(head, a) \<in> successor_rel (head # before)"
      by (cases list, auto)
    then show ?thesis sorry
  qed
    
next
  case False
  then show ?thesis sorry
qed
  

end
