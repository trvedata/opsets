theory List_Spec
  imports Main "~~/src/HOL/Library/Product_Lexorder"
begin

section\<open>List operations, their interpretation, and implementation\<close>
  
datatype 'oid list_op
  = InsertAfter "'oid option"
  | Remove 'oid

fun insert_after :: "'oid \<Rightarrow> 'oid option \<Rightarrow> 'oid list \<Rightarrow> 'oid list" where
  "insert_after oid None       xs     = oid#xs" |
  "insert_after oid _          []     = []" |
  "insert_after oid (Some ref) (x#xs) =
     (if x = ref then
        x#oid#xs
      else
        x#(insert_after oid (Some ref) xs))"
  
fun make_insert :: "'oid list \<Rightarrow> 'oid \<Rightarrow> nat \<Rightarrow> ('oid \<times> 'oid list_op)" where
  "make_insert xs oid 0       = (oid, InsertAfter None)" |
  "make_insert [] oid m       = (oid, InsertAfter None)" |
  "make_insert xs oid (Suc m) = (oid, InsertAfter (Some (xs ! min (length xs - 1) m)))"

fun interp :: "'oid list \<times> 'oid set \<Rightarrow> ('oid \<times> 'oid list_op) \<Rightarrow> 'oid list \<times> 'oid set" where
  "interp (list, tomb) (oid, InsertAfter ref) = (insert_after oid ref list, tomb)" |
  "interp (list, tomb) (oid, Remove      ref) = (list, tomb \<union> {ref})"

definition interp_list :: "('oid \<times> 'oid list_op) list \<Rightarrow> 'oid list \<times> 'oid set" where
  "interp_list ops \<equiv> foldl interp ([], {}) ops"

section\<open>The list specification locale\<close>
  
locale list_spec =
  fixes op_list :: "('oid::{linorder} \<times> 'oid list_op) list"
  assumes sorted_oids [simp, intro!]: "sorted (map fst op_list)"
    and distinct_oids [simp, intro!]: "distinct (map fst op_list)"
    and ref_older: "(oid, InsertAfter (Some ref)) \<in> set op_list \<Longrightarrow> ref < oid"

context list_spec begin
  
definition op_set :: "('oid::{linorder} \<times> 'oid list_op) set" where
  "op_set \<equiv> set op_list"

definition insertions :: "('oid \<times> 'oid list_op) list" where
  "insertions \<equiv> filter (\<lambda>oid_oper.
     case snd oid_oper of
       InsertAfter x \<Rightarrow> True
     | _ \<Rightarrow> False) op_list"

definition ins_list :: "'oid list" where
  "ins_list \<equiv> fst (interp_list op_list)"

definition tombstones :: "'oid set" where
  "tombstones \<equiv> snd (interp_list op_list)"

definition list_order :: "'oid \<Rightarrow> 'oid \<Rightarrow> bool" (infix "\<sqsubset>" 50) where
  "list_order x y \<equiv> \<exists>xs ys zs. ins_list = xs@[x]@ys@[y]@zs"
  
lemma list_orderI [intro!]:
  assumes "ins_list = xs@[x]@ys@[y] @zs"
  shows "x \<sqsubset> y"
  using assms by(auto simp add: list_order_def)
    
lemma list_orderE [elim]:
  assumes "x \<sqsubset> y"
  shows "\<exists>xs ys zs. ins_list = xs@[x]@ys@[y] @zs"
  using assms by(auto simp add: list_order_def)

end
  
lemma list_spec_NilI [intro!]:
  shows "list_spec []"
by(clarsimp simp add: list_spec_def)
  
lemma list_spec_rm_last [dest]:
  assumes "list_spec (xs@[x])"
  shows "list_spec xs"
using assms by(clarsimp simp: list_spec_def) (metis sorted_append)

lemma insert_after_none [simp]:
  shows "set (insert_after oid None xs) = set xs \<union> {oid}"
by(induction xs, auto simp add: insert_commute sup_commute)

lemma insert_after_set [simp]:
  assumes "ref \<in> set xs"
  shows "set (insert_after oid (Some ref) xs) = set xs \<union> {oid}"
using assms proof(induction xs)
  assume "ref \<in> set []"
  thus "set (insert_after oid (Some ref) []) = set [] \<union> {oid}"
    by auto
next
  fix a xs
  assume "ref \<in> set xs \<Longrightarrow> set (insert_after oid (Some ref) xs) = set xs \<union> {oid}"
    and "ref \<in> set (a#xs)"
  thus "set (insert_after oid (Some ref) (a#xs)) = set (a#xs) \<union> {oid}"
    by(cases "a = ref", auto simp add: insert_commute sup_commute)
qed   
      
lemma insert_after_nonex [simp]:
  assumes "ref \<notin> set xs"
  shows "insert_after oid (Some ref) xs = xs"
using assms proof(induction xs)
  show "insert_after oid (Some ref) [] = []"
    by simp
next
  fix a xs
  assume "ref \<notin> set xs \<Longrightarrow> insert_after oid (Some ref) xs = xs"
    and "ref \<notin> set (a#xs)"
  thus "insert_after oid (Some ref) (a#xs) = a#xs"
    by(cases "a = ref", auto simp add: insert_commute sup_commute)
qed

lemma list_greater_non_memb:
  fixes oid :: "'oid::{linorder}"
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> x < oid"
    and "oid \<in> set xs"
  shows "False"
using assms by blast  

lemma insert_after_distinct [intro]:
  fixes oid :: "'oid::{linorder}"
  assumes 1: "distinct xs"
    and 2: "\<And>x. x \<in> set xs \<Longrightarrow> x < oid"
    and 3: "ref = Some r \<longrightarrow> r < oid"
  shows "distinct (insert_after oid ref xs)"
using 1 2 proof(induction xs)
  show "distinct (insert_after oid ref [])"
    by(cases ref, auto)
next
  fix a xs
  assume IH: "distinct xs \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> x < oid) \<Longrightarrow> distinct (insert_after oid ref xs)"
    and D: "distinct (a#xs)"
    and L: "\<And>x. x \<in> set (a#xs) \<Longrightarrow> x < oid"
  show "distinct (insert_after oid ref (a#xs))"
  proof(cases "ref")
    assume "ref = None"
    thus "distinct (insert_after oid ref (a#xs))"
      using D L by auto
  next
    fix id
    assume S: "ref = Some id"
    {
      assume EQ: "a = id"
      hence "id \<noteq> oid"
        using D L by auto
      moreover have "id \<notin> set xs"
        using D EQ by auto
      moreover have "oid \<notin> set xs"
        using L by auto
      ultimately have "id \<noteq> oid \<and> id \<notin> set xs \<and> oid \<notin> set xs \<and> distinct xs"
        using D by auto
    }
    note T = this
    {
      assume NEQ: "a \<noteq> id"
      have 0: "a \<notin> set (insert_after oid (Some id) xs)"
        using D L by(metis distinct.simps insert_after.simps insert_after_none insert_after_nonex
            insert_after_set insert_iff list.set not_less_iff_gr_or_eq)
      have 1: "distinct xs"
        using D by auto
      have "\<And>x. x \<in> set xs \<Longrightarrow> x < oid"
        using L by auto
      hence "distinct (insert_after oid (Some id) xs)"
        using S IH[OF 1] by blast
      hence "a \<notin> set (insert_after oid (Some id) xs) \<and> distinct (insert_after oid (Some id) xs)"
        using 0 by auto
    }
    from this S T show "distinct (insert_after oid ref (a # xs))"
      by clarsimp
  qed
qed

lemma list_oid_subset [simp]:
  assumes "list_spec op_list"
  shows "set (list_spec.ins_list op_list) \<subseteq> set (map fst op_list)"
using assms proof(induction op_list rule: List.rev_induct)
  show "set (list_spec.ins_list []) \<subseteq> set (map fst [])"
    by(auto simp add: list_spec.ins_list_def[OF list_spec_NilI] interp_list_def)
next
  fix x and xs :: "('a \<times> 'a list_op) list"
  assume "list_spec xs \<Longrightarrow> set (list_spec.ins_list xs) \<subseteq> set (map fst xs)"
    and S: "list_spec (xs@[x])"
  hence IH: "set (list_spec.ins_list xs) \<subseteq> set (map fst xs)"
    by blast
  obtain id oper where P: "x = (id, oper)"
    by fastforce
  show "set (list_spec.ins_list (xs@[x])) \<subseteq> set (map fst (xs@[x]))"
  proof(cases oper)
    fix id'
    assume I: "oper = InsertAfter id'"
    {
      fix e
      assume 1: "e \<in> set (list_spec.ins_list (xs @ [(id, InsertAfter id')]))"
        and 2: "e \<notin> fst ` set xs"
      have 3: "list_spec (xs @ [(id, InsertAfter id')])"
        using S I P by auto
      obtain f op' where F: "foldl interp ([], {}) xs = (f, op')"
        by fastforce
      hence 4: "e \<in> set (insert_after id id' f)"
        using 1 2 3 by(clarsimp simp add: list_spec.ins_list_def interp_list_def)
      have "e = id"
      proof(cases id')
        assume "id' = None"
        thus "e = id"
          using 2 4 F IH S by(metis contra_subsetD fst_conv image_set insert_after.simps
              interp_list_def list_spec.ins_list_def list_spec_rm_last set_ConsD)
      next
        fix a
        assume "id' = Some a"
        show "e = id"
        proof(cases "a \<in> set f")
          assume "a \<in> set f"
          show "e = id"
            using 2 3 4 IH F by(metis \<open>a \<in> set f\<close> \<open>id' = Some a\<close> contra_subsetD fst_conv image_set
                insert_after.simps insert_after_none insert_after_set interp_list_def
                list_spec.ins_list_def list_spec_rm_last set_ConsD)
        next
          assume "a \<notin> set f"
          show "e = id"
            using 2 3 4 IH F by(metis \<open>a \<notin> set f\<close> \<open>id' = Some a\<close> contra_subsetD fst_conv image_set
                insert_after_nonex interp_list_def list_spec.ins_list_def list_spec_rm_last)
        qed
      qed 
    }
    thus "set (list_spec.ins_list (xs@[x])) \<subseteq> set (map fst (xs@[x]))"
      by(clarsimp simp add: P I)
  next
    fix id'
    assume "oper = Remove id'"
    from this and IH S show "set (list_spec.ins_list (xs@[x])) \<subseteq> set (map fst (xs@[x]))"
      apply(clarsimp simp add: list_spec.ins_list_def[OF S] interp_list_def)
      apply(clarsimp simp add: P)
      apply(metis contra_subsetD fst_conv interp.simps(2) interp_list_def list_spec.ins_list_def
          list_spec_rm_last old.prod.exhaust)
      done
  qed
qed

lemma last_op_greatest:
  assumes "list_spec (op_list @ [(oid, oper)])"
    and "x \<in> set (map fst op_list)"
    shows "x < oid"
using assms proof(induction op_list)
  assume "x \<in> set (map fst [])"
  thus "x < oid"
    by auto
next
  fix a op_list
  assume IH: "list_spec (op_list @ [(oid, oper)]) \<Longrightarrow> x \<in> set (map fst op_list) \<Longrightarrow> x < oid"
    and 2: "list_spec ((a#op_list) @ [(oid, oper)])"
    and 3: "x \<in> set (map fst (a#op_list))"
  hence L: "list_spec (op_list @ [(oid, oper)])"
    by(simp add: list_spec_def sorted_Cons)
  hence S: "sorted (map fst (op_list @ [(oid, oper)]))"
    by(auto simp add: list_spec_def)
  {
    fix x
    assume A: "x \<in> set (map fst op_list @ [oid])"
    hence "fst a < x"
      using S 2 by(cases a, clarsimp simp add: list_spec_def) (metis A le_neq_trans sorted_Cons)
  }
  note T = this
  have "x = fst a \<or> x \<in> set (map fst op_list)"
    using 3 by auto
  thus "x < oid"
  proof
    assume "x = fst a"
    thus "x < oid"
      using T by auto
  next
    assume "x \<in> set (map fst op_list)"
    thus "x < oid"
      using IH L by auto
  qed
qed

lemma list_distinct:
  assumes "list_spec op_list"
  shows "distinct (list_spec.ins_list op_list)"
  using assms apply (induct op_list rule: rev_induct)
  apply(simp add: list_spec.ins_list_def interp_list_def)
  apply(frule list_spec_rm_last, clarsimp)
  apply(case_tac b, clarsimp)
  apply(subgoal_tac "\<forall>x\<in>set (list_spec.ins_list xs). x < a") prefer 2
  using last_op_greatest list_oid_subset apply blast
  apply(subgoal_tac "distinct (insert_after a x1 (list_spec.ins_list xs))") prefer 2
  apply(metis insert_after.simps(2) insert_after_distinct last_in_set)
  apply(simp add: list_spec.ins_list_def interp_list_def)
  apply(metis Pair_inject interp.simps(1) prod.collapse)
  apply(simp add: list_spec.ins_list_def interp_list_def)
  apply(metis Pair_inject interp.simps(2) prod.collapse)
  done

lemma suffix_eq_distinct_list:
  assumes "ys@suf1 = xs"
      and "ys@suf2 = xs"
    shows "suf1 = suf2"
using assms by(induction xs arbitrary: suf1 suf2 rule: rev_induct, simp) (metis append_eq_append_conv)

lemma distinct_list_split:
  assumes "distinct xs"
    and "xs = xa @ x # ya"
    and "xs = xb @ x # yb"
  shows "xa = xb \<and> ya = yb"
  using assms apply(induction xs arbitrary: xa xb x, simp)
  apply(case_tac xa; case_tac xb; clarsimp)
  done

lemma list_order_trans:
  assumes "list_spec op_list"
    and "list_spec.list_order op_list x y"
    and "list_spec.list_order op_list y z"
  shows "list_spec.list_order op_list x z"
  using assms apply -
  apply(subgoal_tac "\<exists>ws xs ys zs. list_spec.ins_list op_list = ws@[x]@xs@[y]@ys@[z]@zs")
   apply(metis append.assoc list_spec.list_orderI)
  apply(clarsimp simp add: list_spec.list_order_def)
  apply(subgoal_tac "distinct (list_spec.ins_list op_list)") prefer 2
  using assms(1) list_distinct apply blast    
  apply(subgoal_tac "zs = ysa @ z # zsa") prefer 2
  apply(frule_tac xa="xs @ x # ys" and xb=xsa and x=y and ya=zs
    and yb="ysa @ z # zsa" in distinct_list_split, simp, simp, simp)
  apply(rule_tac x=xs in exI, rule_tac x=ys in exI)
  apply(rule_tac x=ysa in exI, rule_tac x=zsa in exI, simp)
  done

lemma insert_somewhere:
  assumes "ref = None \<or> (ref = Some r \<and> r \<in> set list)"
  shows "\<exists>xs ys. list = xs@ys \<and> insert_after oid ref list = xs @ oid # ys"
  using assms apply(induction list, simp)
  apply(case_tac ref, force)
  apply(case_tac "a=aa")
  apply(rule_tac x="[aa]" in exI, rule_tac x=list in exI, simp)
  apply(subgoal_tac "aa \<in> set list", simp) prefer 2 apply simp
  apply(erule exE)+
  apply(rule_tac x="a#xs" in exI, rule_tac x=ys in exI, force)
  done

lemma insert_first_part:
  assumes "ref = None \<or> (ref = Some r \<and> r \<in> set xs)"
  shows "insert_after oid ref (xs @ ys) = (insert_after oid ref xs) @ ys"
  using assms
  apply(induction ys rule: rev_induct, simp, simp)
  apply(induction xs, simp)
  apply(case_tac ref, force)
  apply(case_tac "a=aa", simp_all)
  done

lemma insert_second_part:
  assumes "ref = Some r"
    and "r \<notin> set xs"
    and "r \<in> set ys"
  shows "insert_after oid ref (xs @ ys) = xs @ (insert_after oid ref ys)"
  using assms
  apply(induction xs, simp)
  apply(subgoal_tac "a \<noteq> r", simp, force)
  done

lemma insert_twice:
  assumes "list_spec (before @ (x1, InsertAfter r1) # after @ [(x2, InsertAfter r2)])"
    and   "list_spec (before @                        after @ [(x2, InsertAfter r2)])"
    and "list_spec.ins_list (before @                        after) = xs @      zs"
    and "list_spec.ins_list (before @ (x1, InsertAfter r1) # after) = xs @ ys @ zs"
  shows "\<exists>xsa ysa zsa.
    list_spec.ins_list (before @                        after @ [(x2, InsertAfter r2)]) = xsa @       zsa \<and>
    list_spec.ins_list (before @ (x1, InsertAfter r1) # after @ [(x2, InsertAfter r2)]) = xsa @ ysa @ zsa"
  using assms apply -
  apply(subgoal_tac "list_spec (before @ after)") prefer 2
  using list_spec_rm_last apply force
  apply(subgoal_tac "list_spec (before @ (x1, InsertAfter r1) # after)") prefer 2
  using list_spec_rm_last apply force
  apply(simp add: list_spec.ins_list_def interp_list_def)
  apply(case_tac r2)
  apply(metis fstI interp.simps(1) prod.collapse insert_first_part)
  apply(case_tac "a \<in> set xs")
  apply(metis fstI interp.simps(1) prod.collapse insert_first_part)
  apply(case_tac "a \<in> set ys")
  apply(rule_tac x=xs in exI)
  apply(rule_tac x="insert_after x2 r2 ys" in exI)
  apply(rule_tac x=zs in exI)
  apply(rule conjI)
  apply(subgoal_tac "a \<notin> set zs")
  apply(metis UnE insert_after_nonex interp.simps(1) prod.collapse set_append)
  using assms(4) distinct_append list.simps(15) list_distinct apply force
  apply(metis append_eq_append_conv fstI insert_after_nonex insert_first_part
    insert_second_part insert_somewhere interp.simps(1) not_Cons_self2 prod.collapse)
  apply(case_tac "a \<in> set zs")
  apply(rule_tac x=xs in exI)
  apply(rule_tac x=ys in exI)
  apply(rule_tac x="insert_after x2 r2 zs" in exI)
  apply(metis insert_second_part Un_iff fstI interp.simps(1) prod.collapse set_append)
  apply(metis (no_types, lifting) insert_after_nonex UnE interp.simps(1) prod.collapse set_append)
  done

lemma insert_preserves_order:
  assumes "list_spec op_list" and "list_spec rest"
    and "rest = before @ after"
    and "op_list = before @ (oid, InsertAfter ref) # after"
  shows "\<exists>xs ys zs. list_spec.ins_list rest    = xs @      zs \<and>
                    list_spec.ins_list op_list = xs @ ys @ zs"
  using assms
  apply(induction after arbitrary: rest op_list rule: rev_induct)
   apply clarsimp
   apply(case_tac "ref")
    apply clarsimp
    apply(rule_tac x="[]" in exI, rule_tac x="[oid]" in exI, rule_tac x="list_spec.ins_list before" in exI)
    apply(clarsimp simp add: list_spec.ins_list_def interp_list_def)
    apply(metis eq_fst_iff insert_after.simps(1) interp.simps(1))
    apply(case_tac "a \<in> set (list_spec.ins_list before)")
     apply(simp add: list_spec.ins_list_def interp_list_def)
     apply(frule_tac oid="oid" in insert_somewhere[OF disjI2, OF conjI], assumption)
     apply(erule exE)+
     apply(rule_tac x="xs" in exI, rule_tac x="[oid]" in exI, rule_tac x="ys" in exI)
     apply(metis append_Cons append_Nil fst_conv interp.simps(1) old.prod.exhaust)
    apply clarsimp
    apply(frule_tac oid="oid" in insert_after_nonex)
    apply(rule_tac x="list_spec.ins_list before" in exI, rule_tac x="[]" in exI, rule_tac x="[]" in exI)
    apply clarsimp
  apply(clarsimp simp add: list_spec.ins_list_def)
    apply(rule arg_cong[where f="fst"])
    apply(clarsimp simp add: interp_list_def)
    apply(subgoal_tac "\<exists>e. foldl interp ([], {}) before = (insert_after oid (Some a) (fst (foldl interp ([], {}) before)), e)")
    apply clarsimp
    apply(metis insert_after_nonex interp.simps(1))
   apply(simp add: eq_fst_iff)
    apply(metis prod.collapse)
  apply clarsimp
  apply(erule_tac x="before @ xs" in meta_allE)
  apply(erule_tac x="before @ (oid, InsertAfter ref) # xs" in meta_allE)
  apply clarsimp
  apply(subgoal_tac "list_spec (before @ (oid, InsertAfter ref) # xs)")
   apply clarsimp
  apply(subgoal_tac "list_spec (before @ xs)")
    apply clarsimp
    apply(case_tac b; clarsimp simp add: insert_twice)
    apply(rule_tac x="xsa" in exI, rule_tac x="ys" in exI, rule_tac x="zs" in exI)
    apply(clarsimp simp add: list_spec.ins_list_def interp_list_def)
    apply(rule conjI)
     apply(metis eq_fst_iff interp.simps)
    apply(subgoal_tac "\<exists>e. foldl interp (interp (foldl interp ([], {}) before) (oid, InsertAfter ref)) xs = (xsa @ ys @ zs, e)")
     apply clarsimp
    apply(metis eq_fst_iff)
   apply(metis append.assoc list_spec_rm_last)
  apply(metis append_Cons append_assoc list_spec_rm_last)
  done
  
lemma distinct_fst:
  assumes "distinct (map fst A)"
  shows "distinct A"
  using assms by(induction A, auto)
    
lemma sorted_fst:
  assumes "sorted (map fst A)"
    and "distinct (map fst A)"
  shows "sorted A"
  using assms
  apply(induction A)
   apply force
  apply(case_tac "a"; clarsimp)
  apply(subgoal_tac "sorted (map fst A)")
    apply(rule sorted.intros; clarsimp)
   apply(metis fst_conv image_set le_neq_trans rev_image_eqI sorted_Cons)
  using sorted_Cons by auto
    
lemma subset_distinct_le:
  assumes "set A \<subseteq> set B" and "distinct A" and "distinct B"
  shows "length A \<le> length B"
  using assms
  apply(induction B arbitrary: A)
   apply clarsimp
  apply clarsimp
  apply(case_tac "a \<in> set A")
   apply(erule_tac x="List.remove1 a A" in meta_allE)
   apply clarsimp
   apply(simp add: length_remove1 subset_insert_iff)
  apply(erule_tac x="A" in meta_allE, clarsimp)
    by(simp add: subset_insert)
      
lemma set_subset_length_eq:
  assumes "set A \<subseteq> set B" and "length B \<le> length A" and "distinct A" and "distinct B"
  shows "set A = set B"
  using assms
    apply -
  apply(frule subset_distinct_le, assumption, assumption)
  apply(rule card_subset_eq, force, force)
  apply(simp add: distinct_card)
  done
    
lemma length_diff_Suc_exists:
  assumes "length xs - length ys = Suc m"
    and "set ys \<subseteq> set xs"
    and "distinct ys" and "distinct xs"
  shows "\<exists>e. e \<in> set xs \<and> e \<notin> set ys"
  using assms
  apply(induction xs arbitrary: ys, clarsimp)
  apply clarsimp
  apply(case_tac "a \<in> set ys")
   apply(erule_tac x="List.remove1 a ys" in meta_allE)
   apply(subgoal_tac "length xs - length (remove1 a ys) = Suc m")
    prefer 2
    apply(metis Suc_diff_eq_diff_pred length_pos_if_in_set length_remove1)
   apply clarsimp
   apply(subgoal_tac "set ys - {a} \<subseteq> set xs")
    prefer 2
    apply blast
   apply clarsimp
   apply force
  apply blast
  done
    
lemma distinct_map_fst_remove1:
  assumes "distinct (map fst xs)"
  shows "distinct (map fst (remove1 x xs))"
  using assms
  apply(induction xs, clarsimp)
  apply(subgoal_tac "distinct (map fst xs)")
   prefer 2
   apply force
  apply clarsimp
  apply(metis fst_conv image_eqI notin_set_remove1)
  done
    
lemma list_spec_remove1:
  assumes "list_spec xs"
  shows "list_spec (remove1 x xs)"
  using assms apply(clarsimp simp: list_spec_def)
  using sorted_map_remove1 distinct_map_fst_remove1
  apply(metis notin_set_remove1)
  done
    
lemma app_length_lt_exists:
  assumes "xsa @ zsa = xs @ ys"
    and "length xsa \<le> length xs"
  shows "xsa@(drop (length xsa) xs) = xs"
  using assms
  apply(induction xsa arbitrary: xs zsa ys, clarsimp)
  apply clarsimp
  apply(metis append_Cons append_eq_append_conv_if append_take_drop_id length_Cons)
  done
    
lemma app_length_lt_exists':
  assumes "xsa @ zsa = xs @ ys"
    and "length xsa \<le> length xs"
  shows "\<exists>zs. xsa@zs = xs"
  using assms app_length_lt_exists by blast

lemma diff_tomb:
  shows "fst (foldl interp (ys, A) xs) = fst (foldl interp (ys, B) xs)"
  apply (induct xs rule: rev_induct)
   apply force
  apply (case_tac x)
  apply clarsimp
  apply (case_tac ba)
   apply clarsimp
   apply (case_tac "foldl interp (ys, A) xs"; case_tac "foldl interp (ys, B) xs")
    apply clarsimp
  apply clarsimp
  apply (case_tac "foldl interp (ys, A) xs"; case_tac "foldl interp (ys, B) xs")
  apply clarsimp
    done
    
    
lemma diff_tomb_Remove:
  shows "fst (interp_list (remove1 (a, Remove x) xs)) = fst (interp_list xs)"
  apply (induct xs rule: rev_induct)
   apply (clarsimp simp add: interp_list_def)
  apply safe
  apply (case_tac b)
   apply clarsimp
   apply (clarsimp simp add: interp_list_def)
   apply(case_tac "foldl interp ([], {}) (remove1 (a, Remove x) xs)"; clarsimp)
   apply(case_tac "foldl interp ([], {}) xs"; clarsimp)
   apply(case_tac "foldl interp ([], {}) (remove1 (a, Remove x) (xs @ [(aa, InsertAfter x1)]))"; clarsimp)
   apply(case_tac "(a, Remove x) \<in> set xs")
    apply(simp add: remove1_append)+
    apply (clarsimp simp add: interp_list_def)
   apply(case_tac "foldl interp ([], {}) (remove1 (a, Remove x) xs)"; clarsimp)
  apply(case_tac "foldl interp ([], {}) xs"; clarsimp)
  done
    
lemma
  assumes "list_spec A" and "list_spec B"
    and "set A \<subseteq> set B"
    and "list_spec.list_order A x y"
  shows "list_spec.list_order B x y"
  using assms
  apply(induction rule: measure_induct_rule[where f="\<lambda>x. (length x - length A)"])
  apply(case_tac "length xa - length A")
   apply(subgoal_tac "set A = set xa")
    apply(clarsimp simp add: list_spec_def)
    apply(metis distinct_map map_sorted_distinct_set_unique sup_idem)
   apply(rule set_subset_length_eq, assumption, force)
  using distinct_fst list_spec_def apply blast
  using distinct_fst list_spec_def apply blast
  apply clarsimp
  apply(subgoal_tac "\<exists>e. e \<in> set xa \<and> e \<notin> set A")
   prefer 2
   apply(rule length_diff_Suc_exists, force, force)
  using distinct_fst list_spec_def apply blast
  using distinct_fst list_spec_def apply blast
  apply(erule exE, erule conjE)
  apply(erule_tac x="List.remove1 e xa" in meta_allE)
  apply(subgoal_tac "length (remove1 e xa) - length A < Suc nat")
   prefer 2
   apply(metis (no_types, lifting) diff_Suc_1 diff_commute length_remove1 less_Suc_eq)
  apply clarsimp
  apply(frule_tac x="(a, b)" in list_spec_remove1) back
  apply clarsimp
  apply(subgoal_tac "set A \<subseteq> set (remove1 (a, b) xa)")
   prefer 2
   apply(metis (no_types, lifting) in_set_remove1 subset_iff)
  apply clarsimp
  apply(case_tac "b"; clarsimp simp add: list_spec.list_order_def list_spec.ins_list_def)
   apply(subgoal_tac "\<exists>e. (interp_list (remove1 (a, InsertAfter x1) xa)) = (xs @ x # ys @ y # zs, e)")
    prefer 2 apply(metis prod.collapse)
   apply clarsimp
   apply(subgoal_tac "\<exists>ps ss. xa = ps@[(a, InsertAfter x1)]@ss \<and> (a, InsertAfter x1) \<notin> set ps")
    prefer 2 using split_list_first apply fastforce
   apply clarsimp
   apply(subgoal_tac "interp_list (remove1 (a, InsertAfter x1) (ps @ (a, InsertAfter x1) # ss)) = interp_list (ps @ ss)")
    prefer 2
    apply(simp add: remove1_append)
   apply clarsimp
   apply(frule_tac op_list="ps @ (a, InsertAfter x1) # ss" and rest="ps @ ss" in insert_preserves_order)
      apply(simp add: remove1_append)
     apply(rule refl)+
   apply clarsimp
   apply(subgoal_tac "xsa @ zsa = xs @ x # ys @ y # zs")
    prefer 2
    apply(simp add: list_spec.ins_list_def remove1_append)
   apply clarsimp
   apply(case_tac "length xsa \<le> length xs")
    apply(subgoal_tac "\<exists>ts. xsa@ts = xs")
     prefer 2
  using app_length_lt_exists apply blast
    apply clarsimp
    apply(metis append.assoc list_spec.ins_list_def)
   apply(case_tac "length xsa \<le> length (xs@x#ys)")
    apply(subgoal_tac "\<exists>us. xsa@us = xs@x#ys")
     prefer 2
     apply(simp add: app_length_lt_exists')
    apply clarsimp
    apply(rule_tac x="xs" in exI, rule_tac x="(drop (Suc (length xs)) xsa)@ysa@us" in exI, rule_tac x="zs" in exI)
    apply clarsimp
    apply(subgoal_tac "fst (interp_list (ps @ (a, InsertAfter x1) # ss)) = xsa @ ysa @ zsa")
     prefer 2
     apply(simp add: list_spec.ins_list_def)
    apply clarsimp
    apply(subgoal_tac "xs @ x # drop (Suc (length xs)) xsa = xsa")
     prefer 2
     apply(metis append_eq_append_conv_if id_take_nth_drop linorder_not_less nth_append nth_append_length)
    apply(subgoal_tac "us @ y # zs = zsa")
     apply force
    apply(metis append_Cons append_assoc suffix_eq_distinct_list)
   apply(rule_tac x="xs" in exI, rule_tac x="ys" in exI, rule_tac x="(drop (Suc (Suc (length xs + length ys))) xsa)@ysa@zsa" in exI)
   apply clarsimp
   apply(subgoal_tac "fst (interp_list (ps @ (a, InsertAfter x1) # ss)) = xsa @ ysa @ zsa")
     prefer 2
    apply(simp add: list_spec.ins_list_def)
   apply(subgoal_tac "xs @ x # ys @ y # drop (Suc (Suc (length xs + length ys))) xsa = xsa")
    prefer 2
    apply(insert app_length_lt_exists)[1]
    apply(erule_tac x="xs @ x # ys @ [y]" in meta_allE)
    apply(erule_tac x="zs" in meta_allE)
    apply(erule_tac x="xsa" in meta_allE)
    apply(erule_tac x="zsa" in meta_allE)
    apply(subgoal_tac "length (xs @ x # ys @ [y]) \<le> length xsa")
     prefer 2
     apply clarsimp
    apply force
    apply force
    apply (rule_tac x=xs in exI)
  apply (rule_tac x=ys in exI)
    apply (rule_tac x=zs in exI)
    apply (subgoal_tac "fst (interp_list (remove1 (a, Remove x2) xa)) = fst (interp_list xa)")
   apply force
    apply(rule diff_tomb_Remove) 
  done
    
lemma insert_after_nth_oid:
  assumes "distinct ys"
       and "n < length ys"
     shows "insert_after oid (Some (ys ! n)) ys ! Suc n = oid"
  using assms
  apply(induction ys arbitrary: n)
   apply clarsimp
  apply clarsimp
  apply safe
   apply(subgoal_tac "n = 0")
    prefer 2
    apply(metis distinct.simps(2) length_Cons nth_Cons_0 nth_eq_iff_index_eq zero_less_Suc)
   apply clarsimp
  apply(subgoal_tac "\<exists>m. n = Suc m")
   prefer 2
   apply(metis not0_implies_Suc nth_Cons')
  apply clarsimp
  done
    
lemma ins_list_correct_position_insert:
  assumes "list_spec (xs@[make_insert ys oid m])"
    and "list_spec.ins_list xs = ys"
  shows "list_spec.ins_list (xs@[make_insert ys oid m]) ! min (length ys) m = oid"
  using assms
  apply -
  apply(clarsimp simp add: list_spec.ins_list_def interp_list_def)
  apply(case_tac "(interp (foldl interp ([], {}) xs) (make_insert (list_spec.ins_list xs) oid m))"; clarsimp)
  apply(case_tac "m"; clarsimp)
   apply(case_tac "foldl interp ([], {}) xs"; clarsimp)
  apply(case_tac "foldl interp ([], {}) xs"; clarsimp)
  apply(case_tac "min (length (list_spec.ins_list xs)) (Suc nat) = Suc nat")
    apply clarsimp
   apply(subgoal_tac "min (length (list_spec.ins_list xs) - Suc 0) nat = nat")
    prefer 2
    apply linarith
    apply(case_tac "(list_spec.ins_list xs)")
    apply clarsimp
    apply clarsimp
   apply(subgoal_tac "aa = ys")
    prefer 2
    apply(subgoal_tac "list_spec xs")
     prefer 2
    using list_spec_rm_last apply blast
      apply(clarsimp simp add: list_spec.ins_list_def interp_list_def)
     apply clarsimp
     prefer 2
     apply(subgoal_tac "min (length (list_spec.ins_list xs)) (Suc nat) = length (list_spec.ins_list xs)")
    prefer 2
      apply force
     apply(subgoal_tac "min (length (list_spec.ins_list xs) - Suc 0) nat = length (list_spec.ins_list xs) - Suc 0")
      prefer 2
      apply force
     apply clarsimp
   apply(subgoal_tac "aa = ys")
    prefer 2
    apply(subgoal_tac "list_spec xs")
     prefer 2
    using list_spec_rm_last apply blast
      apply(clarsimp simp add: list_spec.ins_list_def interp_list_def)
     apply clarsimp
     prefer 2
     apply safe
      prefer 2
      apply(subgoal_tac "\<exists>m. nat = Suc m")
       prefer 2
       apply(metis Suc_pred not_gr_zero nth_Cons')
      apply clarsimp
     apply(rule insert_after_nth_oid)
    apply(metis distinct.simps(1) distinct_length_2_or_more list.exhaust list_distinct list_spec_rm_last)
      apply force
     apply(subgoal_tac "nat = 0")
      apply clarsimp
     prefer 2
      apply(case_tac "(list_spec.ins_list xs)")
      apply clarsimp
     apply clarsimp
     apply safe
      apply(subgoal_tac "length list = 0")
       apply clarsimp
      apply(metis distinct.simps(2) list_distinct list_spec_rm_last nth_equal_first_eq order_refl)
     apply(subgoal_tac "\<exists>m. length list = Suc m")
      apply clarsimp
     apply(rule insert_after_nth_oid)
    using list_distinct list_spec_rm_last apply fastforce
      apply force
     apply(metis Suc_diff_1 not_gr_zero nth_Cons')
    apply(subgoal_tac "distinct (ab#list)")
     apply (metis distinct_conv_nth length_Cons length_greater_0_conv lessI list.simps(3) min_Suc_Suc min_less_iff_conj nth_Cons_0)
    apply(metis list_distinct list_spec_rm_last)
    done

end
