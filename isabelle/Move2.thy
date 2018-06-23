theory Move2
  imports Main
begin

datatype 'oid node_ref = Root | Ref 'oid

datatype ('oid, 'key, 'val) tree_op =
  MakeChild "'oid node_ref" 'key |   (* MakeChild obj key: creates a new child node at obj[key] *)
  Move "'oid node_ref" 'key 'oid |   (* Move obj key ref: moves node with ID ref to obj[key] *)
  Assign "'oid node_ref" 'key 'val | (* Assign obj key val: sets obj[key] = val to primitive value *)
  Remove 'oid                        (* Remove ref: removes/overwrites prior assignment *)

datatype ('oid, 'val) val = Child 'oid | Val 'val

type_synonym ('oid, 'key, 'val) tree_state = "('oid \<times> 'oid node_ref \<times> 'key \<times> ('oid, 'val) val) set"


text \<open>\isa{ancestor E anc child} is true if \isa{anc} is an ancestor of \isa{child}
in the element relation \isa{E}.\<close>

inductive ancestor :: "('oid, 'key, 'val) tree_state \<Rightarrow> 'oid node_ref \<Rightarrow> 'oid \<Rightarrow> bool" where
  "\<lbrakk>(oid, obj, key, Child child) \<in> E\<rbrakk> \<Longrightarrow> ancestor E obj child" |
  "\<lbrakk>ancestor E anc obj; (oid, Ref obj, key, Child child) \<in> E\<rbrakk> \<Longrightarrow> ancestor E anc child"

definition do_move :: "('oid, 'key, 'val) tree_state \<Rightarrow> 'oid \<Rightarrow> 'oid node_ref \<Rightarrow> 'key \<Rightarrow> 'oid \<Rightarrow>
                       ('oid, 'key, 'val) tree_state" where
  "do_move E oid obj key ref \<equiv>
     { e \<in> E. snd (snd (snd e)) \<noteq> Child ref } \<union> { (oid, obj, key, Child ref) }"

(* Like tree_spec, but move operation is unconditional (so cycles may occur).
   Using this to practise reasoning about the interpretation. *)
fun unconditional_spec :: "('oid, 'key, 'val) tree_state \<Rightarrow> ('oid \<times> ('oid, 'key, 'val) tree_op) \<Rightarrow>
                           ('oid, 'key, 'val) tree_state" where
  "unconditional_spec E (oid, MakeChild obj key) = E \<union> { (oid, obj, key, Child oid) }" |
  "unconditional_spec E (oid, Move obj key ref) = do_move E oid obj key ref" |
  "unconditional_spec E (oid, Assign obj key val) = E \<union> { (oid, obj, key, Val val) }" |
  "unconditional_spec E (oid, Remove ref) = { e \<in> E. fst e \<noteq> ref }"

definition unconditional_query ::
  "('oid::{linorder} \<times> ('oid, 'key, 'val) tree_op) set \<Rightarrow> ('oid, 'key, 'val) tree_state" where
  "unconditional_query ops \<equiv> {e.
     (\<exists>oid obj key ref. e = (oid, obj, key, Child ref) \<and>
           ((oid, MakeChild obj key) \<in> ops \<and> ref = oid \<or> (oid, Move obj key ref) \<in> ops) \<and>
           (\<nexists>i. (i, Remove oid) \<in> ops) \<and>
           (\<nexists>i. oid < i \<and> (\<exists>obj' key'. (i, Move obj' key' ref) \<in> ops))) \<or>
     (\<exists>oid obj key val. e = (oid, obj, key, Val val) \<and>
           (oid, Assign obj key val) \<in> ops \<and> (\<nexists>i. (i, Remove oid) \<in> ops))}"

(*
definition test_query :: "('oid::{linorder} \<times> ('oid, 'key, 'val) tree_op) set \<Rightarrow> 'val set" where
  "test_query ops \<equiv> {val. \<exists>oid obj key. (oid, Assign obj key val) \<in> ops}"

lemma set_comp_disj:
  shows "{x. P x \<or> x = y} = {x. P x} \<union> {y}"
  by blast

lemma test:
  shows "test_query (ops \<union> {(oid, Assign obj key val)}) = test_query ops \<union> {val}"
proof -
  obtain ops' where ops': "ops' = ops \<union> {(oid, Assign obj key val)}"
    by fastforce
  moreover have "\<And>v. (\<exists>oid obj key. (oid, Assign obj key v) \<in> ops) \<or> v = val \<longleftrightarrow>
                     (\<exists>oid obj key. (oid, Assign obj key v) \<in> ops')"
    using ops' by blast
  hence "{v. \<exists>oid obj key. (oid, Assign obj key v) \<in> ops'} =
         {v. (\<exists>oid obj key. (oid, Assign obj key v) \<in> ops) \<or> v = val}"
    by auto
  moreover have "... = {v. \<exists>oid obj key. (oid, Assign obj key v) \<in> ops} \<union> {val}"
    by blast
  ultimately show ?thesis
    using test_query_def by (metis (mono_tags, lifting))
qed*)

lemma unconditional_MakeChild:
  assumes "\<forall>i \<in> fst ` ops. i < oid"
  shows "unconditional_spec (unconditional_query ops) (oid, MakeChild obj key) =
         unconditional_query (ops \<union> {(oid, MakeChild obj key)})"
proof -
  obtain ops' where ops': "ops' = ops \<union> {(oid, MakeChild obj key)}"
    by fastforce
  obtain elem :: "'a \<times> 'a node_ref \<times> 'b \<times> ('a, 'c) val"
    where elem: "elem = (oid, obj, key, Child oid)"
    by fastforce
  have 1: "\<And>e. (\<exists>oid obj key ref. e = (oid, obj, key, Child ref) \<and>
           ((oid, MakeChild obj key) \<in> ops \<and> ref = oid \<or> (oid, Move obj key ref) \<in> ops)) \<or>
           e = elem \<longleftrightarrow>
       (\<exists>oid obj key ref. e = (oid, obj, key, Child ref) \<and>
           ((oid, MakeChild obj key) \<in> ops' \<and> ref = oid \<or> (oid, Move obj key ref) \<in> ops'))"
    using ops' elem by blast
  have 2: "\<And>e. (\<exists>oid obj key ref. e = (oid, obj, key, Child ref) \<and>
           (\<nexists>i. (i, Remove oid) \<in> ops) \<and>
           (\<nexists>i. oid < i \<and> (\<exists>obj' key'. (i, Move obj' key' ref) \<in> ops))) \<longleftrightarrow>
       (\<exists>oid obj key ref. e = (oid, obj, key, Child ref) \<and>
           (\<nexists>i. (i, Remove oid) \<in> ops') \<and>
           (\<nexists>i. oid < i \<and> (\<exists>obj' key'. (i, Move obj' key' ref) \<in> ops')))"
    by (simp add: ops')
  from 1 2 have "\<And>e. (\<exists>oid obj key ref. e = (oid, obj, key, Child ref) \<and>
           ((oid, MakeChild obj key) \<in> ops \<and> ref = oid \<or> (oid, Move obj key ref) \<in> ops) \<and>
           (\<nexists>i. (i, Remove oid) \<in> ops) \<and>
           (\<nexists>i. oid < i \<and> (\<exists>obj' key'. (i, Move obj' key' ref) \<in> ops))) \<or>
           e = (oid, obj, key, Child oid) \<longleftrightarrow>
       (\<exists>oid obj key ref. e = (oid, obj, key, Child ref) \<and>
           ((oid, MakeChild obj key) \<in> ops' \<and> ref = oid \<or> (oid, Move obj key ref) \<in> ops') \<and>
           (\<nexists>i. (i, Remove oid) \<in> ops') \<and>
           (\<nexists>i. oid < i \<and> (\<exists>obj' key'. (i, Move obj' key' ref) \<in> ops')))"
    sorry
  moreover have "\<And>e. (\<exists>oid obj key val. e = (oid, obj, key, Val val) \<and>
           (oid, Assign obj key val) \<in> ops \<and> (\<nexists>i. (i, Remove oid) \<in> ops)) \<longleftrightarrow>
           (\<exists>oid obj key val. e = (oid, obj, key, Val val) \<and>
           (oid, Assign obj key val) \<in> ops' \<and> (\<nexists>i. (i, Remove oid) \<in> ops'))"
    by (simp add: ops')
  ultimately have "\<And>e.
     (\<exists>oid obj key ref. e = (oid, obj, key, Child ref) \<and>
           ((oid, MakeChild obj key) \<in> ops \<and> ref = oid \<or> (oid, Move obj key ref) \<in> ops) \<and>
           (\<nexists>i. (i, Remove oid) \<in> ops) \<and>
           (\<nexists>i. oid < i \<and> (\<exists>obj' key'. (i, Move obj' key' ref) \<in> ops))) \<or>
     (\<exists>oid obj key val. e = (oid, obj, key, Val val) \<and>
           (oid, Assign obj key val) \<in> ops \<and> (\<nexists>i. (i, Remove oid) \<in> ops)) \<or>
     e = (oid, obj, key, Child oid) \<longleftrightarrow>
     (\<exists>oid obj key ref. e = (oid, obj, key, Child ref) \<and>
           ((oid, MakeChild obj key) \<in> ops' \<and> ref = oid \<or> (oid, Move obj key ref) \<in> ops') \<and>
           (\<nexists>i. (i, Remove oid) \<in> ops') \<and>
           (\<nexists>i. oid < i \<and> (\<exists>obj' key'. (i, Move obj' key' ref) \<in> ops'))) \<or>
     (\<exists>oid obj key val. e = (oid, obj, key, Val val) \<and>
           (oid, Assign obj key val) \<in> ops' \<and> (\<nexists>i. (i, Remove oid) \<in> ops'))"
    sorry
  hence "{e. (\<exists>oid obj key ref. e = (oid, obj, key, Child ref) \<and>
           ((oid, MakeChild obj key) \<in> ops \<and> ref = oid \<or> (oid, Move obj key ref) \<in> ops) \<and>
           (\<nexists>i. (i, Remove oid) \<in> ops) \<and>
           (\<nexists>i. oid < i \<and> (\<exists>obj' key'. (i, Move obj' key' ref) \<in> ops))) \<or>
     (\<exists>oid obj key val. e = (oid, obj, key, Val val) \<and>
           (oid, Assign obj key val) \<in> ops \<and> (\<nexists>i. (i, Remove oid) \<in> ops)) \<or>
     e = (oid, obj, key, Child oid)} =
     {e. (\<exists>oid obj key ref. e = (oid, obj, key, Child ref) \<and>
           ((oid, MakeChild obj key) \<in> ops' \<and> ref = oid \<or> (oid, Move obj key ref) \<in> ops') \<and>
           (\<nexists>i. (i, Remove oid) \<in> ops') \<and>
           (\<nexists>i. oid < i \<and> (\<exists>obj' key'. (i, Move obj' key' ref) \<in> ops'))) \<or>
     (\<exists>oid obj key val. e = (oid, obj, key, Val val) \<and>
           (oid, Assign obj key val) \<in> ops' \<and> (\<nexists>i. (i, Remove oid) \<in> ops'))}"
    by auto
  moreover have "{e. (\<exists>oid obj key ref. e = (oid, obj, key, Child ref) \<and>
           ((oid, MakeChild obj key) \<in> ops \<and> ref = oid \<or> (oid, Move obj key ref) \<in> ops) \<and>
           (\<nexists>i. (i, Remove oid) \<in> ops) \<and>
           (\<nexists>i. oid < i \<and> (\<exists>obj' key'. (i, Move obj' key' ref) \<in> ops))) \<or>
     (\<exists>oid obj key val. e = (oid, obj, key, Val val) \<and>
           (oid, Assign obj key val) \<in> ops \<and> (\<nexists>i. (i, Remove oid) \<in> ops)) \<or>
     e = (oid, obj, key, Child oid)} =
     {e. (\<exists>oid obj key ref. e = (oid, obj, key, Child ref) \<and>
           ((oid, MakeChild obj key) \<in> ops \<and> ref = oid \<or> (oid, Move obj key ref) \<in> ops) \<and>
           (\<nexists>i. (i, Remove oid) \<in> ops) \<and>
           (\<nexists>i. oid < i \<and> (\<exists>obj' key'. (i, Move obj' key' ref) \<in> ops))) \<or>
     (\<exists>oid obj key val. e = (oid, obj, key, Val val) \<and>
           (oid, Assign obj key val) \<in> ops \<and> (\<nexists>i. (i, Remove oid) \<in> ops))} \<union> {(oid, obj, key, Child oid)}"
    using unconditional_query_def by blast
  ultimately have "unconditional_query ops' = (unconditional_query ops) \<union> {(oid, obj, key, Child oid)}"
    using unconditional_query_def by (metis (mono_tags, lifting))
  moreover have "unconditional_spec (unconditional_query ops) (oid, MakeChild obj key) =
        (unconditional_query ops) \<union> {(oid, obj, key, Child oid)}"
    by simp
  ultimately show ?thesis
    by (simp add: ops')
qed

lemma unconditional_Move:
  assumes "\<forall>i \<in> fst ` ops. i < oid"
  shows "unconditional_spec (unconditional_query ops) (oid, Move obj key ref) =
         unconditional_query (ops \<union> {(oid, Move obj key ref)})"
  sorry

lemma unconditional_Assign:
  assumes "\<forall>i \<in> fst ` ops. i < oid"
  shows "unconditional_spec (unconditional_query ops) (oid, Assign obj key val) =
         unconditional_query (ops \<union> {(oid, Assign obj key val)})"
  sorry

lemma unconditional_Remove:
  assumes "\<forall>i \<in> fst ` ops. i < oid"
  shows "unconditional_spec (unconditional_query ops) (oid, Remove ref) =
         unconditional_query (ops \<union> {(oid, Remove ref)})"
  sorry


lemma unconditional_equiv:
  assumes "sorted (map fst ops)" and "distinct (map fst ops)"
  shows "foldl unconditional_spec {} ops = unconditional_query (set ops)"
using assms proof(induction ops rule: List.rev_induct, simp add: unconditional_query_def)
  case (snoc x xs)
  hence "foldl unconditional_spec {} xs = unconditional_query (set xs)"
    using distinct_butlast sorted_butlast by (simp add: sorted_append)
  moreover obtain oid oper where x_pair: "x = (oid, oper)"
    by fastforce
  hence id_max: "\<forall>i \<in> set (map fst xs). i < oid"
    using snoc by (metis disjoint_insert(1) distinct_append empty_set fst_conv less_le
      list.set(2) list.simps(8) list.simps(9) map_append singletonI sorted_append)
  moreover have "unconditional_spec (unconditional_query (set xs)) (oid, oper) =
                 unconditional_query (set xs \<union> {(oid, oper)})"
  proof(cases oper)
    case (MakeChild obj key)
    then show ?thesis using unconditional_MakeChild id_max by fastforce
  next
    case (Move obj key ref)
    then show ?thesis using unconditional_Move id_max by fastforce
  next
    case (Assign obj key val)
    then show ?thesis using unconditional_Assign id_max by fastforce
  next
    case (Remove ref)
    then show ?thesis using unconditional_Remove id_max by fastforce
  qed
  ultimately show ?case
    using x_pair by auto
qed


(* The sequential opset interpretation for a tree with move operation *)
fun tree_spec :: "('oid, 'key, 'val) tree_state \<Rightarrow> ('oid \<times> ('oid, 'key, 'val) tree_op) \<Rightarrow>
                  ('oid, 'key, 'val) tree_state" where
  "tree_spec E (oid, MakeChild obj key) = E \<union> { (oid, obj, key, Child oid) }" |
  "tree_spec E (oid, Move Root key ref) = do_move E oid Root key ref" |
  "tree_spec E (oid, Move (Ref obj) key ref) =
     (if ancestor E (Ref ref) obj then E else do_move E oid (Ref obj) key ref)" |
  "tree_spec E (oid, Assign obj key val) = E \<union> { (oid, obj, key, Val val) }" |
  "tree_spec E (oid, Remove ref) = { e \<in> E. fst e \<noteq> ref }"


end
