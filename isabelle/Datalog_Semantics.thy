theory
  Datalog_Semantics
imports
  Main
  "~~/src/HOL/Library/Monad_Syntax"
begin

subsection \<open>Semantics of Datalog rules\<close>

datatype 'val dterm =
  Var "string" |
  Val "'val"

datatype 'val atom =
  Match "string" "'val dterm list" |
  Equal "'val dterm" "'val dterm"

record 'val rule =
  rule_rel    :: "string"
  rule_params :: "'val dterm list"
  rule_atoms  :: "'val atom set"

type_synonym 'val fact = "string \<times> 'val list"
type_synonym 'val database = "'val fact set"
type_synonym 'val valuation = "string \<Rightarrow> 'val option"

definition subst_term :: "'val dterm \<Rightarrow> 'val valuation \<Rightarrow> 'val option" where
  "subst_term term mapping \<equiv> case term of
     Val x \<Rightarrow> Some x |
     Var v \<Rightarrow> mapping v"

fun subst_vars :: "'val dterm list \<Rightarrow> 'val valuation \<Rightarrow> 'val list option" where
  "subst_vars [] mapping = Some []" |
  "subst_vars (term#terms) mapping = do {
     xs \<leftarrow> subst_vars terms mapping;
     x  \<leftarrow> subst_term term mapping;
     Some (x#xs)
   }"

fun match_vars :: "'val dterm list \<Rightarrow> 'val list \<Rightarrow> 'val valuation \<Rightarrow> bool" where
  "match_vars [] [] mapping = True" |
  "match_vars (term # terms) (val # vals) mapping =
     (subst_term term mapping = Some val \<and> match_vars terms vals mapping)" |
  "match_vars _ _ _ = False"

definition match_atom :: "'val database \<Rightarrow> 'val atom \<Rightarrow> 'val valuation \<Rightarrow> bool" where
  "match_atom db atom mapping \<equiv> case atom of
     Match rel vars \<Rightarrow> \<exists>fact \<in> db. fst fact = rel \<and> match_vars vars (snd fact) mapping |
     Equal v1  v2   \<Rightarrow> subst_term v1 mapping = subst_term v2 mapping"

definition deduce_rule :: "'val database \<Rightarrow> 'val rule \<Rightarrow> 'val fact \<Rightarrow> bool" where
  "deduce_rule db rule derived \<equiv> \<exists>vals valuation. derived = (rule_rel rule, vals) \<and>
     subst_vars (rule_params rule) valuation = Some vals \<and>
     (\<forall>atom \<in> rule_atoms rule. match_atom db atom valuation)"

definition deduce_step :: "'val database \<Rightarrow> 'val rule set \<Rightarrow> 'val database" where
  "deduce_step db rules \<equiv> db \<union> {derived. \<exists>rule \<in> rules. deduce_rule db rule derived}"

inductive fixpoint :: "'val database \<Rightarrow> 'val rule set \<Rightarrow> 'val database \<Rightarrow> bool" where
  "fixpoint db rules db" |
  "\<lbrakk> fixpoint db rules prev; deduce_step prev rules = next \<rbrakk> \<Longrightarrow> fixpoint db rules next"

(*
Alternative definition that fails at "Proving the simplification rules ...":
inductive fixpoint :: "'val database \<Rightarrow> 'val rule set \<Rightarrow> 'val fact \<Rightarrow> bool" where
  "\<lbrakk> fact \<in> db \<rbrakk> \<Longrightarrow> fixpoint db rules fact" |
  "\<lbrakk> rule \<in> rules; deduce_rule {f. fixpoint db rules f} rule derived \<rbrakk> \<Longrightarrow> fixpoint db rules derived"
*)

(*fun satisfies :: "'val database \<Rightarrow> 'val atom \<Rightarrow> bool" (infix "\<Turnstile>" 60) where
  "db \<Turnstile> Match rel vars = (match_atom db rel vars \<noteq> {})"*)

end
