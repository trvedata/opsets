theory Datalog
  imports Main
begin

datatype ('oid, 'val) operation
  = MakeList
  | MakeMap
  | MakeVal "'val"
  | InsertAfter "'oid"
  | ListAssign "'oid" "'oid"
  | MapAssign "'oid" "string" "'oid"
  | ListRemove "'oid"
  | MapRemove  "'oid" "string"

fun oid_references :: "('o, 'v) operation \<Rightarrow> 'o set" where
  "oid_references (InsertAfter oid) = {oid}" |
  "oid_references (ListAssign oid1 oid2) = {oid1, oid2}" |
  "oid_references (MapAssign oid1 _ oid2) = {oid1, oid2}" |
  "oid_references (ListRemove oid) = {oid}" |
  "oid_references (MapRemove oid _) = {oid}" |
  "oid_references _ = {}"

type_synonym ('oid, 'val) database = "'oid \<rightharpoonup> ('oid, 'val) operation"

locale datalog =
  fixes \<D> :: "('oid::{linorder}, 'val) database"
  assumes ref_older: "\<D> oid = Some oper \<Longrightarrow> x \<in> oid_references oper \<Longrightarrow> x < oid"

locale db_extension = datalog +
  fixes oid and oper
  assumes oid_is_latest [simp]: "n \<in> dom \<D> \<Longrightarrow> n < oid"
    and oid_not_present [simp]: "\<D> oid = None"
    and still_valid_database: "datalog (\<D>(oid \<mapsto> oper))"

lemma db_extension_datalog:
  assumes "db_extension \<D> oid oper"
  shows "datalog \<D>"
  using assms db_extension.axioms(1) by blast


end
