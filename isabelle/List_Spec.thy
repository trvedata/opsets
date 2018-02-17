section\<open>Relationship to strong list specification\<close>

theory List_Spec
  imports Insert_Spec
begin

text\<open>Attiya et al.'s specification is as follows~\cite{Attiya:2016kh}:
\begin{displayquote}
An abstract execution $A = (H, \textsf{vis})$ belongs to the \emph{strong list specification} $\mathcal{A}_\textsf{strong}$ if and only if there is a relation $\textsf{lo} \subseteq \textsf{elems}(A) \times \textsf{elems}(A)$, called the \emph{list order}, such that:
\begin{enumerate}
\item Each event $e = \mathit{do}(\mathit{op}, w) \in H$ returns a sequence of elements $w=a_0 \dots a_{n-1}$, where $a_i \in \textsf{elems}(A)$, such that
\begin{enumerate}
\item $w$ contains exactly the elements visible to $e$ that have been inserted, but not deleted:
\[ \forall a.\; a \in w \quad\Longleftrightarrow\quad (\mathit{do}(\textsf{ins}(a, \_), \_) \le_\textsf{vis} e)
\;\wedge\; \neg(\mathit{do}(\textsf{del}(a), \_) \le_\textsf{vis} e). \]
\item The order of the elements is consistent with the list order:
\[ \forall i, j.\; (i < j) \;\Longrightarrow\; (a_i, a_j) \in \textsf{lo}. \]
\item Elements are inserted at the specified position:
if $\mathit{op} = \textsf{ins}(a, k)$, then $a = a_{\mathrm{min} \{k,\; n-1\}}$.
\end{enumerate}
\item The list order $\textsf{lo}$ is transitive, irreflexive and total, and thus determines the order of all insert operations in the execution.
\end{enumerate}
\end{displayquote}
\<close>

datatype ('oid, 'val) list_op =
  Insert "'oid option" "'val" |
  Delete "'oid"

fun interp_op :: "('oid list \<times> ('oid \<rightharpoonup> 'val)) \<Rightarrow> ('oid \<times> ('oid, 'val) list_op)
               \<Rightarrow> ('oid list \<times> ('oid \<rightharpoonup> 'val))" where
  "interp_op (list, vals) (oid, Insert ref val) = (insert_spec list (oid, ref), vals(oid \<mapsto> val))" |
  "interp_op (list, vals) (oid, Delete ref    ) = (list, vals(ref := None))"

definition interp_ops :: "('oid \<times> ('oid, 'val) list_op) list \<Rightarrow> ('oid list \<times> ('oid \<rightharpoonup> 'val))" where
  "interp_ops ops \<equiv> foldl interp_op ([], Map.empty) ops"

fun list_op_deps :: "('oid, 'val) list_op \<Rightarrow> 'oid set" where
  "list_op_deps (Insert (Some ref) _) = {ref}" |
  "list_op_deps (Insert  None      _) = {}"    |
  "list_op_deps (Delete  ref        ) = {ref}"

definition insertions :: "('oid::{linorder} \<times> ('oid, 'val) list_op) list \<Rightarrow> 'oid list" where
  "insertions ops \<equiv> List.map_filter (\<lambda>oper.
      case oper of (oid, Insert ref val) \<Rightarrow> Some oid |
                   (oid, Delete ref    ) \<Rightarrow> None) ops"

definition deletions :: "('oid::{linorder} \<times> ('oid, 'val) list_op) list \<Rightarrow> 'oid list" where
  "deletions ops \<equiv> List.map_filter (\<lambda>oper.
      case oper of (oid, Insert ref val) \<Rightarrow> None |
                   (oid, Delete ref    ) \<Rightarrow> Some ref) ops"

locale list_opset = opset opset list_op_deps
  for opset :: "('oid::{linorder} \<times> ('oid, 'val) list_op) set"

definition list_ops :: "('oid::{linorder} \<times> ('oid, 'val) list_op) list \<Rightarrow> bool" where
  "list_ops ops \<equiv> spec_ops list_op_deps ops"

lemma interp_ops_unfold_last:
  shows "interp_ops (xs @ [x]) = interp_op (interp_ops xs) x"
by (simp add: interp_ops_def)

lemma map_filter_append:
  shows "List.map_filter P (xs @ ys) = List.map_filter P xs @ List.map_filter P ys"
by (auto simp add: List.map_filter_def)

lemma map_filter_Some:
  assumes "P x = Some y"
  shows "List.map_filter P [x] = [y]"
by (simp add: assms map_filter_simps(1) map_filter_simps(2))

lemma map_filter_None:
  assumes "P x = None"
  shows "List.map_filter P [x] = []"
by (simp add: assms map_filter_simps(1) map_filter_simps(2))

lemma insertions_last_ins:
  shows "insertions (xs @ [(oid, Insert ref val)]) = insertions xs @ [oid]"
by (simp add: insertions_def map_filter_Some map_filter_append)

lemma insertions_last_del:
  shows "insertions (xs @ [(oid, Delete ref)]) = insertions xs"
by (simp add: insertions_def map_filter_None map_filter_append)

lemma deletions_last_ins:
  shows "deletions (xs @ [(oid, Insert ref val)]) = deletions xs"
by (simp add: deletions_def map_filter_None map_filter_append)

lemma deletions_last_del:
  shows "deletions (xs @ [(oid, Delete ref)]) = deletions xs @ [ref]"
by (simp add: deletions_def map_filter_Some map_filter_append)

lemma deletions_exist:
  assumes "ref \<in> set (deletions ops)"
  shows "\<exists>i. (i, Delete ref) \<in> set ops"
using assms proof(induction ops rule: List.rev_induct)
  case Nil
  then show "\<exists>i. (i, Delete ref) \<in> set []"
    by (simp add: deletions_def List.map_filter_def)
next
  case (snoc a ops)
  obtain oid oper where a_pair: "a = (oid, oper)"
    by fastforce
  then show "\<exists>i. (i, Delete ref) \<in> set (ops @ [a])"
  proof(cases oper)
    case (Insert r v)
    hence "deletions (ops @ [a]) = deletions ops"
      by (simp add: a_pair deletions_last_ins)
    then show ?thesis
      using snoc.IH snoc.prems by auto
  next
    case (Delete r)
    hence del: "deletions (ops @ [a]) = deletions ops @ [r]"
      by (simp add: a_pair deletions_last_del)
    then show ?thesis
    proof(cases "r = ref")
      case True
      then show ?thesis using Delete a_pair by auto
    next
      case False
      then show ?thesis using del snoc.IH snoc.prems by auto
    qed
  qed
qed

lemma deletions_refs_older:
  assumes "list_ops (ops @ [(oid, oper)])"
  shows "\<And>ref. ref \<in> set (deletions ops) \<Longrightarrow> ref < oid"
proof -
  fix ref
  assume "ref \<in> set (deletions ops)"
  then obtain i where in_ops: "(i, Delete ref) \<in> set ops"
    using deletions_exist by blast
  have "ref < i"
  proof -
    have "\<And>i oper r. (i, oper) \<in> set ops \<Longrightarrow> r \<in> list_op_deps oper \<Longrightarrow> r < i"
      by (meson assms list_ops_def spec_ops_ref_less spec_ops_rem_last)
    thus "ref < i"
      using in_ops by auto
  qed
  moreover have "i < oid"
  proof -
    have "\<And>i. i \<in> set (map fst ops) \<Longrightarrow> i < oid"
      using assms by (simp add: list_ops_def spec_ops_id_inc)
    thus ?thesis
      by (metis in_ops in_set_zipE zip_map_fst_snd)
  qed
  ultimately show "ref < oid"
    using order.strict_trans by blast
qed

theorem inserted_but_not_deleted:
  assumes "list_ops ops"
  shows "dom (snd (interp_ops ops)) = set (insertions ops) - set (deletions ops)"
using assms proof(induction ops rule: List.rev_induct)
  case Nil
  have 1: "interp_ops [] = ([], Map.empty)"
    by (simp add: interp_ops_def)
  moreover have 2: "insertions [] = []" and "deletions [] = []"
    by (auto simp add: insertions_def deletions_def map_filter_simps(2))
  ultimately show "dom (snd (interp_ops [])) = set (insertions []) - set (deletions [])"
    by (simp add: 1 2)
next
  case (snoc x xs)
  hence IH: "dom (snd (interp_ops xs)) = set (insertions xs) - set (deletions xs)"
    using list_ops_def spec_ops_rem_last by blast
  obtain oid oper where x_pair: "x = (oid, oper)"
    by fastforce
  obtain list vals where interp_xs: "interp_ops xs = (list, vals)"
    by fastforce
  then show "dom (snd (interp_ops (xs @ [x]))) =
             set (insertions (xs @ [x])) - set (deletions (xs @ [x]))"
  proof(cases oper)
    case (Insert ref val)
    hence "interp_ops (xs @ [x]) = (insert_spec list (oid, ref), vals(oid \<mapsto> val))"
      by (simp add: interp_ops_unfold_last interp_xs x_pair)
    hence "dom (snd (interp_ops (xs @ [x]))) = (dom vals) \<union> {oid}"
      by simp
    moreover have "set (insertions xs) - set (deletions xs) = dom vals"
      using IH interp_xs by auto
    moreover have "insertions (xs @ [x]) = insertions xs @ [oid]"
      by (simp add: Insert insertions_last_ins x_pair)
    moreover have "deletions (xs @ [x]) = deletions xs"
      by (simp add: Insert deletions_last_ins x_pair)
    hence "set (insertions (xs @ [x])) - set (deletions (xs @ [x])) =
           {oid} \<union> set (insertions xs) - set (deletions xs)"
      using calculation(3) by auto
    moreover have "... = {oid} \<union> (set (insertions xs) - set (deletions xs))"
      using deletions_refs_older snoc.prems x_pair by blast
    ultimately show ?thesis by auto
  next
    case (Delete ref)
    hence "interp_ops (xs @ [x]) = (list, vals(ref := None))"
      by (simp add: interp_ops_unfold_last interp_xs x_pair)
    hence "dom (snd (interp_ops (xs @ [x]))) = (dom vals) - {ref}"
      by simp
    moreover have "set (insertions xs) - set (deletions xs) = dom vals"
      using IH interp_xs by auto
    moreover have "insertions (xs @ [x]) = insertions xs"
      by (simp add: Delete insertions_last_del x_pair)
    moreover have "deletions (xs @ [x]) = deletions xs @ [ref]"
      by (simp add: Delete deletions_last_del x_pair)
    hence "set (insertions (xs @ [x])) - set (deletions (xs @ [x])) =
           set (insertions xs) - (set (deletions xs) \<union> {ref})"
      using calculation(3) by auto
    moreover have "... = set (insertions xs) - set (deletions xs) - {ref}"
      by blast
    ultimately show ?thesis by auto
  qed
qed

corollary inserted_but_not_deleted':
  assumes "list_ops ops"
    and "interp_ops ops = (list, vals)"
  shows "dom (vals) = set (insertions ops) - set (deletions ops)"
using assms inserted_but_not_deleted by fastforce

end
