import Paper19
import Lean.Util.CollectAxioms

open Lean Elab Command

/-! Transitive axiom audit of every `Paper19` production declaration. -/
run_cmd do
  let env ← getEnv
  let names := (env.constants.toList.toArray.filter (fun p =>
    p.1.toString.startsWith "Paper19.")).map Prod.fst
  let names := names.qsort Name.lt
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  let axioms := state.axioms.qsort Name.lt
  let bad := axioms.filter (fun n =>
    n != `propext && n != `Classical.choice && n != `Quot.sound)
  for name in names do
    logInfo m!"AUDITED_PRODUCTION_ROOT {name}"
  logInfo m!"TRANSITIVE_AXIOM_UNION {axioms.toList}"
  unless bad.isEmpty do
    throwError m!"ILLEGAL_TRANSITIVE_AXIOMS: {bad.toList}"
  logInfo m!"AUDIT_PASSED declarations={names.size}; permitted=[propext, Classical.choice, Quot.sound]"
