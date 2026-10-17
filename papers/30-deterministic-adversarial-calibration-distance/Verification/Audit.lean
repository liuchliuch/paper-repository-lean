import CalibrationDistance
import Lean.Util.CollectAxioms

open Lean Elab Command

/-!
Audit every declaration originating in a production module, including private
and compiler-generated declarations. Inspect the checked kernel environment;
share the visited set while collecting every transitive axiom dependency.
This audit does not certify paper coverage.
-/
run_cmd do
  let env ← getEnv
  let isProduction := fun (n : Name) =>
    match env.getModuleIdxFor? n with
    | none => false
    | some idx =>
      let m := env.header.moduleNames[idx]!.toString
      m == "CalibrationDistance" || m.startsWith "CalibrationDistance."
  let names := ((env.constants.toList.toArray.filter fun p => isProduction p.1).map
    Prod.fst).qsort Name.lt
  if names.isEmpty then
    throwError "Production axiom audit has no roots"
  let (_, state) := ((names.forM CollectAxioms.collect).run env).run {}
  let axioms := state.axioms.qsort Name.lt
  let bad := axioms.filter fun n =>
    n != `propext && n != `Classical.choice && n != `Quot.sound
  for name in names do
    logInfo m!"AUDITED_PRODUCTION_ROOT {name}"
  logInfo m!"TRANSITIVE_AXIOM_UNION {axioms.toList}"
  unless bad.isEmpty do
    throwError m!"ILLEGAL_TRANSITIVE_AXIOMS: {bad.toList}"
  logInfo m!"PRODUCTION_AXIOM_AUDIT_PASSED declarations={names.size}"
