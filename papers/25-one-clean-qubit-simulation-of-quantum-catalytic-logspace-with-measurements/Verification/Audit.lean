import Paper25
import Lean.Util.CollectAxioms

/-! Exhaustive transitive-axiom audit of every loaded production declaration,
including private proof helpers and definitions, not merely selected results. -/
open Lean in
run_cmd do
  let env ← getEnv
  let owned := env.constants.toList.filter fun (n, _) =>
    match env.getModuleIdxFor? n with
    | none => false
    | some idx =>
      let module := env.header.moduleNames[idx.toNat]!
      module == `Paper25 || (`Paper25).isPrefixOf module
  let ((), state) := ((owned.forM fun (n, _) => Lean.CollectAxioms.collect n).run env).run {}
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for ax in state.axioms do
    unless allowed.contains ax do
      throwError "Unauthorized transitive axiom: {ax}"
  logInfo m!"PRODUCTION_AXIOM_AUDIT_PASS declarations={owned.length} axioms={state.axioms}"
  for (n, _) in owned do
    logInfo m!"AUDITED {n}"
