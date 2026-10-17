import Paper08
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Audit every declaration originating in a production `Paper08` module, including
private implementation declarations.  `Lean.collectAxioms` follows the actual
kernel expression dependencies, rather than searching the source text.
This file deliberately imports neither the challenge nor negative controls.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let permitted : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if modName == `Paper08 || (`Paper08).isPrefixOf modName then
        names := names.push name
  names := names.qsort Name.lt
  if names.isEmpty then
    throwError "Production audit found no declarations"
  -- A shared visited set traverses the union of the real proof dependencies
  -- once.  This is equivalent to checking each declaration's axiom closure,
  -- and avoids re-traversing the same mathlib proofs for every declaration.
  let (_, closure) := ((names.forM Lean.CollectAxioms.collect).run env).run {}
  for ax in closure.axioms do
    unless permitted.contains ax do
      throwError "Illegal axiom in production dependency closure: {ax}"
  for name in names do
    logInfo m!"AUDITED {name}"
  logInfo m!"AXIOM CLOSURE: {closure.axioms.qsort Name.lt |>.toList}"
  logInfo m!"PRODUCTION AXIOM AUDIT PASSED: {names.size} declarations, \
    {closure.visited.size} transitive dependencies"
