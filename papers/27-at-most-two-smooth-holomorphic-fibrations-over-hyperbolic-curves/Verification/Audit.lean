import Paper27
import Lean.Util.CollectAxioms

/-! Audit every declaration owned by a production Paper27 module. This file
is outside the production import closure. The official Comparator separately
replays the exported solution into a fresh Lean kernel. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let opts ← getOptions
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut owned : Array Name := #[]
  for (n, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? n then
      if `Paper27 |>.isPrefixOf env.header.moduleNames[idx.toNat]! then
        owned := owned.push n
  owned := owned.qsort Name.quickLt
  unless !owned.isEmpty do throwError "Empty production audit"
  for n in owned do
    let some ci := env.find? n | throwError "Missing declaration {n}"
    if ci.isUnsafe then throwError "Unsafe production declaration: {n}"
    match ci with
    | .axiomInfo _ => throwError "Production axiom declaration: {n}"
    | _ => pure ()
    let axioms ← collectAxioms n
    for ax in axioms do
      unless allowed.contains ax do throwError "Illegal axiom {ax} in {n}"
    match Kernel.check env {} ci.type with
    | .error e => throwError "Kernel rejected type of {n}: {e.toMessageData opts}"
    | .ok _ => pure ()
    if let some body := ci.value? (allowOpaque := true) then
      match Kernel.check env {} body with
      | .error e => throwError "Kernel rejected body of {n}: {e.toMessageData opts}"
      | .ok inferred =>
        match Kernel.isDefEq env {} inferred ci.type with
        | .ok true => pure ()
        | _ => throwError "Kernel body/type mismatch: {n}"
    logInfo m!"PRODUCTION_AUDIT {n} axioms={axioms} kernel=checked"
  logInfo m!"PRODUCTION_AUDIT_OK declarations={owned.size}"
