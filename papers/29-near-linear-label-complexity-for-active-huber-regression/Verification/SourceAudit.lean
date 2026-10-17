import Paper29
import Lean.Util.CollectAxioms

/-! Prepared whole-production checked-kernel/transitive-axiom audit.

STATUS: verification_deferred_by_user. Do not compile or run this module until
the user resumes the full audit. Production never imports Verification.

Selection is by ORIGINAL SOURCE MODULE, rather than declaration namespace, so
private and generated declarations from every Paper29 production module are
included. Every selected elaborator declaration must exist in env.checked,
and every transitive axiom must be one of the three standard permitted axioms.
-/
open Lean Elab Command

elab "#audit_p29_production" : command => do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut selected : Array (Name × Name) := #[]
  for (declName, _) in env.constants do
    if let some idx := env.getModuleIdxFor? declName then
      let moduleName := env.header.moduleNames[idx.toNat]!
      if (`Paper29).isPrefixOf moduleName then
        selected := selected.push (declName,moduleName)
  if selected.isEmpty then
    throwError "P29 production audit selected no Paper29 declarations"
  let mut observed : Array Name := #[]
  for (declName,moduleName) in selected do
    unless (env.checked.get.find? declName).isSome do
      throwError "P29 unchecked declaration: {declName} (source module {moduleName})"
    let axioms ← collectAxioms declName
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "P29 unauthorized transitive axiom {axiomName} in {declName} (source {moduleName})"
      unless observed.contains axiomName do
        observed := observed.push axiomName
  logInfo "P29 production audit passed: {selected.size} source-selected declarations; all checked; transitive axioms {observed}"

-- Intentionally prepared but NOT EXECUTED in this session.
-- Compiling this audit module later will run the complete audit:
#audit_p29_production
