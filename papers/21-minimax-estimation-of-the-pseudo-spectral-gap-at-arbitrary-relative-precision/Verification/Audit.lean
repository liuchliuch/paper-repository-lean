import Verification.Solution
import Lean

open Lean Elab Command

/-!
# Axiom audit for the P21 production namespace

Audit every declaration originating in every imported production module, including
definitions and auxiliary results, against its complete transitive axiom
closure.  Only `propext`, `Classical.choice` and `Quot.sound` are permitted.
Module provenance also includes private declarations outside the public namespace.
A residual `sorryAx` fails the audit with a nonzero Lean exit code.
-/

run_cmd do
  let env ← getEnv
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut modules : Array Name := #[]
  for moduleName in env.header.moduleNames do
    if (`PsgEst).isPrefixOf moduleName || moduleName == `Paper21 ||
        moduleName == `Verification.Solution then
      modules := modules.push moduleName
  let mut roots : Array Name := #[]
  for (name, _) in env.constants.toList do
    let production := match env.getModuleIdxFor? name with
      | some idx => modules.contains env.header.moduleNames[idx.toNat]!
      | none => false
    if production then roots := roots.push name
  -- One visited set for the union of every declaration's complete closure.
  -- This checks exactly the same roots without repeatedly traversing shared mathlib proofs.
  let action : CollectAxioms.M Unit := do
    for name in roots do CollectAxioms.collect name
  let (_, audit) := (action.run env).run {}
  logInfo m!"Production modules imported: {modules.size}: {modules}"
  logInfo m!"Production declarations audited: {roots.size}; distinct transitive dependencies: {audit.visited.size}."
  let mut illegal : Array Name := #[]
  for ax in audit.axioms do
    unless permitted.contains ax do
      illegal := illegal.push ax
      logInfo m!"Illegal transitive axiom {ax} in complete production closure"
  if illegal.isEmpty then
    logInfo m!"All production transitive axioms are permitted: {audit.axioms}."
  else
    throwError m!"Production transitive axiom audit FAILED: {illegal}."

#print axioms PsgEst.lhat_contraction
#print axioms PsgEst.lhat_sigma1_one
#print axioms PsgEst.aHat_mem
#print axioms PsgEst.lag_bound
#print axioms PsgEst.bNorm_mul
#print axioms PsgEst.bNorm_mem
#print axioms PsgEst.exists_max_lag
#print axioms PsgEst.hardP_reversible
#print axioms PsgEst.hardPair_disjoint
#print axioms PsgEst.bernKL_le
#print axioms PsgEst.prop1_deterministic
#print axioms PsgEst.pathMeasure_init_le
#print axioms PsgEst.Paper.theorem_1
#print axioms PsgEst.Paper.theorem_2_lower
#print axioms PsgEst.Paper.lemma_1_paper
