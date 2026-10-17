import Paper15
import Paper15.CertificateCompile
import Lean

/-!
Full transitive axiom audit of ALL production declarations, including theorem
types and proof values. Use Lean's own collector with a shared visited set,
so common mathlib dependencies are traversed only once. The audit root imports
the whole production library; challenge and negative controls are excluded.
-/
set_option maxHeartbeats 0
set_option maxRecDepth 100000

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let roots := env.constants.toList.filterMap fun (name, _) =>
    if (`Paper15 |>.isPrefixOf name) || name.toString.startsWith "_private.Paper15." then some name else none
  let (_, closure) := ((roots.forM Lean.CollectAxioms.collect).run env).run {}
  for ax in closure.axioms do
    unless permitted.contains ax do
      throwError "Illegal axiom in the full production dependency closure: {ax}"
  logInfo m!"Paper15 declarations audited: {roots.length}."
  logInfo m!"Full transitive axiom union: {closure.axioms}."
  logInfo "All production declarations have only permitted transitive axioms."
