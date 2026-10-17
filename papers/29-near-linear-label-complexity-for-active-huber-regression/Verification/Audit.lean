import Paper29
import Lean.Util.CollectAxioms

open Lean Elab Command

/-! Audit every public/private P29 production declaration and the union of
its entire dependency closure. The traversal memo is shared across roots, so
large shared mathlib dependencies are checked once. -/
elab "audit_paper29" : command => do
  let env ← getEnv
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    if n.toString.startsWith "Paper29." || n.toString.startsWith "_private.Paper29." then
      let some ci := env.checked.get.find? n
        | throwError "Production declaration missing from checked kernel environment: {n}"
      if ci.isUnsafe then throwError "Unsafe production declaration: {n}"
      match ci with
      | .axiomInfo _ => throwError "Custom production axiom: {n}"
      | _ => pure ()
      roots := roots.push n
      logInfo m!"AUDIT_ROOT {n}: present in checked kernel environment"
  let traversal : CollectAxioms.M Unit := roots.forM CollectAxioms.collect
  let (_, closure) := (traversal.run env).run {}
  for a in closure.axioms do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains a do
      throwError "Illegal transitive axiom {a}"
  let mut dependencies := 0
  for n in closure.visited.toList do
    let some ci := env.checked.get.find? n
      | throwError "Dependency missing from checked kernel environment: {n}"
    if ci.isUnsafe then throwError "Unsafe transitive dependency: {n}"
    dependencies := dependencies + 1
  logInfo m!"P29_PRODUCTION_AUDIT_OK {roots.size} roots; {dependencies} checked transitive declarations; axioms {closure.axioms}"

audit_paper29
