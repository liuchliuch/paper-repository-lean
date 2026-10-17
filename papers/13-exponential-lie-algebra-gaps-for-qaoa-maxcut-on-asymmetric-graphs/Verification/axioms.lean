import StatementContracts.Solution
import Lean.Util.CollectAxioms
/-!
Audit every declaration originating in a production module or Solution, including
private/generated auxiliaries. Use Lean's own transitive collector with a shared
visited set: the union of closures is exactly the closure of the union of roots.
-/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Quot.sound, `Classical.choice]
  let mut count : ℕ := 0
  let mut state : CollectAxioms.State := {}
  for (name, _) in env.constants.toList do
    let production := match env.getModuleIdxFor? name with
      | some idx =>
        let modName := env.header.moduleNames[idx]!
        (`Paper13).isPrefixOf modName || modName == `StatementContracts.Solution
      | none => false
    if production then
      count := count + 1
      let (_, next) := ((CollectAxioms.collect name).run env).run state
      state := next
      logInfo m!"AUDITED {name}"
  let mut bad : ℕ := 0
  for ax in state.axioms do
    unless allowed.contains ax do
      bad := bad + 1
      logError m!"UNAUTHORIZED TRANSITIVE AXIOM {ax}"
  logInfo m!"TRANSITIVE_AXIOM_UNION={state.axioms}"
  logInfo m!"AUDITED_PRODUCTION_DECLARATIONS={count}; UNAUTHORIZED_AXIOM_OCCURRENCES={bad}"
