import Paper38
import Lean.Util.CollectAxioms

/-! Prepared only. The whole-production audit is verification_deferred_by_user.
Run explicitly after a full build; importing this file executes the audit. -/
open Lean Elab Command

run_elab do
  let env ← getEnv
  let roots ← env.constants.foldM (init := (#[] : Array Name)) fun roots n _ => do
    let owned := (env.getModuleIdxFor? n).any fun i =>
      (`Paper38).isPrefixOf env.header.moduleNames[i]!
    return if owned then roots.push n else roots
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut rows : Array Json := #[]
  let mut violations : Array Json := #[]
  for n in roots do
    let axioms ← collectAxioms n
    rows := rows.push <| Json.mkObj [
      ("declaration", toJson n.toString),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    let illegal := axioms.filter fun a => !allowed.contains a
    if !illegal.isEmpty then
      violations := violations.push <| Json.mkObj [
        ("declaration", toJson n.toString),
        ("illegal_axioms", toJson (illegal.map Name.toString))]
  let result := Json.mkObj [
    ("scope", toJson "every declaration owned by every Paper38 production module"),
    ("roots", toJson roots.size), ("declarations", toJson rows),
    ("violations", toJson violations), ("passed", toJson violations.isEmpty)]
  liftIO <| IO.FS.writeFile "Verification/production-axiom-closure.json" result.pretty
  unless violations.isEmpty do
    throwError "Production axiom audit rejected {violations.size} declaration closures"
  logInfo m!"All {roots.size} production declaration closures passed the axiom whitelist"
