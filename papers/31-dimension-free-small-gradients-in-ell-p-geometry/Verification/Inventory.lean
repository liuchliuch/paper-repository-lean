import Paper31
import Lean

open Lean Elab Command Meta

set_option pp.universes true
set_option pp.fullNames true
set_option pp.proofs true
set_option pp.explicit true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true
set_option pp.fieldNotation false
set_option format.width 160
set_option maxHeartbeats 0

run_cmd do
  let env ← getEnv
  let mut records : Array Json := #[]
  let mut theorems : Array Json := #[]
  let mut roots : Array Name := #[]
  let mut counts := 0
  for (n, ci) in env.constants.toList.toArray.qsort (fun a b => a.1.toString < b.1.toString) do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx]!
    unless mod.toString.startsWith "P31." || mod == `Paper31 do continue
    roots := roots.push n
    counts := counts + 1
    let entry := Json.mkObj [("name", toJson n.toString), ("module", toJson mod.toString),
      ("kind", toJson (if wasOriginallyTheorem env n then "theorem" else "declaration"))]
    records := records.push entry
    if wasOriginallyTheorem env n && !n.isInternal && n.toString.startsWith "P31." then
      let ty ← liftTermElabM <| Meta.ppExpr ci.type
      theorems := theorems.push <| Json.mkObj [("name", toJson n.toString),
        ("type", toJson ty.pretty), ("universes", toJson (ci.levelParams.map Name.toString))]
  let action : CollectAxioms.M Unit := do
    for n in roots do CollectAxioms.collect n
  let (_, closure) := (action.run env).run {}
  let allAxioms := closure.axioms
  for ax in allAxioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "Illegal axiom in joint transitive production closure: {ax}"
  liftIO <| IO.FS.createDirAll ".lake/verification"
  liftIO <| IO.FS.writeFile ".lake/verification/axiom-closure.json"
    (Json.pretty (Json.mkObj [("status",toJson "passed"), ("declarations_checked",toJson counts),
      ("permitted_axioms",toJson (#[`propext,`Classical.choice,`Quot.sound].map Name.toString)),
      ("observed_axioms",toJson (allAxioms.map Name.toString)), ("declarations",toJson records)]))
  liftIO <| IO.FS.writeFile ".lake/verification/theorem-inventory.json" (Json.pretty (toJson theorems))
  logInfo m!"Checked {counts} production declarations; {theorems.size} public theorem targets."
