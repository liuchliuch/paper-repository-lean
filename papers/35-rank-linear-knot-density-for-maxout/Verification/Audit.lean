import Verification.Solution
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Audit every definition and theorem in the production import closure.
Trusted challenge holes and deliberately invalid negative controls are excluded. -/
open Lean Elab Command
set_option maxRecDepth 32768
set_option maxHeartbeats 0

run_cmd do
  let env ← getEnv
  let isProjectModule := fun (name : Name) =>
    let s := name.toString
    s == "Paper35" || s.startsWith "Paper35." || s.startsWith "Verification."
  for forbidden in #[`Verification.Challenge, `Verification.NegativeAxiom,
      `Verification.NegativePremise] do
    if env.header.moduleNames.contains forbidden then
      throwError "Nonproduction fixture in proof environment: {forbidden}"
  unless env.header.moduleNames.contains `Paper35 do
    throwError "Production root is missing"
  for sourceFile in (← liftIO <| ("Paper35" : System.FilePath).readDir) do
    if sourceFile.fileName.endsWith ".lean" then
      let stem := String.mk (sourceFile.fileName.toList.take (sourceFile.fileName.length - 5))
      let moduleName := Name.str `Paper35 stem
      unless env.header.moduleNames.contains moduleName do
        throwError "Production module missing from root import closure: {moduleName}"
  let roots := env.constants.toList.filterMap fun (name, _) => do
    let idx ← env.getModuleIdxFor? name
    let moduleName := env.header.moduleNames[idx.toNat]!
    if isProjectModule moduleName then some name else none
  unless roots.length > 0 do
    throwError "No production declarations found"
  for name in roots do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration missing from checked kernel environment: {name}"
  let action : CollectAxioms.M Unit := roots.forM CollectAxioms.collect
  let (_, result) := (action.run env).run {}
  let unexpected := result.axioms.filter fun name =>
    name != ``propext && name != ``Classical.choice && name != ``Quot.sound
  unless unexpected.isEmpty do
    throwError "Unexpected transitive axioms: {unexpected}"
  let names := roots.toArray.qsort Name.lt
  let modules := env.header.moduleNames.filter isProjectModule
  let report := Json.mkObj [
    ("status", toJson "passed"),
    ("declarations", toJson roots.length),
    ("modules", toJson (modules.map Name.toString)),
    ("axioms", toJson ((result.axioms.qsort Name.lt).map Name.toString)),
    ("paper_accepted", toJson false)]
  liftIO do
    IO.FS.createDirAll ".lake/verification"
    IO.FS.writeFile ".lake/verification/axioms.json" (report.pretty ++ "\n")
    IO.FS.writeFile ".lake/verification/declarations.txt"
      (String.intercalate "\n" (names.toList.map Name.toString) ++ "\n")
  logInfo m!"AXIOM_AUDIT_PASS declarations={roots.length} modules={modules.size} axioms={(result.axioms.qsort Name.lt).toList}"
