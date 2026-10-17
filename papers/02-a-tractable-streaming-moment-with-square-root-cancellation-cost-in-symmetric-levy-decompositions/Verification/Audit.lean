import Verification.Solution
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Transitive axiom audit of every declaration in imported project modules.
The trusted challenge is deliberately excluded. -/
open Lean Elab Command
set_option maxRecDepth 32768
set_option maxHeartbeats 0

run_cmd do
  let env ← getEnv
  let isProjectModule := fun (name : Name) =>
    let s := name.toString
    s == "Paper02" || s.startsWith "Paper02." || s.startsWith "Verification."
  if env.header.moduleNames.contains `Verification.Challenge then
    throwError "The trusted challenge must never enter the proof environment"
  for forbidden in #[`Verification.NegativeAxiom, `Verification.NegativePremise] do
    if env.header.moduleNames.contains forbidden then
      throwError "Negative controls must never enter the production proof environment: {forbidden}"
  unless env.header.moduleNames.contains `Paper02 do
    throwError "The production root Paper02 must be imported by Verification.Solution"
  let sourceFiles ← liftIO <| ("Paper02" : System.FilePath).readDir
  for sourceFile in sourceFiles do
    if sourceFile.fileName.endsWith ".lean" then
      let stem := String.mk (sourceFile.fileName.toList.take (sourceFile.fileName.length - 5))
      let moduleName := Name.str `Paper02 stem
      unless env.header.moduleNames.contains moduleName do
        throwError "Production source is missing from the root import closure: {moduleName}"
  let roots := env.constants.toList.filterMap fun (name, _) => do
    let idx ← env.getModuleIdxFor? name
    let moduleName := env.header.moduleNames[idx.toNat]!
    if isProjectModule moduleName then some name else none
  unless roots.length > 0 do
    throwError "No project declarations were loaded"
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
    ("axioms", toJson ((result.axioms.qsort Name.lt).map Name.toString))]
  liftIO do
    IO.FS.createDirAll ".lake/verification"
    IO.FS.writeFile ".lake/verification/axioms.json" (report.pretty ++ "\n")
    IO.FS.writeFile ".lake/verification/declarations.txt"
      (String.intercalate "\n" (names.toList.map Name.toString) ++ "\n")
  logInfo m!"AXIOM_AUDIT_PASS declarations={roots.length} modules={modules.size} axioms={(result.axioms.qsort Name.lt).toList}"
