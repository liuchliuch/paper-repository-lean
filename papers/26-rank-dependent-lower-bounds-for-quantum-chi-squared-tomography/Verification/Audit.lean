import Verification.Solution
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-! Checked-kernel presence and transitive axiom closure of every declaration
in every imported production module and in the checked solution contracts. -/
open Lean Elab Command
set_option maxRecDepth 32768
set_option maxHeartbeats 0

run_cmd do
  let env ← getEnv
  let isProductionModule := fun (name : Name) =>
    let s := name.toString
    s == "Paper26" || s.startsWith "Paper26." || s == "Verification.Solution"
  if env.header.moduleNames.contains `Verification.Challenge then
    throwError "The challenge must not enter the production proof environment"
  for bad in #[`Verification.NegativePremise, `Verification.NegativeAxiom] do
    if env.header.moduleNames.contains bad then
      throwError "Negative control entered production: {bad}"
  let roots := env.constants.toList.filterMap fun (name, _) => do
    let idx ← env.getModuleIdxFor? name
    let moduleName := env.header.moduleNames[idx.toNat]!
    if isProductionModule moduleName then some name else none
  unless roots.length > 0 do
    throwError "No production declarations were loaded"
  for name in roots do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration absent from checked kernel environment: {name}"
  let action : CollectAxioms.M Unit := roots.forM CollectAxioms.collect
  let (_, result) := (action.run env).run {}
  let illegal := result.axioms.filter fun name =>
    name != ``propext && name != ``Classical.choice && name != ``Quot.sound
  unless illegal.isEmpty do
    throwError "Illegal transitive axioms: {illegal}"
  let names := roots.toArray.qsort Name.lt
  let modules := env.header.moduleNames.filter isProductionModule
  let report := Json.mkObj [
    ("status", toJson "passed"),
    ("checked_kernel_declarations", toJson roots.length),
    ("modules", toJson (modules.map Name.toString)),
    ("axioms", toJson ((result.axioms.qsort Name.lt).map Name.toString)),
    ("whole_paper_coverage_claimed", toJson false)]
  liftIO do
    IO.FS.createDirAll ".lake/verification"
    IO.FS.writeFile ".lake/verification/axioms.json" (report.pretty ++ "\n")
    IO.FS.writeFile ".lake/verification/declarations.txt"
      (String.intercalate "\n" (names.toList.map Name.toString) ++ "\n")
  logInfo m!"AXIOM_AUDIT_PASS declarations={roots.length} modules={modules.size} axioms={(result.axioms.qsort Name.lt).toList}"
