import Paper36
import Verification.Solution
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Audit every declaration whose defining module is in the production `Paper36`
source tree, including declarations outside the `Paper36` namespace. Every
production source file must be imported by the production root. Challenge holes
and intentionally invalid negative controls must not enter this environment.

The `checked` membership gate is a checked-kernel-environment audit. The official
Comparator separately exports its selected targets and replays their complete
dependency environment into a fresh Lean kernel; this file is not a replacement
for that official replay.
-/

open Lean Elab Command

set_option maxRecDepth 32768
set_option maxHeartbeats 0

private partial def leanFiles (directory : System.FilePath) : IO (Array System.FilePath) := do
  let mut files := #[]
  if !(← directory.pathExists) then
    return files
  for entry in (← directory.readDir) do
    if ← entry.path.isDir then
      files := files ++ (← leanFiles entry.path)
    else if entry.fileName.endsWith ".lean" then
      files := files.push entry.path
  return files

run_cmd do
  let env ← getEnv
  let isProductionModule := fun (name : Name) =>
    name == `Paper36 || (`Paper36).isPrefixOf name
  let isAuditedModule := fun (name : Name) =>
    isProductionModule name || name == `Verification.Solution
  for forbidden in #[`Verification.Challenge, `Verification.NegativePremise,
      `Verification.NegativeAxiom] do
    if env.header.moduleNames.contains forbidden then
      throwError "Challenge/negative-control module entered production: {forbidden}"
  unless env.header.moduleNames.contains `Paper36 do
    throwError "Production root Paper36 was not imported"
  for path in (← liftIO <| leanFiles "Paper36") do
    let stem := String.mk (path.toString.toList.take (path.toString.length - 5))
    let moduleName := (stem.replace "/" ".").toName
    unless env.header.moduleNames.contains moduleName do
      throwError "Production source is missing from root import closure: {moduleName}"
  let roots := env.constants.toList.filterMap fun (name, info) => do
    let idx ← env.getModuleIdxFor? name
    let moduleName := env.header.moduleNames[idx.toNat]!
    if isAuditedModule moduleName then some (name, info) else none
  unless roots.length > 0 do
    throwError "Production root imported no project declarations"
  for (name, info) in roots do
    unless (env.checked.get.find? name).isSome do
      throwError "Declaration missing from checked kernel environment: {name}"
    if info.isUnsafe then
      throwError "Unsafe production declaration: {name}"
  let action : CollectAxioms.M Unit := (roots.map Prod.fst).forM CollectAxioms.collect
  let (_, result) := (action.run env).run {}
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := result.axioms.filter fun name => !permitted.contains name
  unless unexpected.isEmpty do
    throwError "Unexpected transitive production axioms: {unexpected}"
  let names := (roots.map Prod.fst).toArray.qsort Name.lt
  let modules := env.header.moduleNames.filter isAuditedModule
  let report := Json.mkObj [
    ("status", toJson "passed"),
    ("checked_kernel_declarations", toJson roots.length),
    ("modules", toJson (modules.map Name.toString)),
    ("axioms", toJson ((result.axioms.qsort Name.lt).map Name.toString)),
    ("declarations", toJson (names.map Name.toString))]
  liftIO do
    IO.FS.createDirAll ".lake/verification"
    IO.FS.writeFile ".lake/verification/production-audit.json" (report.pretty ++ "\n")
    IO.FS.writeFile ".lake/verification/production-declarations.txt"
      (String.intercalate "\n" (names.toList.map Name.toString) ++ "\n")
  logInfo m!"PRODUCTION_AUDIT_PASS checked_kernel_declarations={roots.length} modules={modules.size} axioms={(result.axioms.qsort Name.lt).toList}"
