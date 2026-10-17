import CalibrationDistance
import Lean

open Lean Elab Command Meta

/-!
Generate an equality witness for every declaration from every production module.
Each witness explicitly references its production constant, including its value
through the exporter's dependency closure. Exporting all witnesses therefore
forces the official Comparator to replay every production declaration and every
transitive dependency in a fresh Lean kernel. The witnesses are not substitutes
for the separately pinned paper contracts.
-/
run_cmd do
  let env ← getEnv
  let isProduction := fun (n : Name) =>
    match env.getModuleIdxFor? n with
    | none => false
    | some idx =>
      let m := env.header.moduleNames[idx]!.toString
      m == "CalibrationDistance" || m.startsWith "CalibrationDistance."
  let names := ((env.constants.toList.toArray.filter fun p => isProduction p.1).map
    Prod.fst).qsort Name.lt
  if names.isEmpty then
    throwError "Production kernel audit has no roots"
  let mut records : Array Json := #[]
  for i in [:names.size] do
    let name := names[i]!
    let some info := env.find? name | throwError m!"Missing production constant {name}"
    let witnessName := Name.str `P30.KernelAudit ("witness_" ++ toString i)
    let constant := mkConst name (info.levelParams.map Level.param)
    liftTermElabM do
      let type ← mkEq constant constant
      let value ← mkEqRefl constant
      addDecl <| .thmDecl {
        name := witnessName
        levelParams := info.levelParams
        type := type
        value := value
      }
    let idx := (env.getModuleIdxFor? name).get!
    records := records.push <| Json.mkObj [
      ("declaration", toJson name.toString),
      ("module", toJson env.header.moduleNames[idx]!.toString),
      ("witness", toJson witnessName.toString)]
  liftIO <| IO.FS.createDirAll ".lake/verification"
  liftIO <| IO.FS.writeFile ".lake/verification/kernel-targets.json" (Json.pretty <| Json.mkObj [
    ("production_declaration_count", toJson names.size),
    ("roots", Json.arr records)])
  logInfo m!"PRODUCTION_KERNEL_WITNESSES_GENERATED declarations={names.size}"
