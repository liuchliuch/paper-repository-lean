import Paper26
import Lean

open Lean Elab Command
set_option pp.fullNames true
set_option pp.explicit true
set_option pp.coercions true
set_option pp.universes true
set_option pp.notation false
set_option pp.fieldNotation false
set_option pp.funBinderTypes true
set_option pp.proofs true
set_option pp.proofs.threshold 100000000
set_option pp.deepTerms true
set_option pp.deepTerms.threshold 100000000
set_option pp.maxSteps 100000000
set_option maxRecDepth 32768

run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (name, ci) in env.constants.toList.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    if (`Paper26 |>.isPrefixOf name) && ((name.toString.splitOn ".").length == 3) then
      if ci.isTheorem then
        let ty ← liftTermElabM do Meta.ppExpr ci.type
        rows := rows.push <| Json.mkObj [
          ("name", toJson name.toString),
          ("universes", toJson (ci.levelParams.map Name.toString)),
          ("type", toJson ty.pretty)]
  liftIO <| IO.FS.writeFile ".lake/contract-review/contract-types.json" ((toJson rows).pretty ++ "\n")
  logInfo m!"Printed {rows.size} explicit theorem types for contract review."
