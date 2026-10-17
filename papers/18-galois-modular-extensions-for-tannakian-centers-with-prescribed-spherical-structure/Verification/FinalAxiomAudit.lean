import Paper18.AllSources
import Verification.RelativeSolution
import Lean

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count := 0
  let mut privateCount := 0
  let mut solutionCount := 0
  let mut state : CollectAxioms.State := {}
  for (name, _) in env.constants.toList do
    let moduleName := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx]!
      | none => .anonymous
    let ownModule := (`Paper18 |>.isPrefixOf moduleName) ||
      moduleName == `Verification.RelativeSolution
    if ownModule then
      let (_, next) := ((CollectAxioms.collect name).run env).run state
      state := next
      for ax in state.axioms do
        unless permitted.contains ax do
          throwError "Illegal transitive axiom {ax}, discovered while auditing {name} from {moduleName}"
      count := count + 1
      if isPrivateName name then privateCount := privateCount + 1
      if moduleName == `Verification.RelativeSolution then solutionCount := solutionCount + 1
  logInfo m!"Final module-origin declarations audited: {count}; private declarations: {privateCount}; relative solution declarations: {solutionCount}."
  logInfo m!"All transitive axioms are permitted: {state.axioms}"

#print axioms Paper18.Category.CategoricalTheorem11.exists_modularExtension
#print axioms Paper18.Category.FixedBoundary.MinimalExistence.lemmaA1_relative_to_ENO_at_center
#print axioms Paper18.Category.FixedBoundary.MinimalExistence.proposition2_2_relative_to_ENO
#print axioms P18Relative.theorem1_1
#print axioms P18Relative.lemmaA_1
#print axioms P18Relative.proposition2_2
#print axioms P18Relative.positive_extension
