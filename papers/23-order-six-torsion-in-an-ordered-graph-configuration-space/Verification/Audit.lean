import Verification.ProductionImports
import Lean

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Complete production declaration audit

`ProductionImports` is the retained frozen inventory of every source
module in `Paper23.lean` and `Paper23/`. Update it when adding source modules. This audit selects declarations by
their module of origin, including private and generated declarations. It
checks membership in `env.checked.get` before a shared exact axiom-closure
traversal. Strongly connected components are completed together, so cached
closures stay exact for inductive/constructor cycles. Missing downstream
constants are errors. Each unique dependency type/value is fully scanned once.

This is an auxiliary integrity check, not a mathematical coverage claim.
The official Comparator separately replays the selected result proofs.
-/

namespace P23AuditMemo

open Lean

structure Node where
  dependencies : Array Name := #[]
  ownAxioms : NameSet := {}

structure Entry where
  index : Nat
  lowlink : Nat
  node : Node

structure State where
  nextIndex : Nat := 0
  entries : Std.HashMap Name Entry := {}
  stack : Array Name := #[]
  onStack : Std.HashSet Name := {}
  closures : Std.HashMap Name NameSet := {}
  scannedConstants : Nat := 0
  dependencyEdges : Nat := 0
  componentCount : Nat := 0

structure Context where
  lookup : Name → Except String Node

abbrev M := ReaderT Context <| StateT State <| Except String

def getEntry (name : Name) : M Entry := do
  let some entry := (← get).entries[name]?
    | throw s!"Internal SCC invariant: no entry for {name}"
  return entry

def decreaseLowlink (name : Name) (value : Nat) : M Unit := do
  let entry ← getEntry name
  let updated := { entry with lowlink := min entry.lowlink value }
  modify fun s => { s with entries := s.entries.insert name updated }

/-- Finish an entire SCC at once; never cache an incomplete cycle member. -/
def finishComponent (root : Name) : M Unit := do
  let mut component : Array Name := #[]
  let mut done := false
  while !done do
    let some name := (← get).stack.back?
      | throw s!"Internal SCC invariant: stack exhausted at {root}"
    modify fun s => { s with stack := s.stack.pop, onStack := s.onStack.erase name }
    component := component.push name
    done := name == root
  let members := NameSet.ofArray component
  let mut axioms : NameSet := {}
  for name in component do
    let entry ← getEntry name
    axioms := axioms ++ entry.node.ownAxioms
    for dependency in entry.node.dependencies do
      if !members.contains dependency then
        let some known := (← get).closures[dependency]?
          | throw s!"Internal SCC invariant: unfinished outgoing dependency {name} → {dependency}"
        axioms := axioms ++ known
  for name in component do
    modify fun s => { s with closures := s.closures.insert name axioms }
  modify fun s => { s with componentCount := s.componentCount + 1 }

/-- Discover every reachable dependency once and compute exact SCC closures. -/
partial def visit (name : Name) : M Unit := do
  if (← get).entries.contains name then
    return
  let node ← match (← read).lookup name with
    | .ok node => pure node
    | .error error => throw error
  let index := (← get).nextIndex
  modify fun s => { s with
    nextIndex := index + 1
    entries := s.entries.insert name { index, lowlink := index, node }
    stack := s.stack.push name
    onStack := s.onStack.insert name
    scannedConstants := s.scannedConstants + 1
    dependencyEdges := s.dependencyEdges + node.dependencies.size }
  for dependency in node.dependencies do
    if !(← get).entries.contains dependency then
      visit dependency
      decreaseLowlink name (← getEntry dependency).lowlink
    else if (← get).onStack.contains dependency then
      decreaseLowlink name (← getEntry dependency).index
  let entry ← getEntry name
  if entry.lowlink == entry.index then
    finishComponent name

def compute (lookup : Name → Except String Node) (roots : Array Name) : Except String State := do
  let (_, state) ← ((roots.forM visit).run { lookup }).run {}
  unless state.stack.isEmpty && state.onStack.isEmpty do
    throw "Internal SCC invariant: unfinished stack after all roots"
  return state

/--
Read the checked kernel map, never an unchecked elaborator declaration.
A missing dependency is an error, including a missing non-production constant.
Types and values are traversed for definitions/theorems/opaque constants;
inductive constructors are added explicitly, just as in Lean.collectAxioms.
-/
def checkedNode (kernel : Kernel.Environment) (name : Name) : Except String Node := do
  let some info := kernel.find? name
    | throw s!"Dependency absent from checked kernel: {name}"
  let mut dependencies := info.type.getUsedConstantsAsSet
  let mut ownAxioms : NameSet := {}
  match info with
  | .axiomInfo _ => ownAxioms := ownAxioms.insert name
  | .defnInfo value => dependencies := dependencies ++ value.value.getUsedConstantsAsSet
  | .thmInfo value => dependencies := dependencies ++ value.value.getUsedConstantsAsSet
  | .opaqueInfo value => dependencies := dependencies ++ value.value.getUsedConstantsAsSet
  | .inductInfo value =>
    for constructor in value.ctors do
      dependencies := dependencies.insert constructor
  | .quotInfo _ | .ctorInfo _ | .recInfo _ => pure ()
  let mut array : Array Name := #[]
  for dependency in dependencies do
    array := array.push dependency
  return { dependencies := array, ownAxioms }

def computeChecked (kernel : Kernel.Environment) (roots : Array Name) : Except String State :=
  compute (checkedNode kernel) roots

/--
Keep the existing production-root checked/type/safety guards unchanged. This
helper adds the same unsafe/partial guard for callers constructing root lists.
The full traversal above includes type/value dependencies of every such root.
-/
def validateRoot (kernel : Kernel.Environment) (name : Name) : Except String Unit := do
  let some info := kernel.find? name
    | throw s!"Production declaration absent from checked kernel: {name}"
  if info.isUnsafe || info.isPartial then
    throw s!"Unsafe or partial production declaration: {name}"

def axiomArray (axioms : NameSet) : Array Name := Id.run do
  let mut array := #[]
  for axiomName in axioms do
    array := array.push axiomName
  return array

end P23AuditMemo

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let kernel := env.checked.get
  let importedModuleNames := env.header.moduleNames
  let permitted : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut declarations : Array Json := #[]
  let mut roots : Array Name := #[]
  let mut origins : Array Name := #[]
  let mut kinds : Array String := #[]
  let mut theoremCount := 0
  let mut moduleNames : Array Name := #[]
  for (name, info) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let moduleName := importedModuleNames[idx]!
    unless `Paper23 |>.isPrefixOf moduleName do
      continue
    unless moduleNames.contains moduleName do
      moduleNames := moduleNames.push moduleName
    let some checkedInfo := kernel.find? name
      | throwError "Production declaration absent from checked kernel: {name}"
    unless checkedInfo.type == info.type do
      throwError "Elaborator/kernel type mismatch: {name}"
    if checkedInfo.isUnsafe || checkedInfo.isPartial then
      throwError "Unsafe or partial production declaration: {name}"
    let kind := match checkedInfo with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .quotInfo _ => "quotient"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
    if kind == "theorem" then
      theoremCount := theoremCount + 1
    roots := roots.push name
    origins := origins.push moduleName
    kinds := kinds.push kind
  let closureStarted ← liftIO IO.monoMsNow
  let memo ← ofExcept <| P23AuditMemo.computeChecked kernel roots
  let closureMilliseconds := (← liftIO IO.monoMsNow) - closureStarted
  for i in [:roots.size] do
    let name := roots[i]!
    let moduleName := origins[i]!
    let kind := kinds[i]!
    let some cached := memo.closures[name]?
      | throwError "Missing memoized axiom closure for {name}"
    let axioms := P23AuditMemo.axiomArray cached
    for ax in axioms do
      unless permitted.contains ax do
        throwError "Illegal transitive axiom {ax} in {name}"
    declarations := declarations.push <| Json.mkObj [
      ("name", toJson name.toString),
      ("module", toJson moduleName.toString),
      ("kind", toJson kind),
      ("checked_kernel_member", toJson true),
      ("axioms", toJson (axioms.map Name.toString))]
  if declarations.isEmpty then
    throwError "No production declarations were found; refusing an empty audit"
  if theoremCount == 0 then
    throwError "No production theorem was found; no proved result is being audited"
  let result := Json.mkObj [
    ("declaration_count", toJson declarations.size),
    ("unique_dependency_constants", toJson memo.scannedConstants),
    ("dependency_edges", toJson memo.dependencyEdges),
    ("scc_count", toJson memo.componentCount),
    ("closure_milliseconds", toJson closureMilliseconds),
    ("theorem_count", toJson theoremCount),
    ("modules", toJson (moduleNames.map Name.toString)),
    ("permitted_axioms", toJson (permitted.map Name.toString)),
    ("declarations", .arr declarations),
    ("paper_accepted", toJson false)]
  logInfo m!"P23_AUDIT_JSON:{result.compress}"
