import Paper15.NaturalSoundness
import Paper15.ExceptionalRepresentative

/-! Proof assembly only. All mathematical inputs are previously kernel-checked
constants. The assembly commands themselves introduce no computational axiom. -/
namespace Paper15.OrbitCheck
open Lean Elab Command

private def readWords : IO (Array Nat) := do
  let b ← IO.FS.readBinFile "Paper15/CertificateData/representatives.bin"
  unless b.size=61872*4 do throw (IO.userError "Wrong representative data length")
  let mut ws:=#[]
  for i in [:61872] do
    let mut n:=0
    for j in [:4] do n:=n+b[4*i+j]!.toNat*2^(8*j)
    ws:=ws.push n
  return ws
private def allType (p tree : Expr) : Expr := mkApp2 (mkConst ``Words.All) p tree
private def andProof (a b ap bp : Expr) : Expr := mkApp4 (mkConst ``And.intro) a b ap bp
private def addTheorem (name : Name) (type value : Expr) : CoreM Unit :=
  Lean.addDecl <| Declaration.thmDecl {name:=name,levelParams:=[],type:=type,value:=value}
private def wordProperty : Expr :=
  mkLambda `w BinderInfo.default (mkConst ``Nat)
    (mkApp2 (mkConst ``Or)
      (mkApp (mkConst ``GapHolds) (mkApp (mkConst ``DetTriangle.ofPattern) (mkBVar 0)))
      (mkApp (mkConst ``inExceptionalOrbit) (mkApp (mkConst ``DetTriangle.ofPattern) (mkBVar 0))))
private def gapTree : Array Nat → Nat → Nat → CoreM (Expr × Expr)
  | ws,0,pos => do
    let w:=ws[pos]?.getD 0
    let we:=toExpr w
    let te:=mkApp (mkConst ``DetTriangle.ofPattern) we
    let gap:=mkApp (mkConst ``GapHolds) te
    let exc:=mkApp (mkConst ``inExceptionalOrbit) te
    let p ← if w=2889227 then
      pure <| mkApp3 (mkConst ``Or.inr) gap exc (mkConst ``exceptional_representative_in_orbit)
    else do
      let declPrefix:=(`Paper15.NaturalCertificates).str s!"w{w}"
      let traceName:=declPrefix.str "trace"
      let checkedName:=declPrefix.str "checked"
      unless (← getEnv).contains checkedName do throwError "Missing checked gap certificate for {w}"
      let proof:=mkApp3 (mkConst ``NaturalExact.gapHolds_of_valid) we (mkConst traceName) (mkConst checkedName)
      pure <| mkApp3 (mkConst ``Or.inl) gap exc proof
    return (mkApp (mkConst ``Words.leaf) we,p)
  | ws,depth+1,pos => do
    let (l,lp) ← gapTree ws depth pos
    let (r,rp) ← gapTree ws depth (pos+2^depth)
    return (mkApp2 (mkConst ``Words.branch) l r,
      andProof (allType wordProperty l) (allType wordProperty r) lp rp)

elab "assemble_representative_gaps%" : command => do
  let ws ← readWords
  liftCoreM do
    let (_,p) ← gapTree ws 16 0
    addTheorem `Paper15.OrbitCheck.all_representatives_classified
      (allType wordProperty (mkConst ``representatives)) p

private def orbitTree : Nat → Nat → CoreM (Expr × Expr)
  | 0,b => do
    let declPrefix:=(`Paper15.OrbitBatches).str s!"b{b}"
    let treeName:=declPrefix.str "tree"
    let proofName:=declPrefix.str "checked"
    unless (← getEnv).contains proofName do throwError "Missing checked orbit batch {b}"
    return (mkConst treeName,mkConst proofName)
  | depth+1,b => do
    let (l,lp) ← orbitTree depth b
    let (r,rp) ← orbitTree depth (b+2^(9-(depth+1)))
    let pred:=mkConst ``HasCheckedNeighbours
    return (mkApp2 (mkConst ``Words.branch) l r,andProof (allType pred l) (allType pred r) lp rp)

elab "assemble_orbit_neighbours%" : command => do
  liftCoreM do
    let (_,p) ← orbitTree 9 0
    addTheorem `Paper15.OrbitCheck.all_neighbours_checked
      (allType (mkConst ``HasCheckedNeighbours) (mkConst ``representatives)) p
end Paper15.OrbitCheck
