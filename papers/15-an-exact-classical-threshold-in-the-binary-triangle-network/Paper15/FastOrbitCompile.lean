import Paper15.FastOrbitChecker

namespace Paper15.OrbitCheck
open Lean Elab Command Exact

private structure ImportData where
  words : Array Nat
  neighbours : ByteArray
  indices : Std.HashMap Nat Nat
initialize fastOrbitImportData : IO.Ref (Option ImportData) ← IO.mkRef none

private def readLE (b : ByteArray) (pos count : Nat) : Nat := Id.run do
  let mut n:=0
  for j in [:count] do n:=n+b[pos+j]!.toNat*2^(8*j)
  return n
private def reverseBits (n count : Nat) : Nat := Id.run do
  let mut r:=0
  for j in [:count] do r:=2*r+((n/2^j)%2)
  return r
private def imports : IO ImportData := do
  if let some d ← fastOrbitImportData.get then return d
  let b ← IO.FS.readBinFile "Paper15/CertificateData/representatives.bin"
  let neighbours ← IO.FS.readBinFile "Paper15/CertificateData/neighbours.bin"
  unless b.size=4*61872 ∧ neighbours.size=166*61872 do throw (IO.userError "Wrong orbit data lengths")
  let mut words:=#[]
  let mut indices:Std.HashMap Nat Nat:={}
  for i in [:61872] do
    let w:=readLE b (4*i) 4
    words:=words.push w
    indices:=indices.insert w i
  let d:ImportData:=⟨words,neighbours,indices⟩
  fastOrbitImportData.set (some d)
  return d
private def addData (name : Name) (type value : Expr) : CoreM Unit :=
  Lean.addDecl <| Declaration.defnDecl {name:=name,levelParams:=[],type:=type,value:=value,hints:=.regular 0,safety:=.safe}
private def rowExpr (d : ImportData) (idx : Nat) : CoreM Expr := do
  let base:=166*idx
  let mut xs:=#[]
  for bit in [:27] do
    let target:=readLE d.neighbours (base+4+6*bit) 4
    let code:=readLE d.neighbours (base+8+6*bit) 2
    let some ti:=d.indices[target]? | throwError "Missing orbit target"
    xs:=xs.push (mkApp2 (mkConst ``Choice.mk) (toExpr (reverseBits ti 16)) (toExpr code))
  let mut ty:=mkConst ``Choice
  for _ in [:3] do
    let mut next:=#[]
    for i in [:xs.size/3] do
      next:=next.push (mkApp4 (mkConst ``Tri.mk) ty xs[3*i]! xs[3*i+1]! xs[3*i+2]!)
    xs:=next
    ty:=mkApp (mkConst ``Tri) ty
  return xs[0]!
private def compileLeaf (d : ImportData) (idx : Nat) (declPrefix : Name) : CoreM Expr := do
  let idx:=if idx<61872 then idx else 0
  let word:=d.words[idx]!
  let rowName:=declPrefix.str s!"row_{word}"
  let proofName:=declPrefix.str s!"checked_{word}"
  unless (← getEnv).contains rowName do
    let row ← rowExpr d idx
    addData rowName (mkConst ``Row) row
    let rowC:=mkConst rowName
    Lean.addDecl <| Declaration.thmDecl {
      name:=proofName
      levelParams:=[]
      type:=mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool)
        (mkApp2 (mkConst ``fastRowValid) (toExpr word) rowC) (toExpr true)
      value:=mkApp2 (mkConst ``Eq.refl [Level.succ Level.zero]) (mkConst ``Bool) (toExpr true)
    }
  return mkAppN (mkConst ``Exists.intro [Level.succ Level.zero]) #[mkConst ``Row,
    mkLambda `row BinderInfo.default (mkConst ``Row)
      (mkApp3 (mkConst ``Eq [Level.succ Level.zero]) (mkConst ``Bool)
        (mkApp2 (mkConst ``rowValid) (toExpr word) (mkBVar 0)) (toExpr true)),
    mkConst rowName,mkApp3 (mkConst ``fastRowValid_sound) (toExpr word) (mkConst rowName) (mkConst proofName)]
private def compileBranch : ImportData → Nat → Nat → Name → CoreM (Expr × Expr)
  | d,0,pos,declPrefix => do
    let word:=d.words[pos]?.getD 0
    let p ← compileLeaf d pos declPrefix
    return (mkApp (mkConst ``Words.leaf) (toExpr word),p)
  | d,depth+1,pos,declPrefix => do
    let (l,lp) ← compileBranch d depth pos declPrefix
    let (r,rp) ← compileBranch d depth (pos+2^depth) declPrefix
    let tree:=mkApp2 (mkConst ``Words.branch) l r
    let pred:=mkConst ``HasCheckedNeighbours
    let p:=mkApp4 (mkConst ``And.intro)
      (mkApp2 (mkConst ``Words.All) pred l) (mkApp2 (mkConst ``Words.All) pred r) lp rp
    return (tree,p)

elab "certify_fast_orbit_batch% " batch:num : command => do
  let b:=batch.getNat
  unless b<512 do throwError "Orbit batch out of range"
  let d ← imports
  let declPrefix:=(`Paper15.OrbitBatches).str s!"b{b}"
  liftCoreM do
    let (tree,p) ← compileBranch d 7 (reverseBits b 9*128) declPrefix
    let treeName:=declPrefix.str "tree"
    addData treeName (mkConst ``Words) tree
    Lean.addDecl <| Declaration.thmDecl {
      name:=declPrefix.str "checked"
      levelParams:=[]
      type:=mkApp2 (mkConst ``Words.All) (mkConst ``HasCheckedNeighbours) (mkConst treeName)
      value:=p
    }
end Paper15.OrbitCheck
