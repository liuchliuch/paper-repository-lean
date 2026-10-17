import Paper15.CertificateImport
import Paper15.ExactComposition
import Paper15.NaturalChecker

/-!
# Compositional certificate proof generation

The command below generates ordinary data definitions and theorem declarations.
All declarations go through Lean.addDecl, the same kernel-checked API used by
normal Lean declarations. The proof language consists only of reflexivity,
valid_split and valid_checkpoint. A false leaf comparison or false checkpoint
equality fails kernel checking. There is no unchecked declaration insertion,
native_decide, custom axiom or trusted computation result.
-/
namespace Paper15.NaturalExact.Tool
open Lean Elab Command Exact

initialize compiledCertificateBytes : IO.Ref (Option ByteArray) ← IO.mkRef none

private def readCompiledCertificateBytes : IO ByteArray := do
  if let some bytes ← compiledCertificateBytes.get then return bytes
  let bytes ← IO.FS.readBinFile "Paper15/CertificateData/forest.bin"
  compiledCertificateBytes.set (some bytes)
  return bytes

private def numeralCellExpr (c : Cell) : Expr := Id.run do
  let mut values : Array Expr := #[]
  for i in ([0,1,2] : List (Fin 3)) do
    for j in ([0,1,2] : List (Fin 3)) do
      for k in ([0,1,2] : List (Fin 3)) do
        let f := c.corners.get i |>.get j |>.get k
        values := values.push (mkApp3 (Lean.mkConst ``Corner.mk)
          (toExpr f.one) (toExpr f.three) (toExpr f.pair))
  let mut ty := Lean.mkConst ``Corner
  for _ in [:3] do
    let mut next : Array Expr := #[]
    for i in [:values.size/3] do
      next := next.push (mkApp4 (Lean.mkConst ``Tri.mk) ty values[3*i]! values[3*i+1]! values[3*i+2]!)
    values := next
    ty := mkApp (Lean.mkConst ``Tri) ty
  return mkApp2 (Lean.mkConst ``Cell.mk) (toExpr c.den) values[0]!

private def eqTrue (e : Expr) : Expr :=
  mkApp3 (Lean.mkConst ``Eq [Level.succ Level.zero]) (Lean.mkConst ``Bool) e (toExpr true)

private def refl (ty value : Expr) : Expr :=
  mkApp2 (Lean.mkConst ``Eq.refl [Level.succ Level.zero]) ty value

private def addData (declName : Name) (ty value : Expr) : CoreM Unit :=
  Lean.addDecl <| Declaration.defnDecl {
    name := declName
    levelParams := []
    type := ty
    value := value
    hints := .regular 0
    safety := .safe
  }

private def addChecked (declName : Name) (c t proof : Expr) : CoreM Unit :=
  Lean.addDecl <| Declaration.thmDecl {
    name := declName
    levelParams := []
    type := eqTrue (mkApp2 (Lean.mkConst ``valid) c t)
    value := proof
  }

/-- Recursion fuel bounds parsing only; exhaustion is an error, never acceptance. -/
private def compileTree : Nat → ByteArray → Nat → Cell → Expr → Nat → Nat → Bool → Name →
    CoreM (Expr × Expr × Nat)
  | 0, _, _, _, _, _, _, _, _ => throwError "Certificate nesting exceeds the compiler bound"
  | fuel+1, bytes, pos, c, cExpr, depth, origin, fresh, declPrefix => do
    if fresh then
      let cName := declPrefix.str s!"cell_{pos}"
      let tName := declPrefix.str s!"trace_{pos}"
      let pName := declPrefix.str s!"checked_{pos}"
      addData cName (Lean.mkConst ``Cell) (numeralCellExpr c)
      let cc := Lean.mkConst cName
      let (t, p, endPos) ← compileTree fuel bytes pos c cc depth depth false declPrefix
      addData tName (Lean.mkConst ``Trace) t
      let tt := Lean.mkConst tName
      addChecked pName cc tt p
      let wrapped := mkApp2 (Lean.mkConst ``Trace.checkpoint) cc tt
      let proof := mkApp5 (Lean.mkConst ``valid_checkpoint) cExpr cc tt
        (refl (Lean.mkConst ``Cell) cc) (Lean.mkConst pName)
      return (wrapped,proof,endPos)
    unless pos+3 ≤ bytes.size do throwError "Truncated certificate"
    let a := bytes[pos]!.toNat
    let i := bytes[pos+1]!.toNat
    let j := bytes[pos+2]!.toNat
    let trueProof := refl (Lean.mkConst ``Bool) (toExpr true)
    if a ≥ 128 then
      unless a ≤ 131 ∧ i < 27 ∧ j < 27 do throwError "Invalid leaf data"
      let old : Exact.Cell := ⟨c.den,map3 (map3 (map3 (fun f =>
        (⟨(f.one:Int)-3*c.den,(f.three:Int)-c.den,(f.pair:Int)-c.den⟩ : Exact.Corner)))) c.corners⟩
      let wi : Fin 27 := ⟨i%27,by omega⟩
      let wj : Fin 27 := ⟨j%27,by omega⟩
      let w := Exact.witness old (a-128) wi wj
      let we := mkAppN (Lean.mkConst ``Witness.mk) #[toExpr w.x.toNat,toExpr (-w.x).toNat,
        toExpr w.y.toNat,toExpr (-w.y).toNat,toExpr w.d.toNat]
      return (mkApp (Lean.mkConst ``Trace.leaf) we, trueProof, pos+3)
    if depth > origin ∧ depth % 4 = 0 then
      return ← compileTree fuel bytes pos c cExpr depth origin true declPrefix
    unless a < 3 ∧ i < j ∧ j < 3 do throwError "Invalid source axis or unordered edge"
    let af : Fin 3 := ⟨a%3, by omega⟩
    let fi : Fin 3 := ⟨i%3, by omega⟩
    let fj : Fin 3 := ⟨j%3, by omega⟩
    let ae := mkApp (Lean.mkConst ``Exact.fin3) (toExpr a)
    let ie := mkApp (Lean.mkConst ``Exact.fin3) (toExpr i)
    let je := mkApp (Lean.mkConst ``Exact.fin3) (toExpr j)
    let lc := mkApp4 (Lean.mkConst ``child) cExpr ae ie je
    let rc := mkApp4 (Lean.mkConst ``child) cExpr ae je ie
    let (l,lp,next) ← compileTree fuel bytes (pos+3) (child c af fi fj) lc (depth+1) origin false declPrefix
    let (r,rp,endPos) ← compileTree fuel bytes next (child c af fj fi) rc (depth+1) origin false declPrefix
    let t := mkApp5 (Lean.mkConst ``Trace.split) ae ie je l r
    let p := mkAppN (Lean.mkConst ``valid_split) #[cExpr,ae,ie,je,l,r,trueProof,lp,rp]
    return (t,p,endPos)

elab "certify_nat_word% " word:num offset:num nodes:num : command => do
  let w := word.getNat
  let pos := offset.getNat
  let n := nodes.getNat
  let bytes ← readCompiledCertificateBytes
  let declPrefix := (`Paper15.NaturalCertificates).str s!"w{w}"
  liftCoreM do
    let cExpr := mkApp (Lean.mkConst ``root) (toExpr w)
    let (t,p,endPos) ← compileTree 96 bytes pos (root w) cExpr 0 0 false declPrefix
    unless endPos = pos+3*n do throwError "Certificate node count mismatch"
    let tName := declPrefix.str "trace"
    addData tName (Lean.mkConst ``Trace) t
    addChecked (declPrefix.str "checked") cExpr (Lean.mkConst tName) p

end Paper15.NaturalExact.Tool
