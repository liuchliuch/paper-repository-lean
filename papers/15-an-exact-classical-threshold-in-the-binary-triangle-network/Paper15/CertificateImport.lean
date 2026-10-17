import Paper15.CertificateSyntax

/-!
# Importing untrusted certificate data as ordinary Lean terms

The binary file contains only split choices and affine-witness indices. This
elaborator reconstructs cell DATA to break up reduction costs; every such cell
is rechecked by `valid` at a checkpoint. No native evaluation result is used as
a proof. The final `valid ... = true` assertion must be proved in the kernel.
-/
namespace Paper15.Exact
open Lean Elab Term

initialize certificateBytes : IO.Ref (Option ByteArray) ← IO.mkRef none

private def readCertificateBytes : TermElabM ByteArray := do
  if let some bytes ← certificateBytes.get then return bytes
  let bytes ← IO.FS.readBinFile "Paper15/CertificateData/forest.bin"
  certificateBytes.set (some bytes)
  return bytes

private def cellExpr (c : Cell) : Expr := Id.run do
  let mut values : Array Expr := #[]
  for i in ([0,1,2] : List (Fin 3)) do
    for j in ([0,1,2] : List (Fin 3)) do
      for k in ([0,1,2] : List (Fin 3)) do
        let f := Cube.get c.corners i j k
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

private def parseCertificate : Nat → ByteArray → Nat → Cell → Nat → Array Expr → Array Expr → TermElabM (Expr × Nat)
  | 0, _, _, _, _, _, _ => throwError "Certificate nesting exceeds the parser bound"
  | fuel+1, bytes, pos, c, depth, fins3, fins27 => do
    unless pos+3 ≤ bytes.size do throwError "Truncated certificate"
    let a := bytes[pos]!.toNat
    let i := bytes[pos+1]!.toNat
    let j := bytes[pos+2]!.toNat
    if a ≥ 128 then
      unless a ≤ 131 ∧ i < 27 ∧ j < 27 do throwError "Invalid certificate leaf"
      return (mkApp3 (Lean.mkConst ``Trace.leaf) (toExpr (a-128)) fins27[i]! fins27[j]!, pos+3)
    else
      unless a < 3 ∧ i < j ∧ j < 3 do throwError "Invalid source axis or unordered edge"
      let af : Fin 3 := ⟨a%3, by omega⟩
      let fi : Fin 3 := ⟨i%3, by omega⟩
      let fj : Fin 3 := ⟨j%3, by omega⟩
      let (l, next) ← parseCertificate fuel bytes (pos+3) (child c af fi fj) (depth+1) fins3 fins27
      let (r, endPos) ← parseCertificate fuel bytes next (child c af fj fi) (depth+1) fins3 fins27
      let t := mkApp5 (Lean.mkConst ``Trace.split) fins3[a]! fins3[i]! fins3[j]! l r
      if depth > 0 ∧ depth % 4 = 0 then
        return (mkApp2 (Lean.mkConst ``Trace.checkpoint) (cellExpr c) t, endPos)
      else return (t,endPos)

elab "certificate_trace% " word:num offset:num nodes:num : term => do
  let word := word.getNat
  let pos := offset.getNat
  let nodes := nodes.getNat
  let bytes ← readCertificateBytes
  let mut fins3 : Array Expr := #[]
  let mut fins27 : Array Expr := #[]
  for i in [:3] do
    fins3 := fins3.push (← elabTerm (← `(($(quote i) : Fin 3))) none)
  for i in [:27] do
    fins27 := fins27.push (← elabTerm (← `(($(quote i) : Fin 27))) none)
  let (t, endPos) ← parseCertificate 64 bytes pos (root word) 0 fins3 fins27
  unless endPos = pos+3*nodes do throwError "Certificate node count mismatch"
  return t

end Paper15.Exact
