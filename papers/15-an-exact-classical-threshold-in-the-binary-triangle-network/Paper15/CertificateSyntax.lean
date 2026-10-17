import Paper15.ExactChecker
import Lean

/-!
# Compact syntax for untrusted integer checkpoint data

The elaborator expands a packed numeral into ordinary `Cell`, `Tri` and `Int`
constructors. It generates DATA, never a proof. `valid` still checks equality
of every supplied checkpoint to its computed parent in the Lean kernel. This
avoids repeatedly decoding a large packed numeral during kernel reduction.
-/
namespace Paper15.Exact
open Lean Elab Term

elab "packed_cell% " depth:num bits:num : term => do
  let d := depth.getNat
  let packed := bits.getNat
  let den : Nat := 2^d
  let width := d+3
  let mut values : Array Expr := #[]
  for p in [:27] do
    let mut entries : Array Expr := #[]
    for k in [:3] do
      let n := 3*p+k
      let v : Int := Int.ofNat ((packed >>> (n*width)) % (2^width)) - 3*Int.ofNat den
      entries := entries.push (toExpr v)
    values := values.push (mkApp3 (Lean.mkConst ``Corner.mk) entries[0]! entries[1]! entries[2]!)
  let mut ty := Lean.mkConst ``Corner
  for _ in [:3] do
    let mut next : Array Expr := #[]
    for i in [:values.size/3] do
      next := next.push (mkApp4 (Lean.mkConst ``Tri.mk) ty values[3*i]! values[3*i+1]! values[3*i+2]!)
    values := next
    ty := mkApp (Lean.mkConst ``Tri) ty
  return mkApp2 (Lean.mkConst ``Cell.mk) (toExpr (Int.ofNat den)) values[0]!

end Paper15.Exact
