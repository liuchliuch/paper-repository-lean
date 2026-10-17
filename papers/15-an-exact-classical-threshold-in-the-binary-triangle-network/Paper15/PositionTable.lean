import Paper15.OrbitPositions
import Lean
namespace Paper15.OrbitCheck
open Exact Lean Elab Command
abbrev PositionMap := Tri (Tri (Tri Nat))
inductive PositionMaps where
  | leaf (map : PositionMap)
  | branch (left right : PositionMaps)
def PositionMaps.get : PositionMaps → Nat → PositionMap
  | .leaf m,_ => m
  | .branch l r,g => if g%2=0 then l.get (g/2) else r.get (g/2)
def PositionMap.at (m : PositionMap) (p : Fin 27) : Nat :=
  Tri.get (Tri.get (Tri.get m ⟨p.val/9,by omega⟩) ⟨p.val/3%3,by omega⟩) ⟨p.val%3,by omega⟩

def checkPositionMap (g : Nat) (m : PositionMap) : Bool :=
  slots.all (fun p => m.at p == (position g p).val)

private def mapExpr (g : Nat) : Expr := Id.run do
  let mut values : Array Expr:=#[]
  for i in [:27] do
    let p : Fin 27:=⟨i%27,by omega⟩
    values:=values.push (toExpr (if g<1296 then (position g p).val else 0))
  let mut ty:=mkConst ``Nat
  for _ in [:3] do
    let mut next:=#[]
    for i in [:values.size/3] do
      next:=next.push (mkApp4 (mkConst ``Tri.mk) ty values[3*i]! values[3*i+1]! values[3*i+2]!)
    values:=next
    ty:=mkApp (mkConst ``Tri) ty
  return values[0]!
private def tableExpr : Nat → Nat → Nat → Expr
  | 0,pos,_ => mkApp (mkConst ``PositionMaps.leaf) (mapExpr pos)
  | depth+1,pos,stride => mkApp2 (mkConst ``PositionMaps.branch)
      (tableExpr depth pos (2*stride)) (tableExpr depth (pos+stride) (2*stride))

/-- Only ordinary data is emitted. The complete table is checked separately. -/
elab "position_table%" : command =>
  liftCoreM <| Lean.addDecl <| Declaration.defnDecl {
    name:=`Paper15.OrbitCheck.positionMaps
    levelParams:=[]
    type:=mkConst ``PositionMaps
    value:=tableExpr 11 0 1
    hints:=.regular 0
    safety:=.safe
  }
end Paper15.OrbitCheck
