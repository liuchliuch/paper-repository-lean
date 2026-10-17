import Paper15.OrbitChecker
import Lean

namespace Paper15.OrbitCheck
inductive Words where
  | leaf (word : Nat)
  | branch (left right : Words)
  deriving Repr

def Words.at : Words → Nat → Nat
  | .leaf w,_ => w
  | .branch l r,i => if i%2=0 then l.at (i/2) else r.at (i/2)

def Words.All (P : Nat → Prop) : Words → Prop
  | .leaf w => P w
  | .branch l r => l.All P ∧ r.All P

def Words.mem (w : Nat) : Words → Prop
  | .leaf a => w=a
  | .branch l r => l.mem w ∨ r.mem w

theorem Words.at_mem (t : Words) (i : Nat) : t.mem (t.at i) := by
  induction t generalizing i with
  | leaf w => rfl
  | branch l r hl hr =>
    simp only [Words.at,Words.mem]
    split_ifs
    · exact Or.inl (hl _)
    · exact Or.inr (hr _)

theorem Words.all_mem {P : Nat → Prop} {t : Words} (h : t.All P) {w : Nat} (hw : t.mem w) : P w := by
  induction t with
  | leaf a => exact hw ▸ h
  | branch l r hl hr =>
    rcases hw with hwl|hwr
    · exact hl h.1 hwl
    · exact hr h.2 hwr

open Lean Elab Command
private def wordExpr : Array Nat → Nat → Nat → Expr
  | words,0,pos => mkApp (mkConst ``Words.leaf) (toExpr (words[pos]?.getD 0))
  | words,depth+1,pos => mkApp2 (mkConst ``Words.branch)
      (wordExpr words depth pos) (wordExpr words depth (pos+2^depth))

/-- Ordinary data import. No mathematical assertion is made by this command. -/
elab "representative_tree%" : command => do
  let bytes ← IO.FS.readBinFile "Paper15/CertificateData/representatives.bin"
  unless bytes.size=4*61872 do throwError "Wrong representative data length"
  let mut words : Array Nat := #[]
  for i in [:61872] do
    let mut w:=0
    for j in [:4] do w:=w+bytes[4*i+j]!.toNat*2^(8*j)
    words:=words.push w
  liftCoreM <| Lean.addDecl <| Declaration.defnDecl {
    name := `Paper15.OrbitCheck.representatives
    levelParams := []
    type := mkConst ``Words
    value := wordExpr words 16 0
    hints := .regular 0
    safety := .safe
  }
end Paper15.OrbitCheck
