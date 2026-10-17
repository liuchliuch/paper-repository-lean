import Paper15.ExactChecker
/-!
# Natural-number affine-certificate checker

A common positive denominator D is used for all cell corners. Stored features
are D*w1+3D, D*w2+D and D*w3+D, so root and subdivision arithmetic uses only
natural numbers. A leaf supplies arbitrary signed rational multipliers as
nonnegative numerator pairs and a positive denominator. The displayed natural
inequality is the exact affine inequality after moving all negative terms to
the opposite side. Every inequality and checkpoint is reduced in the kernel.
-/
namespace Paper15.NaturalExact
open Exact

structure Corner where
  one : Nat
  three : Nat
  pair : Nat
  deriving Repr, DecidableEq
abbrev Cube := Tri (Tri (Tri Corner))
structure Cell where
  den : Nat
  corners : Cube
  deriving Repr, DecidableEq

def Corner.add (x y : Corner) : Corner := ⟨x.one+y.one,x.three+y.three,x.pair+y.pair⟩
def Corner.double (x : Corner) : Corner := ⟨2*x.one,2*x.three,2*x.pair⟩

def map3 {α β : Type} (f : α → β) (v : Tri α) : Tri β := ⟨f v.a,f v.b,f v.c⟩
def zip3 {α β γ : Type} (f : α → β → γ) (v : Tri α) (w : Tri β) : Tri γ :=
  ⟨f v.a w.a,f v.b w.b,f v.c w.c⟩
def mix3 {α : Type} (add : α → α → α) (double : α → α) (v : Tri α) (i j : Fin 3) : Tri α :=
  if i=0 then ⟨add v.a (v.get j),double v.b,double v.c⟩
  else if i=1 then ⟨double v.a,add v.b (v.get j),double v.c⟩
  else ⟨double v.a,double v.b,add v.c (v.get j)⟩
def rowAdd := zip3 Corner.add
def rowDouble := map3 Corner.double
def planeAdd := zip3 rowAdd
def planeDouble := map3 rowDouble

def child (c : Cell) (a i j : Fin 3) : Cell := ⟨2*c.den,
  if a=0 then mix3 planeAdd planeDouble c.corners i j
  else if a=1 then map3 (fun v => mix3 rowAdd rowDouble v i j) c.corners
  else map3 (fun v => map3 (fun w => mix3 Corner.add Corner.double w i j) v) c.corners⟩

def rootCorner (a b c : Bool) : Corner :=
  ⟨2*((if a then 0 else 1)+(if b then 0 else 1)+(if c then 0 else 1)),
    if xor (xor a b) c then 0 else 2,if a==b && b==c then 4 else 0⟩
def root (w : Nat) : Cell := ⟨1,Tri.tabulate fun i => Tri.tabulate fun j => Tri.tabulate fun k =>
  rootCorner (w.testBit (18+3*j.val+k.val)) (w.testBit (9+3*i.val+k.val)) (w.testBit (3*i.val+j.val))⟩

structure Witness where
  lp : Nat
  ln : Nat
  mp : Nat
  mn : Nat
  den : Nat
  deriving Repr

def satisfies (d : Nat) (w : Witness) (f : Corner) : Bool := decide (
  25*w.den*f.pair+(75*w.lp+25*w.mp)*d+25*w.ln*f.one+25*w.mn*f.three ≤
  (52*w.den+75*w.ln+25*w.mn)*d+25*w.lp*f.one+25*w.mp*f.three)

def leafValid (c : Cell) (w : Witness) : Bool :=
  decide (0<c.den) && decide (0<w.den) &&
    c.corners.all (fun x => x.all (fun y => y.all (satisfies c.den w)))

inductive Trace where
  | leaf (w : Witness)
  | split (a i j : Fin 3) (left right : Trace)
  | checkpoint (cell : Cell) (trace : Trace)

def valid (c : Cell) : Trace → Bool
  | .leaf w => leafValid c w
  | .split a i j l r => decide (i≠j) && valid (child c a i j) l && valid (child c a j i) r
  | .checkpoint cc t => decide (c=cc) && valid cc t

theorem valid_split (c : Cell) (a i j : Fin 3) (l r : Trace)
    (hij : decide (i≠j)=true) (hl : valid (child c a i j) l=true)
    (hr : valid (child c a j i) r=true) : valid c (.split a i j l r)=true := by
  simp only [valid,hij,hl,hr,Bool.and_true]
theorem valid_checkpoint (c cc : Cell) (t : Trace) (he : c=cc) (ht : valid cc t=true) :
    valid c (.checkpoint cc t)=true := by
  subst cc
  simp only [valid,decide_true,ht,Bool.and_true]
def verified (p : Nat × Trace) : Bool := valid (root p.1) p.2
def AllVerified : List (Nat × Trace) → Prop
  | [] => True
  | p :: ps => verified p=true ∧ AllVerified ps
end Paper15.NaturalExact
