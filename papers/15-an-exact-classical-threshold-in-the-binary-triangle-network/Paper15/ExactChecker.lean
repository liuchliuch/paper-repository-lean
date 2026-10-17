import Mathlib.Data.Int.Basic

/-!
# Executable exact certificate checker

Only integer arithmetic is used. A finite trace supplies subdivision choices
and the active-plane indices for each leaf. The checker reconstructs every
corner and every affine witness, insists on positive denominators, and checks
all 27 inequalities. There is no search algorithm, stopping-limit acceptance,
file I/O, floating point, or native_decide in these definitions.
-/
namespace Paper15.Exact

structure Tri (α : Type) where
  a : α
  b : α
  c : α
  deriving Repr, DecidableEq

def Tri.get {α} (v : Tri α) (i : Fin 3) : α :=
  if i = 0 then v.a else if i = 1 then v.b else v.c

def Tri.tabulate {α} (f : Fin 3 → α) : Tri α := ⟨f 0, f 1, f 2⟩

def Tri.all {α} (v : Tri α) (p : α → Bool) : Bool := p v.a && p v.b && p v.c

structure Corner where
  one : Int
  three : Int
  pair : Int
  deriving Repr, DecidableEq

abbrev Cube := Tri (Tri (Tri Corner))

def Cube.get (v : Cube) (i j k : Fin 3) : Corner := Tri.get (Tri.get (Tri.get v i) j) k

def Cube.tabulate (f : Fin 3 → Fin 3 → Fin 3 → Corner) : Cube :=
  Tri.tabulate (fun i => Tri.tabulate (fun j => Tri.tabulate (fun k => f i j k)))

structure Cell where
  den : Int
  corners : Cube
  deriving Repr, DecidableEq

def sign (word bit : Nat) : Int := if word.testBit bit then -1 else 1

def root (word : Nat) : Cell := ⟨1, Cube.tabulate fun i j k =>
  let a := sign word (18 + 3*j.val + k.val)
  let b := sign word (9 + 3*i.val + k.val)
  let c := sign word (3*i.val + j.val)
  ⟨a+b+c, a*b*c, a*b+b*c+c*a⟩⟩

def Corner.add (a b : Corner) : Corner :=
  ⟨a.one+b.one, a.three+b.three, a.pair+b.pair⟩

def Corner.double (a : Corner) : Corner := ⟨2*a.one, 2*a.three, 2*a.pair⟩

def child (c : Cell) (axis replaced other : Fin 3) : Cell :=
  ⟨2*c.den, Cube.tabulate fun i j k =>
    let f := Cube.get c.corners i j k
    if axis = 0 then
      if i = replaced then f.add (Cube.get c.corners other j k) else f.double
    else if axis = 1 then
      if j = replaced then f.add (Cube.get c.corners i other k) else f.double
    else
      if k = replaced then f.add (Cube.get c.corners i j other) else f.double⟩

structure Plane where
  a : Int
  b : Int
  c : Int
  deriving Repr, DecidableEq

def plane (den : Int) (f : Corner) : Plane := ⟨25*f.one, 25*f.three, 25*f.pair-27*den⟩

def Cell.at (c : Cell) (p : Fin 27) : Corner :=
  Cube.get c.corners ⟨p.val/9, by omega⟩ ⟨p.val/3%3, by omega⟩ ⟨p.val%3, by omega⟩

structure Point where
  x : Int
  y : Int
  d : Int
  deriving Repr, DecidableEq

def Point.normalize (p : Point) : Point :=
  if p.d < 0 then ⟨-p.x, -p.y, -p.d⟩ else p

def intersection (p q : Plane) : Point :=
  Point.normalize ⟨p.c*q.b-p.b*q.c, p.a*q.c-p.c*q.a, p.a*q.b-p.b*q.a⟩

def witness (c : Cell) (kind : Nat) (j k : Fin 27) : Point :=
  let p := plane c.den (c.at j)
  let q := plane c.den (c.at k)
  match kind with
  | 0 => ⟨0,0,1⟩
  | 1 => Point.normalize ⟨p.c,0,p.a⟩
  | 2 => Point.normalize ⟨0,p.c,p.b⟩
  | 3 => intersection p q
  | _ => ⟨0,0,0⟩

def satisfies (p : Plane) (w : Point) : Bool := decide (p.c*w.d ≤ p.a*w.x+p.b*w.y)

def leafValid (c : Cell) (kind : Nat) (j k : Fin 27) : Bool :=
  let w := witness c kind j k
  decide (0 < c.den) && decide (0 < w.d) &&
    c.corners.all (fun xs => xs.all (fun ys => ys.all (fun f => satisfies (plane c.den f) w)))

/-- A compact, explicitly supplied cell. Its equality to the computed cell
is rechecked in the kernel at every checkpoint; it is never trusted. -/
def packedCell (depth bits : Nat) : Cell :=
  let den : Nat := 2^depth
  let width := depth+3
  let read (n : Nat) : Int := Int.ofNat ((bits >>> (n*width)) % (2^width)) - 3*Int.ofNat den
  ⟨Int.ofNat den, Cube.tabulate fun i j k =>
    let n := 3*(9*i.val+3*j.val+k.val)
    ⟨read n, read (n+1), read (n+2)⟩⟩

inductive Trace where
  | leaf (kind : Nat) (j k : Fin 27)
  | split (axis i j : Fin 3) (left right : Trace)
  | checkpoint (cell : Cell) (trace : Trace)
  deriving Repr, DecidableEq

def valid (c : Cell) : Trace → Bool
  | .leaf kind j k => leafValid c kind j k
  | .split a i j l r => decide (i ≠ j) && valid (child c a i j) l && valid (child c a j i) r
  | .checkpoint claimed t => decide (c = claimed) && valid claimed t

def verified (v : Nat × Trace) : Bool := valid (root v.1) v.2

end Paper15.Exact
