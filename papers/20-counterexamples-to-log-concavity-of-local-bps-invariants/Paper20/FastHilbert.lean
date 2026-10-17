import Paper20.Hilbert

/-! A list implementation of the same finite coefficient calculation.
Blocks avoid the repeated linear array updates of kernel reduction. Its
semantic connection to the reference array program is proved separately. -/
namespace Paper20.FastHilbert

/-- Successive blocks of size `a`, adding the previous output block.
This is the geometric-series recurrence `u_j=t_j+u_(j-a)`. -/
def geomBlocks (a : ℕ) : ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, _ => []
  | fuel+1, old, prev =>
    if old.isEmpty then [] else
      let cur := List.zipWith Nat.add (old.take a) prev
      cur ++ geomBlocks a fuel (old.drop a) cur

def geom (t : List ℕ) (a : ℕ) : List ℕ :=
  if a = 0 then (geomStep t.toArray a).toList
  else geomBlocks a t.length t (List.replicate a 0)

def series (hooks : List ℕ) (len : ℕ) : List ℕ :=
  hooks.foldl geom ((1 :: List.replicate (len-1) 0).take len)

def summand (r k d : ℕ) (parts : List ℕ) : List ℕ :=
  let Ei := shiftE parts k d
  if Ei < 0 ∨ d < Ei.toNat then List.replicate (d+1) 0 else
    let E := Ei.toNat
    List.replicate E 0 ++
      (series (hooksOf parts) (d-E+1)).map (fun n => dimOf r parts*n)

def addPart (r k d : ℕ) (H : List ℕ) (parts : List ℕ) : List ℕ :=
  let Ei := shiftE parts k d
  if Ei < 0 ∨ d < Ei.toNat then H else
    let E := Ei.toNat
    List.zipWith Nat.add H (List.replicate E 0 ++
      (series (hooksOf parts) (d-E+1)).map (fun n => dimOf r parts*n))

def total (r k : ℕ) : List ℕ :=
  (partitionsOf r).foldl (addPart r k (deg r k)) (List.replicate (deg r k+1) 0)

/-- A transparent linear certificate for one geometric-series update. -/
def checkGeom (a : ℕ) (old out : List ℕ) : Bool :=
  (out.length == old.length) &&
    (if a = 0 then out == old.map (fun n => n+n) else
      out.take a == old.take a &&
      List.zipWith Nat.add (old.drop a) out == out.drop a)

end Paper20.FastHilbert
