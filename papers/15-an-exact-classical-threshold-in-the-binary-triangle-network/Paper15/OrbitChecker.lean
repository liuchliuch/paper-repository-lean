import Paper15.ExactChecker
import Mathlib.Data.Fin.VecNotation
import Mathlib.Logic.Equiv.Fin.Basic

namespace Paper15.OrbitCheck
open Exact

/-- Explicit lexicographic enumeration of the six permutations of Fin 3. -/
def perm3 (n : Nat) : Equiv.Perm (Fin 3) :=
  match n%6 with
  | 0 => Equiv.refl _
  | 1 => Equiv.swap 1 2
  | 2 => Equiv.swap 0 1
  | 3 => (Equiv.swap 1 2).trans (Equiv.swap 0 1)
  | 4 => (Equiv.swap 0 1).trans (Equiv.swap 1 2)
  | _ => Equiv.swap 0 2

structure Tables where
  A : Fin 3 → Fin 3 → Bool
  B : Fin 3 → Fin 3 → Bool
  C : Fin 3 → Fin 3 → Bool

def decode (word : Nat) : Tables where
  A j k := word.testBit (18+3*j.val+k.val)
  B k i := word.testBit (9+3*i.val+k.val)
  C i j := word.testBit (3*i.val+j.val)

def Tables.slot (T : Tables) (p : Fin 27) : Bool :=
  if h : p.val<9 then T.C ⟨p.val/3,by omega⟩ ⟨p.val%3,by omega⟩
  else if h : p.val<18 then T.B ⟨(p.val-9)%3,by omega⟩ ⟨(p.val-9)/3,by omega⟩
  else T.A ⟨(p.val-18)/3,by omega⟩ ⟨(p.val-18)%3,by omega⟩

def relabel (a b c : Equiv.Perm (Fin 3)) (T : Tables) : Tables :=
  ⟨fun y z => T.A (b y) (c z),fun z x => T.B (c z) (a x),fun x y => T.C (a x) (b y)⟩

def party (n : Nat) (T : Tables) : Tables :=
  match n%6 with
  | 0 => T
  | 1 => ⟨fun y z => T.A z y,fun z x => T.C x z,fun x y => T.B y x⟩
  | 2 => ⟨fun y z => T.B z y,fun z x => T.A x z,fun x y => T.C y x⟩
  | 3 => ⟨T.C,T.A,T.B⟩
  | 4 => ⟨T.B,T.C,T.A⟩
  | _ => ⟨fun y z => T.C z y,fun z x => T.B x z,fun x y => T.A y x⟩

def Tables.flip (T : Tables) : Tables := ⟨fun y z => !(T.A y z),fun z x => !(T.B z x),fun x y => !(T.C x y)⟩

def act (code : Nat) (T : Tables) : Tables :=
  let d:=code/2
  let t:=party (d%6) (relabel (perm3 (d/216)) (perm3 (d/36%6)) (perm3 (d/6%6)) T)
  if code%2=1 then t.flip else t

/-- An explicit list, used to make kernel normalization small and predictable. -/
def slots : List (Fin 27) := List.finRange 27

def transition (r bit s code : Nat) : Bool :=
  decide (bit<27) && slots.all (fun p =>
    (act code (decode s)).slot p == (if p.val=bit then !((decode r).slot p) else (decode r).slot p))

end Paper15.OrbitCheck
