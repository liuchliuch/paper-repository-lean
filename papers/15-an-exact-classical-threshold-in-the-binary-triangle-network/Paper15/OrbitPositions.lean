import Paper15.OrbitRows
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
namespace Paper15.OrbitCheck
open Exact
def posA (y z : Fin 3) : Fin 27 := ⟨18+3*y.val+z.val,by omega⟩
def posB (z x : Fin 3) : Fin 27 := ⟨9+3*x.val+z.val,by omega⟩
def posC (x y : Fin 3) : Fin 27 := ⟨3*x.val+y.val,by omega⟩
lemma slotA (T : Tables) (y z : Fin 3) : T.slot (posA y z)=T.A y z := by fin_cases y <;> fin_cases z <;> rfl
lemma slotB (T : Tables) (z x : Fin 3) : T.slot (posB z x)=T.B z x := by fin_cases z <;> fin_cases x <;> rfl
lemma slotC (T : Tables) (x y : Fin 3) : T.slot (posC x y)=T.C x y := by fin_cases x <;> fin_cases y <;> rfl
def relabelPos (a b c : Equiv.Perm (Fin 3)) (p : Fin 27) : Fin 27 :=
  if h : p.val<9 then posC (a ⟨p.val/3,by omega⟩) (b ⟨p.val%3,by omega⟩)
  else if h : p.val<18 then posB (c ⟨(p.val-9)%3,by omega⟩) (a ⟨(p.val-9)/3,by omega⟩)
  else posA (b ⟨(p.val-18)/3,by omega⟩) (c ⟨(p.val-18)%3,by omega⟩)

lemma relabel_slot (a b c : Equiv.Perm (Fin 3)) (T : Tables) (p : Fin 27) :
    (relabel a b c T).slot p=T.slot (relabelPos a b c p) := by
  fin_cases p
  · exact (slotC T (a 0) (b 0)).symm
  · exact (slotC T (a 0) (b 1)).symm
  · exact (slotC T (a 0) (b 2)).symm
  · exact (slotC T (a 1) (b 0)).symm
  · exact (slotC T (a 1) (b 1)).symm
  · exact (slotC T (a 1) (b 2)).symm
  · exact (slotC T (a 2) (b 0)).symm
  · exact (slotC T (a 2) (b 1)).symm
  · exact (slotC T (a 2) (b 2)).symm
  · exact (slotB T (c 0) (a 0)).symm
  · exact (slotB T (c 1) (a 0)).symm
  · exact (slotB T (c 2) (a 0)).symm
  · exact (slotB T (c 0) (a 1)).symm
  · exact (slotB T (c 1) (a 1)).symm
  · exact (slotB T (c 2) (a 1)).symm
  · exact (slotB T (c 0) (a 2)).symm
  · exact (slotB T (c 1) (a 2)).symm
  · exact (slotB T (c 2) (a 2)).symm
  · exact (slotA T (b 0) (c 0)).symm
  · exact (slotA T (b 0) (c 1)).symm
  · exact (slotA T (b 0) (c 2)).symm
  · exact (slotA T (b 1) (c 0)).symm
  · exact (slotA T (b 1) (c 1)).symm
  · exact (slotA T (b 1) (c 2)).symm
  · exact (slotA T (b 2) (c 0)).symm
  · exact (slotA T (b 2) (c 1)).symm
  · exact (slotA T (b 2) (c 2)).symm

def partyPos (n : Nat) (p : Fin 27) : Fin 27 :=
  if h : p.val<9 then
    let x : Fin 3:=⟨p.val/3,by omega⟩
    let y : Fin 3:=⟨p.val%3,by omega⟩
    match n%6 with
    | 0 => posC x y
    | 1 => posB y x
    | 2 => posC y x
    | 3 => posB x y
    | 4 => posA x y
    | _ => posA y x
  else if h : p.val<18 then
    let x : Fin 3:=⟨(p.val-9)/3,by omega⟩
    let z : Fin 3:=⟨(p.val-9)%3,by omega⟩
    match n%6 with
    | 0 => posB z x
    | 1 => posC x z
    | 2 => posA x z
    | 3 => posA z x
    | 4 => posC z x
    | _ => posB x z
  else
    let y : Fin 3:=⟨(p.val-18)/3,by omega⟩
    let z : Fin 3:=⟨(p.val-18)%3,by omega⟩
    match n%6 with
    | 0 => posA y z
    | 1 => posA z y
    | 2 => posB z y
    | 3 => posC y z
    | 4 => posB y z
    | _ => posC z y

lemma party_slot (n : Nat) (T : Tables) (p : Fin 27) :
    (party n T).slot p=T.slot (partyPos n p) := by
  have hn : n%6<6 := Nat.mod_lt _ (by decide)
  generalize h : n%6=k at *
  interval_cases k <;> fin_cases p <;> simp [party,partyPos,h,Tables.slot,posA,posB,posC]

lemma decode_slot (w : Nat) (p : Fin 27) : (decode w).slot p=w.testBit p.val := by
  fin_cases p <;> rfl
lemma flip_slot (T : Tables) (p : Fin 27) : T.flip.slot p=!(T.slot p) := by
  fin_cases p <;> rfl

def position (g : Nat) (p : Fin 27) : Fin 27 :=
  relabelPos (perm3 (g/216)) (perm3 (g/36%6)) (perm3 (g/6%6)) (partyPos (g%6) p)

lemma act_slot (code : Nat) (T : Tables) (p : Fin 27) :
    (act code T).slot p=if code%2=1 then !(T.slot (position (code/2) p)) else T.slot (position (code/2) p) := by
  unfold act
  split_ifs <;> simp only [flip_slot,party_slot,relabel_slot,position]

end Paper15.OrbitCheck
