import Paper15.SymmetryGroup
import Mathlib.Data.Finset.Card

noncomputable section
namespace Paper15
open Finset BigOperators

abbrev ResponseBits := Fin 27 → Bool

def DetTriangle.ofBits (b : ResponseBits) : DetTriangle where
  A := ⟨fun j k => signOfBit (b ⟨18+3*j.val+k.val,by omega⟩),fun _ _ => legalSign_signOfBit _⟩
  B := ⟨fun k i => signOfBit (b ⟨9+3*i.val+k.val,by omega⟩),fun _ _ => legalSign_signOfBit _⟩
  C := ⟨fun i j => signOfBit (b ⟨3*i.val+j.val,by omega⟩),fun _ _ => legalSign_signOfBit _⟩

lemma DetTriangle.signAtPos_ofBits (b : ResponseBits) (p : Fin 27) :
    (DetTriangle.ofBits b).signAtPos p.val = signOfBit (b p) := by
  fin_cases p <;> simp [DetTriangle.signAtPos,DetTriangle.ofBits]

lemma signOfBit_injective : Function.Injective signOfBit := by
  intro a b h
  cases a <;> cases b <;> norm_num [signOfBit] at *

lemma DetTriangle.signAtPos_legal (T : DetTriangle) (p : Fin 27) : legalSign (T.signAtPos p.val) := by
  unfold DetTriangle.signAtPos
  split_ifs
  · exact T.C.legal _ _
  · exact T.B.legal _ _
  · exact T.A.legal _ _
  · omega

lemma DetTriangle.signAtPos_injective {T U : DetTriangle}
    (h : ∀p : Fin 27,T.signAtPos p.val=U.signAtPos p.val) : T=U := by
  apply DetTriangle.ext <;> apply RespTable.ext <;> intro i j
  · have he := h ⟨18+3*i.val+j.val,by omega⟩
    fin_cases i <;> fin_cases j <;> simpa [DetTriangle.signAtPos] using he
  · have he := h ⟨9+3*j.val+i.val,by omega⟩
    fin_cases i <;> fin_cases j <;> simpa [DetTriangle.signAtPos] using he
  · have he := h ⟨3*i.val+j.val,by omega⟩
    fin_cases i <;> fin_cases j <;> simpa [DetTriangle.signAtPos] using he

def DetTriangle.bits (T : DetTriangle) : ResponseBits := fun p => decide (T.signAtPos p.val = -1)

@[simp] lemma DetTriangle.signOfBit_bits (T : DetTriangle) (p : Fin 27) :
    signOfBit (T.bits p) = T.signAtPos p.val := by
  rcases T.signAtPos_legal p with h|h <;> norm_num [DetTriangle.bits,signOfBit,h]

lemma DetTriangle.ofBits_bits (T : DetTriangle) : DetTriangle.ofBits T.bits = T := by
  apply DetTriangle.signAtPos_injective
  intro p
  rw [DetTriangle.signAtPos_ofBits,T.signOfBit_bits]

lemma DetTriangle.bits_ofBits (b : ResponseBits) : (DetTriangle.ofBits b).bits = b := by
  funext p
  apply signOfBit_injective
  rw [DetTriangle.signOfBit_bits,DetTriangle.signAtPos_ofBits]

lemma DetTriangle.ofPattern_eq_ofBits (w : Nat) :
    DetTriangle.ofPattern w = DetTriangle.ofBits (fun p => w.testBit p.val) := by
  apply DetTriangle.signAtPos_injective
  intro p
  rw [DetTriangle.signAtPos_ofPattern p.isLt,DetTriangle.signAtPos_ofBits]
  rfl

def flipAt (T : DetTriangle) (p : Fin 27) : DetTriangle :=
  DetTriangle.ofBits (Function.update T.bits p (!(T.bits p)))

lemma flipAt_bits (T : DetTriangle) (p : Fin 27) :
    (flipAt T p).bits = Function.update T.bits p (!(T.bits p)) := DetTriangle.bits_ofBits _

lemma flipAt_involution (T : DetTriangle) (p : Fin 27) : flipAt (flipAt T p) p=T := by
  unfold flipAt
  rw [DetTriangle.bits_ofBits]
  simp only [Function.update_self, Bool.not_not,Function.update_idem]
  rw [Function.update_eq_self,DetTriangle.ofBits_bits]

/-- Hamming distance between deterministic response assignments. -/
def responseDist (T U : DetTriangle) : Nat :=
  ∑p : Fin 27, if T.bits p=U.bits p then 0 else 1

lemma responseDist_eq_card (T U : DetTriangle) :
    responseDist T U = (univ.filter (fun p => T.bits p≠U.bits p)).card := by
  rw [responseDist,Finset.card_eq_sum_ones]
  rw [Finset.sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases h : T.bits p=U.bits p <;> simp [h]

lemma responseDist_one_iff (T U : DetTriangle) : responseDist T U=1 ↔ ∃p, U=flipAt T p := by
  classical
  rw [responseDist_eq_card,Finset.card_eq_one]
  constructor
  · rintro ⟨p,hp⟩
    refine ⟨p,?_⟩
    apply DetTriangle.signAtPos_injective
    intro q
    rw [← U.signOfBit_bits,← (flipAt T p).signOfBit_bits,flipAt_bits]
    congr 1
    by_cases hq : q=p
    · subst q
      have hdiff : T.bits p≠U.bits p := by
        have := Finset.mem_singleton_self p
        rw [← hp] at this
        simpa using this
      simp only [Function.update_self]
      cases hT : T.bits p <;> cases hU : U.bits p <;> simp_all
    · have heq : T.bits q=U.bits q := by
        by_contra hn
        have hmem : q∈univ.filter (fun p => T.bits p≠U.bits p) := by simp [hn]
        rw [hp,mem_singleton] at hmem
        exact hq hmem
      simp [Function.update_of_ne hq,heq]
  · rintro ⟨p,rfl⟩
    refine ⟨p,?_⟩
    ext q
    simp only [mem_filter,mem_univ,true_and,mem_singleton,flipAt_bits]
    by_cases hq : q=p
    · subst q; simp
    · simp [Function.update_of_ne hq,hq]

end Paper15
