import Paper20.HeckeSpecializationTrace
import Paper20.TranspositionCount

namespace Paper20.OneStayTransposition
open Polynomial Matrix Paper20.BraidWalk Paper20.HeckeOperators Paper20.HeckeMatrices
open Paper20.HeckeWalkExpansion Paper20.HeckeTraceAlgebra Paper20.HalfTwistMatrix
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

abbrev S (r : ℕ) := Equiv.Perm (Fin r)
def swapAt {r : ℕ} (i : Fin (r-1)) : S r := adjacentMove i 1

lemma swapAt_isSwap {r : ℕ} (i : Fin (r-1)) : (swapAt i).IsSwap := by
  refine ⟨⟨i.val,by omega⟩,⟨i.val+1,by omega⟩,?_,?_⟩
  · intro h
    have hv : i.val=i.val+1 := congrArg Fin.val h
    omega
  · simp only [swapAt,adjacentMove,mul_one]

lemma swapAt_inv {r : ℕ} (i : Fin (r-1)) : (swapAt i)⁻¹=swapAt i := by
  simp [swapAt,adjacentMove]

lemma conjugate_isSwap {r : ℕ} (p t : S r) (ht : t.IsSwap) : (p*t*p⁻¹).IsSwap := by
  obtain ⟨a,b,hab,rfl⟩ := ht
  rw [Equiv.mul_swap_eq_swap_mul,mul_assoc,mul_inv_cancel,mul_one]
  exact ⟨p a,p b,fun h => hab (p.injective h),rfl⟩

def allProduct {r : ℕ} : List (Fin (r-1)) → S r
  | [] => 1
  | i::w => allProduct w*swapAt i

def keptProduct {r : ℕ} : List (Fin (r-1) × Bool) → S r
  | [] => 1
  | (i,b)::xs => if b then keptProduct xs else keptProduct xs*swapAt i

lemma endpoint_product {r : ℕ} (xs : List (Fin (r-1) × Bool)) (s : S r) :
    endpoint adjacentMove xs s=keptProduct xs*s := by
  induction xs generalizing s with
  | nil => simp [endpoint,keptProduct]
  | cons a xs ih =>
    obtain ⟨i,b⟩ := a
    cases b <;> simp only [endpoint,keptProduct,↓reduceIte,ih]
    change keptProduct xs*(swapAt i*s)=(keptProduct xs*swapAt i)*s
    exact (mul_assoc ..).symm

lemma no_stays_product {r : ℕ} (xs : List (Fin (r-1) × Bool))
    (hn : (xs.map Prod.snd).count true=0) : keptProduct xs=allProduct (xs.map Prod.fst) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨i,b⟩ := a
    cases b with
    | false =>
      simp only [List.map_cons,List.count_cons,show (false:Bool) ≠ true by decide,
        ↓reduceIte,Nat.add_zero] at hn
      rw [keptProduct,if_neg (by decide),List.map_cons,allProduct,ih hn]
    | true => simp at hn

/-- Omitting exactly one adjacent move changes the complete move product
by an actual conjugate transposition, for every decorated word. -/
theorem one_stay_ratio {r : ℕ} (xs : List (Fin (r-1) × Bool))
    (hn : (xs.map Prod.snd).count true=1) :
    (keptProduct xs*(allProduct (xs.map Prod.fst))⁻¹).IsSwap := by
  induction xs with
  | nil => simp at hn
  | cons a xs ih =>
    obtain ⟨i,b⟩ := a
    cases b with
    | false =>
      have ht : (xs.map Prod.snd).count true=1 := by simpa using hn
      simp only [keptProduct,Bool.false_eq_true,↓reduceIte,List.map_cons,allProduct,
        _root_.mul_inv_rev,swapAt_inv]
      have hc : swapAt i*swapAt i=1 := by simp [swapAt,adjacentMove]
      simpa only [mul_assoc,← mul_assoc (swapAt i),hc,one_mul] using ih ht
    | true =>
      have ht : (xs.map Prod.snd).count true=0 := by simpa using hn
      simp only [keptProduct,Bool.false_eq_true,↓reduceIte,List.map_cons,allProduct,
        _root_.mul_inv_rev,swapAt_inv,no_stays_product xs ht]
      exact conjugate_isSwap _ _ (swapAt_isSwap i)

lemma allProduct_false {r : ℕ} (w : List (Fin (r-1))) :
    keptProduct (w.map (fun i => (i,false)))=allProduct w := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [keptProduct,allProduct,ih]

lemma allProduct_palindrome {r : ℕ} (w : List (Fin (r-1))) :
    allProduct (w++w.reverse)=1 := by
  have he := moving_palindrome adjacentMove adjacentMove_involutive w (1:S r)
  rw [endpoint_product,allProduct_false,mul_one] at he
  exact he

/-- Any single-stay path from an arbitrary state to the identity along a
palindrome must start at an actual transposition. -/
theorem one_stay_endpoint {r : ℕ} (w : List (Fin (r-1)))
    (xs : List (Fin (r-1) × Bool)) (hword : xs.map Prod.fst=w++w.reverse)
    (s : S r) (hend : endpoint adjacentMove xs s=1)
    (hn : (xs.map Prod.snd).count true=1) : s.IsSwap := by
  have ht := one_stay_ratio xs hn
  rw [hword,allProduct_palindrome,inv_one,mul_one] at ht
  have he : keptProduct xs*s=1 := by simpa only [endpoint_product] using hend
  have hs : keptProduct xs=s⁻¹ := (mul_eq_one_iff_eq_inv).1 he
  rw [hs] at ht
  obtain ⟨a,b,hab,heq⟩ := ht
  have hx := congrArg (fun p : S r => p⁻¹) heq
  simp only [inv_inv,Equiv.swap_inv] at hx
  exact ⟨a,b,hab,hx⟩

end
end Paper20.OneStayTransposition
