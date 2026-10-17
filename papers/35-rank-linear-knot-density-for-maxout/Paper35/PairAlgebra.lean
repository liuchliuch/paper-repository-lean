import Paper35.Crossing
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

noncomputable section
open scoped BigOperators ENNReal
namespace Paper35

/-- Strict ordered candidate pairs are pairs j together with an earlier index. -/
def orderedPairEquivSigma (K : ℕ) : OrderedCandidatePair K ≃ (j : Fin K) × Fin j.val where
  toFun q := ⟨q.val.2, ⟨q.val.1.val, q.property⟩⟩
  invFun z := ⟨(⟨z.2.val, lt_trans z.2.isLt z.1.isLt⟩, z.1), z.2.isLt⟩
  left_inv q := by apply Subtype.ext; rfl
  right_inv z := by cases z; rfl

lemma card_orderedCandidatePair (K : ℕ) : Fintype.card (OrderedCandidatePair K) = K.choose 2 := by
  rw [Fintype.card_congr (orderedPairEquivSigma K), Fintype.card_sigma]
  simp only [Fintype.card_fin]
  change (∑ x : Fin K, (fun n : ℕ => n) x.val) = K.choose 2
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => n) K, Finset.sum_range_id, Nat.choose_two_right]

/-- Replace the subtype pair sum by the source's i<j double-sum notation. -/
lemma sum_orderedCandidatePair {M : Type*} [AddCommMonoid M] (K : ℕ)
    (a : Fin K → Fin K → M) :
    (∑ q : OrderedCandidatePair K, a q.val.1 q.val.2) =
      ∑ i, ∑ j, if i < j then a i j else 0 := by
  classical
  calc
    _ = ∑ q ∈ (Finset.univ : Finset (Fin K × Fin K)).filter (fun q => q.1 < q.2),
        a q.1 q.2 := by
      simpa only [Finset.subtype_univ] using
        (Finset.sum_subtype_eq_sum_filter (s := Finset.univ) (p := fun q : Fin K × Fin K => q.1 < q.2)
          (fun q => a q.1 q.2))
    _ = ∑ q : Fin K × Fin K, if q.1 < q.2 then a q.1 q.2 else 0 := by
      rw [Finset.sum_filter]
    _ = _ := Fintype.sum_prod_type _

/-- All remaining iid CDF factors give exactly K-2 copies. -/
lemma prod_erase_pair_const {M : Type*} [CommMonoid M] {K : ℕ}
    (i j : Fin K) (hij : i ≠ j) (a : M) :
    (∏ _k ∈ (Finset.univ.erase i).erase j, a) = a^(K-2) := by
  rw [Finset.prod_const]
  congr 1
  rw [Finset.card_erase_of_mem (by simp [hij.symm]),
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin]
  omega

end Paper35
