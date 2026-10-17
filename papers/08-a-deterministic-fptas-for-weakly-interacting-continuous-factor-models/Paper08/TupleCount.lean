import Paper08.Perturbation
import Mathlib.Data.Fin.Tuple.NatAntidiagonal
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.Sym.Card
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.Antidiag.Finsupp

/-! # Actual total-order enumerations and their cardinalities

The executable enumeration adds a slack coordinate and uses the recursive
antidiagonal-tuple list. It does not enumerate the full refinement-level box.
-/
open scoped BigOperators
namespace Paper08.TupleCount

/-- Enumerate precisely all nonnegative t-tuples whose total is at most J. -/
def boundedTuples (t J : ℕ) : Finset (Fin t → ℕ) :=
  (Finset.Nat.antidiagonalTuple (t + 1) J).image Fin.tail

lemma mem_boundedTuples {t J : ℕ} {ν : Fin t → ℕ} :
    ν ∈ boundedTuples t J ↔ ∑ i, ν i ≤ J := by
  simp only [boundedTuples, Finset.mem_image, Finset.Nat.mem_antidiagonalTuple]
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Fin.sum_univ_succ] at hw
    simp only [Fin.tail]
    omega
  · intro h
    exact ⟨Fin.cons (J - ∑ i, ν i) ν, by simp [Fin.sum_univ_succ, Nat.sub_add_cancel h],
      by simp⟩

lemma boundedTuples_eq_totalLevels (t J : ℕ) :
    boundedTuples t J = Quadrature.totalLevels t J := by
  ext ν
  rw [mem_boundedTuples, Quadrature.mem_totalLevels]
  constructor
  · intro h
    exact ⟨fun i => (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans h, h⟩
  · exact fun h => h.2

noncomputable def tupleSymEquiv (t J : ℕ) :
    boundedTuples t J ≃ Sym (Fin (t + 1)) J where
  toFun v := (Sym.equivNatSumOfFintype (Fin (t + 1)) J).symm
    ⟨Fin.cons (J - ∑ i, v.val i) v.val,
      by simp [Fin.sum_univ_succ, Nat.sub_add_cancel (mem_boundedTuples.mp v.property)]⟩
  invFun w := ⟨Fin.tail ((Sym.equivNatSumOfFintype (Fin (t + 1)) J) w).val, by
    rw [mem_boundedTuples]
    have h := ((Sym.equivNatSumOfFintype (Fin (t + 1)) J) w).property
    rw [Fin.sum_univ_succ] at h
    simp only [Fin.tail]
    omega⟩
  left_inv v := by
    apply Subtype.ext
    simp
  right_inv w := by
    apply (Sym.equivNatSumOfFintype (Fin (t + 1)) J).injective
    simp only [Equiv.apply_symm_apply]
    apply Subtype.ext
    let y := (Sym.equivNatSumOfFintype (Fin (t + 1)) J) w
    have hy : J - ∑ i : Fin t, y.val i.succ = y.val 0 := by
      have h := y.property
      rw [Fin.sum_univ_succ] at h
      omega
    change Fin.cons (J - ∑ i, Fin.tail y.val i) (Fin.tail y.val) = y.val
    simp only [Fin.tail] at hy ⊢
    rw [hy]
    exact Fin.cons_self_tail y.val

/-- Exact stars-and-bars count for the actual executable enumeration. -/
theorem card_boundedTuples (t J : ℕ) :
    (boundedTuples t J).card = (J + t).choose t := by
  have h := Fintype.card_congr (tupleSymEquiv t J)
  rw [Fintype.card_coe, Sym.card_sym_eq_choose, Fintype.card_fin] at h
  rw [show t + 1 + J - 1 = J + t by omega] at h
  rw [h, Nat.choose_symm_add]

theorem card_totalLevels (t J : ℕ) :
    (Quadrature.totalLevels t J).card = (J + t).choose t := by
  rw [← boundedTuples_eq_totalLevels, card_boundedTuples]

/-- The full primitive exponent-vector count (2.14), across all orders ≤s. -/
theorem primitive_exponent_count {h s : ℕ} (hhs : h ≤ s) :
    (boundedTuples h s).card ≤ 4 ^ s := by
  rw [card_boundedTuples]
  calc
    (s + h).choose h ≤ 2 ^ (s + h) := Nat.choose_le_two_pow _ _
    _ ≤ 2 ^ (s + s) := Nat.pow_le_pow_right (by omega) (by omega)
    _ = 4 ^ s := by rw [pow_add, ← mul_pow]; norm_num

theorem sum_ordered {m : ℕ} (B : Finset (Fin m)) (f : Fin m → ℕ) :
    (∑ i : Fin B.card, f (B.orderEmbOfFin rfl i)) = ∑ i ∈ B, f i := by
  conv_rhs => rw [← B.map_orderEmbOfFin_univ rfl, Finset.sum_map]
  rfl

theorem prod_ordered {m : ℕ} {R : Type*} [CommMonoid R]
    (B : Finset (Fin m)) (f : Fin m → R) :
    (∏ i : Fin B.card, f (B.orderEmbOfFin rfl i)) = ∏ i ∈ B, f i := by
  conv_rhs => rw [← B.map_orderEmbOfFin_univ rfl, Finset.prod_map]
  rfl

/-- Sparse B-local exponent enumeration has the same bound, without ever
enumerating tuples on the whole factor set. -/
theorem card_finsuppAntidiag_le {m j s : ℕ} (B : Finset (Fin m))
    (hB : B.card ≤ s) (hj : j ≤ s) : (Finset.finsuppAntidiag B j).card ≤ 4 ^ s := by
  let f : (Fin m →₀ ℕ) → Fin B.card → ℕ := fun d i => d (B.orderEmbOfFin rfl i)
  apply (Finset.card_le_card_of_injOn f (t := boundedTuples B.card s) ?_ ?_).trans
    (primitive_exponent_count hB)
  · intro d hd
    change f d ∈ boundedTuples B.card s
    rw [mem_boundedTuples]
    change (∑ i : Fin B.card, d (B.orderEmbOfFin rfl i)) ≤ s
    rw [sum_ordered]
    exact (Finset.mem_finsuppAntidiag.mp hd).1.le.trans hj
  · intro d hd e he hde
    apply Finsupp.ext
    intro a
    by_cases ha : a ∈ B
    · obtain ⟨i, hi⟩ := (B.orderIsoOfFin rfl).surjective ⟨a, ha⟩
      have hii : B.orderEmbOfFin rfl i = a := congrArg Subtype.val hi
      simpa only [f, hii] using congrFun hde i
    · have hd₀ : d a = 0 := Finsupp.notMem_support_iff.mp
        (fun h => ha ((Finset.mem_finsuppAntidiag.mp hd).2 h))
      have he₀ : e a = 0 := Finsupp.notMem_support_iff.mp
        (fun h => ha ((Finset.mem_finsuppAntidiag.mp he).2 h))
      rw [hd₀, he₀]

end Paper08.TupleCount
