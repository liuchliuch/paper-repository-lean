import Paper02.Hashing
import Paper02.Sampling

/-! # Instantiating the estimator with its actual binary hash seed -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.typeDecidableEq

namespace Paper02.Hashing

open Sampling

/-- The uniform marginal law is proved from the explicit matrix-seed bijection. -/
lemma hash_uniform_expect (J ℓ : ℕ) (u : Fin ℓ → ZMod 2)
    (g : (Fin J → ZMod 2) → ℝ) :
    (FiniteLaw.uniform (Seed J ℓ)).expect (fun s => g (hash u s)) =
      (∑ v, g v) / (2 : ℝ) ^ J := by
  rw [FiniteLaw.uniform_expect, hash_sum]
  have hc : Fintype.card (Seed J ℓ) =
      Fintype.card (Fin J → Fin ℓ → ZMod 2) * 2 ^ J := by
    rw [Fintype.card_congr (singleEquiv J ℓ u), Fintype.card_prod]
    simp [Fintype.card_fun, ZMod.card]
  rw [hc]
  push_cast
  have hn : (Fintype.card (Fin J → Fin ℓ → ZMod 2) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Fin J → Fin ℓ → ZMod 2) ≠ 0)
  field_simp

lemma hash_uniform_pair_expect (J ℓ : ℕ) (u v : Fin ℓ → ZMod 2) (c : Fin ℓ)
    (hc : u c ≠ v c) (g : (Fin J → ZMod 2) → (Fin J → ZMod 2) → ℝ) :
    (FiniteLaw.uniform (Seed J ℓ)).expect (fun s => g (hash u s) (hash v s)) =
      (∑ x, ∑ y, g x y) / ((2 : ℝ) ^ J) ^ 2 := by
  rw [FiniteLaw.uniform_expect, hash_pair_sum J ℓ u v c hc]
  have hcard : Fintype.card (Seed J ℓ) =
      Fintype.card (Fin J → {i : Fin ℓ // i ≠ c} → ZMod 2) * (2 ^ J) ^ 2 := by
    rw [Fintype.card_congr (pairEquiv J ℓ u v c hc)]
    simp [Fintype.card_prod, Fintype.card_fun, ZMod.card, pow_two, Nat.mul_assoc]
  rw [hcard]
  push_cast
  have hn : (Fintype.card (Fin J → {i : Fin ℓ // i ≠ c} → ZMod 2) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (Fin J → {i : Fin ℓ // i ≠ c} → ZMod 2) ≠ 0)
  field_simp

lemma prefix_probability {J j : ℕ} (hj : j ≤ J) (ℓ : ℕ)
    (u : Fin ℓ → ZMod 2) :
    (FiniteLaw.uniform (Seed J ℓ)).expect
      (fun s => if PrefixZero j (hash u s) then (1 : ℝ) else 0) = dyadicProb j := by
  rw [hash_uniform_expect J ℓ u (fun v => if PrefixZero j v then (1 : ℝ) else 0),
    prefixZero_indicator_sum hj]
  unfold dyadicProb
  have hp : (2 : ℝ) ^ J = 2 ^ (J - j) * 2 ^ j := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp]
  field_simp

lemma prefix_pair_probability {J j : ℕ} (hj : j ≤ J) (ℓ : ℕ)
    (u v : Fin ℓ → ZMod 2) (huv : u ≠ v) :
    (FiniteLaw.uniform (Seed J ℓ)).expect (fun s =>
      (if PrefixZero j (hash u s) then (1 : ℝ) else 0) *
        (if PrefixZero j (hash v s) then (1 : ℝ) else 0)) = (dyadicProb j) ^ 2 := by
  obtain ⟨c, hc⟩ : ∃ c, u c ≠ v c := by
    by_contra h
    push_neg at h
    exact huv (funext h)
  rw [hash_uniform_pair_expect J ℓ u v c hc
    (fun x y => (if PrefixZero j x then (1 : ℝ) else 0) *
      (if PrefixZero j y then (1 : ℝ) else 0)), prefixZero_pair_indicator_sum hj]
  unfold dyadicProb
  have hp : (2 : ℝ) ^ J = 2 ^ (J - j) * 2 ^ j := by
    rw [← pow_add]
    congr 1
    omega
  rw [hp]
  field_simp

/-- Retain coordinate `i` exactly when its hash prefix vanishes. -/
def retained {d J ℓ : ℕ} (j : ℕ) (i : Fin d) (s : Seed J ℓ) : ℝ :=
  if PrefixZero j (hash (binaryVector ℓ i.val) s) then 1 else 0

/-- The concrete, short-seed sampler satisfies all first and mixed-moment
hypotheses of the concentration proof. -/
theorem retained_pairwise {d J ℓ j : ℕ} (hd : d ≤ 2 ^ ℓ) (hj : j ≤ J) :
    PairwiseBernoulli (FiniteLaw.uniform (Seed J ℓ))
      (retained (d := d) j) (dyadicProb j) where
  zero_or_one i s := by unfold retained; split_ifs <;> simp
  mean i := prefix_probability hj ℓ (binaryVector ℓ i.val)
  mixed i k hik := by
    apply prefix_pair_probability hj ℓ
    exact fun h => hik (coordinate_binary_injective hd h)

/-- Additional independent checksum seeds preserve the real hash law. -/
lemma uniform_expect_fst {Ω Ξ : Type*} [Fintype Ω] [Nonempty Ω]
    [Fintype Ξ] [Nonempty Ξ] (X : Ω → ℝ) :
    (FiniteLaw.uniform (Ω × Ξ)).expect (fun s => X s.1) =
      (FiniteLaw.uniform Ω).expect X := by
  rw [FiniteLaw.uniform_expect, FiniteLaw.uniform_expect, Fintype.card_prod]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  push_cast
  have hΞ : (Fintype.card Ξ : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card Ξ ≠ 0)
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast (Fintype.card_ne_zero : Fintype.card Ω ≠ 0)
  field_simp

theorem retained_pairwise_extra_seed {d J ℓ j : ℕ} (hd : d ≤ 2 ^ ℓ) (hj : j ≤ J)
    (Ξ : Type*) [Fintype Ξ] [Nonempty Ξ] :
    PairwiseBernoulli (FiniteLaw.uniform (Seed J ℓ × Ξ))
      (fun i s => retained (d := d) j i s.1) (dyadicProb j) where
  zero_or_one i s := (retained_pairwise hd hj).zero_or_one i s.1
  mean i := by
    rw [uniform_expect_fst]
    exact (retained_pairwise hd hj).mean i
  mixed i k hik := by
    rw [uniform_expect_fst (fun s : Seed J ℓ => retained j i s * retained j k s)]
    exact (retained_pairwise hd hj).mixed i k hik

end Paper02.Hashing
