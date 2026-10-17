import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Module.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import GeometricMedianCoresets.VarianceCount

/-!
# Finite-population variance identity (paper Lemma 2.3, eq. (7))

`Ω = (univ : Finset (Fin n)).powersetCard m`,
`uniformAvg f = (∑ I ∈ Ω, f I) / Nat.choose n m`.

For `1 ≤ m ≤ n` and `h : Fin n → H`:

  `uniformAvg (fun I => ‖sampleMean h I - popMean h‖^2)
    = (n-m)/(m*(n-1)) * (1/n) * ∑ i, ‖h i - popMean h‖^2`.
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace GeometricMedianCoresets
namespace FinitePopulation

/-- Uniform average over `m`-subsets of `Fin n`. -/
def uniformAvg {n m : ℕ} (f : (Finset (Fin n)) → ℝ) : ℝ :=
  (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m, f I) / (n.choose m : ℝ)

/-- Population mean. -/
def popMean {H : Type*} [NormedAddCommGroup H] [Module ℝ H] {n : ℕ} (h : Fin n → H) : H :=
  if n = 0 then 0 else (n : ℝ)⁻¹ • (∑ i, h i)

theorem popMean_eq {H : Type*} [NormedAddCommGroup H] [Module ℝ H]
    {n : ℕ} (hn : 0 < n) (h : Fin n → H) :
    popMean h = (n : ℝ)⁻¹ • (∑ i, h i) := by
  unfold popMean
  rw [if_neg (by omega : ¬(n = 0))]

/-- Centered family `w_i = h_i - h̄`. -/
def centered {H : Type*} [NormedAddCommGroup H] [Module ℝ H] {n : ℕ} (h : Fin n → H) : Fin n → H :=
  fun i => h i - popMean h

theorem sum_centered {H : Type*} [NormedAddCommGroup H] [Module ℝ H]
    {n : ℕ} (hn : 0 < n) (h : Fin n → H) :
    ∑ i, centered h i = 0 := by
  unfold centered
  rw [popMean_eq hn h]
  have hsum : ∑ i : Fin n, (h i - (n : ℝ)⁻¹ • (∑ j : Fin n, h j))
      = (∑ i : Fin n, h i) - ∑ i : Fin n, ((n : ℝ)⁻¹ • (∑ j : Fin n, h j)) :=
    Finset.sum_sub_distrib _ _
  rw [hsum]
  have h4 : ∑ _i : Fin n, ((n : ℝ)⁻¹ • (∑ j : Fin n, h j))
      = (n : ℝ) • ((n : ℝ)⁻¹ • (∑ j : Fin n, h j)) := by
    have hcard : (Finset.univ : Finset (Fin n)).card = n := Fintype.card_fin n
    rw [Finset.sum_const, hcard]
    exact Eq.symm (Nat.cast_smul_eq_nsmul (R := ℝ) n ((n : ℝ)⁻¹ • (∑ j : Fin n, h j)))
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [h4, smul_smul, mul_inv_cancel₀ hn0, one_smul, sub_self]

/-- Sample mean of a subset, using its own cardinality. -/
def sampleMean {H : Type*} [NormedAddCommGroup H] [Module ℝ H]
    {n : ℕ} (h : Fin n → H) (I : Finset (Fin n)) : H :=
  if I.card = 0 then 0 else (I.card : ℝ)⁻¹ • ∑ i ∈ I, h i

theorem sampleMean_eq {H : Type*} [NormedAddCommGroup H] [Module ℝ H]
    {n : ℕ} (h : Fin n → H) (I : Finset (Fin n)) (hI : 0 < I.card) :
    sampleMean h I = (I.card : ℝ)⁻¹ • ∑ i ∈ I, h i := by
  unfold sampleMean
  rw [if_neg (by omega : ¬(I.card = 0))]

/-- Squared norm of a sum as a double sum of inner products. -/
theorem norm_sum_sq_eq_double_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (w : Fin n → H) (I : Finset (Fin n)) :
    ‖∑ i ∈ I, w i‖ ^ 2 = ∑ i ∈ I, ∑ j ∈ I, ⟪w i, w j⟫ := by
  have h1 : ‖∑ i ∈ I, w i‖ ^ 2 = ⟪∑ i ∈ I, w i, ∑ i ∈ I, w i⟫ :=
    (real_inner_self_eq_norm_sq _).symm
  rw [h1, sum_inner]
  apply Finset.sum_congr rfl
  intro i _hi
  exact inner_sum I (fun j => w j) (w i)

/-- `h̄_I - h̄ = (1/|I|) Σ_{i∈I} w_i` for `w_i = h_i - h̄`. -/
theorem sampleMean_sub_popMean {H : Type*} [NormedAddCommGroup H] [Module ℝ H]
    {n : ℕ} (hn : 0 < n) (h : Fin n → H)
    (I : Finset (Fin n)) (hI : 0 < I.card) :
    sampleMean h I - popMean h
      = (I.card : ℝ)⁻¹ • ∑ i ∈ I, centered h i := by
  have hm0 : (I.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hI)
  have hsm : sampleMean h I = (I.card : ℝ)⁻¹ • ∑ i ∈ I, h i :=
    sampleMean_eq h I hI
  have hpop : popMean h = (n : ℝ)⁻¹ • (∑ i, h i) := popMean_eq hn h
  have hsum_eq : ∑ i ∈ I, h i
      = ∑ i ∈ I, (h i - popMean h) + (I.card : ℝ) • popMean h := by
    have h1 : ∀ i ∈ I, h i = (h i - popMean h) + popMean h := fun i _ => by abel
    conv_lhs => rw [Finset.sum_congr rfl h1]
    rw [Finset.sum_add_distrib]
    have h2 : ∑ i ∈ I, popMean h = (I.card : ℝ) • popMean h := by
      rw [Finset.sum_const]
      exact Eq.symm (Nat.cast_smul_eq_nsmul (R := ℝ) I.card (popMean h))
    rw [h2]
  have hcancel : (I.card : ℝ)⁻¹ • ((I.card : ℝ) • popMean h) = popMean h := by
    rw [smul_smul, inv_mul_cancel₀ hm0, one_smul]
  have hcent : (∑ i ∈ I, (h i - popMean h)) = ∑ i ∈ I, centered h i :=
    Finset.sum_congr rfl fun i _ => rfl
  rw [hsm, hsum_eq, smul_add, hcancel, ← hcent]
  abel


end FinitePopulation
end GeometricMedianCoresets
