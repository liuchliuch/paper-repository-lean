import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Uniform sampling without replacement (paper §1.1)

A uniform sample of size `m` is a uniformly random `m`-element subset of
`Fin n`. This module defines the uniform law as the counting measure on
`Finset.powersetCard m univ` and proves elementary expectation properties.

The complete probability estimates are proved using this same finite uniform law
in `UniformComparison`, `EuclideanMetric` and `MainLower`; the full variance
identity and anchored second-moment bound appear in `VarianceComplete`.
-/

noncomputable section

open scoped BigOperators

namespace GeometricMedianCoresets
namespace Sampling

/-- Type of samples: `m`-element subsets of `Fin n`. -/
abbrev SampleSpace (n m : ℕ) := Finset (Fin n)

/-- The finite set of all uniform samples. -/
def allSamples (n m : ℕ) : Finset (SampleSpace n m) :=
  (Finset.univ : Finset (Fin n)).powersetCard m

theorem card_allSamples (n m : ℕ) :
    (allSamples n m).card = n.choose m := by
  unfold allSamples
  simp [Finset.card_powersetCard]

/-- Uniform expectation of a real function on samples. -/
def unifExp {n m : ℕ} (f : SampleSpace n m → ℝ) : ℝ :=
  if (n.choose m : ℝ) = 0 then 0
  else (n.choose m : ℝ)⁻¹ * ∑ s ∈ allSamples n m, f s

theorem unifExp_zero_of_empty {n m : ℕ} (h : n.choose m = 0) (f : SampleSpace n m → ℝ) :
    unifExp f = 0 := by
  unfold unifExp
  rw [h]
  norm_num

/-- When `m = n` the unique sample is the full set. -/
theorem allSamples_self (n : ℕ) :
    allSamples n n = {Finset.univ} := by
  unfold allSamples
  ext s
  simp only [Finset.mem_powersetCard, Finset.mem_singleton, Finset.subset_univ, true_and]
  constructor
  · intro h
    have hcard : s.card = Fintype.card (Fin n) := by simpa using h
    exact (Finset.card_eq_iff_eq_univ s).1 hcard
  · intro h
    subst h
    simp

theorem unifExp_full {n : ℕ} (hn : 0 < n) (f : SampleSpace n n → ℝ) :
    unifExp f = f Finset.univ := by
  unfold unifExp
  have hchoose : (n.choose n : ℝ) = 1 := by
    rw [Nat.choose_self]; norm_num
  rw [hchoose, allSamples_self, Finset.sum_singleton, if_neg (by norm_num)]
  ring

/-- Probability of an event (predicate on samples) under the uniform law. -/
def unifProb {n m : ℕ} (E : SampleSpace n m → Prop) [DecidablePred E] : ℝ :=
  unifExp (fun s => if E s then 1 else 0)

theorem unifProb_le_one {n m : ℕ} (E : SampleSpace n m → Prop) [DecidablePred E]
    (h : n.choose m ≠ 0) :
    unifProb E ≤ 1 := by
  unfold unifProb unifExp
  rw [if_neg (by exact_mod_cast h)]
  have hsum : ∑ s ∈ allSamples n m, (if E s then (1:ℝ) else 0)
      = ((allSamples n m).filter E).card := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      Finset.card_filter, nsmul_one]
  rw [hsum]
  have hle : ((allSamples n m).filter E).card ≤ (allSamples n m).card :=
    Finset.card_filter_le _ _
  have hcard : (allSamples n m).card = n.choose m := card_allSamples n m
  rw [hcard] at hle
  have hn0 : (0:ℝ) < n.choose m := by exact_mod_cast Nat.pos_of_ne_zero h
  have hmul : ((allSamples n m).filter E).card * (n.choose m : ℝ)⁻¹
      ≤ (n.choose m : ℝ) * (n.choose m : ℝ)⁻¹ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hle)
      (inv_nonneg.mpr (le_of_lt hn0))
  have h1 : (n.choose m : ℝ) * (n.choose m : ℝ)⁻¹ = 1 := by field_simp
  -- goal is (choose)⁻¹ * card, rewrite to card * (choose)⁻¹
  have hcomm : ((n.choose m : ℝ)⁻¹ * ((allSamples n m).filter E).card)
      = (((allSamples n m).filter E).card * (n.choose m : ℝ)⁻¹) := by ring
  rw [hcomm]
  nlinarith

end Sampling
end GeometricMedianCoresets
