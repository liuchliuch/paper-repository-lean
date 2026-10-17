import Paper29.Geometry
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
Finite IID importance sampling. All expectations are explicit sums over the
actual sample space `Fin m → Fin n` with product probability mass.
This module does not assert the uniform-process estimates of Lemmas 3.5 or 3.6.
-/
noncomputable section
open scoped BigOperators

namespace Paper29.Sampling

/-- Probability mass of an ordered IID sample, allowing repeated indices. -/
def iidMass {n m : ℕ} (π : Fin n → ℝ) (ν : Fin m → Fin n) : ℝ :=
  ∏ j, π (ν j)

/-- Exact expectation over all ordered length-`m` samples. -/
def expectation {n m : ℕ} (π : Fin n → ℝ)
    (X : (Fin m → Fin n) → ℝ) : ℝ := ∑ ν, iidMass π ν * X ν

/-- Linearity of the explicit finite expectation. -/
theorem expectation_sub {n m : ℕ} (π : Fin n → ℝ)
    (X Y : (Fin m → Fin n) → ℝ) :
    expectation π (fun ν => X ν - Y ν) = expectation π X - expectation π Y := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

/-- Importance sampling average for an arbitrary finite real-valued population. -/
def importanceAverage {n m : ℕ} (π : Fin n → ℝ) (ν : Fin m → Fin n)
    (f : Fin n → ℝ) : ℝ := (∑ j, f (ν j) / π (ν j)) / (m : ℝ)

/-- The actual sampled Huber objective. -/
def sampledHuber {n m : ℕ} (π : Fin n → ℝ) (ν : Fin m → Fin n)
    (y : Fin n → ℝ) : ℝ := importanceAverage π ν (fun i => huber (y i))

/-- The sampled affine regression objective on the same ordered sample. -/
def sampledAffine {n d m : ℕ} (π : Fin n → ℝ) (ν : Fin m → Fin n)
    (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) (x : Fin d → ℝ) : ℝ :=
  sampledHuber π ν (fun i => (A.mulVec x) i - b i)

/-- The residual-offset form `Fhat_z(h)` in equation (3.25). -/
def sampledShifted {n d m : ℕ} (π : Fin n → ℝ) (ν : Fin m → Fin n)
    (A : Matrix (Fin n) (Fin d) ℝ) (z : Fin n → ℝ) (x : Fin d → ℝ) : ℝ :=
  sampledHuber π ν (fun i => z i + (A.mulVec x) i)

/-- The sampled design-only objective on that same sample. -/
def sampledUnshifted {n d m : ℕ} (π : Fin n → ℝ) (ν : Fin m → Fin n)
    (A : Matrix (Fin n) (Fin d) ℝ) (x : Fin d → ℝ) : ℝ :=
  sampledHuber π ν (A.mulVec x)

theorem iidMass_nonneg {n m : ℕ} (π : Fin n → ℝ)
    (hπ : ∀ i, 0 ≤ π i) (ν : Fin m → Fin n) : 0 ≤ iidMass π ν :=
  Finset.prod_nonneg fun j _ => hπ (ν j)

theorem iidMass_pos {n m : ℕ} (π : Fin n → ℝ)
    (hπ : ∀ i, 0 < π i) (ν : Fin m → Fin n) : 0 < iidMass π ν :=
  Finset.prod_pos fun j _ => hπ (ν j)

/-- The product mass is normalized, including the empty ordered sample. -/
theorem iidMass_sum {n m : ℕ} (π : Fin n → ℝ) (hπ : ∑ i, π i = 1) :
    ∑ ν : Fin m → Fin n, iidMass π ν = 1 := by
  unfold iidMass
  rw [← Fintype.prod_sum]
  simp [hπ]

/-- A single coordinate of the actual product law has marginal mass `π`. -/
theorem coordinate_expectation {n m : ℕ} (π f : Fin n → ℝ)
    (hπ : ∑ i, π i = 1) (j : Fin m) :
    expectation π (fun ν => f (ν j)) = ∑ i, π i * f i := by
  classical
  have h := Fintype.prod_sum (fun k : Fin m => fun i : Fin n =>
    π i * (if j = k then f i else 1))
  have hleft : (∏ k : Fin m, ∑ i : Fin n, π i * (if j = k then f i else 1)) =
      ∑ i, π i * f i := by
    have he (k : Fin m) : (∑ i, π i * (if j = k then f i else 1)) =
        if j = k then ∑ i, π i * f i else 1 := by
      by_cases hk : j = k <;> simp [hk, hπ]
    simp_rw [he]
    exact Fintype.prod_ite_eq j (fun _ => ∑ i, π i * f i)
  have hright : (∑ ν : Fin m → Fin n,
      ∏ k : Fin m, π (ν k) * (if j = k then f (ν k) else 1)) =
      expectation π (fun ν => f (ν j)) := by
    unfold expectation iidMass
    apply Finset.sum_congr rfl
    intro ν _
    rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq]
  rw [hleft, hright] at h
  exact h.symm

/-- Unbiasedness is derived by summing over the finite IID product law. -/
theorem importanceAverage_unbiased {n m : ℕ} (π f : Fin n → ℝ)
    (hpos : ∀ i, 0 < π i) (hπ : ∑ i, π i = 1) (hm : 0 < m) :
    expectation π (fun ν : Fin m → Fin n => importanceAverage π ν f) = ∑ i, f i := by
  classical
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hcoord (j : Fin m) :
      expectation π (fun ν : Fin m → Fin n => f (ν j) / π (ν j)) = ∑ i, f i := by
    rw [coordinate_expectation π (fun i => f i / π i) hπ j]
    apply Finset.sum_congr rfl
    intro i _
    exact mul_div_cancel₀ (f i) (ne_of_gt (hpos i))
  calc
    expectation π (fun ν : Fin m → Fin n => importanceAverage π ν f) =
        (∑ j : Fin m, expectation π (fun ν : Fin m → Fin n => f (ν j) / π (ν j))) /
          (m : ℝ) := by
      unfold expectation importanceAverage
      simp only [← mul_div_assoc, Finset.mul_sum, ← Finset.sum_div]
      rw [Finset.sum_comm]
    _ = (∑ j : Fin m, ∑ i, f i) / (m : ℝ) := by simp_rw [hcoord]
    _ = ∑ i, f i := by simp [hm0]

/-- Unbiasedness of the sampled empirical Huber objective. -/
theorem sampledHuber_unbiased {n m : ℕ} (π : Fin n → ℝ) (y : Fin n → ℝ)
    (hpos : ∀ i, 0 < π i) (hπ : ∑ i, π i = 1) (hm : 0 < m) :
    expectation π (fun ν : Fin m → Fin n => sampledHuber π ν y) = ∑ i, huber (y i) :=
  importanceAverage_unbiased π (fun i => huber (y i)) hpos hπ hm

/-- Unbiasedness of the genuine affine Huber objective, for every fixed response and point. -/
theorem sampledAffine_unbiased {n d m : ℕ} (π : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) (x : Fin d → ℝ)
    (hpos : ∀ i, 0 < π i) (hπ : ∑ i, π i = 1) (hm : 0 < m) :
    expectation π (fun ν : Fin m → Fin n => sampledAffine π ν A b x) = objective A b x :=
  sampledHuber_unbiased π (fun i => (A.mulVec x) i - b i) hpos hπ hm

/-- Unbiasedness in precisely the residual-offset notation of equation (3.25). -/
theorem sampledShifted_unbiased {n d m : ℕ} (π : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin d) ℝ) (z : Fin n → ℝ) (x : Fin d → ℝ)
    (hpos : ∀ i, 0 < π i) (hπ : ∑ i, π i = 1) (hm : 0 < m) :
    expectation π (fun ν : Fin m → Fin n => sampledShifted π ν A z x) =
      ∑ i, huber (z i + (A.mulVec x) i) :=
  sampledHuber_unbiased π (fun i => z i + (A.mulVec x) i) hpos hπ hm

/-- Centering at the zero parameter preserves unbiasedness of the affine increments. -/
theorem sampledAffine_centered_unbiased {n d m : ℕ} (π : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) (x : Fin d → ℝ)
    (hpos : ∀ i, 0 < π i) (hπ : ∑ i, π i = 1) (hm : 0 < m) :
    expectation π (fun ν : Fin m → Fin n =>
      sampledAffine π ν A b x - sampledAffine π ν A b 0) =
        objective A b x - objective A b 0 := by
  rw [expectation_sub, sampledAffine_unbiased π A b x hpos hπ hm,
    sampledAffine_unbiased π A b 0 hpos hπ hm]

/-- The same law also gives unbiased unshifted Huber estimates. -/
theorem sampledUnshifted_unbiased {n d m : ℕ} (π : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin d) ℝ) (x : Fin d → ℝ)
    (hpos : ∀ i, 0 < π i) (hπ : ∑ i, π i = 1) (hm : 0 < m) :
    expectation π (fun ν : Fin m → Fin n => sampledUnshifted π ν A x) = unshifted A x :=
  sampledHuber_unbiased π (A.mulVec x) hpos hπ hm

/-- Identification with an actual finite weighted Huber sum on sampled coordinates. -/
theorem sampledHuber_eq_weighted {n m : ℕ} (π : Fin n → ℝ)
    (ν : Fin m → Fin n) (y : Fin n → ℝ) :
    sampledHuber π ν y = weightedHuber (fun j => 1 / ((m : ℝ) * π (ν j)))
      (fun j => y (ν j)) := by
  unfold sampledHuber importanceAverage weightedHuber
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Every sampled objective has nonnegative weights. -/
theorem sampledHuber_nonneg {n m : ℕ} (π : Fin n → ℝ)
    (ν : Fin m → Fin n) (y : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) :
    0 ≤ sampledHuber π ν y := by
  rw [sampledHuber_eq_weighted]
  apply weightedHuber_nonneg
  intro j
  exact div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg m) (hπ (ν j)))

/-- A triangle inequality for one shared importance sample. -/
theorem sampledHuber_triangle {n m : ℕ} (π : Fin n → ℝ)
    (ν : Fin m → Fin n) (y z : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) :
    Real.sqrt (sampledHuber π ν (fun i => y i + z i)) ≤
      Real.sqrt (sampledHuber π ν y) + Real.sqrt (sampledHuber π ν z) := by
  simp only [sampledHuber_eq_weighted]
  apply weightedHuber_triangle
  intro j
  exact div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg m) (hπ (ν j)))

/-- The squared shared-sample triangle envelope used in the affine transfer. -/
theorem sampledHuber_envelope {n m : ℕ} (π : Fin n → ℝ)
    (ν : Fin m → Fin n) (y z : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) :
    sampledHuber π ν (fun i => y i + z i) ≤
      2 * sampledHuber π ν y + 2 * sampledHuber π ν z := by
  simp only [sampledHuber_eq_weighted]
  unfold weightedHuber
  calc
    (∑ j, (1 / ((m : ℝ) * π (ν j))) * huber (y (ν j) + z (ν j))) ≤
        ∑ j, (2 * ((1 / ((m : ℝ) * π (ν j))) * huber (y (ν j))) +
          2 * ((1 / ((m : ℝ) * π (ν j))) * huber (z (ν j)))) := by
      apply Finset.sum_le_sum
      intro j _
      have hw : 0 ≤ 1 / ((m : ℝ) * π (ν j)) :=
        div_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg m) (hπ (ν j)))
      have h := mul_le_mul_of_nonneg_left (huber_add_le (y (ν j)) (z (ν j))) hw
      nlinarith
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum]

/-- The shared-sample envelope for the response-vector form of affine regression. -/
theorem sampledAffine_envelope {n d m : ℕ} (π : Fin n → ℝ)
    (ν : Fin m → Fin n) (A : Matrix (Fin n) (Fin d) ℝ)
    (z : Fin n → ℝ) (u : Fin d → ℝ) (hπ : ∀ i, 0 ≤ π i) :
    sampledAffine π ν A z u ≤
      2 * sampledAffine π ν A z 0 + 2 * sampledUnshifted π ν A u := by
  have h := sampledHuber_envelope π ν (fun i => -z i) (A.mulVec u) hπ
  simpa only [sampledAffine, sampledUnshifted, Matrix.mulVec_zero,
    Pi.zero_apply, zero_sub, sub_eq_add_neg, add_comm, add_zero] using h

/-- The pointwise shared-sample envelope in the exact residual-offset notation of
Section 3.2: `Fhat_z(u) ≤ 2 Fhat_z(0) + 2 Phihat(u)`. -/
theorem sampledShifted_envelope {n d m : ℕ} (π : Fin n → ℝ)
    (ν : Fin m → Fin n) (A : Matrix (Fin n) (Fin d) ℝ)
    (z : Fin n → ℝ) (u : Fin d → ℝ) (hπ : ∀ i, 0 ≤ π i) :
    sampledShifted π ν A z u ≤
      2 * sampledShifted π ν A z 0 + 2 * sampledUnshifted π ν A u := by
  have h := sampledHuber_envelope π ν z (A.mulVec u) hπ
  simpa only [sampledShifted, sampledUnshifted, Matrix.mulVec_zero,
    Pi.zero_apply, add_zero] using h

/-- A finite event's mass for an arbitrary explicit nonnegative mass function. -/
def eventMass {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) (E : Finset Ω) : ℝ := ∑ ω ∈ E, p ω

/-- Finite Markov inequality. The expectation is the actual finite weighted sum. -/
theorem finite_markov {Ω : Type*} [Fintype Ω] (p X : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hX : ∀ ω, 0 ≤ X ω) (a : ℝ) (ha : 0 < a) :
    eventMass p (Finset.univ.filter (fun ω => a ≤ X ω)) ≤
      (∑ ω, p ω * X ω) / a := by
  classical
  apply (le_div_iff₀ ha).mpr
  unfold eventMass
  rw [Finset.sum_mul]
  calc
    ∑ ω ∈ Finset.univ.filter (fun ω => a ≤ X ω), p ω * a ≤
        ∑ ω ∈ Finset.univ.filter (fun ω => a ≤ X ω), p ω * X ω := by
      apply Finset.sum_le_sum
      intro ω hω
      exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hω).2 (hp ω)
    _ ≤ ∑ ω, p ω * X ω := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun ω _ _ => mul_nonneg (hp ω) (hX ω))

/-- Markov's inequality specialized to the finite IID product law. -/
theorem iid_markov {n m : ℕ} (π : Fin n → ℝ)
    (hπ : ∀ i, 0 ≤ π i) (X : (Fin m → Fin n) → ℝ)
    (hX : ∀ ν, 0 ≤ X ν) (a : ℝ) (ha : 0 < a) :
    eventMass (iidMass π) (Finset.univ.filter (fun ν => a ≤ X ν)) ≤
      expectation π X / a :=
  finite_markov (iidMass π) X (iidMass_nonneg π hπ) hX a ha

/-- The Markov bound for the true empirical Huber objective follows from unbiasedness. -/
theorem sampledHuber_markov {n m : ℕ} (π : Fin n → ℝ) (y : Fin n → ℝ)
    (hpos : ∀ i, 0 < π i) (hπ : ∑ i, π i = 1) (hm : 0 < m)
    (a : ℝ) (ha : 0 < a) :
    eventMass (iidMass π)
      (Finset.univ.filter (fun ν : Fin m → Fin n => a ≤ sampledHuber π ν y)) ≤
        (∑ i, huber (y i)) / a := by
  have h := iid_markov π (fun i => (hpos i).le)
    (fun ν : Fin m → Fin n => sampledHuber π ν y)
    (fun ν => sampledHuber_nonneg π ν y (fun i => (hpos i).le)) a ha
  rw [sampledHuber_unbiased π y hpos hπ hm] at h
  exact h

end Paper29.Sampling
