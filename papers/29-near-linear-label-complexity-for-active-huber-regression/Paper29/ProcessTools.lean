import Paper29.Chaining
import Paper29.Sampling
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! Explicit finite expectation and supremum tools used in Sections3.1–3.2.
All probabilistic quantities are actual sums over the ordered IID sample space. -/
noncomputable section
open scoped BigOperators ENNReal
namespace Paper29.ProcessTools

/-- Suprema are only used below with an explicit boundedness proof. -/
def supremum {T : Type*} (f : T → ℝ) : ℝ := sSup (Set.range f)

theorem le_supremum {T : Type*} (f : T → ℝ) (hb : BddAbove (Set.range f)) (t : T) :
    f t ≤ supremum f := le_csSup hb ⟨t, rfl⟩

theorem supremum_le {T : Type*} [Nonempty T] (f : T → ℝ) {b : ℝ}
    (h : ∀ t, f t ≤ b) : supremum f ≤ b :=
  csSup_le (Set.range_nonempty f) (by rintro _ ⟨t, rfl⟩; exact h t)

theorem supremum_nonneg {T : Type*} [Nonempty T] (f : T → ℝ)
    (hb : BddAbove (Set.range f)) (hf : ∀ t, 0 ≤ f t) : 0 ≤ supremum f := by
  obtain ⟨t⟩ := ‹Nonempty T›
  exact (hf t).trans (le_supremum f hb t)

theorem expectation_mono {n m : ℕ} (π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i)
    (f g : (Fin m → Fin n) → ℝ) (h : ∀ ν, f ν ≤ g ν) :
    Sampling.expectation π f ≤ Sampling.expectation π g := by
  apply Finset.sum_le_sum
  intro ν _
  exact mul_le_mul_of_nonneg_left (h ν) (Sampling.iidMass_nonneg π hπ ν)

theorem expectation_const {n m : ℕ} (π : Fin n → ℝ) (hπ : ∑ i, π i = 1) (c : ℝ) :
    Sampling.expectation π (fun _ : Fin m → Fin n => c) = c := by
  unfold Sampling.expectation
  rw [← Finset.sum_mul, Sampling.iidMass_sum π hπ, one_mul]

theorem expectation_add {n m : ℕ} (π : Fin n → ℝ)
    (f g : (Fin m → Fin n) → ℝ) :
    Sampling.expectation π (fun ν => f ν + g ν) =
      Sampling.expectation π f + Sampling.expectation π g := by
  simp [Sampling.expectation, mul_add, Finset.sum_add_distrib]

theorem expectation_mul_const {n m : ℕ} (π : Fin n → ℝ)
    (f : (Fin m → Fin n) → ℝ) (c : ℝ) :
    Sampling.expectation π (fun ν => c * f ν) = c * Sampling.expectation π f := by
  simp only [Sampling.expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ν _
  ring

/-- Finite Jensen/Cauchy–Schwarz, with the true IID masses. -/
theorem expectation_sqrt_le {n m : ℕ} (π : Fin n → ℝ)
    (hπ : ∀ i, 0 ≤ π i) (hsum : ∑ i, π i = 1)
    (f : (Fin m → Fin n) → ℝ) (hf : ∀ ν, 0 ≤ f ν) :
    Sampling.expectation π (fun ν => Real.sqrt (f ν)) ≤
      Real.sqrt (Sampling.expectation π f) := by
  have hp (ν : Fin m → Fin n) := Sampling.iidMass_nonneg π hπ ν
  have h := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin m → Fin n))
    hp (fun ν => mul_nonneg (hp ν) (hf ν))
  have he (ν : Fin m → Fin n) : Real.sqrt (Sampling.iidMass π ν) *
      Real.sqrt (Sampling.iidMass π ν * f ν) = Sampling.iidMass π ν * Real.sqrt (f ν) := by
    rw [Real.sqrt_mul (hp ν), ← mul_assoc, ← pow_two, Real.sq_sqrt (hp ν)]
  simpa only [he, Sampling.iidMass_sum π hsum, Real.sqrt_one, one_mul,
    Sampling.expectation] using h

/-- Literal empirical error over an arbitrary class of population functions. -/
def errorSup {n m : ℕ} {T : Type*} (π : Fin n → ℝ) (f : Fin n → T → ℝ)
    (ν : Fin m → Fin n) : ℝ :=
  supremum (fun t => |Sampling.importanceAverage π ν (fun i => f i t) - ∑ i, f i t|)

/-- The actual Euclidean increment metric of the conditional Rademacher process. -/
def sampleMetric {n m : ℕ} {T : Type*} (π : Fin n → ℝ) (f : Fin n → T → ℝ)
    (ν : Fin m → Fin n) (s t : T) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (∑ j, ((f (ν j) s - f (ν j) t) / ((m : ℝ) * π (ν j))) ^ 2))

end Paper29.ProcessTools
