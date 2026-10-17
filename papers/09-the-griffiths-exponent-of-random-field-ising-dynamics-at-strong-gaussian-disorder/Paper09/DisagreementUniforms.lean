import Paper09.DisagreementMarks
import Paper09.PercolationLabels
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open Finset BigOperators Classical MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

namespace Paper09.DisagreementUniforms

/-- The conditional opening parameter at a fixed realization of the fields. -/
def openingParameter {V : Type*} (h : V → ℝ) (K ρ : ℝ) (x : V) : ℝ :=
  if |h x| ≤ K then 1 else ρ

theorem openingParameter_nonneg {V : Type*} (h : V → ℝ) (K ρ : ℝ) (hρ : 0 ≤ ρ)
    (x : V) : 0 ≤ openingParameter h K ρ x := by
  unfold openingParameter
  split_ifs <;> linarith

theorem openingParameter_le_one {V : Type*} (h : V → ℝ) (K ρ : ℝ) (hρ1 : ρ ≤ 1)
    (x : V) : openingParameter h K ρ x ≤ 1 := by
  unfold openingParameter
  split_ifs <;> linarith

/-- The actual one-site mark as a function of a uniform random variable. -/
def uniformMark (K ρ a t : ℝ) : Bool := decide (|a| ≤ K ∨ 1 - ρ < t)

theorem measurable_uniformMark (K ρ a : ℝ) : Measurable (uniformMark K ρ a) := by
  apply measurable_to_bool
  have hs : (uniformMark K ρ a) ⁻¹' {true} = {t | |a| ≤ K ∨ 1 - ρ < t} := by
    ext t
    simp [uniformMark]
  rw [hs]
  exact (measurableSet_le (f := fun _t : ℝ => |a|) (g := fun _t : ℝ => K)
    measurable_const measurable_const).union
    (measurableSet_lt measurable_const measurable_id)

/-- Exact one-site opening probability under the actual continuous uniform law. -/
theorem uniformMark_true (K ρ a : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    Percolation.uniformLaw {t | uniformMark K ρ a t = true} =
      ENNReal.ofReal (if |a| ≤ K then 1 else ρ) := by
  by_cases ha : |a| ≤ K
  · simp [uniformMark, ha]
  · have hs : {t | uniformMark K ρ a t = true} = Set.Ioi (1 - ρ) := by
      ext t
      simp [uniformMark, ha]
    rw [hs, if_neg ha]
    exact Percolation.uniformLaw_tail ρ hρ hρ1

/-- Both singleton masses of the thresholded actual uniform variable. -/
theorem uniformMark_mass (K ρ a : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (b : Bool) :
    Percolation.uniformLaw {t | uniformMark K ρ a t = b} =
      ENNReal.ofReal (DisagreementMarks.bernoulliWeight (if |a| ≤ K then 1 else ρ) b) := by
  cases b
  · have hs : {t | uniformMark K ρ a t = false} = {t | uniformMark K ρ a t = true}ᶜ := by
      ext t
      cases hb : uniformMark K ρ a t <;> simp [hb]
    have hm : MeasurableSet {t | uniformMark K ρ a t = true} :=
      (measurable_uniformMark K ρ a) (MeasurableSet.singleton true)
    rw [hs, measure_compl hm (by finiteness), measure_univ, uniformMark_true K ρ a hρ hρ1]
    rw [DisagreementMarks.bernoulliWeight_false, ENNReal.ofReal_sub _ (by split_ifs <;> linarith)]
    simp
  · exact uniformMark_true K ρ a hρ hρ1

variable {V : Type*}

/-- A thresholded uniform mark on the active set, and a closed mark outside it. -/
def coordinateMark (h : V → ℝ) (K ρ : ℝ) (U : Finset V) (x : V) (t : ℝ) : Bool :=
  if x ∈ U then uniformMark K ρ (h x) t else false

theorem measurable_coordinateMark (h : V → ℝ) (K ρ : ℝ) (U : Finset V) (x : V) :
    Measurable (coordinateMark h K ρ U x) := by
  unfold coordinateMark
  by_cases hx : x ∈ U
  · simpa [coordinateMark, hx] using measurable_uniformMark K ρ (h x)
  · simp only [if_neg hx]
    exact measurable_const

/-- Each coordinate fiber has exactly the prescribed Bernoulli or closed mass. -/
theorem coordinateMark_mass (h : V → ℝ) (K ρ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (U : Finset V) (x : V) (b : Bool) :
    Percolation.uniformLaw {t | coordinateMark h K ρ U x t = b} =
      ENNReal.ofReal (DisagreementMarks.markFactor (openingParameter h K ρ) U x b) := by
  by_cases hx : x ∈ U
  · simpa only [coordinateMark, if_pos hx, DisagreementMarks.markFactor, openingParameter] using
      uniformMark_mass K ρ (h x) hρ hρ1 b
  · cases b <;> simp [coordinateMark, hx, DisagreementMarks.markFactor]

/-- Pull actual independent uniforms from distinct infinite-lattice sites, and
form the finite active mark configuration used by the exploration. -/
def uniformMarks {d : ℕ} (h : V → ℝ) (K ρ : ℝ)
    (f : V → LatticeGeometry.Point d) (U : Finset V)
    (u : LatticeGeometry.Point d → ℝ) : V → Bool :=
  fun x => coordinateMark h K ρ U x (u (f x))

theorem measurable_uniformMarks {d : ℕ} (h : V → ℝ) (K ρ : ℝ)
    (f : V → LatticeGeometry.Point d) (U : Finset V) :
    Measurable (uniformMarks h K ρ f U) := by
  apply measurable_pi_lambda
  intro x
  exact (measurable_coordinateMark h K ρ U x).comp (measurable_pi_apply (f x))

/-- On a restricted infinite field, these are exactly the source marks (3.2). -/
theorem uniformMarks_true {d : ℕ} (h : LatticeGeometry.Point d → ℝ) (K ρ : ℝ)
    (f : V → LatticeGeometry.Point d) (U : Finset V)
    (u : LatticeGeometry.Point d → ℝ) (x : V) :
    uniformMarks (fun z => h (f z)) K ρ f U u x = true ↔
      x ∈ U ∧ Percolation.siteOpen K ρ h u (f x) := by
  by_cases hx : x ∈ U <;> simp [uniformMarks, coordinateMark, uniformMark, Percolation.siteOpen, hx]

variable [Fintype V]

/-- Every complete finite assignment has the exact mass of the independently
constructed Bernoulli product. Distinctness of sites is the only independence input. -/
theorem uniformMarks_fiber {d : ℕ} (h : V → ℝ) (K ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (f : V → LatticeGeometry.Point d)
    (hf : Function.Injective f) (U : Finset V) (ω : V → Bool) :
    Percolation.noiseLaw d {u | uniformMarks h K ρ f U u = ω} =
      ENNReal.ofReal ((DisagreementMarks.productMarks (openingParameter h K ρ)
        (openingParameter_nonneg h K ρ hρ) (openingParameter_le_one h K ρ hρ1) U).w ω) := by
  let A (x : V) : Set ℝ := {t | coordinateMark h K ρ U x t = ω x}
  have hA (x : V) : MeasurableSet (A x) :=
    (measurable_coordinateMark h K ρ U x) (MeasurableSet.singleton (ω x))
  have hs : {u | uniformMarks h K ρ f U u = ω} =
      (fun u x => u (f x)) ⁻¹' Set.univ.pi A := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
    exact ⟨fun he x => congrFun he x, fun he => funext he⟩
  rw [hs, ← Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hA)]
  change (Measure.map (fun u x => u (f x))
    (Measure.infinitePi (fun _ : LatticeGeometry.Point d => Percolation.uniformLaw)))
      (Set.univ.pi A) = _
  rw [ProductCoordinates.infinitePi_map_injective _ f hf, Measure.pi_pi]
  change (∏ x, Percolation.uniformLaw {t | coordinateMark h K ρ U x t = ω x}) = _
  simp_rw [coordinateMark_mass h K ρ hρ hρ1 U]
  change (∏ x, ENNReal.ofReal (DisagreementMarks.markFactor (openingParameter h K ρ) U x (ω x))) =
    ENNReal.ofReal (∏ x, DisagreementMarks.markFactor (openingParameter h K ρ) U x (ω x))
  exact (ENNReal.ofReal_prod_of_nonneg (fun x _ => DisagreementMarks.markFactor_nonneg _
    (openingParameter_nonneg h K ρ hρ) (openingParameter_le_one h K ρ hρ1) U x (ω x))).symm

/-- The same exact assignment identity, expressed as a real probability. -/
theorem uniformMarks_real_fiber {d : ℕ} (h : V → ℝ) (K ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (f : V → LatticeGeometry.Point d)
    (hf : Function.Injective f) (U : Finset V) (ω : V → Bool) :
    (Percolation.noiseLaw d).real {u | uniformMarks h K ρ f U u = ω} =
      (DisagreementMarks.productMarks (openingParameter h K ρ)
        (openingParameter_nonneg h K ρ hρ) (openingParameter_le_one h K ρ hρ1) U).w ω := by
  unfold Measure.real
  rw [uniformMarks_fiber h K ρ hρ hρ1 f hf U ω, ENNReal.toReal_ofReal]
  exact (DisagreementMarks.productMarks (openingParameter h K ρ)
    (openingParameter_nonneg h K ρ hρ) (openingParameter_le_one h K ρ hρ1) U).nonneg ω

/-- Every finite statistic has exactly the same expectation under the finite
exploration marks and the source's actual infinite independent uniform noise. -/
theorem uniformMarks_expect {d : ℕ} (h : V → ℝ) (K ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (f : V → LatticeGeometry.Point d)
    (hf : Function.Injective f) (U : Finset V) (F : (V → Bool) → ℝ) :
    (DisagreementMarks.productMarks (openingParameter h K ρ)
      (openingParameter_nonneg h K ρ hρ) (openingParameter_le_one h K ρ hρ1) U).expect F =
      ∫ u, F (uniformMarks h K ρ f U u) ∂Percolation.noiseLaw d := by
  let M := DisagreementMarks.productMarks (openingParameter h K ρ)
    (openingParameter_nonneg h K ρ hρ) (openingParameter_le_one h K ρ hρ1) U
  let ν := (Percolation.noiseLaw d).map (uniformMarks h K ρ f U)
  have hm := measurable_uniformMarks h K ρ f U
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hm.aemeasurable
  have hi : Integrable F ν := Integrable.of_finite
  have hν (ω : V → Bool) : ν.real {ω} = M.w ω := by
    unfold Measure.real
    rw [Measure.map_apply hm (MeasurableSet.singleton ω)]
    exact uniformMarks_real_fiber h K ρ hρ hρ1 f hf U ω
  change M.expect F = _
  calc
    M.expect F = ∑ ω, ν.real {ω} • F ω := by simp only [FinProb.expect, hν, smul_eq_mul]
    _ = ∫ ω, F ω ∂ν := (integral_fintype F hi).symm
    _ = ∫ u, F (uniformMarks h K ρ f U u) ∂Percolation.noiseLaw d :=
      integral_map hm.aemeasurable hi.aestronglyMeasurable

/-- Every event of finite marks has its literal source-noise probability,
including arbitrary finite cluster events. -/
theorem uniformMarks_event {d : ℕ} (h : V → ℝ) (K ρ : ℝ)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (f : V → LatticeGeometry.Point d)
    (hf : Function.Injective f) (U : Finset V) (A : (V → Bool) → Prop) :
    (Percolation.noiseLaw d).real {u | A (uniformMarks h K ρ f U u)} =
      (DisagreementMarks.productMarks (openingParameter h K ρ)
        (openingParameter_nonneg h K ρ hρ) (openingParameter_le_one h K ρ hρ1) U).expect
          (fun ω => if A ω then 1 else 0) := by
  have hA : MeasurableSet {u | A (uniformMarks h K ρ f U u)} :=
    (measurable_uniformMarks h K ρ f U) (Set.toFinite {ω : V → Bool | A ω}).measurableSet
  rw [← integral_indicator_one hA]
  simpa [Set.indicator] using
    (uniformMarks_expect h K ρ hρ hρ1 f hf U (fun ω => if A ω then 1 else 0)).symm

end Paper09.DisagreementUniforms
