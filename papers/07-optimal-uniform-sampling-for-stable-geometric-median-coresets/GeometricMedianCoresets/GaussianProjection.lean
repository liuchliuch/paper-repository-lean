import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! The actual finite-dimensional standard Gaussian and its linear projections. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace GeometricMedianCoresets.GaussianProjection

/-- Independent standard normal coordinates. -/
def standard (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi (fun _ => gaussianReal 0 1)
instance (d : ℕ) : IsProbabilityMeasure (standard d) := by unfold standard; infer_instance

/-- The Gaussian linear functional associated to a Euclidean vector. -/
def project {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) (g : Fin d → ℝ) : ℝ :=
  ∑ i, g i * z i

lemma measurable_project {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) : Measurable (project z) := by
  unfold project
  fun_prop

lemma gaussian_finset_sum {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [DecidableEq ι] (f : ι → Ω → ℝ) (v : ι → ℝ≥0)
    (hf : ∀ i, Measurable (f i)) (hind : iIndepFun f μ)
    (hmap : ∀ i, μ.map (f i) = gaussianReal 0 (v i)) (s : Finset ι) :
    μ.map (fun ω => ∑ i ∈ s, f i ω) = gaussianReal 0 (∑ i ∈ s, v i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    have ih' : μ.map (∑ j ∈ s, f j) = gaussianReal 0 (∑ j ∈ s, v j) := by
      convert ih using 1
      congr 1
      funext ω
      simp
    have h := gaussianReal_add_gaussianReal_of_indepFun
      (hind.indepFun_finset_sum_of_notMem hf his).symm (hmap i) ih'
    simp only [Finset.sum_insert his, zero_add] at h ⊢
    convert h using 1
    congr 1
    funext ω
    simp

/-- A linear functional of the coordinate product has variance equal to squared Euclidean norm. -/
theorem map_project {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) :
    (standard d).map (project z) = gaussianReal 0 ⟨‖z‖ ^ 2, sq_nonneg _⟩ := by
  let f : Fin d → (Fin d → ℝ) → ℝ := fun i g => g i * z i
  let v : Fin d → ℝ≥0 := fun i => ⟨(z i) ^ 2, sq_nonneg _⟩
  have hf : ∀ i, Measurable (f i) := by intro i; fun_prop
  have hind : iIndepFun f (standard d) :=
    iIndepFun_pi (fun i => (measurable_id.mul_const (z i)).aemeasurable)
  have hmap : ∀ i, (standard d).map (f i) = gaussianReal 0 (v i) := by
    intro i
    have heval := (measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i).map_eq
    change (standard d).map (fun g => g i) = gaussianReal 0 1 at heval
    calc (standard d).map (f i) =
        ((standard d).map (fun g => g i)).map (fun r : ℝ => r * z i) := by
          exact (Measure.map_map (measurable_id.mul_const (z i)) (measurable_pi_apply i)).symm
      _ = _ := by rw [heval, gaussianReal_map_mul_const]; simp [v]
  have hsum := gaussian_finset_sum f v hf hind hmap Finset.univ
  have hv : (∑ i, v i) = ⟨‖z‖ ^ 2, sq_nonneg _⟩ := by
    apply NNReal.eq
    simp only [NNReal.coe_sum, v, NNReal.coe_mk, EuclideanSpace.norm_sq_eq,
      Real.norm_eq_abs, sq_abs]
  rw [hv] at hsum
  exact hsum

/-- The projection has the law of the norm times one standard normal. -/
theorem map_project_scale {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) :
    (standard d).map (project z) = (gaussianReal 0 1).map (fun r => ‖z‖ * r) := by
  rw [map_project, gaussianReal_map_const_mul]
  simp

lemma integrable_project {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) :
    Integrable (project z) (standard d) := by
  have hi : Integrable (id : ℝ → ℝ) ((standard d).map (project z)) := by
    rw [map_project]
    exact (memLp_one_iff_integrable).1 (memLp_id_gaussianReal 1)
  exact hi.comp_measurable (measurable_project z)

/-- The positive normalization constant; it is evaluated explicitly in `GaussianMoment`. -/
def firstMoment : ℝ := ∫ r : ℝ, |r| ∂gaussianReal 0 1

/-- Exact absolute first moment of every finite Gaussian projection. -/
theorem integral_abs_project {d : ℕ} (z : EuclideanSpace ℝ (Fin d)) :
    (∫ g, |project z g| ∂standard d) = ‖z‖ * firstMoment := by
  calc (∫ g, |project z g| ∂standard d) =
      ∫ r : ℝ, |r| ∂(standard d).map (project z) :=
        (integral_map (measurable_project z).aemeasurable (by fun_prop)).symm
    _ = ∫ r : ℝ, |‖z‖ * r| ∂gaussianReal 0 1 := by
      rw [map_project_scale, integral_map (by fun_prop) (by fun_prop)]
    _ = ‖z‖ * firstMoment := by
      simp_rw [abs_mul, abs_of_nonneg (norm_nonneg z)]
      exact integral_const_mul _ _

end GeometricMedianCoresets.GaussianProjection
