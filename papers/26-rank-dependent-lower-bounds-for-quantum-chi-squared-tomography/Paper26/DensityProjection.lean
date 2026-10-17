import Paper26.FrobeniusAmplification
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-! The actual Frobenius projection onto density matrices. Its existence,
continuity and distance contraction are proved from the Hilbert projection
theorem in mathlib, with no estimator or error bound as an external input. -/
noncomputable section
open scoped ENNReal ComplexOrder
open MeasureTheory InnerProductSpace

namespace Paper26.DensityProjection
open QuantumModel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (K : Set E) (hne : K.Nonempty) (hclosed : IsComplete K) (hconv : Convex ℝ K)

def projection (x : E) : E :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hne hclosed hconv x)

theorem projection_mem (x : E) : projection K hne hclosed hconv x ∈ K :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hclosed hconv x)).1

theorem projection_variational (x : E) (z : E) (hz : z ∈ K) :
    inner ℝ (x - projection K hne hclosed hconv x)
      (z - projection K hne hclosed hconv x) ≤ 0 := by
  exact (norm_eq_iInf_iff_real_inner_le_zero hconv (projection_mem K hne hclosed hconv x)).mp
    (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hclosed hconv x)).2 z hz

theorem projection_norm_sub_le (x y : E) :
    ‖projection K hne hclosed hconv x - projection K hne hclosed hconv y‖ ≤ ‖x-y‖ := by
  let p := projection K hne hclosed hconv x
  let q := projection K hne hclosed hconv y
  have h₁ := projection_variational K hne hclosed hconv x q (projection_mem K hne hclosed hconv y)
  have h₂ := projection_variational K hne hclosed hconv y p (projection_mem K hne hclosed hconv x)
  change inner ℝ (x-p) (q-p) ≤ 0 at h₁
  change inner ℝ (y-q) (p-q) ≤ 0 at h₂
  rw [show q-p = -(p-q) by abel, inner_neg_right] at h₁
  have hid : inner ℝ (x-y) (p-q) = inner ℝ (x-p) (p-q) -
      inner ℝ (y-q) (p-q) + ‖p-q‖^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right]
    ring
  have hs : ‖p-q‖^2 ≤ ‖x-y‖ * ‖p-q‖ := by
    have hc := real_inner_le_norm (x-y) (p-q)
    linarith
  change ‖p-q‖ ≤ _
  by_cases hz : ‖p-q‖ = 0
  · rw [hz]
    exact norm_nonneg _
  · exact (mul_le_mul_iff_left₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz))).mp
      (by simpa only [pow_two] using hs)

theorem projection_continuous : Continuous (projection K hne hclosed hconv) := by
  have hl : LipschitzWith 1 (projection K hne hclosed hconv) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using
        projection_norm_sub_le K hne hclosed hconv x y
  exact hl.continuous

theorem projection_fixed {z : E} (hz : z ∈ K) : projection K hne hclosed hconv z = z := by
  have h := projection_variational K hne hclosed hconv z z hz
  rw [real_inner_self_eq_norm_sq] at h
  have he : ‖z - projection K hne hclosed hconv z‖ = 0 := by
    nlinarith [norm_nonneg (z - projection K hne hclosed hconv z)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp he)).symm

theorem projection_distance_to_member (x : E) {z : E} (hz : z ∈ K) :
    ‖projection K hne hclosed hconv x-z‖ ≤ ‖x-z‖ := by
  simpa only [projection_fixed K hne hclosed hconv hz] using
    projection_norm_sub_le K hne hclosed hconv x z

variable (d : ℕ) [NeZero d]
local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))
local instance matrixBorelSpace (m n : Type*) [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℂ) := inferInstanceAs (BorelSpace (m → n → ℂ))

def densitySet : Set (FrobeniusAmplification.Coordinates d) :=
  {x | ((MatrixCoordinates.coordinates d d).symm x).PosSemidef ∧
    Matrix.trace ((MatrixCoordinates.coordinates d d).symm x) = 1}

theorem densitySet_nonempty : (densitySet d).Nonempty := by
  refine ⟨MatrixCoordinates.coordinates d d (AdaptiveCollectiveEmbedding.uniformState (Fin d)).matrix, ?_⟩
  simp only [densitySet, Set.mem_setOf_eq, ContinuousLinearEquiv.symm_apply_apply]
  exact ⟨(AdaptiveCollectiveEmbedding.uniformState (Fin d)).positive,
    (AdaptiveCollectiveEmbedding.uniformState (Fin d)).trace_one⟩

omit [NeZero d] in
theorem densitySet_closed : IsClosed (densitySet d) := by
  apply IsClosed.inter
  · exact (AdaptiveCollectiveEmbedding.isClosed_setOf_posSemidef (ι := Fin d)).preimage
      (MatrixCoordinates.coordinates d d).symm.continuous
  · exact isClosed_eq (by fun_prop) continuous_const

omit [NeZero d] in
theorem densitySet_convex : Convex ℝ (densitySet d) := by
  intro x hx y hy a b ha hb hab
  change (((MatrixCoordinates.coordinates d d).symm (a • x+b • y)).PosSemidef ∧ _)
  rw [map_add, map_smul, map_smul]
  refine ⟨(hx.1.smul ha).add (hy.1.smul hb), ?_⟩
  simp only [Matrix.trace_add, Matrix.trace_smul, hx.2, hy.2, Complex.real_smul, mul_one]
  exact_mod_cast hab

def projectCoordinates : FrobeniusAmplification.Coordinates d → FrobeniusAmplification.Coordinates d :=
  projection (densitySet d) (densitySet_nonempty d) (densitySet_closed d).isComplete
    (densitySet_convex d)

def project (A : Matrix (Fin d) (Fin d) ℂ) : Density (Fin d) where
  matrix := (MatrixCoordinates.coordinates d d).symm
    (projectCoordinates d (MatrixCoordinates.coordinates d d A))
  positive := (projection_mem (densitySet d) (densitySet_nonempty d)
    (densitySet_closed d).isComplete (densitySet_convex d) _).1
  trace_one := (projection_mem (densitySet d) (densitySet_nonempty d)
    (densitySet_closed d).isComplete (densitySet_convex d) _).2

theorem measurable_project : Measurable (project d) := by
  have hc : Continuous (projectCoordinates d) := projection_continuous _ _ _ _
  have hm : Measurable (fun A => ((project d A).matrix : Fin d → Fin d → ℂ)) :=
    (MatrixCoordinates.coordinates d d).symm.continuous.measurable.comp
      (hc.measurable.comp (MatrixCoordinates.coordinates d d).continuous.measurable)
  intro S hS
  obtain ⟨T, hT, rfl⟩ := hS
  exact hm hT

theorem frobenius_error_le (A : Matrix (Fin d) (Fin d) ℂ) (ρ : Density (Fin d)) :
    SpectralLoss.frobeniusSq ((project d A).matrix-ρ.matrix) ≤
      SpectralLoss.frobeniusSq (A-ρ.matrix) := by
  have hρ : MatrixCoordinates.coordinates d d ρ.matrix ∈ densitySet d := by
    simpa only [densitySet, Set.mem_setOf_eq, ContinuousLinearEquiv.symm_apply_apply] using
      And.intro ρ.positive ρ.trace_one
  have h := projection_distance_to_member (densitySet d) (densitySet_nonempty d)
    (densitySet_closed d).isComplete (densitySet_convex d)
    (MatrixCoordinates.coordinates d d A) hρ
  have hs := mul_self_le_mul_self (norm_nonneg _) h
  have he : MatrixCoordinates.coordinates d d (project d A).matrix =
      projection (densitySet d) (densitySet_nonempty d) (densitySet_closed d).isComplete
        (densitySet_convex d) (MatrixCoordinates.coordinates d d A) := by
    simp only [project, ContinuousLinearEquiv.apply_symm_apply, projectCoordinates]
  rw [← he] at hs
  simp_rw [← pow_two, ← map_sub, ← MatrixCoordinates.frobeniusSq_eq_norm_sq] at hs
  simpa only [Regularization.frobeniusSq_eq_entryNorm] using hs

end Paper26.DensityProjection
