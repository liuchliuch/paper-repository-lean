import Paper10.ProposalLaw
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.CStarAlgebra.Matrix

noncomputable section
open Matrix MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace Paper10
instance matrixMeasurableSpace (q : ℕ) : MeasurableSpace (Matrix (Fin q) (Fin q) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin q → Fin q → ℝ))
instance matrixBorelSpace (q : ℕ) : BorelSpace (Matrix (Fin q) (Fin q) ℝ) :=
  inferInstanceAs (BorelSpace (Fin q → Fin q → ℝ))

/-- Linear splitting of the first coordinate from a finite real vector. -/
def splitGaussianCoordinates (m : ℕ) : (Fin (m + 1) → ℝ) ≃ₗ[ℝ] ℝ × (Fin m → ℝ) where
  __ := (Fin.insertNthEquiv (fun _ : Fin (m + 1) => ℝ) 0).symm
  map_add' := by intros; ext <;> rfl
  map_smul' := by intros; ext <;> rfl

/-- The product standard-normal model is Gaussian in Mathlib's intrinsic linear-functional sense. -/
instance stdGaussianMeasure_isGaussian (m : ℕ) : IsGaussian (stdGaussianMeasure m) := by
  induction m with
  | zero =>
    have he : stdGaussianMeasure 0 = Measure.dirac (0 : Fin 0 → ℝ) := by
      exact Measure.pi_of_empty _ _
    rw [he]
    infer_instance
  | succ m ih =>
    letI : IsGaussian (stdGaussianMeasure m) := ih
    let e := (splitGaussianCoordinates m).toContinuousLinearEquiv
    have he : Measure.map e.symm ((gaussianReal 0 1).prod (stdGaussianMeasure m)) =
        stdGaussianMeasure (m + 1) := by
      exact (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => gaussianReal 0 1) 0).symm.map_eq
    have hh : IsGaussian (Measure.map e.symm ((gaussianReal 0 1).prod (stdGaussianMeasure m))) := by
      infer_instance
    rwa [he] at hh

/-- Gaussian matrix construction as a genuine continuous linear map. -/
def gaussianMatrixLinearMap {q m : ℕ} (B : Fin m → Matrix (Fin q) (Fin q) ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] Matrix (Fin q) (Fin q) ℝ where
  toFun := gaussianMatrix B
  map_add' := by intros; simp [gaussianMatrix, add_smul, Finset.sum_add_distrib]
  map_smul' := by intros; simp [gaussianMatrix, MulAction.mul_smul, Finset.smul_sum]

/-- Actual Gaussian law of any finite matrix combination, allowing arbitrary correlations. -/
theorem gaussianMatrix_isGaussian {q m : ℕ} (B : Fin m → Matrix (Fin q) (Fin q) ℝ) :
    IsGaussian ((stdGaussianMeasure m).map (gaussianMatrix B)) := by
  exact ProbabilityTheory.isGaussian_map (E := Fin m → ℝ) (F := Matrix (Fin q) (Fin q) ℝ)
    (μ := stdGaussianMeasure m) (gaussianMatrixLinearMap B).toContinuousLinearMap

/-- The proposal is a linear image of independent standard normals, hence intrinsically Gaussian. -/
theorem proposalStep_isGaussian {q m : ℕ} (F : Fin m → Matrix (Fin q) (Fin q) ℝ)
    (R : Matrix (Fin q) (Fin q) ℝ) (s r : ℝ) (E : Matrix (Fin m) (Fin m) ℝ)
    (hs : 0 < s) (hE : E.PosSemidef) :
    IsGaussian ((stdGaussianMeasure m).map (proposalStep F R s r E hs hE)) := by
  let B := fun a => Real.sqrt (auxiliaryEigenvalues s E hs hE a) •
    rotateF F (auxiliaryRotation s E hs hE) a
  have he : proposalStep F R s r E hs hE =
      gaussianMatrix (fun a => (tOf (q := q) r s) • (R * B a * Rᴴ)) := by
    funext ω
    unfold proposalStep gaussianMatrix
    dsimp [B]
    simp only [Finset.smul_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    ring
  rw [he]
  exact gaussianMatrix_isGaussian _

end Paper10
