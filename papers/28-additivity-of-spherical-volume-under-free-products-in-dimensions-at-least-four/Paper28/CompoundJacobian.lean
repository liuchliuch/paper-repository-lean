import Paper28.PluckerCoordinates

/-! The actual kth compound linear map on Euclidean exterior coordinates.
Its norm on a simple vector is the genuine Gram k-Jacobian. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open WithLp

def compoundMatrix {d m : ℕ} (k : ℕ) (D : Matrix (Fin m) (Fin d) ℝ) :
    Matrix (PluckerIndex m k) (PluckerIndex d k) ℝ := fun s t =>
  (D.submatrix (orderedMinorIndices s) (orderedMinorIndices t)).det

def compoundAction {d m : ℕ} (k : ℕ) (D : Matrix (Fin m) (Fin d) ℝ) :
    EuclideanExterior d k →ₗ[ℝ] EuclideanExterior m k := Matrix.toEuclideanLin (compoundMatrix k D)

theorem compoundAction_plucker (hCB : CauchyBinetInput) {d m k : ℕ}
    (D : Matrix (Fin m) (Fin d) ℝ) (e : Fin k → EuclideanSpace ℝ (Fin d)) :
    compoundAction k D (pluckerCoordinates e) =
      pluckerCoordinates (fun i => Matrix.toEuclideanLin D (e i)) := by
  have hCoord : frameCoordinateMatrix (fun i => Matrix.toEuclideanLin D (e i)) =
      D*frameCoordinateMatrix e := by
    ext i j
    rfl
  ext s
  change (∑ t : PluckerIndex d k, compoundMatrix k D s t * pluckerCoordinates e t) = _
  rw [pluckerCoordinates_apply,hCoord]
  have hSub : (D*frameCoordinateMatrix e).submatrix (orderedMinorIndices s) id =
      (D.submatrix (orderedMinorIndices s) id)*frameCoordinateMatrix e := rfl
  rw [hSub,hCB]
  rfl

def exteriorJacobian {d m k : ℕ} (D : Matrix (Fin m) (Fin d) ℝ)
    (τ : EuclideanExterior d k) : ℝ := ‖compoundAction k D τ‖

theorem exteriorJacobian_plucker (hCB : CauchyBinetInput) {d m k : ℕ}
    (D : Matrix (Fin m) (Fin d) ℝ) (e : Fin k → EuclideanSpace ℝ (Fin d)) :
    exteriorJacobian (k := k) D (pluckerCoordinates e) =
      Real.sqrt (Matrix.gram ℝ (fun i => Matrix.toEuclideanLin D (e i))).det := by
  rw [exteriorJacobian,compoundAction_plucker hCB,pluckerCoordinates_norm_eq_gram hCB]

theorem exteriorJacobian_nonneg {d m k : ℕ} (D : Matrix (Fin m) (Fin d) ℝ)
    (τ : EuclideanExterior d k) : 0 ≤ exteriorJacobian (k := k) D τ := norm_nonneg _

theorem exteriorJacobian_continuous {d m k : ℕ} :
    Continuous (fun p : Matrix (Fin m) (Fin d) ℝ × EuclideanExterior d k => exteriorJacobian (k := k) p.1 p.2) := by
  have hOut : Continuous
      (fun p : Matrix (Fin m) (Fin d) ℝ × EuclideanExterior d k => compoundAction k p.1 p.2) := by
    apply (PiLp.continuous_toLp 2 (fun _ : PluckerIndex m k => ℝ)).comp
    apply continuous_pi
    intro s
    change Continuous (fun p : Matrix (Fin m) (Fin d) ℝ × EuclideanExterior d k =>
      ∑ t : PluckerIndex d k, (p.1.submatrix (orderedMinorIndices s) (orderedMinorIndices t)).det * p.2 t)
    apply continuous_finset_sum
    intro t _
    exact ((continuous_fst.matrix_submatrix _ _).matrix_det).mul
      ((PiLp.continuous_apply 2 _ t).comp continuous_snd)
  exact hOut.norm

attribute [irreducible] exteriorJacobian

theorem exteriorJacobian_continuousOn {X : Type*} [TopologicalSpace X] {d m k : ℕ}
    (S : Set X) (D : X → Matrix (Fin m) (Fin d) ℝ) (τ : X → EuclideanExterior d k)
    (hD : ContinuousOn D S) (hτ : ContinuousOn τ S) :
    ContinuousOn (fun x => exteriorJacobian (k := k) (D x) (τ x)) S := by
  have hPair : ContinuousOn (fun x => (D x,τ x)) S := hD.prodMk hτ
  exact (exteriorJacobian_continuous (d := d) (m := m) (k := k)).comp_continuousOn hPair

end Paper28
