import Paper29.OrthonormalReduction

noncomputable section
open scoped BigOperators Classical
namespace Paper29.Reduction

abbrev retainedCount {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) := Fintype.card (RetainedRows A)

def retainedEnum {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) : Fin (retainedCount A) ≃ RetainedRows A :=
  (Fintype.equivFin (RetainedRows A)).symm

def retainedIndex {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (i : Fin (retainedCount A)) : Fin n :=
  (retainedEnum A i).val

theorem retainedIndex_injective {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    Function.Injective (retainedIndex A) := Subtype.val_injective.comp (retainedEnum A).injective

/-- The literal finite matrix of equation (3.37), with row indices Fin N. -/
def finiteReducedDesign {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    Matrix (Fin (retainedCount A)) (Fin A.rank) ℝ :=
  (coordinateDesign A (OrthonormalReduction.coordinates A)).submatrix (retainedEnum A) id

theorem finiteReducedDesign_rank {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    (finiteReducedDesign A).rank = A.rank := by
  change ((coordinateDesign A (OrthonormalReduction.coordinates A)).submatrix
    (retainedEnum A) (Equiv.refl (Fin A.rank))).rank = _
  rw [Matrix.rank_submatrix]
  exact (OrthonormalReduction.orthonormal_retained_reduction A).2.2.1

theorem finiteReducedDesign_nozero {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (i : Fin (retainedCount A)) : finiteReducedDesign A i ≠ 0 :=
  (OrthonormalReduction.orthonormal_retained_reduction A).2.2.2.1 (retainedEnum A i)

theorem finiteReducedDesign_objective {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b : Fin n → ℝ) (y : Fin A.rank → ℝ) :
    objective (finiteReducedDesign A) (fun i => b (retainedIndex A i)) y =
      coordinateObjective A (OrthonormalReduction.coordinates A) b y := by
  change (∑ i : Fin (retainedCount A), huber
    (((coordinateDesign A (OrthonormalReduction.coordinates A)).mulVec y) (retainedEnum A i) -
      b (retainedEnum A i).val)) = _
  exact (retainedEnum A).sum_comp (fun i : RetainedRows A =>
    huber (((coordinateDesign A (OrthonormalReduction.coordinates A)).mulVec y) i - b i.val))

theorem finite_loss_nonneg {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) (x : Fin d → ℝ) :
    0 ≤ objective A b x := Finset.sum_nonneg (fun i _ => huber_nonneg _)

/-- The same norm approximation survives both reindexing and actual column/
zero-row reduction. -/
theorem finiteReduced_relative_guarantee {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b : Fin n → ℝ) (yhat : Fin A.rank → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hgood : ∀ y, Real.sqrt (objective (finiteReducedDesign A) (fun i => b (retainedIndex A i)) yhat) ≤
      (1+ε)*Real.sqrt (objective (finiteReducedDesign A) (fun i => b (retainedIndex A i)) y)) :
    ∀ x, Real.sqrt (objective A b ((OrthonormalReduction.coordinates A).mulVec yhat)) ≤
      (1+ε)*Real.sqrt (objective A b x) := by
  have hloss : ∀ y, coordinateObjective A (OrthonormalReduction.coordinates A) b yhat ≤
      (1+ε)^2 * coordinateObjective A (OrthonormalReduction.coordinates A) b y := by
    intro y
    have hh := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).2 (hgood y)
    rw [Real.sq_sqrt (finite_loss_nonneg (finiteReducedDesign A) _ yhat), mul_pow,
      Real.sq_sqrt (finite_loss_nonneg (finiteReducedDesign A) _ y),
      finiteReducedDesign_objective, finiteReducedDesign_objective] at hh
    exact hh
  intro x
  have hbound := coordinate_relative_guarantee A (OrthonormalReduction.coordinates A) b
    (OrthonormalReduction.coordinate_predictions_cover A) yhat (by nlinarith : 1 ≤ (1+ε)^2) hloss x
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
  rw [Real.sq_sqrt (finite_loss_nonneg A b _), mul_pow,
    Real.sq_sqrt (finite_loss_nonneg A b x)]
  exact hbound

end Paper29.Reduction
