import Paper29.Reduction
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The orthonormal rank coordinates of equation (3.37)

The matrix map is transported to finite-dimensional Euclidean space. Its
kernel complement is proved to have dimension `rank A`, and its orthonormal
basis is converted into actual matrix columns. No prediction factorization
or orthonormality hypothesis is assumed.
-/
noncomputable section
open scoped BigOperators

namespace Paper29.OrthonormalReduction

/-- The canonical linear identification of Euclidean vectors with their coordinates. -/
def domainEquiv (d : ℕ) : EuclideanSpace ℝ (Fin d) ≃ₗ[ℝ] (Fin d → ℝ) :=
  WithLp.linearEquiv 2 ℝ (Fin d → ℝ)

/-- The actual input matrix as a linear map on its Euclidean decision space. -/
def matrixMap {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (Fin n → ℝ) :=
  A.mulVecLin.comp (domainEquiv d).toLinearMap

/-- The source subspace `(ker A)^perp`, with the Euclidean inner product. -/
def kernelPerp {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) := (LinearMap.ker (matrixMap A))ᗮ

/-- The matrix map restricted to the kernel's orthogonal complement. -/
def restrictedMap {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    kernelPerp A →ₗ[ℝ] (Fin n → ℝ) :=
  (matrixMap A).comp (kernelPerp A).subtype

theorem matrixMap_range {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    LinearMap.range (matrixMap A) = LinearMap.range A.mulVecLin := by
  exact LinearMap.range_comp_of_range_eq_top A.mulVecLin
    (LinearMap.range_eq_top.mpr (domainEquiv d).surjective)

/-- Kernel intersection with its orthogonal complement is zero, so restriction
of the actual matrix map is injective. -/
theorem restrictedMap_injective {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    Function.Injective (restrictedMap A) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro v hv
  have hk : (v : EuclideanSpace ℝ (Fin d)) ∈ LinearMap.ker (matrixMap A) := hv
  have hboth : (v : EuclideanSpace ℝ (Fin d)) ∈
      LinearMap.ker (matrixMap A) ⊓ (LinearMap.ker (matrixMap A))ᗮ :=
    ⟨hk, v.property⟩
  rw [(LinearMap.ker (matrixMap A)).inf_orthogonal_eq_bot] at hboth
  change v = 0
  exact Subtype.ext hboth

/-- Orthogonal decomposition shows that the restriction has every original
matrix prediction in its range. -/
theorem restrictedMap_range {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    LinearMap.range (restrictedMap A) = LinearMap.range (matrixMap A) := by
  apply le_antisymm
  · rintro z ⟨v, rfl⟩
    exact ⟨v.val, rfl⟩
  · rintro z ⟨x, rfl⟩
    obtain ⟨k, hk, v, hv, hx⟩ :=
      (LinearMap.ker (matrixMap A)).exists_add_mem_mem_orthogonal x
    refine ⟨⟨v, hv⟩, ?_⟩
    change matrixMap A v = matrixMap A x
    have hk0 : matrixMap A k = 0 := hk
    rw [hx, map_add, hk0, zero_add]

/-- The kernel complement has exactly the rank of the original matrix. -/
theorem kernelPerp_finrank {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    Module.finrank ℝ (kernelPerp A) = A.rank := by
  rw [← LinearMap.finrank_range_of_inj (restrictedMap_injective A),
    restrictedMap_range, matrixMap_range]
  rfl

/-- A chosen orthonormal basis of the actual kernel complement, indexed by
exactly `Fin (rank A)`. The choice depends only on the design matrix. -/
def coordinateBasis {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    OrthonormalBasis (Fin A.rank) ℝ (kernelPerp A) :=
  (stdOrthonormalBasis ℝ (kernelPerp A)).reindex (finCongr (kernelPerp_finrank A))

/-- The lifting map formed from that orthonormal basis. -/
def liftMap {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    (Fin A.rank → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
  (domainEquiv d).toLinearMap.comp
    ((kernelPerp A).subtype.comp (coordinateBasis A).toBasis.equivFun.symm.toLinearMap)

/-- The actual source lifting matrix `U`. -/
def coordinates {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    Matrix (Fin d) (Fin A.rank) ℝ := LinearMap.toMatrix' (liftMap A)

/-- A matrix column interpreted as the corresponding Euclidean vector. -/
def euclideanColumn {d r : ℕ} (U : Matrix (Fin d) (Fin r) ℝ)
    (j : Fin r) : EuclideanSpace ℝ (Fin d) := (domainEquiv d).symm (U.col j)

/-- Multiplication by the actual coordinate matrix is the basis lifting map. -/
theorem coordinates_mulVec {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (y : Fin A.rank → ℝ) :
    (coordinates A).mulVec y =
      domainEquiv d ((coordinateBasis A).toBasis.equivFun.symm y).val := by
  exact LinearMap.toMatrix'_mulVec (liftMap A) y

/-- Each actual matrix column is exactly the corresponding orthonormal basis vector. -/
theorem column_eq_basis {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (j : Fin A.rank) :
    euclideanColumn (coordinates A) j = ((coordinateBasis A) j).val := by
  classical
  have hs : (coordinateBasis A).toBasis.equivFun.symm (Pi.single j 1) =
      (coordinateBasis A) j := by
    apply (coordinateBasis A).toBasis.equivFun.injective
    simp only [LinearEquiv.apply_symm_apply]
    funext k
    simpa only [Pi.single_apply, eq_comm] using
      ((coordinateBasis A).toBasis.equivFun_self j k).symm
  unfold euclideanColumn
  rw [← Matrix.mulVec_single_one, coordinates_mulVec, hs,
    LinearEquiv.symm_apply_apply]

/-- The matrix-column family is exactly the chosen Euclidean basis family. -/
theorem columns_eq_basis {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    euclideanColumn (coordinates A) =
      (fun j : Fin A.rank => ((coordinateBasis A) j).val) :=
  funext (column_eq_basis A)

/-- The columns of the constructed matrix are genuinely orthonormal. -/
theorem columns_orthonormal {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    Orthonormal ℝ (euclideanColumn (coordinates A)) := by
  have h := (coordinateBasis A).orthonormal.comp_linearIsometry
    (kernelPerp A).subtypeₗᵢ
  rw [columns_eq_basis]
  exact h

/-- The actual columns span exactly the source kernel complement. -/
theorem columns_span_kernelPerp {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    Submodule.span ℝ (Set.range (euclideanColumn (coordinates A))) = kernelPerp A := by
  have h := congrArg (Submodule.map (kernelPerp A).subtype)
    (coordinateBasis A).toBasis.span_eq
  rw [Submodule.map_span, Submodule.map_subtype_top] at h
  have himage : (kernelPerp A).subtype '' Set.range (coordinateBasis A).toBasis =
      Set.range (fun j : Fin A.rank => ((coordinateBasis A) j).val) := by
    ext v
    constructor
    · rintro ⟨w, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨(coordinateBasis A) j, ⟨j, rfl⟩, rfl⟩
  rw [himage] at h
  rw [columns_eq_basis]
  exact h

/-- Predictions of the coordinate matrix are the original matrix map on the
chosen orthonormal-basis coordinates. -/
theorem coordinate_predictions {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (y : Fin A.rank → ℝ) :
    (A * coordinates A).mulVec y =
      restrictedMap A ((coordinateBasis A).toBasis.equivFun.symm y) := by
  rw [← Matrix.mulVec_mulVec, coordinates_mulVec]
  rfl

/-- Full column rank follows from the actual kernel-complement restriction. -/
theorem coordinate_predictions_injective {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) :
    Function.Injective (A * coordinates A).mulVec := by
  intro y z hyz
  apply (coordinateBasis A).toBasis.equivFun.symm.injective
  apply restrictedMap_injective A
  simpa only [coordinate_predictions] using hyz

/-- Every original prediction has coordinates in the constructed orthonormal
basis. This includes rank zero and all degenerate matrices. -/
theorem coordinate_predictions_cover {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (x : Fin d → ℝ) :
    ∃ y : Fin A.rank → ℝ, (A * coordinates A).mulVec y = A.mulVec x := by
  have hx : A.mulVec x ∈ LinearMap.range (restrictedMap A) := by
    rw [restrictedMap_range, matrixMap_range]
    exact ⟨x, rfl⟩
  obtain ⟨v, hv⟩ := hx
  refine ⟨(coordinateBasis A).toBasis.equivFun v, ?_⟩
  rw [coordinate_predictions, LinearEquiv.symm_apply_apply]
  exact hv

/-- The full orthonormal coordinate construction required in equation (3.37).
All listed properties are conclusions for a design-only choice of `U`. -/
theorem exists_orthonormal_rank_coordinates {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) :
    ∃ U : Matrix (Fin d) (Fin A.rank) ℝ,
      Orthonormal ℝ (euclideanColumn U) ∧
      Submodule.span ℝ (Set.range (euclideanColumn U)) = kernelPerp A ∧
      Function.Injective (A * U).mulVec ∧
      ∀ x : Fin d → ℝ, ∃ y : Fin A.rank → ℝ, (A * U).mulVec y = A.mulVec x := by
  exact ⟨coordinates A, columns_orthonormal A, columns_span_kernelPerp A,
    coordinate_predictions_injective A, coordinate_predictions_cover A⟩

/-- After deleting precisely the original zero rows, these same orthonormal
coordinates give a full-column-rank design with no zero row, as in (3.37). -/
theorem orthonormal_retained_reduction {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) :
    Orthonormal ℝ (euclideanColumn (coordinates A)) ∧
      Submodule.span ℝ (Set.range (euclideanColumn (coordinates A))) = kernelPerp A ∧
      (Reduction.coordinateDesign A (coordinates A)).rank = A.rank ∧
      (∀ i : Reduction.RetainedRows A, Reduction.coordinateDesign A (coordinates A) i ≠ 0) ∧
      ∀ x : Fin d → ℝ, ∃ y : Fin A.rank → ℝ,
        (A * coordinates A).mulVec y = A.mulVec x := by
  refine ⟨columns_orthonormal A, columns_span_kernelPerp A, ?_,
    Reduction.coordinate_row_nonzero A (coordinates A) (coordinate_predictions_cover A),
    coordinate_predictions_cover A⟩
  have hinj := Reduction.coordinate_injective_of_full_injective A (coordinates A)
    (coordinate_predictions_injective A)
  change Module.finrank ℝ (LinearMap.range
    (Reduction.coordinateDesign A (coordinates A)).mulVecLin) = A.rank
  rw [LinearMap.finrank_range_of_inj hinj]
  simp

end Paper29.OrthonormalReduction
