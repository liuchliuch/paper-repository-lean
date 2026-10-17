import Paper38.Model
import Paper38.Mobility
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.CompactOpen
import Mathlib.Tactic

/-!
# The source Euclidean--Frobenius Hilbert coordinates

The raw encoding `Model.Coordinates` does not prescribe the paper's Hilbert
norm. For smooth coordinate transport this file explicitly opens the Frobenius
matrix norm; the raw product still carries its maximum norm. We flatten matrix
entries into a Euclidean space and take the L² product for the source metric.  The actual tangent type is the
symmetric-matrix subspace, so it contains no antisymmetric tangent directions.
-/
noncomputable section
open scoped BigOperators Matrix InnerProductSpace Matrix.Norms.Frobenius

namespace Paper38.HilbertCoordinates
open Paper38.Model

abbrev Flat (d : ℕ) := EuclideanSpace ℝ (Fin d × Fin d)
abbrev Ambient (d : ℕ) := WithLp 2 (E d × Flat d)

/-- Reindexing matrix entries, with the Euclidean norm on the codomain. -/
def flattenLinearEquiv (d : ℕ) : Mat d ≃ₗ[ℝ] Flat d where
  toFun A := WithLp.toLp 2 (fun p => A p.1 p.2)
  invFun u := fun i j => u (i, j)
  left_inv A := by rfl
  right_inv u := by ext p; rfl
  map_add' A B := by ext p; rfl
  map_smul' c A := by ext p; rfl

/-- A smooth linear change of topology; its target norm is Frobenius. -/
def flattenEquiv (d : ℕ) : Mat d ≃L[ℝ] Flat d :=
  (flattenLinearEquiv d).toContinuousLinearEquiv

@[simp] lemma flattenEquiv_apply {d : ℕ} (A : Mat d) (p : Fin d × Fin d) :
    flattenEquiv d A p = A p.1 p.2 := rfl

@[simp] theorem norm_flatten_sq {d : ℕ} (A : Mat d) :
    ‖flattenEquiv d A‖ ^ 2 = frobSq A := by
  simp [EuclideanSpace.norm_sq_eq, frobSq, Fintype.sum_prod_type]

/-- Full ambient linear identification; positivity is subsequently restricted
 to the symmetric tangent subspace. -/
def ambientLinearEquiv (d : ℕ) : Coordinates d ≃ₗ[ℝ] Ambient d :=
  ((LinearEquiv.refl ℝ (E d)).prodCongr (flattenLinearEquiv d)).trans
    (WithLp.linearEquiv 2 ℝ (E d × Flat d)).symm

def ambientEquiv (d : ℕ) : Coordinates d ≃L[ℝ] Ambient d :=
  (ambientLinearEquiv d).toContinuousLinearEquiv

@[simp] lemma ambientEquiv_apply {d : ℕ} (q : Coordinates d) :
    ambientEquiv d q = WithLp.toLp 2 (q.1, flattenEquiv d q.2) := rfl

@[simp] theorem norm_ambient_sq {d : ℕ} (q : Coordinates d) :
    ‖ambientEquiv d q‖ ^ 2 = ‖q.1‖ ^ 2 + frobSq q.2 := by
  rw [ambientEquiv_apply, WithLp.prod_norm_sq_eq_of_L2]
  change ‖q.1‖ ^ 2 + ‖flattenEquiv d q.2‖ ^ 2 = _
  rw [norm_flatten_sq]

/-- Exact source norm, not the default matrix/product norm. -/
theorem coordinateSqDist_eq_norm_ambient {d : ℕ} (q r : Coordinates d) :
    coordinateSqDist q r = ‖ambientEquiv d q - ambientEquiv d r‖ ^ 2 := by
  rw [← map_sub, norm_ambient_sq]
  rfl

/-- Ordinary Frobenius bilinear product in orthonormal matrix coordinates. -/
def matrixInner {d : ℕ} (A B : Mat d) : ℝ := ∑ i, ∑ j, A i j * B i j

lemma matrixInner_eq_frobenius {d : ℕ} (A B : Mat d) :
    matrixInner A B = Paper38.Mobility.frobenius A B := by
  simp only [matrixInner, Paper38.Mobility.frobenius, Matrix.trace, Matrix.diag,
    Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

theorem inner_ambient {d : ℕ} (q r : Coordinates d) :
    ⟪ambientEquiv d q, ambientEquiv d r⟫_ℝ =
      ⟪q.1, r.1⟫_ℝ + matrixInner q.2 r.2 := by
  rw [ambientEquiv_apply, ambientEquiv_apply, WithLp.prod_inner_apply]
  change ⟪q.1, r.1⟫_ℝ + ⟪flattenEquiv d q.2, flattenEquiv d r.2⟫_ℝ = _
  congr 1
  simp [EuclideanSpace.inner_eq_star_dotProduct, matrixInner, dotProduct,
    Fintype.sum_prod_type, mul_comm]

/-- The actual raw symmetric tangent subspace R^d × Sym(d). -/
def symmetricRaw (d : ℕ) : Submodule ℝ (Coordinates d) where
  carrier := {q | q.2ᵀ = q.2}
  zero_mem' := by simp
  add_mem' := by
    intro q r hq hr
    change q.2ᵀ = q.2 at hq
    change r.2ᵀ = r.2 at hr
    change (q.2 + r.2)ᵀ = q.2 + r.2
    rw [Matrix.transpose_add, hq, hr]
  smul_mem' := by
    intro c q hq
    change q.2ᵀ = q.2 at hq
    change (c • q.2)ᵀ = c • q.2
    rw [Matrix.transpose_smul, hq]

/-- The same symmetric subspace with the Euclidean--Frobenius Hilbert norm. -/
def tangentSubmodule (d : ℕ) : Submodule ℝ (Ambient d) :=
  (symmetricRaw d).map (ambientLinearEquiv d).toLinearMap

abbrev Tangent (d : ℕ) := tangentSubmodule d

/-- Normed linear equivalence between the two encodings of the symmetric space. -/
def tangentEquiv (d : ℕ) : symmetricRaw d ≃L[ℝ] Tangent d :=
  ((ambientLinearEquiv d).submoduleMap (symmetricRaw d)).toContinuousLinearEquiv

/-- Embedding of source Hilbert coordinates into the actual paper model. -/
def toModel (d : ℕ) : Tangent d →L[ℝ] Coordinates d :=
  (ambientEquiv d).symm.toContinuousLinearMap.comp (tangentSubmodule d).subtypeL

@[simp] lemma toModel_apply {d : ℕ} (q : Tangent d) :
    toModel d q = (ambientEquiv d).symm (q : Ambient d) := rfl

@[simp] lemma ambient_toModel {d : ℕ} (q : Tangent d) :
    ambientEquiv d (toModel d q) = (q : Ambient d) :=
  (ambientEquiv d).apply_symm_apply q

lemma toModel_injective (d : ℕ) : Function.Injective (toModel d) :=
  (ambientEquiv d).symm.injective.comp Subtype.val_injective

@[simp] lemma toModel_tangentEquiv {d : ℕ} (q : symmetricRaw d) :
    toModel d (tangentEquiv d q) = (q : Coordinates d) :=
  (ambientEquiv d).symm_apply_apply q

/-- Every represented matrix and every tangent direction is symmetric. -/
theorem toModel_symmetric {d : ℕ} (q : Tangent d) :
    (toModel d q).2ᵀ = (toModel d q).2 := by
  exact ((tangentEquiv d).symm q).property

/-- Encoding any actual symmetric model state in the source Hilbert space. -/
def ofModel {d : ℕ} (q : Coordinates d) (hq : q.2ᵀ = q.2) : Tangent d :=
  tangentEquiv d ⟨q, hq⟩

@[simp] lemma toModel_ofModel {d : ℕ} (q : Coordinates d) (hq : q.2ᵀ = q.2) :
    toModel d (ofModel q hq) = q := toModel_tangentEquiv ⟨q, hq⟩

@[simp] lemma ofModel_toModel {d : ℕ} (q : Tangent d) :
    ofModel (toModel d q) (toModel_symmetric q) = q := by
  apply toModel_injective d
  rw [toModel_ofModel]

/-- Smooth mean-coordinate projection. -/
def meanProjection (d : ℕ) : Tangent d →L[ℝ] E d :=
  (ContinuousLinearMap.fst ℝ (E d) (Mat d)).comp (toModel d)

/-- Smooth symmetric-matrix-coordinate projection. -/
def matrixProjection (d : ℕ) : Tangent d →L[ℝ] Mat d :=
  (ContinuousLinearMap.snd ℝ (E d) (Mat d)).comp (toModel d)

@[simp] lemma meanProjection_apply {d : ℕ} (q : Tangent d) :
    meanProjection d q = (toModel d q).1 := rfl

@[simp] lemma matrixProjection_apply {d : ℕ} (q : Tangent d) :
    matrixProjection d q = (toModel d q).2 := rfl

/-- The Hilbert distance is literally the source coordinate squared distance. -/
theorem coordinateSqDist_toModel {d : ℕ} (q r : Tangent d) :
    coordinateSqDist (toModel d q) (toModel d r) = ‖q - r‖ ^ 2 := by
  rw [coordinateSqDist_eq_norm_ambient, ambient_toModel, ambient_toModel]
  rfl

/-- Frobenius product identity for the intrinsic source tangent Hilbert space. -/
theorem inner_toModel {d : ℕ} (q r : Tangent d) :
    ⟪q, r⟫_ℝ = ⟪(toModel d q).1, (toModel d r).1⟫_ℝ +
      matrixInner (toModel d q).2 (toModel d r).2 := by
  calc
    ⟪q, r⟫_ℝ = ⟪(q : Ambient d), (r : Ambient d)⟫_ℝ := rfl
    _ = ⟪ambientEquiv d (toModel d q), ambientEquiv d (toModel d r)⟫_ℝ := by
      rw [ambient_toModel, ambient_toModel]
    _ = _ := inner_ambient _ _

/-- Exact bridge to the pairing used in the source mobility calculation. -/
theorem inner_eq_mobility_pairing {d : ℕ} (q r : Tangent d) :
    ⟪q, r⟫_ℝ = Paper38.Mobility.pairing
      (WithLp.ofLp (toModel d q).1) (toModel d q).2
      (WithLp.ofLp (toModel d r).1) (toModel d r).2 := by
  rw [inner_toModel, matrixInner_eq_frobenius]
  unfold Paper38.Mobility.pairing
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial]
  rw [dotProduct_comm]

lemma tangentSubmodule_closed (d : ℕ) : IsClosed (tangentSubmodule d : Set (Ambient d)) :=
  (tangentSubmodule d).closed_of_finiteDimensional

/-- The paper's positive definite domain, now in its intrinsic symmetric space. -/
def Domain (d : ℕ) : Set (Tangent d) := {q | (toModel d q).2.PosDef}

/-- A fixed interior anchor, independent of minimizer existence. -/
def anchor (d : ℕ) : Tangent d := ofModel (0, (1 : Mat d)) (by simp)

@[simp] theorem toModel_anchor (d : ℕ) : toModel d (anchor d) = (0, (1 : Mat d)) := by
  exact toModel_ofModel _ _

@[simp] theorem anchor_mem_Domain (d : ℕ) : anchor d ∈ Domain d := by
  change (toModel d (anchor d)).2.PosDef
  rw [toModel_anchor]
  exact Matrix.PosDef.one

theorem Domain_nonempty (d : ℕ) : (Domain d).Nonempty := ⟨anchor d, anchor_mem_Domain d⟩

lemma domain_subset_symmetric (d : ℕ) : domain d ⊆ symmetricRaw d := by
  intro q hq
  change q.2.PosDef at hq
  change q.2ᵀ = q.2
  simpa using hq.1

lemma domain_convex (d : ℕ) : Convex ℝ (domain d) := by
  intro q hq r hr a b ha hb hab
  change q.2.PosDef at hq
  change r.2.PosDef at hr
  change (a • q.2 + b • r.2).PosDef
  rcases eq_or_lt_of_le ha with ha | ha
  · have hb' : b = 1 := by linarith
    simpa [← ha, hb'] using hr
  · exact (hq.smul ha).add_posSemidef (hr.posSemidef.smul hb)

theorem Domain_convex (d : ℕ) : Convex ℝ (Domain d) :=
  (domain_convex d).linear_preimage (toModel d).toLinearMap

abbrev UnitSphere (d : ℕ) := ↥(Metric.sphere (0 : E d) 1)

instance unitSphere_compactSpace (d : ℕ) : CompactSpace (UnitSphere d) :=
  isCompact_iff_compactSpace.mp (isCompact_sphere (0 : E d) 1)

/-- Actual real quadratic form of a matrix on a Euclidean vector. -/
def quadratic {d : ℕ} (A : Mat d) (v : E d) : ℝ :=
  WithLp.ofLp v ⬝ᵥ (A *ᵥ WithLp.ofLp v)

/-- A symmetric matrix is positive definite exactly when its quadratic form is
positive on the compact Euclidean unit sphere. The converse uses its actual
orthonormal eigenbasis. -/
lemma posDef_iff_quadratic_unit {d : ℕ} (A : Mat d) (hA : Aᵀ = A) :
    A.PosDef ↔ ∀ v : UnitSphere d, 0 < quadratic A v.val := by
  have hh : A.IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  constructor
  · intro hp v
    have hv : WithLp.ofLp v.val ≠ 0 := by
      intro hz
      have hz' : v.val = 0 := congrArg (WithLp.toLp 2) hz
      have hn : ‖v.val‖ = 1 := by
        simpa only [Metric.mem_sphere, dist_zero_right] using v.property
      rw [hz', norm_zero] at hn
      norm_num at hn
    simpa only [quadratic, star_trivial] using hp.2 _ hv
  · intro hp
    rw [hh.posDef_iff_eigenvalues_pos]
    intro i
    rw [hh.eigenvalues_eq]
    have hn : hh.eigenvectorBasis i ∈ Metric.sphere (0 : E d) 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using
        hh.eigenvectorBasis.orthonormal.norm_eq_one i
    simpa only [quadratic, star_trivial, RCLike.re_to_real] using
      hp ⟨hh.eigenvectorBasis i, hn⟩

/-- Quadratic forms on the compact sphere, equipped with compact-open topology. -/
def sphereQuadratic {d : ℕ} (q : Tangent d) : C(UnitSphere d, ℝ) where
  toFun v := quadratic (toModel d q).2 v.val
  continuous_toFun := by
    unfold quadratic Matrix.mulVec dotProduct
    fun_prop

lemma continuous_sphereQuadratic (d : ℕ) : Continuous (sphereQuadratic (d := d)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : Tangent d × UnitSphere d => quadratic (toModel d p.1).2 p.2.val)
  unfold quadratic Matrix.mulVec dotProduct
  fun_prop

lemma Domain_eq_sphere_preimage (d : ℕ) :
    Domain d = sphereQuadratic ⁻¹'
      {f : C(UnitSphere d, ℝ) | Set.MapsTo f Set.univ (Set.Ioi 0)} := by
  ext q
  change (toModel d q).2.PosDef ↔ Set.MapsTo (sphereQuadratic q) Set.univ (Set.Ioi 0)
  constructor
  · intro hq v _
    exact (posDef_iff_quadratic_unit _ (toModel_symmetric q)).mp hq v
  · intro hq
    exact (posDef_iff_quadratic_unit _ (toModel_symmetric q)).mpr
      (fun v => hq (Set.mem_univ v))

/-- The positive definite domain is open in the actual symmetric tangent space.
No openness in the full nonsymmetric matrix ambient space is asserted. -/
theorem Domain_isOpen (d : ℕ) : IsOpen (Domain d) := by
  rw [Domain_eq_sphere_preimage]
  exact (ContinuousMap.isOpen_setOf_mapsTo isCompact_univ isOpen_Ioi).preimage
    (continuous_sphereQuadratic d)

/-- Positive semidefiniteness is closed in the intrinsic symmetric space. -/
theorem isClosed_posSemidef (d : ℕ) :
    IsClosed {q : Tangent d | (toModel d q).2.PosSemidef} := by
  have hc (v : E d) : Continuous (fun q : Tangent d => quadratic (toModel d q).2 v) := by
    unfold quadratic Matrix.mulVec dotProduct
    fun_prop
  have hclosed : IsClosed (⋂ v : E d, {q : Tangent d | 0 ≤ quadratic (toModel d q).2 v}) :=
    isClosed_iInter (fun v => isClosed_le continuous_const (hc v))
  convert hclosed using 1
  ext q
  simp only [Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro hq v
    simpa only [quadratic, star_trivial] using hq.2 (WithLp.ofLp v)
  · intro hq
    refine ⟨?_, fun x => ?_⟩
    · simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using toModel_symmetric q
    · simpa only [quadratic, Model.vec, WithLp.ofLp_toLp, star_trivial] using hq (vec d x)

/-- A limit of positive definite source states can only reach the PSD boundary. -/
theorem Domain_closure_posSemidef {d : ℕ} {q : Tangent d}
    (hq : q ∈ closure (Domain d)) : (toModel d q).2.PosSemidef := by
  have hsub : Domain d ⊆ {q : Tangent d | (toModel d q).2.PosSemidef} := by
    intro r hr
    exact hr.posSemidef
  exact closure_minimal hsub (isClosed_posSemidef d) hq

/-- Determinant separation prevents a source-domain limit from reaching the boundary. -/
theorem Domain_closure_det_ne_zero {d : ℕ} {q : Tangent d}
    (hq : q ∈ closure (Domain d)) (hdet : (toModel d q).2.det ≠ 0) : q ∈ Domain d := by
  have hp := Domain_closure_posSemidef hq
  exact hp.posDef_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))

/-- Literal pullback of the paper's energy to the correct Hilbert space. -/
def energy {d : ℕ} (V : E d → ℝ) (q : Tangent d) : ℝ := Model.energy V (toModel d q)

@[simp] theorem energy_eq {d : ℕ} (V : E d → ℝ) (q : Tangent d) :
    energy V q = Model.energy V (toModel d q) := rfl

/-- The source energy in its actual Gaussian-expectation/log-determinant form. -/
theorem energy_explicit {d : ℕ} (V : E d → ℝ) (q : Tangent d) :
    energy V q =
      (∫ z, V (meanProjection d q + matVec (matrixProjection d q) z)
        ∂standardGaussian d) - Real.log (matrixProjection d q).det := rfl

lemma toModel_contDiff (d : ℕ) (n : WithTop ℕ∞) : ContDiff ℝ n (toModel d) :=
  (toModel d).contDiff

/-- Chain-rule transport is along symmetric tangent directions only. -/
theorem hasFDerivAt_energy_of_model {d : ℕ} {V : E d → ℝ} {q : Tangent d}
    {L : Coordinates d →L[ℝ] ℝ} (h : HasFDerivAt (Model.energy V) L (toModel d q)) :
    HasFDerivAt (energy V) (L.comp (toModel d)) q :=
  h.comp q (toModel d).hasFDerivAt

end Paper38.HilbertCoordinates
