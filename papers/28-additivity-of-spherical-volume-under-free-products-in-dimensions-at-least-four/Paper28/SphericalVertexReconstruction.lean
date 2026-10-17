import Paper28.NormalizedAffineMaps
import Paper28.FiniteLipschitzCalculus
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Basis.Basic

/-! Explicit continuous linear reconstruction from independent spherical
vertex vectors, extended using the actual orthogonal projection. Dividing
by the reconstructed barycentric sum gives the actual inverse projective
formula; its local Lipschitz regularity is proved. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Set Module
open scoped Topology
variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [NormedSpace ℝ H]
  {m : ℕ}

def vertexReconstructionLinear (q : ι → EuclideanSpace ℝ (Fin m)) (hq : LinearIndependent ℝ q) (p : ι → H) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] H :=
  ((Basis.span hq).constr ℝ p).toContinuousLinearMap.comp (Submodule.span ℝ (Set.range q)).orthogonalProjection

theorem vertexReconstructionLinear_vertex (q : ι → EuclideanSpace ℝ (Fin m))
    (hq : LinearIndependent ℝ q) (p : ι → H) (i : ι) : vertexReconstructionLinear q hq p (q i) = p i := by
  let S := Submodule.span ℝ (Set.range q)
  have hp : S.orthogonalProjection (q i) = Basis.span hq i := by
    apply Subtype.ext
    rw [Basis.span_apply]
    exact congrArg Subtype.val (S.orthogonalProjection_mem_subspace_eq_self ⟨q i,Submodule.subset_span (mem_range_self i)⟩)
  change ((Basis.span hq).constr ℝ p) (S.orthogonalProjection (q i)) = p i
  rw [hp,Basis.constr_basis]

attribute [irreducible] vertexReconstructionLinear

def affineProjectiveReconstruction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] H) (ell : E →L[ℝ] ℝ) (u : E) : H := (ell u)⁻¹ • P u

theorem affineProjectiveReconstruction_near_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : E →L[ℝ] H) (ell : E →L[ℝ] ℝ) (u : E) (hu : ell u ≠ 0) :
    ∃ L : NNReal, ∃ S : Set E, S ∈ 𝓝 u ∧ LipschitzOnWith L (affineProjectiveReconstruction P ell) S := by
  let g : E → ℝ×H := fun v => (ell v,P v)
  let φ : ℝ×H → H := fun v => v.1⁻¹ • v.2
  have hg : LipschitzWith (max ‖ell‖₊ ‖P‖₊) g := ell.lipschitz.prodMk P.lipschitz
  have hφ : ContDiffAt ℝ 1 φ (g u) := (contDiffAt_fst.inv hu).smul contDiffAt_snd
  exact lipschitz_comp_contDiff_neighborhood g _ hg φ u hφ

theorem affineProjectiveReconstruction_normalized
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →L[ℝ] H) (ell : E →L[ℝ] ℝ) (v : E) (hell : ell v = 1) :
    affineProjectiveReconstruction P ell (sphericalNormalize v) = P v := by
  have hv : v ≠ 0 := by intro h; rw [h,map_zero] at hell; exact zero_ne_one hell
  unfold affineProjectiveReconstruction sphericalNormalize
  rw [map_smul,map_smul,hell,smul_eq_mul,mul_one,inv_inv,smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv),one_smul]

end Paper28
