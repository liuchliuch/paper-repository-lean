import ELV.GramRealization
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Lemma 2.1 stabilization: gluing isometries on orthogonal complements
-/

noncomputable section

namespace ELV

namespace Stabilize

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

variable {K L : Submodule 𝕜 E} [CompleteSpace K] [CompleteSpace L]

/-- Glued continuous linear map: `x ↦ f(π_K x) + g(π_{Kᗮ} x)`. -/
def glueCLM (f : K ≃ₗᵢ[𝕜] L) (g : Kᗮ ≃ₗᵢ[𝕜] Lᗮ) : E →L[𝕜] E :=
  L.subtypeL ∘L (f.toLinearIsometry.toContinuousLinearMap ∘L K.orthogonalProjection)
    + Lᗮ.subtypeL ∘L (g.toLinearIsometry.toContinuousLinearMap ∘L Kᗮ.orthogonalProjection)

theorem glueCLM_apply (f : K ≃ₗᵢ[𝕜] L) (g : Kᗮ ≃ₗᵢ[𝕜] Lᗮ) (x : E) :
    glueCLM f g x
      = (f (K.orthogonalProjection x) : E) + (g (Kᗮ.orthogonalProjection x) : E) := by
  simp [glueCLM]

/-- The two glued pieces are orthogonal (`L ⟂ Lᗮ`). -/
theorem glueCLM_inner (f : K ≃ₗᵢ[𝕜] L) (g : Kᗮ ≃ₗᵢ[𝕜] Lᗮ) (x : E) :
    inner 𝕜 (f (K.orthogonalProjection x) : E)
        (g (Kᗮ.orthogonalProjection x) : E) = 0 := by
  have h1 : (f (K.orthogonalProjection x) : E) ∈ L :=
    (f (K.orthogonalProjection x)).2
  have h2 : (g (Kᗮ.orthogonalProjection x) : E) ∈ Lᗮ :=
    (g (Kᗮ.orthogonalProjection x)).2
  exact Submodule.isOrtho_iff_inner_eq.mp (Submodule.isOrtho_orthogonal_right L)
    _ h1 _ h2

/-- Pythagoras for the two glued pieces. -/
theorem glueCLM_norm_sq (f : K ≃ₗᵢ[𝕜] L) (g : Kᗮ ≃ₗᵢ[𝕜] Lᗮ) (x : E) :
    ‖glueCLM f g x‖ ^ 2
      = ‖(f (K.orthogonalProjection x) : E)‖ ^ 2
        + ‖(g (Kᗮ.orthogonalProjection x) : E)‖ ^ 2 := by
  rw [glueCLM_apply]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (f (K.orthogonalProjection x) : E) (g (Kᗮ.orthogonalProjection x) : E)
    (glueCLM_inner f g x)
  simpa [pow_two] using h

/-- The two projections of `x` are orthogonal. -/
theorem proj_orthogonal (x : E) :
    inner 𝕜 (K.orthogonalProjection x : E) (Kᗮ.orthogonalProjection x : E) = 0 :=
  Submodule.isOrtho_iff_inner_eq.mp (Submodule.isOrtho_orthogonal_right K)
    _ (K.orthogonalProjection x).2 _ (Kᗮ.orthogonalProjection x).2

/-- Pythagoras for the two projections of `x`. -/
theorem proj_norm_sq (x : E) :
    ‖x‖ ^ 2 = ‖K.orthogonalProjection x‖ ^ 2 + ‖Kᗮ.orthogonalProjection x‖ ^ 2 := by
  have hx : (x : E) = K.starProjection x + Kᗮ.starProjection x := by
    have h : Kᗮ.starProjection = ContinuousLinearMap.id 𝕜 E - K.starProjection :=
      Submodule.starProjection_orthogonal K
    have h2 : Kᗮ.starProjection x = x - K.starProjection x := by
      rw [h]
      simp
    rw [h2]
    abel
  have hc : (K.orthogonalProjection x : E) = K.starProjection x := rfl
  have hc' : (Kᗮ.orthogonalProjection x : E) = Kᗮ.starProjection x := rfl
  rw [← hc, ← hc'] at hx
  rw [hx]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (K.orthogonalProjection x : E) (Kᗮ.orthogonalProjection x : E)
    (proj_orthogonal x)
  simpa [pow_two] using h

/-- The glued map preserves norms. -/
theorem glueCLM_norm (f : K ≃ₗᵢ[𝕜] L) (g : Kᗮ ≃ₗᵢ[𝕜] Lᗮ) (x : E) :
    ‖glueCLM f g x‖ = ‖x‖ := by
  have h1 : ‖(f (K.orthogonalProjection x) : E)‖ ^ 2
      = ‖K.orthogonalProjection x‖ ^ 2 := by
    have h : ‖(f (K.orthogonalProjection x) : E)‖ = ‖(K.orthogonalProjection x : E)‖ := by
      rw [Submodule.norm_coe, Submodule.norm_coe]
      exact LinearIsometryEquiv.norm_map f _
    have h' : ‖(K.orthogonalProjection x : E)‖ = ‖K.orthogonalProjection x‖ := rfl
    rw [h, h']
  have h2 : ‖(g (Kᗮ.orthogonalProjection x) : E)‖ ^ 2
      = ‖Kᗮ.orthogonalProjection x‖ ^ 2 := by
    have h : ‖(g (Kᗮ.orthogonalProjection x) : E)‖ = ‖(Kᗮ.orthogonalProjection x : E)‖ := by
      rw [Submodule.norm_coe, Submodule.norm_coe]
      exact LinearIsometryEquiv.norm_map g _
    have h' : ‖(Kᗮ.orthogonalProjection x : E)‖ = ‖Kᗮ.orthogonalProjection x‖ := rfl
    rw [h, h']
  have hclm := glueCLM_norm_sq f g x
  have hpy := proj_norm_sq (K := K) x
  have hnn : 0 ≤ ‖glueCLM f g x‖ := norm_nonneg _
  have hnn2 : 0 ≤ ‖x‖ := norm_nonneg _
  nlinarith [h1, h2, hclm, hpy, sq_nonneg (‖glueCLM f g x‖), sq_nonneg ‖x‖]

/-- Glued linear isometry. -/
def glueIsometry (f : K ≃ₗᵢ[𝕜] L) (g : Kᗮ ≃ₗᵢ[𝕜] Lᗮ) : E →ₗᵢ[𝕜] E where
  toLinearMap := (glueCLM f g).toLinearMap
  norm_map' := glueCLM_norm f g

/-- Projection of a `K`-vector is itself. -/
theorem proj_K_of_mem (x : K) :
    K.orthogonalProjection (x : E) = x :=
  Submodule.orthogonalProjection_mem_subspace_eq_self x

/-- Projection of a `Kᗮ`-vector is zero. -/
theorem proj_K_of_mem_orthogonal (x : Kᗮ) :
    K.orthogonalProjection (x : E) = 0 :=
  Submodule.orthogonalProjection_eq_zero_iff.mpr x.2

/-- Projection of a `Kᗮ`-vector onto `Kᗮ` is itself. -/
theorem proj_Korth_of_mem (x : Kᗮ) :
    Kᗮ.orthogonalProjection (x : E) = x :=
  Submodule.orthogonalProjection_mem_subspace_eq_self x

/-- Projection of a `K`-vector onto `Kᗮ` is zero. -/
theorem proj_Korth_of_mem_K (x : K) :
    Kᗮ.orthogonalProjection (x : E) = 0 :=
  Submodule.orthogonalProjection_eq_zero_iff.mpr
    (Submodule.isOrtho_iff_le.mp (Submodule.isOrtho_orthogonal_right K) x.2)

/-- Explicit surjectivity of the glued isometry. -/
theorem glueIsometry_surjective (f : K ≃ₗᵢ[𝕜] L) (g : Kᗮ ≃ₗᵢ[𝕜] Lᗮ) :
    Function.Surjective (glueIsometry f g : E → E) := by
  intro y
  refine ⟨(f.symm (L.orthogonalProjection y) : E)
      + (g.symm (Lᗮ.orthogonalProjection y) : E), ?_⟩
  -- y = π_L y + π_Lᗮ y
  have hy : y = (L.orthogonalProjection y : E) + (Lᗮ.orthogonalProjection y : E) := by
    have hx : (y : E) = L.starProjection y + Lᗮ.starProjection y := by
      have h : Lᗮ.starProjection = ContinuousLinearMap.id 𝕜 E - L.starProjection :=
        Submodule.starProjection_orthogonal L
      have h2 : Lᗮ.starProjection y = y - L.starProjection y := by
        rw [h]; simp
      rw [h2]; abel
    -- starProjection = orthogonalProjection coerced
    have hc : (L.orthogonalProjection y : E) = L.starProjection y := rfl
    have hc' : (Lᗮ.orthogonalProjection y : E) = Lᗮ.starProjection y := rfl
    rw [← hc, ← hc'] at hx
    exact hx
  -- projections of the preimage
  have hK : K.orthogonalProjection
        ((f.symm (L.orthogonalProjection y) : E)
          + (g.symm (Lᗮ.orthogonalProjection y) : E))
      = f.symm (L.orthogonalProjection y) := by
    rw [map_add, proj_K_of_mem, proj_K_of_mem_orthogonal, add_zero]
  have hKo : Kᗮ.orthogonalProjection
        ((f.symm (L.orthogonalProjection y) : E)
          + (g.symm (Lᗮ.orthogonalProjection y) : E))
      = g.symm (Lᗮ.orthogonalProjection y) := by
    rw [map_add, proj_Korth_of_mem_K, proj_Korth_of_mem, zero_add]
  -- glueCLM on the preimage
  have hglue : glueCLM f g
        ((f.symm (L.orthogonalProjection y) : E)
          + (g.symm (Lᗮ.orthogonalProjection y) : E))
      = (f (f.symm (L.orthogonalProjection y)) : E)
        + (g (g.symm (Lᗮ.orthogonalProjection y)) : E) := by
    rw [glueCLM_apply, hK, hKo]
  -- glueIsometry is glueCLM
  have hcoe : (glueIsometry f g :
        E → E) = glueCLM f g := rfl
  rw [hcoe, hglue]
  have hf : (f (f.symm (L.orthogonalProjection y)) : E)
      = (L.orthogonalProjection y : E) := by
    rw [f.apply_symm_apply]
  have hg : (g (g.symm (Lᗮ.orthogonalProjection y)) : E)
      = (Lᗮ.orthogonalProjection y : E) := by
    rw [g.apply_symm_apply]
  rw [hf, hg]
  exact hy.symm

/-- Glued linear isometric equivalence. -/
noncomputable def glueIsometryEquiv (f : K ≃ₗᵢ[𝕜] L) (g : Kᗮ ≃ₗᵢ[𝕜] Lᗮ) :
    E ≃ₗᵢ[𝕜] E :=
  LinearIsometryEquiv.ofSurjective (glueIsometry f g)
    (glueIsometry_surjective f g)

/-- The glued equivalence acts as `f` on `K`. -/
theorem glueIsometryEquiv_of_mem_K (f : K ≃ₗᵢ[𝕜] L) (g : Kᗮ ≃ₗᵢ[𝕜] Lᗮ)
    (x : K) : (glueIsometryEquiv f g (x : E) : E) = (f x : E) := by
  have h1 : K.orthogonalProjection (x : E) = x := proj_K_of_mem x
  have h2 : Kᗮ.orthogonalProjection (x : E) = 0 := proj_Korth_of_mem_K x
  have hglue : glueCLM f g (x : E) = (f x : E) + (g (0 : Kᗮ) : E) := by
    rw [glueCLM_apply, h1, h2]
  have h0 : (g (0 : Kᗮ) : E) = 0 := by simp
  have hcoe : (glueIsometry f g : E → E) = glueCLM f g := rfl
  rw [glueIsometryEquiv, LinearIsometryEquiv.coe_ofSurjective, hcoe, hglue, h0, add_zero]

section Julia

open InnerProduct

/-- Julia operator on `E ⊕₂ E`:
    `U(x,y) = (A x + π_{Lᗮ} y, π_{Kᗮ} x - (ContinuousLinearMap.adjoint A) y)`. -/
def juliaMap (K L : Submodule 𝕜 E) [CompleteSpace K] [CompleteSpace L]
    (A : E →L[𝕜] E) (z : WithLp 2 (E × E)) : WithLp 2 (E × E) :=
  WithLp.toLp 2
    (A (WithLp.ofLp z).1 + Lᗮ.starProjection (WithLp.ofLp z).2,
      Kᗮ.starProjection (WithLp.ofLp z).1 - (ContinuousLinearMap.adjoint A) ((WithLp.ofLp z).2))

theorem juliaMap_ofLp (K L : Submodule 𝕜 E) [CompleteSpace K] [CompleteSpace L]
    (A : E →L[𝕜] E) (x y : E) :
    WithLp.ofLp (juliaMap K L A (WithLp.toLp 2 (x, y)))
      = (A x + Lᗮ.starProjection y, Kᗮ.starProjection x - (ContinuousLinearMap.adjoint A) y) := by
  simp [juliaMap]

/-- Julia map on a `K`-vector in the first component. -/
theorem juliaMap_on_K (A : E →L[𝕜] E) (x : K) :
    WithLp.ofLp (juliaMap K L A (WithLp.toLp 2 ((x : E), 0)))
      = (A x, (0 : E)) := by
  rw [juliaMap_ofLp]
  simp [proj_Korth_of_mem_K x]

/-- Julia map on a `K`-vector: first component is `A x`, second is `0`. -/
theorem juliaMap_on_K_apply (A : E →L[𝕜] E) (x : K) :
    juliaMap K L A (WithLp.toLp 2 ((x : E), 0))
      = WithLp.toLp 2 (A x, (0 : E)) := by
  have h := juliaMap_on_K (K := K) (L := L) A x
  have h1 : WithLp.ofLp (juliaMap K L A (WithLp.toLp 2 ((x : E), 0)))
      = WithLp.ofLp (WithLp.toLp 2 (A x, (0 : E))) := by
    rw [h]
    simp
  have h2 : (WithLp.toLp 2 (WithLp.ofLp
        (juliaMap K L A (WithLp.toLp 2 ((x : E), 0)))) : WithLp 2 (E × E))
      = juliaMap K L A (WithLp.toLp 2 ((x : E), 0)) := by
    simp
  rw [← h2, h1]
  simp

end Julia

end Stabilize

end ELV
