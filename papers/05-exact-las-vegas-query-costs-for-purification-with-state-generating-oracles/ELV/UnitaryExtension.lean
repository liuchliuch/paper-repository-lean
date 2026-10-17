import ELV.Stabilize

/-! A unitary dilation of an isometry between closed subspaces.
The extra copy of the ambient space removes the complement obstruction.
No equivalence between the original orthogonal complements is assumed. -/
noncomputable section
namespace ELV.Stabilize

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {K L : Submodule 𝕜 E} [CompleteSpace K] [CompleteSpace L]

abbrev HilbertPair (E F : Type*) := WithLp 2 (E × F)

/-- Exchange the initial and final subspaces through `f`, and exchange the
remaining two orthogonal components directly. -/
def dilationLM (f : K ≃ₗᵢ[𝕜] L) : HilbertPair E E →ₗ[𝕜] HilbertPair E E where
  toFun z := WithLp.toLp 2
    ((f (K.orthogonalProjection z.fst) : E) + (Lᗮ.orthogonalProjection z.snd : E),
     (f.symm (L.orthogonalProjection z.snd) : E) + (Kᗮ.orthogonalProjection z.fst : E))
  map_add' x y := by
    apply (WithLp.equiv 2 (E × E)).injective
    ext <;> simp [map_add, add_add_add_comm]
  map_smul' c x := by
    apply (WithLp.equiv 2 (E × E)).injective
    ext <;> simp [map_smul, smul_add]

@[simp] theorem dilationLM_fst (f : K ≃ₗᵢ[𝕜] L) (z : HilbertPair E E) :
    (dilationLM f z).fst =
      (f (K.orthogonalProjection z.fst) : E) + (Lᗮ.orthogonalProjection z.snd : E) := rfl

@[simp] theorem dilationLM_snd (f : K ≃ₗᵢ[𝕜] L) (z : HilbertPair E E) :
    (dilationLM f z).snd =
      (f.symm (L.orthogonalProjection z.snd) : E) + (Kᗮ.orthogonalProjection z.fst : E) := rfl

lemma orthogonal_sum_norm_sq (x : K) (y : Kᗮ) :
    ‖(x : E) + (y : E)‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have h : inner 𝕜 (x : E) (y : E) = 0 :=
    Submodule.isOrtho_iff_inner_eq.mp (Submodule.isOrtho_orthogonal_right K) _ x.2 _ y.2
  simpa [pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x : E) (y : E) h

lemma projection_sum (K : Submodule 𝕜 E) [CompleteSpace K] (x : E) :
    (K.orthogonalProjection x : E) + (Kᗮ.orthogonalProjection x : E) = x := by
  change K.starProjection x + Kᗮ.starProjection x = x
  rw [Submodule.starProjection_orthogonal]
  simp

lemma dilationLM_norm (f : K ≃ₗᵢ[𝕜] L) (z : HilbertPair E E) :
    ‖dilationLM f z‖ = ‖z‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2,
    dilationLM_fst, dilationLM_snd, orthogonal_sum_norm_sq, orthogonal_sum_norm_sq,
    f.norm_map, f.symm.norm_map,
    proj_norm_sq (K := K) z.fst, proj_norm_sq (K := L) z.snd]
  ring

lemma dilationLM_inverse (f : K ≃ₗᵢ[𝕜] L) (z : HilbertPair E E) :
    dilationLM f.symm (dilationLM f z) = z := by
  apply (WithLp.equiv 2 (E × E)).injective
  apply Prod.ext
  · change (dilationLM f.symm (dilationLM f z)).fst = z.fst
    simp only [dilationLM_fst, dilationLM_snd, map_add,
      proj_K_of_mem, proj_K_of_mem_orthogonal, proj_Korth_of_mem_K,
      proj_Korth_of_mem, add_zero, zero_add, map_zero,
      LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_symm]
    exact projection_sum K z.fst
  · change (dilationLM f.symm (dilationLM f z)).snd = z.snd
    simp only [dilationLM_fst, dilationLM_snd, map_add,
      proj_K_of_mem, proj_K_of_mem_orthogonal, proj_Korth_of_mem_K,
      proj_Korth_of_mem, add_zero, zero_add, map_zero,
      LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.symm_symm]
    exact projection_sum L z.snd

/-- A genuine unitary on two copies, with an explicit inverse. -/
def dilation (f : K ≃ₗᵢ[𝕜] L) : HilbertPair E E ≃ₗᵢ[𝕜] HilbertPair E E where
  toLinearEquiv :=
    { toLinearMap := dilationLM f
      invFun := dilationLM f.symm
      left_inv := dilationLM_inverse f
      right_inv := dilationLM_inverse f.symm }
  norm_map' := dilationLM_norm f

@[simp] theorem dilation_on_subspace (f : K ≃ₗᵢ[𝕜] L) (x : K) :
    dilation f (WithLp.toLp 2 ((x : E), (0 : E))) =
      WithLp.toLp 2 ((f x : E), (0 : E)) := by
  apply (WithLp.equiv 2 (E × E)).injective
  change ((dilationLM f _).fst, (dilationLM f _).snd) = _
  simp [proj_K_of_mem, proj_Korth_of_mem_K]

end ELV.Stabilize

namespace ELV.Gram
variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-- Stabilized Gram realization with a second ambient copy. The original
family index remains arbitrary, including uncountable families. -/
def doubleUnitary {a b : ι → V} (h : EqualGram a b) :
    Stabilize.HilbertPair V V ≃ₗᵢ[ℂ] Stabilize.HilbertPair V V :=
  Stabilize.dilation (cspanEquiv h)

theorem doubleUnitary_apply {a b : ι → V} (h : EqualGram a b) (x : ι) :
    doubleUnitary h (WithLp.toLp 2 (a x, (0 : V))) =
      WithLp.toLp 2 (b x, (0 : V)) := by
  have hx : a x ∈ cspan a := Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self x))
  simpa [doubleUnitary, cspanEquiv_apply] using
    Stabilize.dilation_on_subspace (cspanEquiv h) (⟨a x, hx⟩ : cspan a)

end ELV.Gram
