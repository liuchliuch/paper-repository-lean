import Paper28.FiberProjection
import Paper28.RectifiableCalculusInput
import Mathlib.Order.Filter.Finite

/-! Identification of the actual approximate differential of every finite
shadow on all coordinate strata, derived from the generic published calculus
laws. There is no assumed shadow derivative, stratum rule or Jacobian bound. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open WithLp MeasureTheory
universe u v
variable {ι κ : Type u} [Fintype ι] [Fintype κ] [DecidableEq κ]

def coordinateMask (s : Finset κ) : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ :=
  (show EuclideanSpace ℝ κ →ₗ[ℝ] EuclideanSpace ℝ κ from
    { toFun := fun z => toLp 2 fun b => if b ∈ s then z b else 0
      map_add' := by
        intro z w
        ext b
        by_cases hb : b ∈ s <;> simp [hb]
      map_smul' := by
        intro a z
        ext b
        by_cases hb : b ∈ s <;> simp [hb] }).toContinuousLinearMap

def maskedShadow (f : ι → κ) (s : Finset κ) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ κ :=
  coordinateMask s (finiteShadow f x)

def maskedShadowDerivative (f : ι → κ) (s : Finset κ) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun b => if b ∈ s then branchNormDerivative f x b else 0)

theorem maskedShadowDerivative_apply (f : ι → κ) (s : Finset κ)
    (x h : EuclideanSpace ℝ ι) (b : κ) :
    maskedShadowDerivative f s x h b = if b ∈ s then shadowDifferential f x h b else 0 := by
  by_cases hb : b ∈ s
  · change (if b ∈ s then branchNormDerivative f x b else 0) h = _
    rw [if_pos hb, if_pos hb, branchNormDerivative_apply]
  · change (if b ∈ s then branchNormDerivative f x b else 0) h = _
    simp [hb]

/-- A fixed active-branch mask is smooth whenever its retained branch
norms are nonzero. The derivative is assembled from actual norm derivatives. -/
theorem hasFDerivAt_maskedShadow (f : ι → κ) (s : Finset κ) (x : EuclideanSpace ℝ ι)
    (hx : ∀ b ∈ s, finiteShadow f x b ≠ 0) :
    HasFDerivAt (maskedShadow f s) (maskedShadowDerivative f s x) x := by
  have hpi : HasFDerivAt
      (fun y : EuclideanSpace ℝ ι => fun b : κ => if b ∈ s then finiteShadow f y b else 0)
      (ContinuousLinearMap.pi fun b => if b ∈ s then branchNormDerivative f x b else 0) x := by
    apply hasFDerivAt_pi.mpr
    intro b
    by_cases hb : b ∈ s
    · simpa only [if_pos hb] using hasFDerivAt_branchNorm f x b (hx b hb)
    · simpa only [if_neg hb] using hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : κ => ℝ)).symm.toContinuousLinearMap.hasFDerivAt.comp x hpi

theorem finiteShadow_hasLipschitzConstant (f : ι → κ) : HasLipschitzConstant (finiteShadow f) := by
  refine ⟨1, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  simpa using finiteShadow_dist f x y

theorem maskedShadow_hasLipschitzConstant (f : ι → κ) (s : Finset κ) :
    HasLipschitzConstant (maskedShadow f s) := by
  obtain ⟨K,hK⟩ := finiteShadow_hasLipschitzConstant f
  exact ⟨‖coordinateMask s‖₊ * K, (coordinateMask s).lipschitz.comp hK⟩

theorem maskedShadow_eq (f : ι → κ) (s : Finset κ) (x : EuclideanSpace ℝ ι)
    (hzero : ∀ b, b ∉ s → finiteShadow f x b = 0) : maskedShadow f s x = finiteShadow f x := by
  ext b
  change (if b ∈ s then finiteShadow f x b else 0) = finiteShadow f x b
  by_cases hb : b ∈ s
  · rw [if_pos hb]
  · rw [if_neg hb, hzero b hb]

theorem maskedShadowDerivative_eq (f : ι → κ) (s : Finset κ) (x h : EuclideanSpace ℝ ι)
    (hzero : ∀ b, b ∉ s → finiteShadow f x b = 0) :
    maskedShadowDerivative f s x h = shadowDifferential f x h := by
  ext b
  rw [maskedShadowDerivative_apply]
  by_cases hb : b ∈ s
  · rw [if_pos hb]
  · rw [if_neg hb, shadowDifferential_zero_coordinate f x h b (hzero b hb)]

variable [MeasurableSpace (EuclideanSpace ℝ ι)]
variable (I : RectifiableSphereCalculusInput.{u,v} (EuclideanSpace ℝ ι))

/-- The original approximate tangential differential of the finite shadow
is the explicit canonical differential almost everywhere, including all zero
branches. Finite locality across the actual active masks proves the assertion. -/
theorem finiteShadow_approx_differential_ae (f : ι → κ) {n : ℕ} (C : I.Current n) :
    ∀ᵐ x ∂I.massMeasure C, ∀ h : I.plane C x,
      I.approxDifferential (finiteShadow f) C x h = shadowDifferential f x h.val := by
  have hs := Filter.eventually_all.mpr (fun s : Finset κ =>
    I.smooth_ae (maskedShadow f s) (maskedShadow_hasLipschitzConstant f s) C)
  have hl := Filter.eventually_all.mpr (fun s : Finset κ =>
    I.locality_ae (finiteShadow f) (maskedShadow f s)
      (finiteShadow_hasLipschitzConstant f) (maskedShadow_hasLipschitzConstant f s) C)
  filter_upwards [hs,hl] with x hSmooth hLocal
  let s := Finset.univ.filter (fun b => finiteShadow f x b ≠ 0)
  have hactive : ∀ b ∈ s, finiteShadow f x b ≠ 0 := fun b hb => (Finset.mem_filter.mp hb).2
  have hzero : ∀ b, b ∉ s → finiteShadow f x b = 0 := by
    intro b hb
    by_contra hn
    exact hb (Finset.mem_filter.mpr ⟨Finset.mem_univ b, hn⟩)
  intro h
  calc
    _ = I.approxDifferential (maskedShadow f s) C x h :=
      hLocal s (maskedShadow_eq f s x hzero).symm h
    _ = maskedShadowDerivative f s x h.val :=
      hSmooth s (maskedShadowDerivative f s x) (hasFDerivAt_maskedShadow f s x hactive) h
    _ = _ := maskedShadowDerivative_eq f s x h.val hzero

end Paper28
