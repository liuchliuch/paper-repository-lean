import Paper28.ShadowDifferential

/-! Orthogonal coordinate projections defining the actual branch norms,
and their smooth norm differentials off a zero branch. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open WithLp
open scoped InnerProductSpace
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

def fiberProjection (f : ι → κ) (b : κ) : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun u := toLp 2 fun i => if f i = b then u i else 0
  map_add' u v := by
    ext i
    by_cases h : f i = b <;> simp [h]
  map_smul' a u := by
    ext i
    by_cases h : f i = b <;> simp [h]

@[simp] theorem fiberProjection_apply (f : ι → κ) (b : κ) (u : EuclideanSpace ℝ ι) (i : ι) :
    fiberProjection f b u i = if f i = b then u i else 0 := rfl

theorem fiberProjection_norm_sq (f : ι → κ) (b : κ) (u : EuclideanSpace ℝ ι) :
    ‖fiberProjection f b u‖ ^ 2 = ∑ i ∈ Finset.univ.filter (fun i => f i = b), u i ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, fiberProjection_apply,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem fiberProjection_norm (f : ι → κ) (b : κ) (u : EuclideanSpace ℝ ι) :
    ‖fiberProjection f b u‖ = finiteShadow f u b := by
  have hsq := fiberProjection_norm_sq f b u
  rw [← finiteShadow_sq] at hsq
  nlinarith [norm_nonneg (fiberProjection f b u), finiteShadow_nonneg f u b]

theorem fiberProjection_inner (f : ι → κ) (b : κ) (u h : EuclideanSpace ℝ ι) :
    ⟪fiberProjection f b u, fiberProjection f b h⟫_ℝ =
      ∑ i ∈ Finset.univ.filter (fun i => f i = b), u i * h i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    fiberProjection_apply, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [mul_comm]

def fiberProjectionCLM (f : ι → κ) (b : κ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι := (fiberProjection f b).toContinuousLinearMap

def branchNormDerivative (f : ι → κ) (u : EuclideanSpace ℝ ι) (b : κ) :
    EuclideanSpace ℝ ι →L[ℝ] ℝ :=
  (hilbertNormDerivative (fiberProjection f b u)).comp (fiberProjectionCLM f b)

theorem branchNormDerivative_apply (f : ι → κ) (u h : EuclideanSpace ℝ ι) (b : κ) :
    branchNormDerivative f u b h = shadowDifferential f u h b := by
  change (1 / ‖fiberProjection f b u‖) *
    ⟪fiberProjection f b u, fiberProjection f b h⟫_ℝ = _
  rw [fiberProjection_inner, fiberProjection_norm, shadowDifferential_apply]
  ring

/-- Actual Frechet derivative of a single branch norm off its zero set. -/
theorem hasFDerivAt_branchNorm (f : ι → κ) (u : EuclideanSpace ℝ ι) (b : κ)
    (hu : finiteShadow f u b ≠ 0) :
    HasFDerivAt (fun x => finiteShadow f x b) (branchNormDerivative f u b) u := by
  have hp : fiberProjection f b u ≠ 0 := by
    intro h
    apply hu
    rw [← fiberProjection_norm, h, norm_zero]
  have hd := (hasFDerivAt_hilbertNorm (fiberProjection f b u) hp).comp u
    (fiberProjectionCLM f b).hasFDerivAt
  convert hd using 1
  · funext x
    exact (fiberProjection_norm f b x).symm

end Paper28
