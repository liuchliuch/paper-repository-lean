import Paper28.ShadowComposition
import Paper28.NJacobian

/-! Canonical linear differential of a finite branch norm. At a zero
branch it is zero, agreeing with the derivative on its coordinate stratum.
All formulas below are derived from the actual finite fiber sums. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open WithLp
open scoped InnerProductSpace
variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
  [DecidableEq κ] [DecidableEq τ]

/-- The explicit norm derivative, including the zero-stratum convention. -/
def shadowDifferential (f : ι → κ) (u : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ κ where
  toFun h := toLp 2 fun b =>
    (∑ i ∈ Finset.univ.filter (fun i => f i = b), u i * h i) / finiteShadow f u b
  map_add' h k := by
    ext b
    simp [mul_add, Finset.sum_add_distrib, add_div]
  map_smul' a h := by
    ext b
    change (∑ i ∈ Finset.univ.filter (fun i => f i = b), u i * (a * h i)) /
        finiteShadow f u b =
      a * ((∑ i ∈ Finset.univ.filter (fun i => f i = b), u i * h i) / finiteShadow f u b)
    rw [← mul_div_assoc, Finset.mul_sum]
    apply congrArg (fun r : ℝ => r / finiteShadow f u b)
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem shadowDifferential_apply (f : ι → κ) (u h : EuclideanSpace ℝ ι) (b : κ) :
    shadowDifferential f u h b =
      (∑ i ∈ Finset.univ.filter (fun i => f i = b), u i * h i) / finiteShadow f u b := rfl

theorem shadow_branch_inner_zero (f : ι → κ) (u h : EuclideanSpace ℝ ι) (b : κ)
    (hb : finiteShadow f u b = 0) :
    (∑ i ∈ Finset.univ.filter (fun i => f i = b), u i * h i) = 0 := by
  have hs : (∑ i ∈ Finset.univ.filter (fun i => f i = b), u i ^ 2) = 0 := by
    rw [← finiteShadow_sq, hb, zero_pow (by decide)]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ.filter (fun i => f i = b)) (fun i => u i) (fun i => h i)
  rw [hs, zero_mul] at hc
  exact sq_eq_zero_iff.mp (le_antisymm hc (sq_nonneg _))

theorem shadowDifferential_radial (f : ι → κ) (u h : EuclideanSpace ℝ ι) (b : κ) :
    finiteShadow f u b * shadowDifferential f u h b =
      ∑ i ∈ Finset.univ.filter (fun i => f i = b), u i * h i := by
  rw [shadowDifferential_apply]
  by_cases hb : finiteShadow f u b = 0
  · rw [hb, zero_mul, shadow_branch_inner_zero f u h b hb]
  · exact mul_div_cancel₀ _ hb

/-- Exact derivative chain identity for coarsening branch partitions,
including zero fibers. -/
theorem shadowDifferential_comp (f : κ → τ) (g : ι → κ)
    (u h : EuclideanSpace ℝ ι) :
    shadowDifferential f (finiteShadow g u) (shadowDifferential g u h) =
      shadowDifferential (f ∘ g) u h := by
  ext c
  rw [shadowDifferential_apply, finiteShadow_comp, shadowDifferential_apply]
  congr 1
  simp_rw [shadowDifferential_radial]
  exact sum_composed_fibers f g (fun i => u i * h i) c

/-- Every canonical branch differential is a Hilbert contraction. -/
theorem shadowDifferential_norm_le (f : ι → κ) (u h : EuclideanSpace ℝ ι) :
    ‖shadowDifferential f u h‖ ≤ ‖h‖ := by
  have hcoord (b : κ) : (shadowDifferential f u h b) ^ 2 ≤
      ∑ i ∈ Finset.univ.filter (fun i => f i = b), h i ^ 2 := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ.filter (fun i => f i = b)) (fun i => u i) (fun i => h i)
    rw [← finiteShadow_sq] at hc
    by_cases hb : finiteShadow f u b = 0
    · rw [shadowDifferential_apply, hb, div_zero]
      simpa using (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ.filter (fun i => f i = b)) => sq_nonneg (h i)))
    · rw [shadowDifferential_apply, div_pow]
      exact (div_le_iff₀ (sq_pos_of_ne_zero hb)).mpr (by simpa [mul_comm] using hc)
  have hs : ‖shadowDifferential f u h‖ ^ 2 ≤ ‖h‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    calc
      _ ≤ ∑ b, ∑ i ∈ Finset.univ.filter (fun i => f i = b), h i ^ 2 :=
        Finset.sum_le_sum (fun b _ => hcoord b)
      _ = _ := Finset.sum_fiberwise Finset.univ f (fun i => h i ^ 2)
  nlinarith [norm_nonneg (shadowDifferential f u h), norm_nonneg h]

/-- The differential takes sphere tangent vectors to sphere tangent vectors. -/
theorem shadowDifferential_tangent (f : ι → κ) (u h : EuclideanSpace ℝ ι) :
    ⟪finiteShadow f u, shadowDifferential f u h⟫_ℝ = ⟪u,h⟫_ℝ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp_rw [mul_comm (shadowDifferential f u h _) (finiteShadow f u _), shadowDifferential_radial]
  simpa [mul_comm] using Finset.sum_fiberwise Finset.univ f (fun i => u i * h i)

/-- Image planes automatically satisfy every zero-coordinate stratum. -/
theorem shadowDifferential_zero_coordinate (f : ι → κ) (u h : EuclideanSpace ℝ ι)
    (b : κ) (hb : finiteShadow f u b = 0) : shadowDifferential f u h b = 0 := by
  rw [shadowDifferential_apply, hb, div_zero]

end Paper28
