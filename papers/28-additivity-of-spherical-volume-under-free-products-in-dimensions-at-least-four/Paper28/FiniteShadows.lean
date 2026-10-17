import Paper28.NormFoldings

/-! Finite-coordinate branch norm maps. A map `branch : Edge → Branch`
encodes a partition of the edge midpoints; in Definition 2.2 it is the
branch determined by deletion of the chosen tree vertex. The norm and
contraction results here hold for every finite partition.
No tree Jacobian estimate is asserted in this file. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open WithLp
open scoped InnerProductSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- Norm folding along a finite partition, exactly the finite sum in (5). -/
def finiteShadow (branch : ι → κ) (u : EuclideanSpace ℝ ι) : EuclideanSpace ℝ κ :=
  toLp 2 fun b => Real.sqrt (∑ i ∈ Finset.univ.filter (fun i => branch i = b), u i ^ 2)

theorem finiteShadow_sq (branch : ι → κ) (u : EuclideanSpace ℝ ι) (b : κ) :
    finiteShadow branch u b ^ 2 =
      ∑ i ∈ Finset.univ.filter (fun i => branch i = b), u i ^ 2 := by
  apply Real.sq_sqrt
  exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem finiteShadow_norm (branch : ι → κ) (u : EuclideanSpace ℝ ι) :
    ‖finiteShadow branch u‖ = ‖u‖ := by
  have h : ‖finiteShadow branch u‖ ^ 2 = ‖u‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    simp_rw [finiteShadow_sq]
    exact Finset.sum_fiberwise Finset.univ branch (fun i => u i ^ 2)
  nlinarith [norm_nonneg (finiteShadow branch u), norm_nonneg u]

theorem finiteShadow_nonneg (branch : ι → κ) (u : EuclideanSpace ℝ ι) (b : κ) :
    0 ≤ finiteShadow branch u b := Real.sqrt_nonneg _

/-- Cauchy--Schwarz on one finite branch, preserving arbitrary signs of u,v. -/
theorem branch_inner_le (s : Finset ι) (u v : ι → ℝ) :
    ∑ i ∈ s, u i * v i ≤
      Real.sqrt (∑ i ∈ s, u i ^ 2) * Real.sqrt (∑ i ∈ s, v i ^ 2) := by
  have hu : 0 ≤ ∑ i ∈ s, u i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hv : 0 ≤ ∑ i ∈ s, v i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s u v
  have hprod := mul_nonneg (Real.sqrt_nonneg (∑ i ∈ s, u i ^ 2))
    (Real.sqrt_nonneg (∑ i ∈ s, v i ^ 2))
  nlinarith [Real.sq_sqrt hu, Real.sq_sqrt hv]

theorem finiteShadow_inner (branch : ι → κ) (u v : EuclideanSpace ℝ ι) :
    ⟪u, v⟫_ℝ ≤ ⟪finiteShadow branch u, finiteShadow branch v⟫_ℝ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [← Finset.sum_fiberwise Finset.univ branch (fun i => v i * u i)]
  apply Finset.sum_le_sum
  intro b _
  exact branch_inner_le _ v u

theorem finiteShadow_angular (branch : ι → κ) (u v : EuclideanSpace ℝ ι) :
    angular (finiteShadow branch u) (finiteShadow branch v) ≤ angular u v :=
  Real.arccos_le_arccos (finiteShadow_inner branch u v)

/-- The finite branch formula genuinely maps the unit sphere to the unit sphere. -/
def sphereFiniteShadow (branch : ι → κ)
    (u : {u : EuclideanSpace ℝ ι // ‖u‖ = 1}) :
    {v : EuclideanSpace ℝ κ // ‖v‖ = 1} :=
  ⟨finiteShadow branch u.val, (finiteShadow_norm branch u.val).trans u.property⟩

end Paper28
