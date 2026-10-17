import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Actual finite-coordinate orthogonal projections on the regular real
Hilbert space. The projections, contraction and finite approximation are
constructed using mathlib's native l2 space, without an approximation input. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter
open scoped Topology
variable {ι : Type*} [DecidableEq ι]

abbrev CoordinateHilbert (ι : Type*) := lp (fun _ : ι => ℝ) 2

def l2CoordinateProjection (F : Finset ι) : CoordinateHilbert ι →ₗ[ℝ] CoordinateHilbert ι where
  toFun u := ∑ i ∈ F, lp.single 2 i (u i)
  map_add' u v := by
    simp only [lp.coeFn_add, Pi.add_apply, lp.single_add, Finset.sum_add_distrib]
  map_smul' a u := by
    simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_smul, Finset.smul_sum, RingHom.id_apply]

theorem l2CoordinateProjection_norm_le (F : Finset ι) (u : CoordinateHilbert ι) :
    ‖l2CoordinateProjection F u‖ ≤ ‖u‖ := by
  have hsum := lp.norm_sum_single (p := 2) (by norm_num) (fun i => u i) F
  have hsub := lp.norm_sub_norm_compl_sub_single (p := 2) (by norm_num) u F
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hsum hsub
  change ‖∑ i ∈ F, lp.single 2 i (u i)‖ ≤ ‖u‖
  nlinarith [sq_nonneg ‖u - ∑ i ∈ F, lp.single 2 i (u i)‖,
    norm_nonneg u, norm_nonneg (∑ i ∈ F, lp.single 2 i (u i))]

def l2CoordinateProjectionCLM (F : Finset ι) : CoordinateHilbert ι →L[ℝ] CoordinateHilbert ι :=
  (l2CoordinateProjection F).mkContinuous 1 (fun u => by simpa using l2CoordinateProjection_norm_le F u)

@[simp] theorem l2CoordinateProjection_apply (F : Finset ι) (u : CoordinateHilbert ι) (i : ι) :
    l2CoordinateProjection F u i = if i ∈ F then u i else 0 := by
  simp [l2CoordinateProjection, lp.coeFn_sum, lp.single_apply, Finset.sum_pi_single]

theorem l2CoordinateProjection_error_mono (F E : Finset ι) (hFE : F ⊆ E) (u : CoordinateHilbert ι) :
    ‖l2CoordinateProjection E u - u‖ ≤ ‖l2CoordinateProjection F u - u‖ := by
  have hF := lp.norm_compl_sum_single (p := 2) (by norm_num) u F
  have hE := lp.norm_compl_sum_single (p := 2) (by norm_num) u E
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hF hE
  have hs : (∑ i ∈ F, ‖u i‖ ^ 2) ≤ ∑ i ∈ E, ‖u i‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hFE (fun _ _ _ => sq_nonneg _)
  change ‖(∑ i ∈ E, lp.single 2 i (u i)) - u‖ ≤ ‖(∑ i ∈ F, lp.single 2 i (u i)) - u‖
  rw [show ‖(∑ i ∈ E, lp.single 2 i (u i)) - u‖ = ‖u - ∑ i ∈ E, lp.single 2 i (u i)‖ from norm_sub_rev _ _,
    show ‖(∑ i ∈ F, lp.single 2 i (u i)) - u‖ = ‖u - ∑ i ∈ F, lp.single 2 i (u i)‖ from norm_sub_rev _ _]
  nlinarith [norm_nonneg (u - ∑ i ∈ E, lp.single 2 i (u i)),
    norm_nonneg (u - ∑ i ∈ F, lp.single 2 i (u i))]

/-- Native finite-support approximation at one actual l2 vector. -/
theorem exists_l2CoordinateProjection_close (u : CoordinateHilbert ι) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset ι, ‖l2CoordinateProjection F u - u‖ < ε := by
  have ht : Tendsto (fun F : Finset ι => l2CoordinateProjection F u) atTop (𝓝 u) :=
    lp.hasSum_single (by norm_num) u
  obtain ⟨F,hF⟩ := ((Metric.tendsto_nhds.mp ht) ε hε).exists
  exact ⟨F, by simpa only [dist_eq_norm] using hF⟩

end Paper28
