import Paper28.EuclideanDeformationInput
import Paper28.DeformationMesh

/-! Paper-owned exact-cycle refinement of localized Euclidean approximation
in (15). The published inputs only give the two decompositions. Mesh choice,
integer polyhedral cycle closure, fillings, strict mass convergence and
shrinking support neighborhoods are all derived here. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Set
open scoped Topology
universe v

set_option maxHeartbeats 600000 in
theorem localized_euclidean_cycle_approximation {d : ℕ}
    (I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance)
    (S : EuclideanSimplexIntegrationInput d I) (E : EuclideanDeformationInput d I S)
    (k : ℕ) (T : I.Current (k+1)) (hCycle : I.boundary k T = 0) :
    ∃ Ti : ℕ → I.Current (k+1), ∃ Si : ℕ → I.Current (k+2), ∃ ρ : ℕ → ℝ,
      (∀ i, Ti i ∈ euclideanPolyhedralCurrents S (k+1)) ∧
      (∀ i, I.boundary k (Ti i) = 0) ∧
      (∀ i, T-Ti i = I.boundary (k+1) (Si i)) ∧
      Tendsto (fun i => I.mass (Ti i)) atTop (𝓝 (I.mass T)) ∧
      Tendsto (fun i => I.mass (Si i)) atTop (𝓝 0) ∧
      (∀ i, 0 < ρ i) ∧ Tendsto ρ atTop (𝓝 0) ∧
      (∀ i, I.support (Ti i) ∪ I.support (Si i) ⊆ Metric.thickening (ρ i) (I.support T)) := by
  let e : ℕ → ℝ := fun i => 1/((i : ℝ)+1)
  have he : ∀ i, 0 < e i := by intro i; dsimp [e]; positivity
  have he1 : ∀ i, e i ≤ 1 := by
    intro i
    apply (div_le_one (by positivity : 0 < (i : ℝ)+1)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) i]
  have heT : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose P R W hP hDecomp hMP hMRW hLoc using
    fun i => E.localized_approximation k T hCycle (e i) (e i) (he i) (he i)
  have hMR : ∀ i, I.mass (R i) ≤ e i := fun i => by
    linarith [hMRW i,I.mass_nonneg (W i)]
  have hMW : ∀ i, I.mass (W i) ≤ e i := fun i => by
    linarith [hMRW i,I.mass_nonneg (R i)]
  have hBoundaryR : ∀ i, I.boundary k (R i) ∈ euclideanPolyhedralCurrents S k := by
    intro i
    have hb := congrArg (I.boundary k) (hDecomp i)
    rw [map_add,map_add,hCycle,I.boundary_squared_zero,add_zero] at hb
    have hBR : I.boundary k (R i) = -I.boundary k (P i) := by
      apply eq_neg_iff_add_eq_zero.mpr
      simpa only [add_comm] using hb.symm
    rw [hBR]
    exact (euclideanPolyhedralCurrents S k).neg_mem (euclideanPolyhedral_boundary_mem S k (P i) (hP i))
  let m : ℕ → ℝ := fun i => I.mass (I.boundary k (R i))
  have hm : ∀ i, 0 ≤ m i := fun i => I.mass_nonneg _
  let a := deformationMesh m
  have ha : ∀ i, 0 < a i := deformationMesh_pos m hm
  have hae : ∀ i, a i ≤ e i := deformationMesh_le m hm
  have ha1 : ∀ i, a i ≤ 1 := fun i => (hae i).trans (he1 i)
  have ham : ∀ i, a i*m i ≤ e i := deformationMesh_mul_le m hm
  have haT : Tendsto a atTop (𝓝 0) := deformationMesh_tendsto_zero m hm
  choose P' U V hP' hU hR hMP' hMU hMV hLoc' using
    fun i => E.boundary_deformation k (R i) (hBoundaryR i) (a i) (ha i)
  let Ti : ℕ → I.Current (k+1) := fun i => P i+P' i+U i
  let Si : ℕ → I.Current (k+2) := fun i => W i+V i
  let ρ : ℕ → ℝ := fun i => E.constant*a i+e i
  have hPoly : ∀ i, Ti i ∈ euclideanPolyhedralCurrents S (k+1) := fun i =>
    (euclideanPolyhedralCurrents S (k+1)).add_mem
      ((euclideanPolyhedralCurrents S (k+1)).add_mem (hP i) (hP' i)) (hU i)
  have hHom : ∀ i, T-Ti i = I.boundary (k+1) (Si i) := by
    intro i
    dsimp [Ti,Si]
    rw [hDecomp i,hR i,map_add]
    abel
  have hCycles : ∀ i, I.boundary k (Ti i) = 0 := fun i =>
    current_cycle_of_homologous I k T (Ti i) hCycle ⟨Si i,hHom i⟩
  have hUpper : ∀ i, I.mass (Ti i) ≤ I.mass T+(1+2*E.constant)*e i := by
    intro i
    have hcR : E.constant*I.mass (R i) ≤ E.constant*e i :=
      mul_le_mul_of_nonneg_left (hMR i) E.constant_pos.le
    have hcU : E.constant*a i*I.mass (I.boundary k (R i)) ≤ E.constant*e i := by
      have h := mul_le_mul_of_nonneg_left (ham i) E.constant_pos.le
      simpa only [m,mul_assoc] using h
    have hmass := (I.mass_add_le (P i+P' i) (U i)).trans
      (add_le_add_right (I.mass_add_le (P i) (P' i)) (I.mass (U i)))
    dsimp [Ti]
    linarith [hMP i,hMP' i,hMU i]
  have hFillUpper : ∀ i, I.mass (Si i) ≤ (1+E.constant)*e i := by
    intro i
    have haR : a i*I.mass (R i) ≤ e i :=
      (mul_le_mul_of_nonneg_right (ha1 i) (I.mass_nonneg (R i))).trans (by simpa using hMR i)
    have hcV : E.constant*a i*I.mass (R i) ≤ E.constant*e i := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left haR E.constant_pos.le
    dsimp [Si]
    linarith [I.mass_add_le (W i) (V i),hMW i,hMV i]
  have hFillT : Tendsto (fun i => I.mass (Si i)) atTop (𝓝 0) := by
    apply squeeze_zero (fun i => I.mass_nonneg (Si i)) hFillUpper
    simpa using tendsto_const_nhds.mul heT
  have hErrT : Tendsto (fun i => (1+2*E.constant)*e i) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul heT
  have hMassT : Tendsto (fun i => I.mass (Ti i)) atTop (𝓝 (I.mass T)) := by
    apply Metric.tendsto_nhds.mpr
    intro δ hδ
    have hErr : ∀ᶠ i in atTop, (1+2*E.constant)*e i < δ/2 :=
      hErrT.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < δ/2))
    filter_upwards [hErr,I.mass_lower_semicontinuity (k+1) T Ti Si hHom hFillT (δ/2) (by positivity)] with i hi hlo
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> linarith [hUpper i]
  have hρ : ∀ i, 0 < ρ i := by
    intro i
    dsimp [ρ]
    exact add_pos (mul_pos E.constant_pos (ha i)) (he i)
  have hρT : Tendsto ρ atTop (𝓝 0) := by
    simpa [ρ] using (tendsto_const_nhds.mul haT).add heT
  refine ⟨Ti,Si,ρ,hPoly,hCycles,hHom,hMassT,hFillT,hρ,hρT,?_⟩
  intro i
  have hRLoc : I.support (R i) ⊆ Metric.thickening (e i) (I.support T) :=
    fun _ hx => hLoc i (Or.inl (Or.inr hx))
  have hNewLoc : I.support (P' i) ∪ I.support (U i) ∪ I.support (V i) ⊆
      Metric.thickening (ρ i) (I.support T) :=
    (hLoc' i).trans ((Metric.thickening_subset_of_subset _ hRLoc).trans
      (Metric.thickening_thickening_subset _ _ _))
  have hOldLoc : Metric.thickening (e i) (I.support T) ⊆ Metric.thickening (ρ i) (I.support T) :=
    Metric.thickening_mono (by dsimp [ρ]; nlinarith [E.constant_pos,ha i]) _
  intro x hx
  rcases hx with hx | hx
  · rcases I.support_add_subset (P i+P' i) (U i) hx with hx | hx
    · rcases I.support_add_subset (P i) (P' i) hx with hx | hx
      · exact hOldLoc (hLoc i (Or.inl (Or.inl hx)))
      · exact hNewLoc (Or.inl (Or.inl hx))
    · exact hNewLoc (Or.inl (Or.inr hx))
  · rcases I.support_add_subset (W i) (V i) hx with hx | hx
    · exact hOldLoc (hLoc i (Or.inr hx))
    · exact hNewLoc (Or.inr hx)

end Paper28
