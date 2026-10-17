import Paper28.CutoffDerivativeEquivariance
import Paper28.RegularSphereAction
import Mathlib.Analysis.Normed.Group.Bounded

/-! Cutoff sums descend to the actual orbit quotient. Compactness gives a
uniform derivative-sum constant on an open invariant neighborhood, before
any projection error or coordinate support is chosen. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter
open scoped Topology
variable {G J : Type*} [Group G] [DecidableEq G] [Fintype J]
variable (c : J → CoordinateHilbert G) [∀ j, Fintype (regularStabilizer (c j))]
variable (b : ∀ j, ContDiffBump (c j))

def quotientCutoffDenominator : RegularOrbitQuotient G → ℝ :=
  Quotient.lift (fun u : RegularSphere G => cutoffDenominator c b u.val) (by
    intro u v huv
    obtain ⟨γ,hγ⟩ := huv
    rw [← hγ]
    exact cutoffDenominator_equivariant c b γ v.val)

def quotientCutoffGradient : RegularOrbitQuotient G → ℝ :=
  Quotient.lift (fun u : RegularSphere G => cutoffGradientSum c b u.val) (by
    intro u v huv
    obtain ⟨γ,hγ⟩ := huv
    rw [← hγ]
    exact cutoffGradientSum_equivariant c b γ v.val)

@[simp] theorem quotientCutoffDenominator_apply (u : RegularSphere G) :
    quotientCutoffDenominator c b (regularQuotientMap u) = cutoffDenominator c b u.val := rfl

@[simp] theorem quotientCutoffGradient_apply (u : RegularSphere G) :
    quotientCutoffGradient c b (regularQuotientMap u) = cutoffGradientSum c b u.val := rfl

theorem quotientCutoffDenominator_continuousAt (hR : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hU : ∀ j, ‖c j‖ = 1) (u : RegularSphere G) :
    ContinuousAt (quotientCutoffDenominator c b) (regularQuotientMap u) := by
  have hf : ContinuousAt (fun v : RegularSphere G => cutoffDenominator c b v.val) u :=
    (cutoffDenominator_contDiffAt c b hR hU u.val u.property 0).continuousAt.comp
      continuous_subtype_val.continuousAt
  have ho : IsOpenQuotientMap (regularQuotientMap : RegularSphere G → RegularOrbitQuotient G) :=
    MulAction.isOpenQuotientMap_quotientMk
  exact (ho.continuousAt_comp_iff (g := quotientCutoffDenominator c b) (x := u)).mp hf

theorem quotientCutoffDenominator_continuous (hR : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hU : ∀ j, ‖c j‖ = 1) : Continuous (quotientCutoffDenominator c b) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  obtain ⟨u,rfl⟩ := Quotient.mk_surjective q
  exact quotientCutoffDenominator_continuousAt c b hR hU u

theorem quotientCutoffGradient_continuousAt (hR : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hU : ∀ j, ‖c j‖ = 1) (q : RegularOrbitQuotient G)
    (hD : 0 < quotientCutoffDenominator c b q) : ContinuousAt (quotientCutoffGradient c b) q := by
  obtain ⟨u,rfl⟩ := Quotient.mk_surjective q
  have hf : ContinuousAt (fun v : RegularSphere G => cutoffGradientSum c b v.val) u :=
    (cutoffGradientSum_continuousAt c b hR hU u.val u.property hD).comp continuous_subtype_val.continuousAt
  have ho : IsOpenQuotientMap (regularQuotientMap : RegularSphere G → RegularOrbitQuotient G) :=
    MulAction.isOpenQuotientMap_quotientMk
  exact (ho.continuousAt_comp_iff (g := quotientCutoffGradient c b) (x := u)).mp hf

/-- The source's finite C0 bound is constructed on an open neighborhood of
K, independently of every later finite-coordinate projection precision. -/
theorem exists_quotient_cutoff_bound (hR : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hU : ∀ j, ‖c j‖ = 1) (K : Set (RegularOrbitQuotient G)) (hK : IsCompact K)
    (hPositive : ∀ q ∈ K, 0 < quotientCutoffDenominator c b q) :
    ∃ C0 : ℝ, 0 < C0 ∧ ∃ U : Set (RegularOrbitQuotient G), IsOpen U ∧ K ⊆ U ∧
      ∀ q ∈ U, 0 < quotientCutoffDenominator c b q ∧ quotientCutoffGradient c b q ≤ C0 := by
  have hCont : ContinuousOn (quotientCutoffGradient c b) K := fun q hq =>
    (quotientCutoffGradient_continuousAt c b hR hU q (hPositive q hq)).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hCont
  let C0 := max C 0 + 1
  let U := {q | 0 < quotientCutoffDenominator c b q ∧ quotientCutoffGradient c b q < C0}
  have hC0 : 0 < C0 := by dsimp [C0]; linarith [le_max_right C 0]
  refine ⟨C0,hC0,U,?_,?_,?_⟩
  · apply isOpen_iff_mem_nhds.mpr
    intro q hq
    have hd := (quotientCutoffDenominator_continuous c b hR hU).continuousAt.eventually (Ioi_mem_nhds hq.1)
    have hg := (quotientCutoffGradient_continuousAt c b hR hU q hq.1).eventually (Iio_mem_nhds hq.2)
    exact hd.and hg
  · intro q hq
    refine ⟨hPositive q hq,?_⟩
    have hle := (le_abs_self (quotientCutoffGradient c b q)).trans (hC q hq)
    dsimp [C0]
    linarith [le_max_left C 0]
  · intro q hq
    exact ⟨hq.1,hq.2.le⟩

end Paper28
