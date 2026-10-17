import Paper28.StandardChartWeights
import Paper28.GlobalRelativeFixing
import Paper28.RelativeNearIsometry

/-! Assembly of the actual relative equivariant finite-projection construction.
All chart, cutoff, projection, active-error and sharp derivative data are
constructed here from compactness and actual finite-support relative pieces.
The final round/quotient metric Lipschitz passage is handled separately. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {G A : Type*} [Group G] [DecidableEq G] [Fintype A]
local instance (C : Finset (RegularSphere G)) :
    ∀ j : C, Fintype (regularStabilizer (standardChartCenters C j)) := standardChartStabilizers C

def standardGlobalProjection (C : Finset (RegularSphere G)) (F : C → Finset G) : CoordinateHilbert G → CoordinateHilbert G :=
  globalProjection (standardChartCenters C) (standardChartBumps C) F

def standardGlobalNormalizedProjection (C : Finset (RegularSphere G)) (F : C → Finset G) : CoordinateHilbert G → CoordinateHilbert G :=
  globalNormalizedProjection (standardChartCenters C) (standardChartBumps C) F

def standardGlobalHomotopy (C : Finset (RegularSphere G)) (F : C → Finset G) : ℝ → CoordinateHilbert G → CoordinateHilbert G :=
  globalProjectionHomotopy (standardChartCenters C) (standardChartBumps C) F

/-- The paper-owned construction, through the actual sharp differential and
relative homotopy statements. No deformation, approximation precision or
sharp estimate is supplied as a premise. -/
theorem exists_relative_deformation_construction
    (K : Set (RegularOrbitQuotient G)) (hK : IsCompact K)
    (P : A → Set (CoordinateHilbert G)) (hP : ∀ a, IsCompact (P a))
    (hUnit : ∀ a, ∀ u ∈ P a, ‖u‖ = 1) (S : A → Finset G)
    (hS : ∀ a, ∀ u ∈ P a, u ∈ coordinateSupportSubspace (S a))
    (η : ℝ) (hη : 0 < η) :
    ∃ C : Finset (RegularSphere G), ∃ F : C → Finset G,
      (∀ j, (1 : G) ∈ F j) ∧
      ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∃ U : Set (RegularOrbitQuotient G), IsOpen U ∧ K ⊆ U ∧
      ∀ u : RegularSphere G, regularQuotientMap u ∈ U →
        (0 < cutoffDenominator (standardChartCenters C) (standardChartBumps C) u.val) ∧
        (‖standardGlobalProjection C F u.val-u.val‖ ≤ ε) ∧
        (‖standardGlobalNormalizedProjection C F u.val‖ = 1) ∧
        (∃ D : CoordinateHilbert G →L[ℝ] CoordinateHilbert G,
          HasFDerivAt (standardGlobalNormalizedProjection C F) D u.val ∧ ∀ v, ‖D v‖ ≤ (1+η)*‖v‖) ∧
        (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          1-ε ≤ ‖(1-t) • u.val+t • standardGlobalProjection C F u.val‖) ∧
        (u.val ∈ liftedRelativePieces P →
          standardGlobalNormalizedProjection C F u.val = u.val ∧
            ∀ t, standardGlobalHomotopy C F t u.val = u.val) := by
  classical
  obtain ⟨C,hCover,C0,hC0,U0,hU0,hKU0,hBound⟩ := exists_standard_chart_weights K hK
  letI : ∀ j : C, Fintype (regularStabilizer j.val.val) := fun j => regularStabilizerFintype j.val
  obtain ⟨ε,hε,hε1,hSharp⟩ := exists_normalization_error C0 η hC0.le hη
  have hδ : 0 < ε/2 := by positivity
  choose F hF using fun j : C => exists_chart_relative_coordinates j.val K hK P hP hUnit S hS (ε/2) hδ
  have hApprox : ∀ j : C, ∀ u : RegularSphere G, regularQuotientMap u ∈ K → dist u j.val ≤ (1/8 : ℝ) →
      ‖l2CoordinateProjection (F j) u.val-u.val‖ < ε/2 := fun j => (hF j).2.2.1
  have hFix : ∀ j : C, ∀ a, ∀ v ∈ P a, ∀ γ : G,
      dist j.val.val (leftRegular γ v) < (1/8 : ℝ) →
      l2CoordinateProjection (F j) (leftRegular γ v) = leftRegular γ v := fun j => (hF j).2.2.2
  obtain ⟨U1,hU1,hKU1,hError⟩ := exists_projection_error_neighborhood (fun j : C => j.val)
    (standardChartBumps C) (by intro j; norm_num [standardChartBumps,regularStandardBump]) F K (ε/2) hδ hApprox
  refine ⟨C,F,(fun j => (hF j).1),ε,hε,hε1,U0∩U1,hU0.inter hU1,
    (fun q hq => ⟨hKU0 hq,hKU1 hq⟩),?_⟩
  intro u hu
  have hD : 0 < cutoffDenominator (standardChartCenters C) (standardChartBumps C) u.val := (hBound _ hu.1).1
  have hGrad : cutoffGradientSum (standardChartCenters C) (standardChartBumps C) u.val ≤ C0 := (hBound _ hu.1).2
  have hR : ∀ j : C, (standardChartBumps C j).rOut < (1/4 : ℝ) := by
    intro j
    norm_num [standardChartBumps,regularStandardBump]
  have hCenters : ∀ j : C, ‖standardChartCenters C j‖ = 1 := fun j => j.val.property
  have hErr : ∀ i : C×G, translatedCutoff (standardChartCenters C) (standardChartBumps C) i u.val ≠ 0 →
      ‖translatedProjection F i u.val-u.val‖ ≤ ε := by
    intro i hi
    have h := hError u hu.2 i hi
    linarith
  obtain ⟨s,hs⟩ := translatedCutoff_local_finite (standardChartCenters C) (standardChartBumps C) hR hCenters u.val u.property
  have he := globalProjection_error (standardChartCenters C) (standardChartBumps C) F u.val s
    (fun i hi => hs u.val (by simp) i hi) hD ε hε.le hErr
  have hn := globalNormalizedProjection_norm (standardChartCenters C) (standardChartBumps C) F hR hCenters
    u.val u.property hD ε hε.le hε1 hErr
  obtain ⟨D,hDactual,hDnorm⟩ := globalNormalizedProjection_sharp_derivative
    (standardChartCenters C) (standardChartBumps C) F hR hCenters u.val u.property hD ε C0 hε.le hε1 hGrad hErr
  refine ⟨hD,he,hn,⟨D,hDactual,?_⟩,?_,?_⟩
  · intro v
    exact (hDnorm v).trans (mul_le_mul_of_nonneg_right hSharp (norm_nonneg v))
  · intro t ht0 ht1
    exact globalProjectionHomotopy_denominator (standardChartCenters C) (standardChartBumps C) F
      u.val u.property ε hε.le he t ht0 ht1
  · intro hRel
    exact globalProjection_relative_fixed (fun j : C => j.val) (standardChartBumps C)
      (by intro j; norm_num [standardChartBumps,regularStandardBump]) F P hFix u.val u.property hRel hD

end Paper28
