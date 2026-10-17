import Paper18.Category.QuasiFusionPivotal
import Paper18.Category.DrinfeldSemisimple
import Paper18.Category.DrinfeldGeneralNondegenerate
import Paper18.Category.DrinfeldPivotal
import Paper18.Category.DrinfeldDimension

/-! # The actual positive integral modular center of a cocycle category -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.QuasiFusion.CocycleVec
attribute [local instance 2000] RightRigidCategory.rightDual
variable {G : Type} [Group G] [Fintype G] (ψ : ThreeCocycle G)

/-- The actual positive pivotal structure supplies actual left rigid duals. -/
instance leftRigid : LeftRigidCategory (CocycleVec ψ) :=
  Drinfeld.pivotalLeftRigidCategory (pivotalStructure ψ)

/-- The actual finite complete simple index of the actual Drinfeld center. -/
abbrev CenterIndex := Drinfeld.CenterSimpleIndex (skeleton ψ) (pivotalStructure ψ)

/-- Finite semisimplicity of this actual center is a conclusion of actual
central induction and averaging, not an input to its construction. -/
def centerSkeleton : FiniteSemisimpleSkeleton (Center (CocycleVec ψ)) (CenterIndex ψ) :=
  Drinfeld.centerSkeleton (skeleton ψ) (pivotalStructure ψ)

/-- The actual center is integral because its actual tensor forgetful
functor preserves FP dimensions of every actual object. -/
theorem center_integral : (centerSkeleton ψ).Integral := by
  intro Z hZ
  obtain ⟨n, hn⟩ := (skeleton ψ).fpdim_integer (integral ψ) Z.1
  refine ⟨n, ?_⟩
  rw [← (centerSkeleton ψ).fpdim_map (skeleton ψ) (Center.forget (CocycleVec ψ)) Z]
  exact hn

/-- The actual center is Müger nondegenerate, including for a nonabelian
grading group and a nontrivial associator. -/
theorem center_nondegenerate : IsNondegenerate (C := Center (CocycleVec ψ)) :=
  Drinfeld.center_nondegenerate (skeleton ψ) (pivotalStructure ψ)

/-- Actual pivotal structure on the actual center, lifted through the
constructed central cups, caps, and half-braidings. -/
def centerPivotal : PivotalStructure (Center (CocycleVec ψ)) :=
  Drinfeld.centerPivotal (pivotalStructure ψ)

theorem centerPivotal_spherical : (centerPivotal ψ).Spherical :=
  Drinfeld.centerPivotal_spherical (pivotalStructure ψ) (pivotal_spherical ψ)

/-- Lifted pivotal dimension is the actual ambient scalar dimension. -/
lemma centerPivotal_rightDim (Z : Center (CocycleVec ψ)) :
    (centerPivotal ψ).rightDim Z = (pivotalStructure ψ).rightDim Z.1 := by
  have hs := unitScalarEquiv_spec (C := Center (CocycleVec ψ))
    ((centerPivotal ψ).rightDimension Z)
  have hh := congrArg (fun f : 𝟙_ (Center (CocycleVec ψ)) ⟶ 𝟙_ (Center (CocycleVec ψ)) => f.f) hs
  change (centerPivotal ψ).rightDim Z • 𝟙 (𝟙_ (CocycleVec ψ)) =
    ((centerPivotal ψ).rightDimension Z).f at hh
  rw [show ((centerPivotal ψ).rightDimension Z).f =
      (pivotalStructure ψ).rightDimension Z.1 from
        Drinfeld.centerPivotal_rightTrace (pivotalStructure ψ) (𝟙 Z)] at hh
  have he := congrArg (unitScalarEquiv (C := CocycleVec ψ)) hh
  simpa only [unitScalarEquiv_smul_id] using he

/-- The actual lifted pivotal structure is positive on every actual central
simple, by actual FP preservation and positivity of the actual FP character. -/
theorem centerPivotal_positive : (centerPivotal ψ).Positive := by
  intro Z hZ
  letI := hZ
  have hd : (centerPivotal ψ).rightDim Z = ((centerSkeleton ψ).fpdim Z : ℂ) := by
    rw [centerPivotal_rightDim,
      (pivotalStructure ψ).rightDim_eq_fpdim (skeleton ψ) (pivotal_positive ψ)]
    exact congrArg (fun x : ℝ => (x : ℂ))
      ((centerSkeleton ψ).fpdim_map (skeleton ψ) (Center.forget (CocycleVec ψ)) Z)
  rw [hd]
  constructor
  · have h := (centerSkeleton ψ).fpdim_simple_ge_one Z
    change 0 < (centerSkeleton ψ).fpdim Z
    linarith
  · rfl

/-- The actual dimension-square theorem computes this center's total FP
dimension from the finite group, with no center skeleton premise. -/
theorem center_totalFPdim :
    (centerSkeleton ψ).fusionBasis.totalFPdim = (Fintype.card G : ℝ) ^ 2 := by
  rw [Drinfeld.center_totalFPdim (skeleton ψ) (pivotalStructure ψ) (centerSkeleton ψ)]
  exact congrArg (fun x : ℝ => x ^ 2) (totalFPdim ψ)

end Paper18.Category.QuasiFusion.CocycleVec
