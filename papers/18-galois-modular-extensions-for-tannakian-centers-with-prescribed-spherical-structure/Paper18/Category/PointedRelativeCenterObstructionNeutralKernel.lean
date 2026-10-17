import Paper18.Category.PointedRelativeCenterObstructionNeutralRealization
import Paper18.Category.PointedRelativeCenterObstructionKernelMonoidal
import Paper18.Category.PointedRelativeCenterObstructionNeutralLinear
import Paper18.Category.DrinfeldEquivalenceMapEquivalence
import Paper18.Category.DrinfeldEquivalenceMapLinear

/-! # The actual neutral component is the actual twisted-kernel center -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling QuasiFusion
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G]
  (p : Γ →* G) (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
  (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))

namespace NeutralComponent
instance realization_additive : (realization p ψ ω hψ).Additive where
  map_add := by intros; apply Center.Hom.ext; rfl
instance realization_linear : (realization p ψ ω hψ).Linear ℂ where
  map_smul := by intros; apply Center.Hom.ext; rfl

/-- The actual neutral homogeneous relative-center component is mapped
by its actual half-braiding realization and actual kernel-fiber restriction. -/
def toKernelCenter : NeutralComponent p ψ ω hψ ⥤
    Center (CocycleVec (kernelCocycleOfPrimitive p ψ ω hψ)) :=
  realization p ψ ω hψ ⋙ DrinfeldEquivalence.map (kernelTwistedRestriction p ψ ω hψ)

instance toKernelCenter_monoidal : (toKernelCenter p ψ ω hψ).Monoidal :=
  inferInstanceAs (realization p ψ ω hψ ⋙
    DrinfeldEquivalence.map (kernelTwistedRestriction p ψ ω hψ)).Monoidal
instance toKernelCenter_braided : (toKernelCenter p ψ ω hψ).Braided :=
  inferInstanceAs (realization p ψ ω hψ ⋙
    DrinfeldEquivalence.map (kernelTwistedRestriction p ψ ω hψ)).Braided
instance toKernelCenter_isEquivalence : (toKernelCenter p ψ ω hψ).IsEquivalence :=
  inferInstanceAs (realization p ψ ω hψ ⋙
    DrinfeldEquivalence.map (kernelTwistedRestriction p ψ ω hψ)).IsEquivalence
instance toKernelCenter_additive : (toKernelCenter p ψ ω hψ).Additive :=
  inferInstanceAs (realization p ψ ω hψ ⋙
    DrinfeldEquivalence.map (kernelTwistedRestriction p ψ ω hψ)).Additive
instance toKernelCenter_linear : (toKernelCenter p ψ ω hψ).Linear ℂ :=
  inferInstanceAs ((realization p ψ ω hψ ⋙
    DrinfeldEquivalence.map (kernelTwistedRestriction p ψ ω hψ)).Linear ℂ)

/-- A genuine complex-linear braided tensor equivalence with the actual
Drinfeld center of the actual restricted cocycle category. -/
def kernelCenterEquivalence : NeutralComponent p ψ ω hψ ≌
    Center (CocycleVec (kernelCocycleOfPrimitive p ψ ω hψ)) :=
  (toKernelCenter p ψ ω hψ).asEquivalence

end NeutralComponent
end Paper18.Category.PointedRelativeCenterObstruction
