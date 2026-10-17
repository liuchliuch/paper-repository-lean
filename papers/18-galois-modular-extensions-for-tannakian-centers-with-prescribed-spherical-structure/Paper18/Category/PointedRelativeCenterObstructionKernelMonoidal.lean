import Paper18.Category.PointedRelativeCenterObstructionKernelUnit
import Paper18.Category.PointedRelativeCenterObstructionKernelAssociativity
import Paper18.Category.QuasiFusionCategory

/-! # The actual twisted kernel restriction tensor equivalence -/
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling QuasiFusion
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G] (p : Γ →* G)
  (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
  (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
local notation "κ" => kernelCocycleOfPrimitive p ψ ω hψ

/-- Actual fiber restriction between the types recording the actual
neutral and kernel cocycle associators. -/
def kernelTwistedRestriction : NeutralTwistedVec.{0} p ψ ω hψ ⥤ CocycleVec κ := kernelRestriction p

/-- Every structure map is the actual restriction map on convolution
summands; associativity uses the actual restricted third cocycle. -/
def kernelRestrictionTwistedCoreMonoidal : (kernelTwistedRestriction p ψ ω hψ).CoreMonoidal where
  εIso := kernelUnitIso p
  μIso X Y := kernelTensorIso p X Y
  μIso_hom_natural_left {X Y} f X' := by
    simpa only [Functor.map_id, MonoidalCategory.tensorHom_id] using
      kernelTensorHom_naturality p f (𝟙 X')
  μIso_hom_natural_right {X Y} X' f := by
    simpa only [Functor.map_id, MonoidalCategory.id_tensorHom] using
      kernelTensorHom_naturality p (𝟙 X') f
  associativity X Y Z := kernelTensorHom_twisted_associativity p ψ ω hψ X Y Z
  left_unitality X := kernelTensorHom_left_unitality p X
  right_unitality X := kernelTensorHom_right_unitality p X

/-- Genuine monoidality of actual kernel restriction with both actual
twisted associators fixed by the category types. -/
instance kernelTwistedRestriction_monoidal : (kernelTwistedRestriction p ψ ω hψ).Monoidal :=
  Functor.CoreMonoidal.toMonoidal (kernelRestrictionTwistedCoreMonoidal p ψ ω hψ)
instance kernelTwistedRestriction_additive : (kernelTwistedRestriction p ψ ω hψ).Additive :=
  kernelRestriction_additive p
instance kernelTwistedRestriction_linear : (kernelTwistedRestriction p ψ ω hψ).Linear ℂ :=
  kernelRestriction_linear p
instance kernelTwistedRestriction_isEquivalence : (kernelTwistedRestriction p ψ ω hψ).IsEquivalence :=
  kernelRestriction_isEquivalence p

/-- The actual neutral graded-vector-space category is tensor equivalent
to the actual kernel cocycle category. -/
def kernelTwistedEquivalence : NeutralTwistedVec.{0} p ψ ω hψ ≌ CocycleVec κ :=
  (kernelTwistedRestriction p ψ ω hψ).asEquivalence

end Paper18.Category.PointedRelativeCenterObstruction
