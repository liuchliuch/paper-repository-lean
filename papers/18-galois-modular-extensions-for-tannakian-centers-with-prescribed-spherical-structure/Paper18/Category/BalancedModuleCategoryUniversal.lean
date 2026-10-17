import Paper18.Category.BalancedModuleCategoryCategory
import Mathlib.CategoryTheory.Equivalence

/-! # The genuine balanced module-category tensor universal property

The restriction functor is proved fully faithful and essentially
surjective by the actual split generators and coequalizer extension.
No universal-property or product-equivalence premise appears.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u vE uE
namespace Paper18.Category.BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {E : Type uE} [Category.{vE} E] [HasCoequalizers E]

/-- Every actual balanced functor is obtained by actual restriction. -/
theorem restrictionEssSurj (SB : SeparableAlgebra B) :
    (restriction (A := A) (B := B) (E := E)).EssSurj where
  mem_essImage F := ⟨F.extension, ⟨restrictionObjIso SB F⟩⟩

/-- Actual native (A,B)-bimodules represent the balanced product of
left A-modules, with their right ambient action, and right B-modules,
with their left ambient action. This is a constructed equivalence of
actual functor categories. -/
def balancedEquivalence (SA : SeparableAlgebra A) (SB : SeparableAlgebra B) :
    (BimoduleRelativeTensor.Native A B ⥤ E) ≌ BalancedFunctor (A := A) (B := B) E := by
  letI := (restrictionFullyFaithful (E := E) SA SB).full
  letI := (restrictionFullyFaithful (E := E) SA SB).faithful
  letI := restrictionEssSurj (A := A) (E := E) SB
  letI : (restriction (A := A) (B := B) (E := E)).IsEquivalence :=
    { full := (restrictionFullyFaithful (E := E) SA SB).full
      faithful := (restrictionFullyFaithful (E := E) SA SB).faithful
      essSurj := restrictionEssSurj (A := A) (E := E) SB }
  exact restriction.asEquivalence

end Paper18.Category.BalancedModuleCategory
