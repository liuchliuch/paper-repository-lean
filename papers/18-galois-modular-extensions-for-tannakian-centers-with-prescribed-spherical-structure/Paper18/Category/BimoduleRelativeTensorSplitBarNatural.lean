import Paper18.Category.BimoduleRelativeTensorSplitBar

/-! # The actual separable bar presentation is natural in native bimodules -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor.SplitBar
open ModuleFunctor BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

abbrev outerResolutionFunctor : Native A B ⥤ Native A B :=
  Mod_.forget (D := Mod_ D A) (mop B) ⋙ outerFree

/-- The actual native separability sections form an actual natural
transformation to the actual outer free resolution. -/
def outerSectionNat (SB : SeparableAlgebra B) :
    𝟭 (Native A B) ⟶ outerResolutionFunctor where
  app P := outerSection SB P
  naturality {P Q} f := by
    apply Mod_.Hom.ext
    exact SeparableAction.section_naturality (separableMop SB) f

@[reassoc (attr := simp)] lemma outerSectionNat_counit (SB : SeparableAlgebra B) :
    outerSectionNat (A := A) SB ≫
      (outerFreeForgetAdjunction (A := A) (B := B)).counit = 𝟙 (𝟭 (Native A B)) := by
  apply NatTrans.ext
  funext P
  exact outerSection_projection SB P

/-- The identity functor of actual native bimodules is the actual split
bar coequalizer in the actual functor category. -/
def outerNaturalSplitCoequalizer (SB : SeparableAlgebra B) :
    IsSplitCoequalizer
      (Functor.whiskerLeft outerResolutionFunctor
        (outerFreeForgetAdjunction (A := A) (B := B)).counit)
      (Functor.whiskerRight (outerFreeForgetAdjunction (A := A) (B := B)).counit
        outerResolutionFunctor)
      (outerFreeForgetAdjunction (A := A) (B := B)).counit :=
  ofCounitNaturalSection (outerFreeForgetAdjunction (A := A) (B := B))
    (outerSectionNat SB) (outerSectionNat_counit SB)

def outerNaturalIsColimit (SB : SeparableAlgebra B) :
    IsColimit (outerNaturalSplitCoequalizer (A := A) SB).asCofork :=
  (outerNaturalSplitCoequalizer SB).isCoequalizer

end Paper18.Category.BimoduleRelativeTensor.SplitBar
