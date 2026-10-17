import Paper18.Category.BimoduleRelativeTensorSplitBarBasic
import Paper18.Category.BalancedModuleCategoryAdjunction

/-! # Actual absolute native bimodule bar presentations from separability -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u vE uE
namespace Paper18.Category.BimoduleRelativeTensor.SplitBar
open ModuleFunctor BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

abbrev outerResolution (P : Native A B) : Native A B :=
  (outerFree (A := A) (B := B)).obj P.X

def outerProjection (P : Native A B) : outerResolution P ⟶ P :=
  (outerFreeForgetAdjunction (A := A) (B := B)).counit.app P

def outerTop (P : Native A B) : outerResolution (outerResolution P) ⟶ outerResolution P :=
  (outerFreeForgetAdjunction (A := A) (B := B)).counit.app (outerResolution P)

def outerBottom (P : Native A B) : outerResolution (outerResolution P) ⟶ outerResolution P :=
  (outerFree (A := A) (B := B)).map
    ((Mod_.forget (D := Mod_ D A) (mop B)).map (outerProjection P))

def outerSection (SB : SeparableAlgebra B) (P : Native A B) : P ⟶ outerResolution P :=
  SeparableAction.sectionHom (separableMop SB) P

def outerLift (SB : SeparableAlgebra B) (P : Native A B) :
    outerResolution P ⟶ outerResolution (outerResolution P) :=
  (outerFree (A := A) (B := B)).map
    ((Mod_.forget (D := Mod_ D A) (mop B)).map (outerSection SB P))

@[reassoc (attr := simp)] lemma outerSection_projection (SB : SeparableAlgebra B)
    (P : Native A B) : outerSection SB P ≫ outerProjection P = 𝟙 P := by
  exact (SeparableAction.freeRetract (separableMop SB) P).retract

/-- The actual native bar presentation is split by the canonical actual
separability section. No universal property is supplied as input. -/
def outerSplitCoequalizer (SB : SeparableAlgebra B) (P : Native A B) :
    IsSplitCoequalizer (outerTop P) (outerBottom P) (outerProjection P) :=
  ofCounitSection (outerFreeForgetAdjunction (A := A) (B := B)) P
    (outerSection SB P) (outerSection_projection SB P)

@[reassoc (attr := simp)] lemma outerLift_bottom (SB : SeparableAlgebra B) (P : Native A B) :
    outerLift SB P ≫ outerBottom P = 𝟙 (outerResolution P) :=
  (outerSplitCoequalizer SB P).leftSection_bottom

@[reassoc (attr := simp)] lemma outerLift_top (SB : SeparableAlgebra B) (P : Native A B) :
    outerLift SB P ≫ outerTop P = outerProjection P ≫ outerSection SB P :=
  (outerSplitCoequalizer SB P).leftSection_top

@[reassoc] lemma outer_condition (P : Native A B) :
    outerTop P ≫ outerProjection P = outerBottom P ≫ outerProjection P := by
  simpa only [outerTop, outerBottom, outerProjection, Functor.comp_map] using
    ((outerFreeForgetAdjunction (A := A) (B := B)).counit.naturality
      ((outerFreeForgetAdjunction (A := A) (B := B)).counit.app P)).symm

/-- This is a genuine coequalizer in the actual native bimodule category. -/
def outerIsColimit (SB : SeparableAlgebra B) (P : Native A B) :
    IsColimit (outerSplitCoequalizer SB P).asCofork :=
  (outerSplitCoequalizer SB P).isCoequalizer

variable {E : Type uE} [Category.{vE} E] (H : Native A B ⥤ E)

/-- The actual bar presentation is absolute, so every actual functor
carries it to a genuine coequalizer. -/
def mappedOuterSplitCoequalizer (SB : SeparableAlgebra B) (P : Native A B) :
    IsSplitCoequalizer (H.map (outerTop P)) (H.map (outerBottom P))
      (H.map (outerProjection P)) :=
  (outerSplitCoequalizer SB P).map H

def mappedOuterIsColimit (SB : SeparableAlgebra B) (P : Native A B) :
    IsColimit (mappedOuterSplitCoequalizer H SB P).asCofork :=
  (mappedOuterSplitCoequalizer H SB P).isCoequalizer

end Paper18.Category.BimoduleRelativeTensor.SplitBar
