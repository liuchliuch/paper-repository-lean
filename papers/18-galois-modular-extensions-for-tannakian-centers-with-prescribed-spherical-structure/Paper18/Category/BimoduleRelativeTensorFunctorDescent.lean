import Paper18.Category.BimoduleRelativeTensorFunctorDescentBasic
import Paper18.Category.BimoduleRelativeTensorSplitBar
import Paper18.Category.BalancedModuleCategoryAlgebras

/-! # Actual recovery of every functor from its native free-object descent -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u vE uE
namespace Paper18.Category.BimoduleRelativeTensor.FunctorDescent
open BalancedModuleCategory SplitBar
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {E : Type uE} [Category.{vE} E] [HasCoequalizers E]
  (SB : SeparableAlgebra B) (K : Native A B ⥤ E)

abbrev outerRightModule : RightMonadModule (E := E) (outerMonad (A := A) (B := B)) :=
  rightModule (outerFreeForgetAdjunction (A := A) (B := B)) K

lemma outerProjection_hom (P : Native A B) : (outerProjection P).hom = γ[mop B,P.X] :=
  ModuleFunctor.SeparableAction.actionHom_hom P

/-- The actual split bar makes the displayed mapped coequalizer an
actual value of K, without a colimit-preservation premise on K. -/
def barIso (P : Native A B) :
    coequalizer (K.map (outerTop P)) (K.map (outerBottom P)) ≅ K.obj P :=
  (coequalizerIsCoequalizer (K.map (outerTop P)) (K.map (outerBottom P))).coconePointUniqueUpToIso
    (mappedOuterIsColimit K SB P)

@[reassoc (attr := simp)] lemma barIso_π (P : Native A B) :
    coequalizer.π (K.map (outerTop P)) (K.map (outerBottom P)) ≫
      (barIso SB K P).hom = K.map (outerProjection P) := by
  exact (coequalizerIsCoequalizer (K.map (outerTop P)) (K.map (outerBottom P))).comp_coconePointUniqueUpToIso_hom
    (mappedOuterIsColimit K SB P) WalkingParallelPair.one

/-- Coequalizer descent of the actual restricted right monad module
recovers each actual functor value. -/
def recoverySplitCoequalizer (P : Native A B) :
    IsSplitCoequalizer ((outerRightModule K).action.app P.X)
      ((outerRightModule K).toFunctor.map (toAlgebraObj P).a) (K.map (outerProjection P)) := by
  change IsSplitCoequalizer (K.map (outerTop P))
    (K.map ((outerFree (A := A) (B := B)).map γ[mop B,P.X])) (K.map (outerProjection P))
  rw [← outerProjection_hom P]
  exact mappedOuterSplitCoequalizer K SB P

def recoveryIso (P : Native A B) :
    (outerRightModule K).descent.obj ((nativeAlgebraEquivalence (A := A) (B := B)).functor.obj P) ≅
      K.obj P :=
  (coequalizerIsCoequalizer ((outerRightModule K).action.app P.X)
    ((outerRightModule K).toFunctor.map (toAlgebraObj P).a)).coconePointUniqueUpToIso
      (recoverySplitCoequalizer SB K P).isCoequalizer

@[reassoc (attr := simp)] lemma recoveryIso_π (P : Native A B) :
    (outerRightModule K).descentπ ((nativeAlgebraEquivalence (A := A) (B := B)).functor.obj P) ≫
        (recoveryIso SB K P).hom = K.map (outerProjection P) := by
  exact (coequalizerIsCoequalizer ((outerRightModule K).action.app P.X)
    ((outerRightModule K).toFunctor.map (toAlgebraObj P).a)).comp_coconePointUniqueUpToIso_hom
      (recoverySplitCoequalizer SB K P).isCoequalizer WalkingParallelPair.one

/-- Arbitrary actual functors are recovered naturally from the actual
native-algebra/coequalizer descent of their free-object restriction. -/
def recoveryNatIso :
    (nativeAlgebraEquivalence (A := A) (B := B)).functor ⋙ (outerRightModule K).descent ≅ K :=
  NatIso.ofComponents (recoveryIso SB K) (by
    intro P Q f
    apply (cancel_epi ((outerRightModule K).descentπ (toAlgebraObj P))).mp
    change (outerRightModule K).descentπ (toAlgebraObj P) ≫
        (outerRightModule K).descentMap (toAlgebras.map f) ≫ (recoveryIso SB K Q).hom =
      (outerRightModule K).descentπ (toAlgebraObj P) ≫ (recoveryIso SB K P).hom ≫ K.map f
    rw [RightMonadModule.descentπ_map_assoc]
    change K.map ((outerFree (A := A) (B := B)).map f.hom) ≫
        (outerRightModule K).descentπ (nativeAlgebraEquivalence.functor.obj Q) ≫
          (recoveryIso SB K Q).hom =
      (outerRightModule K).descentπ (nativeAlgebraEquivalence.functor.obj P) ≫
        (recoveryIso SB K P).hom ≫ K.map f
    rw [recoveryIso_π, recoveryIso_π_assoc, ← K.map_comp, ← K.map_comp]
    exact congrArg K.map
      ((outerFreeForgetAdjunction (A := A) (B := B)).counit.naturality f))

end Paper18.Category.BimoduleRelativeTensor.FunctorDescent
