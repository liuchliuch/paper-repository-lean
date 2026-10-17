import Paper18.Category.BimoduleRelativeTensorFunctorTransformation

/-! # Actual relative tensor functor composition and unit comparisons -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {R S T : D} [MonObj R] [MonObj S] [MonObj T]

/-- The actual associator of relative tensor supplies the actual
composition comparison on every left module. -/
def tensorCompositionComponent (P : Native R S) (Q : Native S T) (N : Mod_ D T) :
    (tensorFunctor (tensor P Q)).obj N ≅ (tensorFunctor P).obj ((tensorFunctor Q).obj N) where
  hom := (associator P Q (moduleAsNative N)).hom.hom
  inv := (associator P Q (moduleAsNative N)).inv.hom
  hom_inv_id := congrArg Mod_.Hom.hom (associator P Q (moduleAsNative N)).hom_inv_id
  inv_hom_id := congrArg Mod_.Hom.hom (associator P Q (moduleAsNative N)).inv_hom_id

/-- Actual relative tensor reverses the order in mathlib's endofunctor
composition convention. -/
def tensorCompositionIso (P : Native R S) (Q : Native S T) :
    tensorFunctor (tensor P Q) ≅ tensorFunctor Q ⋙ tensorFunctor P :=
  NatIso.ofComponents (tensorCompositionComponent P Q) (fun {N N'} f => by
    letI := nativeBicategory (D := D)
    exact congrArg Mod_.Hom.hom
      (Bicategory.associator_naturality_right
        (a := Mon.mk R) (b := Mon.mk S) (c := Mon.mk T) (d := Mon.mk (𝟙_ D))
        P Q (moduleAsNativeFunctor.map f)))

@[reassoc]
lemma moduleπ_composition (P : Native R S) (Q : Native S T) (N : Mod_ D T) :
    π P Q ▷ N.X ≫ moduleπ (tensor P Q) N ≫ ((tensorCompositionIso P Q).hom.app N).hom =
      (α_ P.X.X Q.X.X N.X).hom ≫ P.X.X ◁ moduleπ Q N ≫
        moduleπ P ((tensorFunctor Q).obj N) := by
  exact π_associator P Q (moduleAsNative N)

/-- The regular bimodule acts by the actual identity module functor. -/
def tensorUnitComponent (R : D) [MonObj R] (N : Mod_ D R) :
    (tensorFunctor (regular R)).obj N ≅ N where
  hom := (leftUnitor (moduleAsNative N)).hom.hom
  inv := (leftUnitor (moduleAsNative N)).inv.hom
  hom_inv_id := congrArg Mod_.Hom.hom (leftUnitor (moduleAsNative N)).hom_inv_id
  inv_hom_id := congrArg Mod_.Hom.hom (leftUnitor (moduleAsNative N)).inv_hom_id

def tensorUnitIso (R : D) [MonObj R] : tensorFunctor (regular R) ≅ 𝟭 (Mod_ D R) :=
  NatIso.ofComponents (tensorUnitComponent R) (fun {N N'} f => by
    letI := nativeBicategory (D := D)
    exact congrArg Mod_.Hom.hom (Bicategory.leftUnitor_naturality
      (a := Mon.mk R) (b := Mon.mk (𝟙_ D)) (moduleAsNativeFunctor.map f)))

@[reassoc (attr := simp)]
lemma moduleπ_unit (R : D) [MonObj R] (N : Mod_ D R) :
    moduleπ (regular R) N ≫ ((tensorUnitIso R).hom.app N).hom = γ[R,N.X] :=
  π_leftUnitor (moduleAsNative N)

end Paper18.Category.BimoduleRelativeTensor
