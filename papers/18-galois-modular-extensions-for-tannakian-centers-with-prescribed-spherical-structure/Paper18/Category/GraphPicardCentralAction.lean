import Paper18.Category.GraphPicardCentralBimodule
import Paper18.Category.GraphPicardCenterOpposite
import Paper18.Category.InternalModuleAmbientActionLinear
import Paper18.Category.ModuleAlphaInductionFunctor

/-! # The actual module-natural action of a central commutative algebra -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.GraphPicard
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  (A : Center D) [MonObj A] [IsCommMonObj A]
local instance centralActionUnderlyingMonObj : MonObj A.1 :=
  Functor.monObjObj (F := Center.forget D) A
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- Tensoring a module and then acting by the central algebra equals the
actual inverse half-braiding followed by the original right action. -/
lemma centralRightAction_tensor (M : Mod_ D A.1) (Y : D) :
    centralRightAction A (RelativeTensor.ambientTensor M Y) =
      (α_ M.X Y A.1).hom ≫ M.X ◁ (A.2.β Y).inv ≫
        (α_ M.X A.1 Y).inv ≫ centralRightAction A M ▷ Y := by
  unfold centralRightAction
  change (A.2.β (M.X ⊗ Y)).inv ≫
    (α_ A.1 M.X Y).inv ≫ γ[A.1,M.X] ▷ Y = _
  rw [Drinfeld.halfBraiding_inv_monoidal]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, comp_whiskerRight]

/-- The actual right action gives a genuine natural transformation from
the central action functor to the identity on internal modules. -/
def centralActionCounit :
    ModuleAlphaInduction.centralFunctor (M := Mod_ D A.1) (centerOpposite.obj A) ⟶
      𝟭 (Mod_ D A.1) where
  app M := centralRightActionHom A M
  naturality {M N} f := by
    apply Mod_.Hom.ext
    exact (centralRightAction_naturality A f).symm

@[simp] lemma centralActionCounit_app_hom (M : Mod_ D A.1) :
    ((centralActionCounit A).app M).hom = centralRightAction A M := rfl

/-- The actual commutative central algebra action is module-natural for
the genuine ambient right action, presented as a left opposite action. -/
instance centralActionCounit_moduleNatural :
    ModuleFunctor.IsModuleNatural Dᴹᵒᵖ (centralActionCounit A) where
  lineator X M := by
    rw [ModuleAlphaInduction.central_μ]
    dsimp only [ModuleAlphaInduction.centralLineator, Iso.trans_inv, Iso.symm_inv,
      Functor.mapIso_inv, MonoidalLeftAction.actionRight_map]
    apply Mod_.Hom.ext
    dsimp only [centerOpposite, oppositeHalfBraiding, InternalModule.ambientMonoidalOppositeLeftAction,
      MonoidalLeftAction.monoidalOppositeLeftAction, InternalModule.ambientRightAction,
      ModuleFunctor.identityActionLeftLinear, RelativeTensor.ambientTensorAssoc,
      RelativeTensor.ambientTensorMap, RelativeTensor.ambientTensorMapRight,
      centralActionCounit, centralRightActionHom]
    simp only [Iso.symm_inv, Iso.symm_hom, Functor.mapIso_inv,
      mopFunctor_map, Quiver.Hom.unmop_mop,
      Mod_.comp_hom', Mod_.id_hom']
    simp only [Category.assoc]
    change (α_ M.X A.1 X.unmop).hom ≫ M.X ◁ (A.2.β X.unmop).hom ≫
        (α_ M.X X.unmop A.1).inv ≫
        centralRightAction A (RelativeTensor.ambientTensor M X.unmop) =
      centralRightAction A M ▷ X.unmop ≫ 𝟙 _
    rw [centralRightAction_tensor]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc, ← whiskerLeft_comp_assoc,
      Iso.hom_inv_id, whiskerLeft_id, Category.id_comp, Category.comp_id]

/-- Every actual central map to the commutative algebra acts by an actual
module-natural transformation on all actual internal modules. -/
def centralCapTransformation {Z : Center D} (q : Z ⟶ A) :
    ModuleAlphaInduction.centralFunctor (M := Mod_ D A.1) (centerOpposite.obj Z) ⟶
      𝟭 (Mod_ D A.1) :=
  ModuleAlphaInduction.centralMap (centerOpposite.map q) ≫ centralActionCounit A

instance centralCapTransformation_moduleNatural {Z : Center D} (q : Z ⟶ A) :
    ModuleFunctor.IsModuleNatural Dᴹᵒᵖ (centralCapTransformation A q) := by
  unfold centralCapTransformation
  infer_instance

@[simp] lemma centralCapTransformation_app_hom {Z : Center D} (q : Z ⟶ A)
    (M : Mod_ D A.1) :
    ((centralCapTransformation A q).app M).hom =
      M.X ◁ q.f ≫ centralRightAction A M := rfl

end Paper18.Category.GraphPicard
