import Paper18.Category.BalancedModuleCategoryBalancing
import Paper18.Category.ModuleFunctorSemisimpleBimodules

/-! # Actual separable split generators for the native balanced product

Every genuine native bimodule is an actual retract of the external tensor
of a free left module and the regular right module. The two splittings are
constructed from the given actual separability sections.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The actual free extension for the outer right action. -/
abbrev outerFree : Mod_ D A ⥤ BimoduleRelativeTensor.Native A B :=
  ModuleFunctor.SeparableAction.freeFunctor (A := mop B)

/-- The actual free bimodule with underlying object (A ⊗ X) ⊗ B. -/
abbrev doubleFree (X : D) : BimoduleRelativeTensor.Native A B :=
  outerFree.obj (InternalModule.free A X)

lemma doubleFree_rightAction (X : D) :
    γ[mop B,(doubleFree (A := A) (B := B) X).X].hom =
      (α_ (A ⊗ X) B B).hom ≫ (A ⊗ X) ◁ μ[B] :=
  congrArg Mod_.Hom.hom
    (ModuleFunctor.SeparableAction.free_smul (A := mop B) (InternalModule.free A X))

/-- The actual double-free native object is the actual external tensor
of the left free object and the right regular object. -/
def doubleFreeExternalIso (X : D) :
    doubleFree (A := A) (B := B) X ≅
      externalObj (InternalModule.free A X) (Mod_.regular (mop B)) := by
  let e : (BimoduleRelativeTensor.toBimod A B).obj (doubleFree X) ≅
      externalBimodObj (InternalModule.free A X) (Mod_.regular (mop B)) :=
    Bimod.isoOfIso (Iso.refl ((A ⊗ X) ⊗ B)) (by
      change γ[A,(doubleFree (A := A) (B := B) X).X.X] ≫ 𝟙 _ =
        A ◁ 𝟙 _ ≫ γ[A,(RelativeTensor.ambientTensor (InternalModule.free A X) B).X]
      simp only [comp_id, whiskerLeft_id, id_comp]) (by
      change γ[mop B,(doubleFree (A := A) (B := B) X).X].hom ≫ 𝟙 _ =
        𝟙 ((A ⊗ X) ⊗ B) ▷ B ≫
          (α_ (A ⊗ X) B B).hom ≫ (A ⊗ X) ◁ μ[B]
      rw [doubleFree_rightAction]
      simp only [comp_id, id_whiskerRight, id_comp])
  exact (BimoduleRelativeTensor.nativeRoundtripComponent A B (doubleFree X)).symm ≪≫
    (BimoduleRelativeTensor.fromBimod A B).mapIso e

/-- The inner actual free-module splitting, using only separability. -/
def leftFreeRetract (S : SeparableAlgebra A) (M : Mod_ D A) :
    Retract M (InternalModule.free A M.X) where
  i := S.moduleSectionHom M
  r := InternalModule.actionHom M
  retract := by
    apply Mod_.Hom.ext
    exact S.moduleSection_action M

/-- The two actual algebra sections give a retract of a double-free
object; this is constructed before any universal-product statement. -/
def doubleFreeRetract (SA : SeparableAlgebra A) (SB : SeparableAlgebra B)
    (P : BimoduleRelativeTensor.Native A B) :
    Retract P (doubleFree (A := A) (B := B) P.X.X) :=
  (ModuleFunctor.SeparableAction.freeRetract (ModuleFunctor.separableMop SB) P).trans
    ((leftFreeRetract SA P.X).map (outerFree (B := B)))

/-- Every actual native bimodule is an actual retract of the external
tensor of a left free module and the right regular module. -/
def externalFreeRetract (SA : SeparableAlgebra A) (SB : SeparableAlgebra B)
    (P : BimoduleRelativeTensor.Native A B) :
    Retract P (externalObj (InternalModule.free A P.X.X) (Mod_.regular (mop B))) :=
  (doubleFreeRetract SA SB P).trans (Retract.ofIso (doubleFreeExternalIso P.X.X))

theorem external_retract_dominant (SA : SeparableAlgebra A) (SB : SeparableAlgebra B)
    (P : BimoduleRelativeTensor.Native A B) :
    ∃ M N, Nonempty (Retract P ((external (A := A) (B := B)).obj (M, N))) :=
  ⟨InternalModule.free A P.X.X, Mod_.regular (mop B), ⟨externalFreeRetract SA SB P⟩⟩

end Paper18.Category.BalancedModuleCategory
