import Paper18.Category.GraphPicardCentralCharacter
import Paper18.Category.ModuleComponentAction
import Paper18.Category.SeparableModulesSemisimple

/-! # The actual central algebra character on an actual simple orbit

The character on the genuine full component is obtained by restricting
the actual algebra action. Its module naturality, unit and multiplication
are reflected by the actual full component inclusion.
-/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.GraphPicard
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  (A : Center D) [MonObj A] [IsCommMonObj A]
local instance componentCharacterUnderlyingMonObj : MonObj A.1 :=
  Functor.monObjObj (F := Center.forget D) A
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w} [Fintype κ] (SM : FiniteSemisimpleSkeleton (Mod_ D A.1) κ) (i : κ)
local notation "Comp" => ModuleComponent.Component (C := Dᴹᵒᵖ) SM i

/-- The genuine central action restricts to the actual simple component. -/
def componentActionCounit :
    ModuleAlphaInduction.centralFunctor (M := Comp) (centerOpposite.obj A) ⟶ 𝟭 Comp where
  app m := centralRightActionHom A m.obj
  naturality {m n} f := (centralActionCounit A).naturality (show m.obj ⟶ n.obj from f)

instance componentActionCounit_moduleNatural :
    ModuleFunctor.IsModuleNatural Dᴹᵒᵖ (componentActionCounit A SM i) where
  lineator X m := by
    exact ModuleFunctor.IsModuleNatural.lineator (C := Dᴹᵒᵖ)
      (τ := centralActionCounit A) X m.obj

/-- The actual central character inside the actual component endofunctors. -/
def componentCentralCharacter : (rightCentralAction D Comp).obj A ⟶
    𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ Comp) :=
  ⟨componentActionCounit A SM i,
    show ModuleFunctor.IsModuleNatural Dᴹᵒᵖ (componentActionCounit A SM i) from inferInstance⟩

/-- The actual restricted algebra unit acts as the actual identity. -/
lemma componentCentralCharacter_one :
    (rightCentralUnitIso D Comp).hom ≫ (rightCentralAction D Comp).map η[A] ≫
      componentCentralCharacter A SM i = 𝟙 _ := by
  apply ModuleFunctor.bundled_hom_ext
  ext m
  apply Mod_.Hom.ext
  exact congrArg (fun t => (t.val.app m.obj).hom) (centralCharacter_one A)

/-- The actual restricted algebra multiplication acts by the actual
composition tensor product of its actions. -/
lemma componentCentralCharacter_mul :
    (rightCentralTensorIso D Comp A A).hom ≫ (rightCentralAction D Comp).map μ[A] ≫
      componentCentralCharacter A SM i =
    (componentCentralCharacter A SM i ⊗ₘ componentCentralCharacter A SM i) ≫
      (λ_ (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ Comp))).hom := by
  apply ModuleFunctor.bundled_hom_ext
  ext m
  apply Mod_.Hom.ext
  exact congrArg (fun t => (t.val.app m.obj).hom) (centralCharacter_mul A)

/-- The restricted character is a genuine homomorphism from the genuine
mapped algebra, without an algebra-character premise. -/
def componentCentralCharacter_isMonHom :
    letI : MonObj ((rightCentralAction D Comp).obj A) :=
      Functor.monObjObj (F := rightCentralAction D Comp) A
    IsMonHom (componentCentralCharacter A SM i) := by
  letI : MonObj ((rightCentralAction D Comp).obj A) :=
    Functor.monObjObj (F := rightCentralAction D Comp) A
  refine { one_hom := ?_, mul_hom := ?_ }
  · change ((rightCentralUnitIso D Comp).hom ≫ (rightCentralAction D Comp).map η[A]) ≫
      componentCentralCharacter A SM i = 𝟙 _
    simpa only [Category.assoc] using componentCentralCharacter_one A SM i
  · change ((rightCentralTensorIso D Comp A A).hom ≫ (rightCentralAction D Comp).map μ[A]) ≫
      componentCentralCharacter A SM i =
        (componentCentralCharacter A SM i ⊗ₘ componentCentralCharacter A SM i) ≫
          (λ_ (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ Comp))).hom
    simpa only [Category.assoc] using componentCentralCharacter_mul A SM i

end Paper18.Category.GraphPicard
