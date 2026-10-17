import Paper18.Category.BalancedModuleCategoryAdjunction
import Paper18.Category.BalancedModuleCategoryStructure
import Paper18.Category.BalancedModuleCategoryFreeNaturality

/-! # A balanced functor supplies an actual natural right-monad-action map -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u vE uE
namespace Paper18.Category.BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

lemma outerMonad_map {M N : Mod_ D A} (f : M ⟶ N) :
    (outerMonad (A := A) (B := B)).map f = RelativeTensor.ambientTensorMap f B := rfl

lemma outerMonad_unit (M : Mod_ D A) :
    (outerMonad (A := A) (B := B)).η.app M =
      (InternalModule.ambientTensorUnit M).inv ≫ RelativeTensor.ambientTensorMapRight M η[B] := by
  apply Mod_.Hom.ext
  rw [outerMonad_unit_hom]
  rfl

lemma outerMonad_multiplication (M : Mod_ D A) :
    (outerMonad (A := A) (B := B)).μ.app M =
      (RelativeTensor.ambientTensorAssoc M B B).hom ≫ RelativeTensor.ambientTensorMapRight M μ[B] := by
  apply Mod_.Hom.ext
  rw [outerMonad_multiplication_hom]
  rfl

omit [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
lemma ambientRightFunctor_map_id_right {M N : Mod_ D A} (f : M ⟶ N) (X : D) :
    ambientRightFunctor.map (CategoryTheory.Prod.mkHom f (𝟙 X)) =
      RelativeTensor.ambientTensorMap f X := by
  apply Mod_.Hom.ext
  change f.hom ▷ X ≫ N.X ◁ 𝟙 X = f.hom ▷ X
  rw [whiskerLeft_id, comp_id]

variable {E : Type uE} [Category.{vE} E]
namespace BalancedFunctor
variable (F : BalancedFunctor (A := A) (B := B) E)

/-- Evaluate the balanced functor on the actual right regular module. -/
def regularSlice : Mod_ D A ⥤ E := CategoryTheory.Prod.sectL _ (Mod_.regular (mop B)) ⋙ F.toFunctor

/-- Move the acting right algebra through the actual balancing map and
then multiply its actual regular module. -/
def rightActionApp (M : Mod_ D A) :
    F.regularSlice.obj ((outerMonad (A := A) (B := B)).obj M) ⟶ F.regularSlice.obj M :=
  F.comparison.hom.app ((M, B), Mod_.regular (mop B)) ≫
    F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightRegularMultiply (B := B)))

/-- Naturality is derived from actual three-variable balancing naturality
and the actual product-category square for regular multiplication. -/
def rightActionMap : (outerMonad (A := A) (B := B)).toFunctor ⋙ F.regularSlice ⟶ F.regularSlice where
  app := F.rightActionApp
  naturality M N f := by
    have hn := F.comparison.hom.naturality (CategoryTheory.Prod.mkHom
      (CategoryTheory.Prod.mkHom f (𝟙 B)) (𝟙 (Mod_.regular (mop B))))
    change F.toFunctor.map (CategoryTheory.Prod.mkHom
        (ambientRightFunctor.map (CategoryTheory.Prod.mkHom f (𝟙 B))) (𝟙 (Mod_.regular (mop B)))) ≫
        F.comparison.hom.app ((N, B), Mod_.regular (mop B)) =
      F.comparison.hom.app ((M, B), Mod_.regular (mop B)) ≫
        F.toFunctor.map (CategoryTheory.Prod.mkHom f
          (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom (𝟙 B) (𝟙 (Mod_.regular (mop B)))))) at hn
    have hi : ambientLeftFunctor.map (CategoryTheory.Prod.mkHom (𝟙 B) (𝟙 (Mod_.regular (mop B)))) =
        𝟙 (rightAmbientTensor (Mod_.regular (mop B)) B) :=
      ambientLeftFunctor.map_id (B, Mod_.regular (mop B))
    rw [ambientRightFunctor_map_id_right, hi] at hn
    have hm :
        F.toFunctor.map (CategoryTheory.Prod.mkHom f (𝟙 (rightAmbientTensor (Mod_.regular (mop B)) B))) ≫
          F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 N) (rightRegularMultiply (B := B))) =
        F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightRegularMultiply (B := B))) ≫
          F.toFunctor.map (CategoryTheory.Prod.mkHom f (𝟙 (Mod_.regular (mop B)))) := by
      rw [← F.toFunctor.map_comp, ← F.toFunctor.map_comp]
      congr 1
      apply CategoryTheory.prod.hom_ext
      · change f ≫ 𝟙 N = 𝟙 M ≫ f
        rw [comp_id, id_comp]
      · change 𝟙 _ ≫ rightRegularMultiply = rightRegularMultiply ≫ 𝟙 _
        rw [id_comp, comp_id]
    change F.toFunctor.map (CategoryTheory.Prod.mkHom ((outerMonad (A := A) (B := B)).map f)
        (𝟙 (Mod_.regular (mop B)))) ≫ F.rightActionApp N =
      F.rightActionApp M ≫ F.toFunctor.map (CategoryTheory.Prod.mkHom f (𝟙 (Mod_.regular (mop B))))
    rw [outerMonad_map]
    exact vertical_square hn hm

end BalancedFunctor
end Paper18.Category.BalancedModuleCategory
