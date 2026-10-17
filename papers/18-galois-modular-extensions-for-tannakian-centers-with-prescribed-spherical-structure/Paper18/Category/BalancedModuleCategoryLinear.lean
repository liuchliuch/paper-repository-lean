import Paper18.Category.BalancedModuleCategoryStructure

/-! # Actual separate complex linearity of the external balanced tensor -/
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

def externalLeft (N : RightModules B) : Mod_ D A ⥤ BimoduleRelativeTensor.Native A B :=
  CategoryTheory.Prod.sectL _ N ⋙ external

def externalRight (M : Mod_ D A) : RightModules B ⥤ BimoduleRelativeTensor.Native A B :=
  CategoryTheory.Prod.sectR M _ ⋙ external

instance externalLeft_additive (N : RightModules B) :
    (externalLeft (A := A) N).Additive where
  map_add {M M'} f g := by
    apply Mod_.Hom.ext
    apply Mod_.Hom.ext
    change (f.hom + g.hom) ⊗ₘ 𝟙 (rightUnderlying N) =
      (f.hom ⊗ₘ 𝟙 (rightUnderlying N)) + (g.hom ⊗ₘ 𝟙 (rightUnderlying N))
    simp

instance externalLeft_linear (N : RightModules B) :
    (externalLeft (A := A) N).Linear ℂ where
  map_smul f z := by
    apply Mod_.Hom.ext
    apply Mod_.Hom.ext
    change (z • f.hom) ⊗ₘ 𝟙 (rightUnderlying N) = z • (f.hom ⊗ₘ 𝟙 (rightUnderlying N))
    simp

instance externalRight_additive (M : Mod_ D A) :
    (externalRight (B := B) M).Additive where
  map_add {N N'} f g := by
    apply Mod_.Hom.ext
    apply Mod_.Hom.ext
    change 𝟙 M.X ⊗ₘ (f.hom.unmop + g.hom.unmop) =
      (𝟙 M.X ⊗ₘ f.hom.unmop) + (𝟙 M.X ⊗ₘ g.hom.unmop)
    simp

instance externalRight_linear (M : Mod_ D A) :
    (externalRight (B := B) M).Linear ℂ where
  map_smul f z := by
    apply Mod_.Hom.ext
    apply Mod_.Hom.ext
    change 𝟙 M.X ⊗ₘ (z • f.hom.unmop) = z • (𝟙 M.X ⊗ₘ f.hom.unmop)
    simp

variable {E : Type uE} [Category.{vE} E] [Preadditive E] [Linear ℂ E]

/-- Bilinearity means separate actual additive and linear functor
structures. It is not joint linearity on a product-category Hom space. -/
class BalancedFunctor.IsBilinear (F : BalancedFunctor (A := A) (B := B) E) : Prop where
  left_additive : ∀ N, (CategoryTheory.Prod.sectL _ N ⋙ F.toFunctor).Additive
  left_linear : ∀ N, (CategoryTheory.Prod.sectL _ N ⋙ F.toFunctor).Linear ℂ
  right_additive : ∀ M, (CategoryTheory.Prod.sectR M _ ⋙ F.toFunctor).Additive
  right_linear : ∀ M, (CategoryTheory.Prod.sectR M _ ⋙ F.toFunctor).Linear ℂ

instance nativeBalanced_bilinear :
    BalancedFunctor.IsBilinear (nativeBalanced (A := A) (B := B)) where
  left_additive N := externalLeft_additive N
  left_linear N := externalLeft_linear N
  right_additive M := externalRight_additive M
  right_linear M := externalRight_linear M

end Paper18.Category.BalancedModuleCategory
