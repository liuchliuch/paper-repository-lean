import Paper18.Category.BalancedModuleCategoryRightPresentation
import Paper18.Category.BalancedModuleCategorySplitTransport

/-! # Balancing identifies the actual external object's coequalizer diagram -/
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

lemma external_algebra_action (M : Mod_ D A) (N : RightModules B) :
    (toAlgebraObj (externalObj M N)).a =
      (RelativeTensor.ambientTensorAssoc M (rightUnderlying N) B).hom ≫
        RelativeTensor.ambientTensorMapRight M (rightAction N) := by
  apply Mod_.Hom.ext
  rfl

variable {E : Type uE} [Category.{vE} E]
namespace BalancedFunctor
variable (F : BalancedFunctor (A := A) (B := B) E)

/-- The regular slice resolves the second module by its actual free module. -/
def externalNodeIso (M : Mod_ D A) (N : RightModules B) :
    F.regularSlice.obj (toAlgebraObj (externalObj M N)).A ≅
      F.toFunctor.obj (M, rightResolution N) :=
  F.comparison.app ((M, rightUnderlying N), Mod_.regular (mop B))

/-- The corresponding actual isomorphism at the two-fold free term. -/
def externalSourceIso (M : Mod_ D A) (N : RightModules B) :
    F.regularSlice.obj ((outerMonad (A := A) (B := B)).obj
      (toAlgebraObj (externalObj M N)).A) ≅
      F.toFunctor.obj (M, rightResolution (rightResolution N)) :=
  F.toFunctor.mapIso ((RelativeTensor.ambientTensorAssoc M (rightUnderlying N) B).prod
    (Iso.refl (Mod_.regular (mop B)))) ≪≫
      F.comparison.app ((M, rightUnderlying N ⊗ B), Mod_.regular (mop B))

lemma external_bottom_square (M : Mod_ D A) (N : RightModules B) :
    F.regularSlice.map (toAlgebraObj (externalObj M N)).a ≫ (F.externalNodeIso M N).hom =
      (F.externalSourceIso M N).hom ≫
        F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightBottom N)) := by
  change F.toFunctor.map (CategoryTheory.Prod.mkHom (toAlgebraObj (externalObj M N)).a
      (𝟙 (Mod_.regular (mop B)))) ≫ F.comparison.hom.app
        ((M, rightUnderlying N), Mod_.regular (mop B)) = _
  rw [external_algebra_action]
  have hp : CategoryTheory.Prod.mkHom
      ((RelativeTensor.ambientTensorAssoc M (rightUnderlying N) B).hom ≫
        RelativeTensor.ambientTensorMapRight M (rightAction N)) (𝟙 (Mod_.regular (mop B))) =
      CategoryTheory.Prod.mkHom (RelativeTensor.ambientTensorAssoc M (rightUnderlying N) B).hom
        (𝟙 (Mod_.regular (mop B))) ≫
      CategoryTheory.Prod.mkHom (RelativeTensor.ambientTensorMapRight M (rightAction N))
        (𝟙 (Mod_.regular (mop B))) := by
    apply CategoryTheory.prod.hom_ext
    · rfl
    · exact (comp_id _).symm
  rw [hp, F.toFunctor.map_comp]
  have hn := F.comparison_naturality_ambient M (rightAction N) (Mod_.regular (mop B))
  change _ = (F.toFunctor.map (CategoryTheory.Prod.mkHom
    (RelativeTensor.ambientTensorAssoc M (rightUnderlying N) B).hom (𝟙 (Mod_.regular (mop B)))) ≫
      F.comparison.hom.app ((M, rightUnderlying N ⊗ B), Mod_.regular (mop B))) ≫ _
  rw [rightBottom_formula]
  simpa only [Category.assoc] using congrArg
    (fun f => F.toFunctor.map (CategoryTheory.Prod.mkHom
      (RelativeTensor.ambientTensorAssoc M (rightUnderlying N) B).hom
        (𝟙 (Mod_.regular (mop B)))) ≫ f) hn

lemma external_top_square (M : Mod_ D A) (N : RightModules B) :
    F.rightActionMap.app (toAlgebraObj (externalObj M N)).A ≫ (F.externalNodeIso M N).hom =
      (F.externalSourceIso M N).hom ≫
        F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightTop N)) := by
  let R := Mod_.regular (mop B)
  let n := rightUnderlying N
  have hn := F.comparison_naturality_right M n (rightRegularMultiply (B := B))
  have ha := F.assoc_condition M n B R
  have hm :
      F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightAmbientAssoc R n B).hom) ≫
        F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightTop N)) =
      F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M)
        (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom (𝟙 n) (rightRegularMultiply (B := B))))) := by
    rw [← F.toFunctor.map_comp]
    congr 1
    apply CategoryTheory.prod.hom_ext
    · exact comp_id _
    · change (rightAmbientAssoc R n B).hom ≫ rightTop N = _
      rw [rightTop_formula]
      exact Iso.hom_inv_id_assoc _ _
  change (F.comparison.hom.app ((RelativeTensor.ambientTensor M n, B), R) ≫
      F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 (RelativeTensor.ambientTensor M n))
        (rightRegularMultiply (B := B)))) ≫ F.comparison.hom.app ((M, n), R) =
    (F.toFunctor.map (CategoryTheory.Prod.mkHom (RelativeTensor.ambientTensorAssoc M n B).hom (𝟙 R)) ≫
      F.comparison.hom.app ((M, n ⊗ B), R)) ≫ _
  calc
    _ = F.comparison.hom.app ((RelativeTensor.ambientTensor M n, B), R) ≫
        F.comparison.hom.app ((M, n), rightAmbientTensor R B) ≫
          F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M)
            (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom (𝟙 n) (rightRegularMultiply (B := B))))) := by
      simpa only [Category.assoc] using congrArg
        (fun f => F.comparison.hom.app ((RelativeTensor.ambientTensor M n, B), R) ≫ f) hn
    _ = _ := by
      have hh := congrArg (fun f => f ≫ F.toFunctor.map
        (CategoryTheory.Prod.mkHom (𝟙 M) (rightTop N))) ha
      simpa only [Category.assoc, hm] using hh.symm

/-- The actual external coequalizer is split using the actual
separability section of the second input. -/
def externalSplitCoequalizer (SB : SeparableAlgebra B) (M : Mod_ D A) (N : RightModules B) :
    IsSplitCoequalizer
      (F.rightActionMap.app (toAlgebraObj (externalObj M N)).A)
      (F.regularSlice.map (toAlgebraObj (externalObj M N)).a)
      ((F.externalNodeIso M N).hom ≫
        F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightProjection N))) :=
  transportSplitCoequalizer
    ((rightSplitCoequalizer SB N).map (CategoryTheory.Prod.sectR M _ ⋙ F.toFunctor))
    (F.externalSourceIso M N) (F.externalNodeIso M N)
    (F.external_top_square M N) (F.external_bottom_square M N)

end BalancedFunctor
end Paper18.Category.BalancedModuleCategory
