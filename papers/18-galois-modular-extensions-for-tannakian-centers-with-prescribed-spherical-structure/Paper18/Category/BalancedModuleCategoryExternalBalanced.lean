import Paper18.Category.BalancedModuleCategoryExternalComparison

/-! # The actual external comparison respects balancing -/
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

omit [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
lemma balancingIso_underlying (M : Mod_ D A) (X : D) (N : RightModules B) :
    (balancingIso M X N).hom.hom = (RelativeTensor.ambientTensorAssoc M X (rightUnderlying N)).hom := by
  apply Mod_.Hom.ext
  rfl

omit [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D] in
lemma rightProjection_leftTensor (X : D) (N : RightModules B) :
    rightProjection (rightAmbientTensor N X) =
      (rightAmbientAssoc (Mod_.regular (mop B)) X (rightUnderlying N)).inv ≫
        ambientLeftFunctor.map (CategoryTheory.Prod.mkHom (𝟙 X) (rightProjection N)) := by
  apply Mod_.Hom.ext
  apply Quiver.Hom.unmop_inj
  simp only [Mod_.comp_hom', unmop_comp, ambientLeftFunctor_map_hom]
  change (α_ X (rightUnderlying N) B).hom ≫ X ◁ rightAction N =
    (α_ X (rightUnderlying N) B).hom ≫ (𝟙 X ⊗ₘ rightAction N)
  rw [id_tensorHom]

variable {E : Type uE} [Category.{vE} E]
namespace BalancedFunctor
variable (F : BalancedFunctor (A := A) (B := B) E)

lemma externalPresentationMap_balancing (M : Mod_ D A) (X : D) (N : RightModules B) :
    F.regularSlice.map (balancingIso M X N).hom.hom ≫
        F.externalPresentationMap M (rightAmbientTensor N X) =
      F.externalPresentationMap (RelativeTensor.ambientTensor M X) N ≫
        F.comparison.hom.app ((M, X), N) := by
  let R := Mod_.regular (mop B)
  let n := rightUnderlying N
  have ha := F.assoc_condition M X n R
  have hn := F.comparison_naturality_right M X (rightProjection N)
  have hm :
      F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightAmbientAssoc R X n).hom) ≫
        F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightProjection (rightAmbientTensor N X))) =
      F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M)
        (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom (𝟙 X) (rightProjection N)))) := by
    rw [← F.toFunctor.map_comp]
    congr 1
    apply CategoryTheory.prod.hom_ext
    · exact comp_id _
    · change (rightAmbientAssoc R X n).hom ≫ rightProjection (rightAmbientTensor N X) = _
      rw [rightProjection_leftTensor]
      exact Iso.hom_inv_id_assoc _ _
  rw [balancingIso_underlying]
  change F.toFunctor.map (CategoryTheory.Prod.mkHom (RelativeTensor.ambientTensorAssoc M X n).hom (𝟙 R)) ≫
      (F.comparison.hom.app ((M, X ⊗ n), R) ≫
        F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightProjection (rightAmbientTensor N X)))) =
    (F.comparison.hom.app ((RelativeTensor.ambientTensor M X, n), R) ≫
      F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 (RelativeTensor.ambientTensor M X))
        (rightProjection N))) ≫ F.comparison.hom.app ((M, X), N)
  calc
    _ = F.comparison.hom.app ((RelativeTensor.ambientTensor M X, n), R) ≫
        F.comparison.hom.app ((M, X), rightAmbientTensor R n) ≫
          F.toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M)
            (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom (𝟙 X) (rightProjection N)))) := by
      have hh := congrArg (fun f => f ≫ F.toFunctor.map
        (CategoryTheory.Prod.mkHom (𝟙 M) (rightProjection (rightAmbientTensor N X)))) ha
      simpa only [Category.assoc, hm] using hh
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun f => F.comparison.hom.app ((RelativeTensor.ambientTensor M X, n), R) ≫ f) hn.symm

variable [HasCoequalizers E]

/-- The external comparison is an actual balanced natural isomorphism,
with its balancing square proved from actual associativity and naturality. -/
theorem extensionExternalNatIso_balanced (SB : SeparableAlgebra B)
    (M : Mod_ D A) (X : D) (N : RightModules B) :
    F.extension.map (balancingIso M X N).hom ≫
        (F.extensionExternalNatIso SB).hom.app (M, rightAmbientTensor N X) =
      (F.extensionExternalNatIso SB).hom.app (RelativeTensor.ambientTensor M X, N) ≫
        F.comparison.hom.app ((M, X), N) := by
  apply (cancel_epi (F.rightMonadModule.descentπ
    (toAlgebraObj (externalObj (RelativeTensor.ambientTensor M X) N)))).mp
  change F.rightMonadModule.descentπ
      (toAlgebraObj (externalObj (RelativeTensor.ambientTensor M X) N)) ≫
        F.rightMonadModule.descentMap (toAlgebras.map (balancingIso M X N).hom) ≫
          (F.extensionExternalIso SB M (rightAmbientTensor N X)).hom =
    F.rightMonadModule.descentπ
      (toAlgebraObj (externalObj (RelativeTensor.ambientTensor M X) N)) ≫
        (F.extensionExternalIso SB (RelativeTensor.ambientTensor M X) N).hom ≫
          F.comparison.hom.app ((M, X), N)
  rw [RightMonadModule.descentπ_map_assoc, extensionExternalIso_π_assoc]
  change F.regularSlice.map (balancingIso M X N).hom.hom ≫
      (F.rightMonadModule.descentπ (toAlgebraObj (externalObj M (rightAmbientTensor N X))) ≫
        (F.extensionExternalIso SB M (rightAmbientTensor N X)).hom) = _
  rw [extensionExternalIso_π]
  exact F.externalPresentationMap_balancing M X N

end BalancedFunctor
end Paper18.Category.BalancedModuleCategory
