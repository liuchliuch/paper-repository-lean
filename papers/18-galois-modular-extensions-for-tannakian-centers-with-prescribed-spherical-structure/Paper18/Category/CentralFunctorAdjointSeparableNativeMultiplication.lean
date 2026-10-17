import Paper18.Category.CentralFunctorAdjointSeparableNativeTensorCoordinates
import Paper18.Category.CentralFunctorAdjointSeparableNativeNormalization

/-! # The genuine module multiplication law of the native cap action

The positive crossing in the actual precomposition action cancels the
negative crossing in the canonical diagonal multiplication. The remaining
identity is the proved rigid tensor-cap identity.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction MonObj
universe v u vM uM vN uN w wM
namespace Paper18.Category.CentralFunctorAdjointSeparable
open MonoidalLeftAction ModuleFunctor.DiagonalAction
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [HasFiniteBiproducts N] [MonoidalLeftAction C N]
  [∀ X : C, (actionLeft M X).Additive] [∀ X : C, (actionLeft M X).Linear ℂ]
  [∀ X : C, (actionLeft N X).Additive] [∀ X : C, (actionLeft N X).Linear ℂ]
  [∀ m : M, (actionRight C m).Additive] [∀ m : M, (actionRight C m).Linear ℂ]
  [∀ n : N, (actionRight C n).Additive] [∀ n : N, (actionRight C n).Linear ℂ]

omit [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts N]
  [∀ m : M, (actionRight C m).Additive] [∀ m : M, (actionRight C m).Linear ℂ]
  [∀ n : N, (actionRight C n).Additive] [∀ n : N, (actionRight C n).Linear ℂ] in
/-- Actual covariance in the two pair labels cancels any genuine
second-label isomorphism with its inverse around a first-label map. -/
@[reassoc]
lemma pairRightLeftIso_cancel (F : Ordinary C M N) {A B Y Z : C}
    (f : A ⟶ B) (e : Y ≅ Z) :
    (pairMapRight A e.hom).app F ≫ (pairMapLeft f Z).app F ≫
        (pairMapRight B e.inv).app F = (pairMapLeft f Y).app F := by
  apply ordinary_hom_ext
  intro m
  change A ⊴ₗ (toFunctor F).map (e.hom ⊵ₗ m) ≫
      f ⊵ₗ (toFunctor F).obj (Z ⊙ₗ m) ≫ B ⊴ₗ (toFunctor F).map (e.inv ⊵ₗ m) =
    f ⊵ₗ (toFunctor F).obj (Y ⊙ₗ m)
  rw [action_exchange_assoc, ← actionHomRight_comp, ← Functor.map_comp,
    ← comp_actionHomLeft, Iso.hom_inv_id, id_actionHomLeft]
  erw [(toFunctor F).map_id]
  rw [actionHomRight_id, Category.comp_id]

/-- The genuine native pair tensorator and the genuine cap identities
prove the required multiplication coordinate with no supplied diagram. -/
lemma nativeCap_tensor (F : Ordinary C M N) (X Y : C) :
    (DeligneProduct.externalTensorIso Xᘁ Yᘁ X Y).hom ⊵ₗ F ≫
        DiagonalAlgebra.capPairMap (dualTensorIso Y X).inv (β_ Y X).inv ⊵ₗ F ≫
          nativeCap F (Y ⊗ X) =
      (αₗ (DeligneProduct.externalObject Xᘁ X) (DeligneProduct.externalObject Yᘁ Y) F).hom ≫
        DeligneProduct.externalObject Xᘁ X ⊴ₗ nativeCap F Y ≫ nativeCap F X := by
  apply (cancel_epi
    (αₗ (DeligneProduct.externalObject Xᘁ X) (DeligneProduct.externalObject Yᘁ Y) F).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  dsimp only [nativeCap]
  rw [nativePairIso_map_assoc, nativePairIso_tensor_assoc]
  rw [pairRightLeftIso_cancel_assoc]
  rw [ordinaryCap_tensor]
  rw [← reassoc_of% (nativePairIso_naturality Xᘁ X (ordinaryCap F Y))]
  simp only [actionHomRight_comp, Category.assoc]
  rfl

variable [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  [HasFiniteBiproducts M]
  {κ : Type wM} [Fintype κ] (T : FiniteSemisimpleSkeleton M κ)
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]

/-- The actual coend-descended native map satisfies the genuine
associative algebra-module action law. -/
lemma nativeActionMap_mul (F : Ordinary C M N) :
    μ[DiagonalAlgebra.canonicalAlgebra S] ⊵ₗ F ≫ nativeActionMap S T F =
      (αₗ (DiagonalAlgebra.canonicalAlgebra S) (DiagonalAlgebra.canonicalAlgebra S) F).hom ≫
        DiagonalAlgebra.canonicalAlgebra S ⊴ₗ nativeActionMap S T F ≫
        nativeActionMap S T F :=
  (nativeActionMap_mul_iff S T F).mpr (nativeCap_tensor F)

end Paper18.Category.CentralFunctorAdjointSeparable
