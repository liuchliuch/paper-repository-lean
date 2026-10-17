import Paper18.Category.ModuleFunctorDiagonalActionNormalization
import Paper18.Category.DeligneProductEmbedding

/-! # Pointwise unit and tensor normalization of the actual action

These formulas evaluate the proved monoidal singleton comparison. They
retain the actual positive crossing in the second tensor factor.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.CentralFunctorAdjointSeparable
open MonoidalLeftAction ModuleFunctor.DiagonalAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M] [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N] [MonoidalLeftAction C N]
  [∀ X : C, (actionLeft M X).Additive] [∀ X : C, (actionLeft M X).Linear ℂ]
  [∀ X : C, (actionLeft N X).Additive] [∀ X : C, (actionLeft N X).Linear ℂ]
  [∀ m : M, (actionRight C m).Additive] [∀ m : M, (actionRight C m).Linear ℂ]
  [∀ n : N, (actionRight C n).Additive] [∀ n : N, (actionRight C n).Linear ℂ]
  [HasFiniteBiproducts N]
attribute [local instance] CategoryTheory.endofunctorMonoidalCategory

/-- The actual native unit has the exact two inverse action-unitors as
its regular external-pair coordinate. -/
@[reassoc]
lemma nativePairIso_unit (F : Ordinary C M N) :
    (λₗ[DeligneProduct C C] F).inv ≫ (nativePairIso F (𝟙_ C) (𝟙_ C)).hom =
      (pairUnitComponent F).hom := by
  have h := congrArg (fun k => k.unmop.app F)
    (nativePairEndIso_unit (C := C) (M := M) (N := N))
  simpa only [unmop_comp, NatTrans.comp_app, rawActionFunctor_ε_app] using h

/-- The actual native associator on external pairs is the actual raw
post/precomposition tensor comparison followed by the positive crossing
that reverses the second-factor order. -/
@[reassoc]
lemma nativePairIso_tensor (F : Ordinary C M N) (X Y X' Y' : C) :
    (αₗ (DeligneProduct.externalObject X Y) (DeligneProduct.externalObject X' Y') F).inv ≫
        (DeligneProduct.externalTensorIso X X' Y Y').hom ⊵ₗ F ≫
        (nativePairIso F (X ⊗ X') (Y ⊗ Y')).hom =
      DeligneProduct.externalObject X Y ⊴ₗ (nativePairIso F X' Y').hom ≫
        (nativePairIso (pairObject X' Y' F) X Y).hom ≫
        (pairTensorComponent X Y X' Y' F).hom ≫
        (pairMapRight (X ⊗ X') (β_ Y' Y).hom).app F := by
  have h := congrArg (fun k => k.unmop.app F)
    (nativePairEndIso_tensor (M := M) (N := N)
      (⟨X,Y⟩ : LinearTensor C C) ⟨X',Y'⟩)
  simpa only [unmop_comp, NatTrans.comp_app, unmop_tensorHom, tensorHom_def',
    Functor.whiskerLeft_app, Functor.whiskerRight_app, rawActionFunctor_μ_app,
    Category.assoc] using h

end Paper18.Category.CentralFunctorAdjointSeparable
