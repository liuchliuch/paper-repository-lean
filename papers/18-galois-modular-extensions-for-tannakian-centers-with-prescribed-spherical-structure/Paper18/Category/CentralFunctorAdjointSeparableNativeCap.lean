import Paper18.Category.CentralFunctorAdjointSeparableOrdinaryCapTensor
import Paper18.Category.ModuleFunctorDiagonalActionNative
import Paper18.Category.DeligneProductEmbedding

/-! # Cap coordinates for the genuine native diagonal action

The actual external-pair comparison transports the actual cap maps to
the proved native action. Compatibility with these genuine action maps
is precisely native module naturality.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM vN uN
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

/-- The actual cap component, now with source given by the genuine
native Deligne action. -/
def nativeCap (F : Ordinary C M N) (X : C) :
    DeligneProduct.externalObject Xᘁ X ⊙ₗ F ⟶ F :=
  (nativePairIso F Xᘁ X).hom ≫ ordinaryCap F X

/-- The native pair comparison identifies action compatibility on all
cap coordinates with the actual original module-naturality equation. -/
theorem nativeCap_comm_iff {F G : Ordinary C M N} (τ : F ⟶ G) :
    (∀ X : C, nativeCap F X ≫ τ =
      (DeligneProduct.externalObject Xᘁ X) ⊴ₗ τ ≫ nativeCap G X) ↔
      ModuleFunctor.IsModuleNatural C τ := by
  rw [← ordinaryCap_comm_iff]
  constructor
  · intro h X
    apply (cancel_epi (nativePairIso F Xᘁ X).hom).mp
    have hn := congrArg (fun k => k ≫ ordinaryCap G X)
      (nativePairIso_naturality Xᘁ X τ)
    have hh := h X
    dsimp only [nativeCap] at hh
    simp only [Category.assoc] at hn hh ⊢
    exact hh.trans hn
  · intro h X
    dsimp only [nativeCap]
    rw [Category.assoc, h X]
    simpa only [Category.assoc] using
      (congrArg (fun k => k ≫ ordinaryCap G X)
        (nativePairIso_naturality Xᘁ X τ)).symm

/-- Every actual module-natural map commutes with every native cap
component of the genuine diagonal action. -/
@[reassoc]
lemma nativeCap_naturality {F G : Ordinary C M N} (τ : F ⟶ G)
    [ModuleFunctor.IsModuleNatural C τ] (X : C) :
    nativeCap F X ≫ τ =
      (DeligneProduct.externalObject Xᘁ X) ⊴ₗ τ ≫ nativeCap G X :=
  (nativeCap_comm_iff τ).mpr inferInstance X

end Paper18.Category.CentralFunctorAdjointSeparable
