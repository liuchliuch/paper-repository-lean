import Paper18.Category.ModuleFunctorDiagonalActionMonoidal
import Paper18.Category.GraphPicardNativeMonoidalBasic
import Mathlib.CategoryTheory.Monoidal.Action.End

/-! # The actual native Deligne action on ordinary module-functor objects -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalLeftAction MonoidalOpposite
open scoped MonoidalLeftAction TensorProduct
universe v u vM uM vN uN
namespace Paper18.Category.ModuleFunctor.DiagonalAction
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

/-- Forgetting the additive linear object data retains actual ordinary
transformations and the genuine strong composition structure. -/
def actionFunctor : DeligneProduct C C ⥤ (Ordinary C M N ⥤ Ordinary C M N)ᴹᵒᵖ :=
  deligneActionEnd ⋙ GraphPicard.simultaneousMop LinearEnd.forget

instance actionFunctorMonoidal : (actionFunctor (C := C) (M := M) (N := N)).Monoidal := by
  unfold actionFunctor
  infer_instance

/-- This is the actual native action supplied by the proved strong
monoidal functor; every action coherence law is consequently derived. -/
instance nativeAction : MonoidalLeftAction (DeligneProduct C C) (Ordinary C M N) :=
  actionOfMonoidalFunctorToEndofunctorMop actionFunctor

/-- The full ordinary endofunctor at a genuine external pair is naturally
isomorphic to the required actual post/precomposition endofunctor. -/
def nativePairEndIso (X Y : C) :
    (actionFunctor (M := M) (N := N)).obj
      ((Mat_.embedding (LinearTensor C C)).obj ⟨X, Y⟩) ≅ mop (pairEnd (M := M) (N := N) X Y) :=
  (GraphPicard.simultaneousMop LinearEnd.forget).mapIso (deligneActionEndPairIso X Y)

/-- Exact pair values of the actual native action. -/
def nativePairIso (F : Ordinary C M N) (X Y : C) :
    ((Mat_.embedding (LinearTensor C C)).obj ⟨X, Y⟩) ⊙ₗ F ≅ pairObject X Y F :=
  (nativePairEndIso X Y).unmop.app F

lemma nativePairIso_naturality (X Y : C) {F G : Ordinary C M N} (τ : F ⟶ G) :
    ((Mat_.embedding (LinearTensor C C)).obj ⟨X, Y⟩) ⊴ₗ τ ≫ (nativePairIso G X Y).hom =
      (nativePairIso F X Y).hom ≫ (pairEnd X Y).map τ :=
  (nativePairEndIso X Y).unmop.hom.naturality τ

instance nativeActionLeftAdditive (P : DeligneProduct C C) :
    (actionLeft (Ordinary C M N) P).Additive := by
  change (LinearEnd.toFunctor ((deligneActionEnd (M := M) (N := N)).obj P).unmop).Additive
  infer_instance
instance nativeActionLeftLinear (P : DeligneProduct C C) :
    (actionLeft (Ordinary C M N) P).Linear ℂ := by
  change (LinearEnd.toFunctor ((deligneActionEnd (M := M) (N := N)).obj P).unmop).Linear ℂ
  infer_instance

instance nativeActionRightAdditive (F : Ordinary C M N) :
    (actionRight (DeligneProduct C C) F).Additive where
  map_add {P Q} f g := by
    exact congrArg (fun k => k.unmop.app F)
      ((deligneActionEnd (M := M) (N := N)).map_add (f := f) (g := g))

instance nativeActionRightLinear (F : Ordinary C M N) :
    (actionRight (DeligneProduct C C) F).Linear ℂ where
  map_smul f z := by
    exact congrArg (fun k => k.unmop.app F)
      (Functor.Linear.map_smul (F := deligneActionEnd (M := M) (N := N)) f z)

/-- Covariance of the actual external-pair normalization on arbitrary
actual maps in both factors. -/
lemma nativePairIso_covariance (F : Ordinary C M N) {X X' Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (Mat_.embedding (LinearTensor C C)).map
        (show (⟨X,Y⟩ : LinearTensor C C) ⟶ ⟨X',Y'⟩ from f ⊗ₜ[ℂ] g) ⊵ₗ F ≫
        (nativePairIso F X' Y').hom =
      (nativePairIso F X Y).hom ≫
        ((pairMapLeft f Y).app F ≫ (pairMapRight X' g).app F) := by
  have h := (linearMatLiftEmbeddingIso
    (LinearTensor.lift (sameFunctor (M := M) (N := N)))).hom.naturality
      (show (⟨X,Y⟩ : LinearTensor C C) ⟶ ⟨X',Y'⟩ from f ⊗ₜ[ℂ] g)
  have ht := congrArg (fun k =>
    ((GraphPicard.simultaneousMop LinearEnd.forget).map k).unmop.app F) h
  simpa only [CategoryTheory.Functor.map_comp, unmop_comp, NatTrans.comp_app] using ht

end Paper18.Category.ModuleFunctor.DiagonalAction
