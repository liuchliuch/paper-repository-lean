import Paper18.Category.ModuleFunctorDiagonalActionNative
import Paper18.Category.DeligneTensorProductMapSingleton
import Paper18.Category.DeligneTensorProductMapWhisker

/-! # Monoidal normalization of the genuine native action on external pairs -/
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

def rawActionFunctor : LinearTensor C C ⥤ (Ordinary C M N ⥤ Ordinary C M N)ᴹᵒᵖ :=
  linearActionEnd ⋙ GraphPicard.simultaneousMop LinearEnd.forget
instance rawActionFunctorMonoidal : (rawActionFunctor (C := C) (M := M) (N := N)).Monoidal := by
  unfold rawActionFunctor
  infer_instance

/-- The actual singleton comparison is monoidal, so it simultaneously
normalizes all genuine unit and tensor coherence maps of the native action. -/
def nativeEmbeddingEndIso :
    Mat_.embedding (LinearTensor C C) ⋙ actionFunctor (M := M) (N := N) ≅ rawActionFunctor :=
  (Functor.associator (Mat_.embedding (LinearTensor C C))
    (deligneActionEnd (M := M) (N := N))
      (GraphPicard.simultaneousMop LinearEnd.forget)).symm ≪≫
    Functor.isoWhiskerRight
      (linearMatLiftEmbeddingIso (LinearTensor.lift (sameFunctor (C := C) (M := M) (N := N))))
        (GraphPicard.simultaneousMop LinearEnd.forget)

instance nativeEmbeddingEndIsoMonoidal :
    NatTrans.IsMonoidal (nativeEmbeddingEndIso (C := C) (M := M) (N := N)).hom := by
  let e := linearMatLiftEmbeddingIso (LinearTensor.lift (sameFunctor (C := C) (M := M) (N := N)))
  let H := GraphPicard.simultaneousMop (LinearEnd.forget (D := Ordinary C M N))
  haveI : NatTrans.IsMonoidal e.hom := by dsimp [e]; infer_instance
  haveI : NatTrans.IsMonoidal (Functor.whiskerRight e.hom H) := by infer_instance
  haveI : NatTrans.IsMonoidal
      (Functor.associator (Mat_.embedding (LinearTensor C C))
        (deligneActionEnd (M := M) (N := N)) H).inv := by infer_instance
  change NatTrans.IsMonoidal
    ((Functor.associator (Mat_.embedding (LinearTensor C C))
      (deligneActionEnd (M := M) (N := N)) H).inv ≫ Functor.whiskerRight e.hom H)
  infer_instance

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
lemma nativeEmbeddingEndIso_app (P : LinearTensor C C) :
    (nativeEmbeddingEndIso (C := C) (M := M) (N := N)).app P = nativePairEndIso P.left P.right := by
  apply Iso.ext
  change 𝟙 _ ≫ (nativePairEndIso P.left P.right).hom = _
  exact Category.id_comp _

/-- The genuine native unit tensorator agrees with the exact regular-pair
comparison; this is the actual monoidal singleton comparison's unit law. -/
lemma nativePairEndIso_unit :
    Functor.LaxMonoidal.ε (actionFunctor (C := C) (M := M) (N := N)) ≫
      (nativePairEndIso (𝟙_ C) (𝟙_ C)).hom = Functor.LaxMonoidal.ε (rawActionFunctor (C := C) (M := M) (N := N)) := by
  have h := NatTrans.IsMonoidal.unit (τ := (nativeEmbeddingEndIso (C := C) (M := M) (N := N)).hom)
  dsimp only [Functor.LaxMonoidal.comp_ε, Functor.comp_obj] at h
  have he : Functor.LaxMonoidal.ε (Mat_.embedding (LinearTensor C C)) =
      𝟙 (𝟙_ (Mat_ (LinearTensor C C))) := rfl
  rw [he, CategoryTheory.Functor.map_id, Category.comp_id] at h
  change _ ≫ ((nativeEmbeddingEndIso (C := C) (M := M) (N := N)).app (𝟙_ (LinearTensor C C))).hom = _ at h
  rw [nativeEmbeddingEndIso_app] at h
  exact h

/-- Exact tensor normalization, including the genuine singleton tensor
matrix. No coherence equation is passed in as an assumption. -/
lemma nativePairEndIso_tensor (P Q : LinearTensor C C) :
    Functor.LaxMonoidal.μ (actionFunctor (M := M) (N := N))
        ((Mat_.embedding (LinearTensor C C)).obj P) ((Mat_.embedding (LinearTensor C C)).obj Q) ≫
      (actionFunctor (M := M) (N := N)).map
        (Functor.LaxMonoidal.μ (Mat_.embedding (LinearTensor C C)) P Q) ≫
      (nativePairEndIso (P.left ⊗ Q.left) (P.right ⊗ Q.right)).hom =
    ((nativePairEndIso P.left P.right).hom ⊗ₘ (nativePairEndIso Q.left Q.right).hom) ≫
      Functor.LaxMonoidal.μ rawActionFunctor P Q := by
  have h := NatTrans.IsMonoidal.tensor (τ := (nativeEmbeddingEndIso (C := C) (M := M) (N := N)).hom) P Q
  dsimp only [Functor.LaxMonoidal.comp_μ, Functor.comp_obj] at h
  change (_ ≫ _) ≫ ((nativeEmbeddingEndIso (C := C) (M := M) (N := N)).app (P ⊗ Q)).hom =
    (((nativeEmbeddingEndIso (C := C) (M := M) (N := N)).app P).hom ⊗ₘ
      ((nativeEmbeddingEndIso (C := C) (M := M) (N := N)).app Q).hom) ≫ _ at h
  rw [nativeEmbeddingEndIso_app, nativeEmbeddingEndIso_app, nativeEmbeddingEndIso_app] at h
  simpa only [Category.assoc] using h

omit [HasFiniteBiproducts N] in
/-- The raw unit is exactly the two actual inverse action unitors. -/
lemma rawActionFunctor_ε_app (F : Ordinary C M N) :
    (Functor.LaxMonoidal.ε (rawActionFunctor (C := C) (M := M) (N := N))).unmop.app F =
      (pairUnitComponent F).hom := by
  change (𝟙 F) ≫ ((pairUnitIso.hom ≫ _).app F) = _
  simp only [Category.id_comp, NatTrans.comp_app]
  apply ordinary_hom_ext
  intro m
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app]
  change _ ≫ ((𝟙 (𝟙_ C)) ⊵ₗ (toFunctor F).obj ((𝟙_ C) ⊙ₗ m) ≫
    (𝟙_ C) ⊴ₗ (toFunctor F).map ((𝟙 (𝟙_ C)) ⊵ₗ m)) = _
  simp only [id_actionHomLeft, CategoryTheory.Functor.map_id, actionHomRight_id, Category.comp_id]
  rfl

omit [HasFiniteBiproducts N] in
/-- The raw tensorator contains the actual positive crossing of the
second factor, with the native pre/postcomposition tensor comparison. -/
lemma rawActionFunctor_μ_app (X Y X' Y' : C) (F : Ordinary C M N) :
    (Functor.LaxMonoidal.μ (rawActionFunctor (M := M) (N := N))
      (⟨X,Y⟩ : LinearTensor C C) ⟨X',Y'⟩).unmop.app F =
    (pairTensorComponent X Y X' Y' F).hom ≫
      (pairMapRight (X ⊗ X') (β_ Y' Y).hom).app F := by
  change (𝟙 _) ≫ ((pairTensorIso X Y X' Y').hom ≫ _).app F = _
  rw [Category.id_comp]
  apply ordinary_hom_ext
  intro m
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app,
    pairTensorComponent_hom_app, Category.assoc]
  change _ ≫ ((𝟙 (X ⊗ X')) ⊵ₗ (toFunctor F).obj ((Y' ⊗ Y) ⊙ₗ m) ≫
    (X ⊗ X') ⊴ₗ (toFunctor F).map ((β_ Y' Y).hom ⊵ₗ m)) = _
  simp only [id_actionHomLeft, Category.id_comp]
  exact Category.assoc _ _ _

end Paper18.Category.ModuleFunctor.DiagonalAction
