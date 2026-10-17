import Paper18.Category.BalancedModuleCategoryMonadDescent

/-! # Actual descent of action-compatible right-monad-module transformations -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u vE uE
namespace Paper18.Category.BimoduleRelativeTensor.FunctorDescent
open BalancedModuleCategory
variable {C : Type u} [Category.{v} C] {E : Type uE} [Category.{vE} E]
  [HasCoequalizers E] {T : Monad C}
  {H K L : RightMonadModule (E := E) T}

def mapTransformationComponent (τ : H.toFunctor ⟶ K.toFunctor)
    (hτ : ∀ X, H.action.app X ≫ τ.app X = τ.app (T.obj X) ≫ K.action.app X)
    (P : Monad.Algebra T) : H.descent.obj P ⟶ K.descent.obj P :=
  coequalizer.desc (τ.app P.A ≫ K.descentπ P) (by
    calc
      _ = τ.app (T.obj P.A) ≫ K.action.app P.A ≫ K.descentπ P := by
        rw [← assoc, hτ, assoc]
      _ = τ.app (T.obj P.A) ≫ K.toFunctor.map P.a ≫ K.descentπ P := by
        rw [K.descent_condition]
      _ = _ := (τ.naturality_assoc P.a (K.descentπ P)).symm)

@[reassoc (attr := simp)] lemma mapTransformationComponent_π
    (τ : H.toFunctor ⟶ K.toFunctor)
    (hτ : ∀ X, H.action.app X ≫ τ.app X = τ.app (T.obj X) ≫ K.action.app X)
    (P : Monad.Algebra T) :
    H.descentπ P ≫ mapTransformationComponent τ hτ P = τ.app P.A ≫ K.descentπ P :=
  coequalizer.π_desc _ _

/-- The actual component coequalizer maps form an actual natural transformation. -/
def mapTransformation (τ : H.toFunctor ⟶ K.toFunctor)
    (hτ : ∀ X, H.action.app X ≫ τ.app X = τ.app (T.obj X) ≫ K.action.app X) :
    H.descent ⟶ K.descent where
  app := mapTransformationComponent τ hτ
  naturality {P Q} f := by
    apply (cancel_epi (H.descentπ P)).mp
    change H.descentπ P ≫ H.descentMap f ≫ mapTransformationComponent τ hτ Q =
      H.descentπ P ≫ mapTransformationComponent τ hτ P ≫ K.descentMap f
    rw [RightMonadModule.descentπ_map_assoc, mapTransformationComponent_π,
      mapTransformationComponent_π_assoc, RightMonadModule.descentπ_map]
    exact τ.naturality_assoc f.f (K.descentπ Q)

@[reassoc (attr := simp)] lemma mapTransformation_π (τ : H.toFunctor ⟶ K.toFunctor)
    (hτ : ∀ X, H.action.app X ≫ τ.app X = τ.app (T.obj X) ≫ K.action.app X)
    (P : Monad.Algebra T) :
    H.descentπ P ≫ (mapTransformation τ hτ).app P = τ.app P.A ≫ K.descentπ P :=
  mapTransformationComponent_π τ hτ P

lemma actionCompatible_id (H : RightMonadModule (E := E) T) (X : C) :
    H.action.app X ≫ (NatTrans.id H.toFunctor).app X =
      (NatTrans.id H.toFunctor).app (T.obj X) ≫ H.action.app X := by simp

lemma actionCompatible_comp (τ : H.toFunctor ⟶ K.toFunctor)
    (hτ : ∀ X, H.action.app X ≫ τ.app X = τ.app (T.obj X) ≫ K.action.app X)
    (σ : K.toFunctor ⟶ L.toFunctor)
    (hσ : ∀ X, K.action.app X ≫ σ.app X = σ.app (T.obj X) ≫ L.action.app X) (X : C) :
    H.action.app X ≫ (τ ≫ σ).app X = (τ ≫ σ).app (T.obj X) ≫ L.action.app X := by
  change H.action.app X ≫ τ.app X ≫ σ.app X =
    (τ.app (T.obj X) ≫ σ.app (T.obj X)) ≫ L.action.app X
  rw [← assoc, hτ, assoc, hσ, assoc]

@[simp] lemma mapTransformation_id (H : RightMonadModule (E := E) T) :
    mapTransformation (𝟙 H.toFunctor) (actionCompatible_id H) = 𝟙 H.descent := by
  apply NatTrans.ext
  funext P
  apply (cancel_epi (H.descentπ P)).mp
  rw [mapTransformation_π]
  simp only [NatTrans.id_app, id_comp]
  exact (comp_id _).symm

lemma mapTransformation_comp (τ : H.toFunctor ⟶ K.toFunctor)
    (hτ : ∀ X, H.action.app X ≫ τ.app X = τ.app (T.obj X) ≫ K.action.app X)
    (σ : K.toFunctor ⟶ L.toFunctor)
    (hσ : ∀ X, K.action.app X ≫ σ.app X = σ.app (T.obj X) ≫ L.action.app X) :
    mapTransformation (τ ≫ σ) (actionCompatible_comp τ hτ σ hσ) =
      mapTransformation τ hτ ≫ mapTransformation σ hσ := by
  apply NatTrans.ext
  funext P
  apply (cancel_epi (H.descentπ P)).mp
  change H.descentπ P ≫ (mapTransformation (τ ≫ σ) _).app P =
    H.descentπ P ≫ (mapTransformation τ hτ).app P ≫ (mapTransformation σ hσ).app P
  rw [mapTransformation_π, mapTransformation_π_assoc, mapTransformation_π]
  exact assoc _ _ _

lemma actionCompatible_inv (e : H.toFunctor ≅ K.toFunctor)
    (he : ∀ X, H.action.app X ≫ e.hom.app X = e.hom.app (T.obj X) ≫ K.action.app X)
    (X : C) :
    K.action.app X ≫ e.inv.app X = e.inv.app (T.obj X) ≫ H.action.app X := by
  apply (cancel_epi (e.hom.app (T.obj X))).mp
  calc
    _ = H.action.app X ≫ e.hom.app X ≫ e.inv.app X := by rw [← assoc, ← he, assoc]
    _ = H.action.app X := by rw [Iso.hom_inv_id_app, comp_id]
    _ = _ := by rw [← assoc, Iso.hom_inv_id_app, id_comp]

/-- An actual action-compatible natural isomorphism descends to an
actual isomorphism of the coequalizer functors. -/
def mapIso (e : H.toFunctor ≅ K.toFunctor)
    (he : ∀ X, H.action.app X ≫ e.hom.app X = e.hom.app (T.obj X) ≫ K.action.app X) :
    H.descent ≅ K.descent where
  hom := mapTransformation e.hom he
  inv := mapTransformation e.inv (actionCompatible_inv e he)
  hom_inv_id := by
    apply NatTrans.ext
    funext P
    apply (cancel_epi (H.descentπ P)).mp
    change H.descentπ P ≫ (mapTransformation e.hom he).app P ≫
      (mapTransformation e.inv _).app P = H.descentπ P ≫ 𝟙 _
    rw [mapTransformation_π_assoc, mapTransformation_π]
    simp
  inv_hom_id := by
    apply NatTrans.ext
    funext P
    apply (cancel_epi (K.descentπ P)).mp
    change K.descentπ P ≫ (mapTransformation e.inv _).app P ≫
      (mapTransformation e.hom he).app P = K.descentπ P ≫ 𝟙 _
    rw [mapTransformation_π_assoc, mapTransformation_π]
    simp

end Paper18.Category.BimoduleRelativeTensor.FunctorDescent
