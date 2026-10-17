import Paper18.Category.DiagonalCondensationEmbeddingLocal

/-! # Actual free embeddings into a categorical centralizer -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u v' u' v₂ u₂
namespace Paper18.Category.DiagonalCondensation
variable {B : Type u} [Category.{v} B] [Preadditive B] [Linear ℂ B]
  [MonoidalCategory B] [BraidedCategory B]
  {W : Type u'} [Category.{v'} W] [Preadditive W] [Linear ℂ W]
  [MonoidalCategory W] [BraidedCategory W] [MonoidalPreadditive W] [MonoidalLinear ℂ W]
  [RightRigidCategory W] [HasCoequalizers W]
  {A : W} [MonObj A] [IsCommMonObj A]
  (H : B ⥤ W) [H.Braided] [H.Additive] [H.Linear ℂ]
  (hH : ∀ X, Centralizes A (H.obj X))
  {B₂ : Type u₂} [Category.{v₂} B₂] [Preadditive B₂] [Linear ℂ B₂]
  [MonoidalCategory B₂] [BraidedCategory B₂]
  (H₂ : B₂ ⥤ W) [H₂.Braided] [H₂.Additive] [H₂.Linear ℂ]
  (hH₂ : ∀ X, Centralizes A (H₂.obj X))
  (hcross : ∀ X Y, Centralizes (H.obj X) (H₂.obj Y))

/-- The actual local free image lies in the categorical centralizer of the
other actual local free image, by the proved ambient monodromy descent. -/
def localFreeAlongCentralizer : B ⥤
    CentralizerCategory (Set.range (localFreeAlong H₂ hH₂).obj) :=
  fullSubcategoryLift (centralizerProperty (Set.range (localFreeAlong H₂ hH₂).obj))
    (localFreeAlong H hH) (fun X Y hY => by
      obtain ⟨Z, rfl⟩ := hY
      exact localFreeAlong_centralizes H hH H₂ hH₂ X Z (hcross X Z))

instance localFreeAlongCentralizer_braided :
    (localFreeAlongCentralizer H hH H₂ hH₂ hcross).Braided := by
  dsimp [localFreeAlongCentralizer]; infer_instance

instance localFreeAlongCentralizer_additive :
    (localFreeAlongCentralizer H hH H₂ hH₂ hcross).Additive := by
  dsimp [localFreeAlongCentralizer]; infer_instance

instance localFreeAlongCentralizer_linear :
    (localFreeAlongCentralizer H hH H₂ hH₂ hcross).Linear ℂ := by
  dsimp [localFreeAlongCentralizer]; infer_instance

/-- The actual centralizer-valued lift is fully faithful when the actual
module-valued free functor has the full faithfulness proved by the diagonal
Hom calculation. No new Hom or centralizer-equality premise is introduced. -/
def localFreeAlongCentralizerFullyFaithful
    (h : (H ⋙ InternalModule.freeFunctor (A := A)).FullyFaithful) :
    (localFreeAlongCentralizer H hH H₂ hH₂ hcross).FullyFaithful := by
  letI := (localFreeAlongFullyFaithful H hH h).full
  letI := (localFreeAlongFullyFaithful H hH h).faithful
  dsimp only [localFreeAlongCentralizer]
  exact Functor.FullyFaithful.ofFullyFaithful _

end Paper18.Category.DiagonalCondensation
