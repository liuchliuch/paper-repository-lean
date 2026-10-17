import Paper18.Category.DiagonalCondensationEmbedding
import Paper18.Category.LocalModulesFree
import Paper18.Category.FusionSubcategoryFunctor

/-! # Actual braided local free embeddings along centralizing functors -/
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

/-- The actual lift into the centralizer of the algebra. -/
def centralizingLift : B ⥤ CentralizerCategory ({A} : Set W) :=
  fullSubcategoryLift (centralizerProperty ({A} : Set W)) H (fun X Y hY => by
    obtain rfl := Set.mem_singleton_iff.mp hY
    exact (hH X).symm)

instance centralizingLift_braided : (centralizingLift H hH).Braided := by
  dsimp [centralizingLift]; infer_instance

/-- The actual braided free functor with values in local modules. -/
def localFreeAlong : B ⥤ LocalModules A :=
  centralizingLift H hH ⋙ localFreeFunctor

instance localFreeAlong_braided : (localFreeAlong H hH).Braided := by
  dsimp [localFreeAlong]; infer_instance

instance localFreeAlong_additive : (localFreeAlong H hH).Additive where
  map_add {X Y} f g := by
    change (H ⋙ InternalModule.freeFunctor (A := A)).map (f + g) =
      (H ⋙ InternalModule.freeFunctor (A := A)).map f +
        (H ⋙ InternalModule.freeFunctor (A := A)).map g
    exact (H ⋙ InternalModule.freeFunctor (A := A)).map_add

instance localFreeAlong_linear : (localFreeAlong H hH).Linear ℂ where
  map_smul f c := by
    change (H ⋙ InternalModule.freeFunctor (A := A)).map (c • f) =
      c • (H ⋙ InternalModule.freeFunctor (A := A)).map f
    exact (H ⋙ InternalModule.freeFunctor (A := A)).map_smul c f

/-- Full faithfulness of the actual module-valued free functor descends to
its full local-module category. The inverse maps are the same actual maps. -/
def localFreeAlongFullyFaithful
    (h : (H ⋙ InternalModule.freeFunctor (A := A)).FullyFaithful) :
    (localFreeAlong H hH).FullyFaithful where
  preimage f := h.preimage f
  map_preimage f := h.map_preimage f
  preimage_map f := h.preimage_map f

variable {B₂ : Type u₂} [Category.{v₂} B₂] [Preadditive B₂] [Linear ℂ B₂]
  [MonoidalCategory B₂] [BraidedCategory B₂]
  (H₂ : B₂ ⥤ W) [H₂.Braided] [H₂.Additive] [H₂.Linear ℂ]
  (hH₂ : ∀ X, Centralizes A (H₂.obj X))

/-- Actual ambient centralization descends to the two actual local free
images, even when their source categories are different. -/
lemma localFreeAlong_centralizes (X : B) (Y : B₂)
    (h : Centralizes (H.obj X) (H₂.obj Y)) :
    Centralizes ((localFreeAlong H hH).obj X) ((localFreeAlong H₂ hH₂).obj Y) := by
  let p := (centralizingLift H hH).obj X
  let q := (centralizingLift H₂ hH₂).obj Y
  have hpq : Centralizes p q :=
    (centralizes_map_iff (centralizerInclusion ({A} : Set W)) p q).mp h
  exact hpq.map (localFreeFunctor (A := A))

end Paper18.Category.DiagonalCondensation
