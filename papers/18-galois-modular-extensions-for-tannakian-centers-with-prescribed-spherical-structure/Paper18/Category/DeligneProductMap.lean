import Paper18.Category.DeligneProductMapMonoidal
import Paper18.Category.LinearMatLiftFullyFaithful

/-! # Actual Deligne products of linear tensor functors

The functor is constructed on tensor-product Hom spaces and extended by
actual finite biproducts. Full faithfulness, tensor coherence and braiding
are inherited from these actual constructions.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory
universe v u v' u' v₁ u₁ v₂ u₂
namespace Paper18.Category.DeligneProduct
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  {E : Type u₁} [Category.{v₁} E] [Preadditive E] [Linear ℂ E]
  {H : Type u₂} [Category.{v₂} H] [Preadditive H] [Linear ℂ H]
  (F : C ⥤ E) [F.Additive] [F.Linear ℂ]
  (G : D ⥤ H) [G.Additive] [G.Linear ℂ]

/-- The actual product functor on the actual additive linear tensor product. -/
def map : DeligneProduct C D ⥤ DeligneProduct E H :=
  linearMatLift (LinearTensor.map F G ⋙ Mat_.embedding (LinearTensor E H))

instance map_additive : (map F G).Additive := by unfold map; infer_instance
instance map_linear : (map F G).Linear ℂ := by unfold map; infer_instance
instance map_full [F.Full] [G.Full] [F.Faithful] [G.Faithful] : (map F G).Full := by
  unfold map; infer_instance
instance map_faithful [F.Full] [G.Full] [F.Faithful] [G.Faithful] :
    (map F G).Faithful := by unfold map; infer_instance

/-- Actual comparison on every embedded pair object. -/
def mapPairIso (X : C) (Y : D) :
    (map F G).obj ((Mat_.embedding (LinearTensor C D)).obj ⟨X,Y⟩) ≅
      (Mat_.embedding (LinearTensor E H)).obj ⟨F.obj X,G.obj Y⟩ :=
  linearMatLiftSingletonIso (LinearTensor.map F G ⋙ Mat_.embedding (LinearTensor E H)) ⟨X,Y⟩

def mapEmbeddingIso : Mat_.embedding (LinearTensor C D) ⋙ map F G ≅
    LinearTensor.map F G ⋙ Mat_.embedding (LinearTensor E H) :=
  linearMatLiftEmbeddingIso (LinearTensor.map F G ⋙ Mat_.embedding (LinearTensor E H))

section Monoidal
variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalLinear ℂ E]
  [MonoidalCategory H] [MonoidalPreadditive H] [MonoidalLinear ℂ H]

instance map_monoidal [F.Monoidal] [G.Monoidal] : (map F G).Monoidal := by
  unfold map; infer_instance

instance map_braided [BraidedCategory C] [BraidedCategory D]
    [BraidedCategory E] [BraidedCategory H] [F.Braided] [G.Braided] :
    (map F G).Braided := by unfold map; infer_instance

end Monoidal
end Paper18.Category.DeligneProduct
