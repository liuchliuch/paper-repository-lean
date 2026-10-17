import Paper18.Category.GraphPicardGenerators
import Paper18.Category.DiagonalAlgebraCapGeneratorDinatural

/-! # Actual dinaturality of the graph cap family -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped TensorProduct
universe v u w
namespace Paper18.Category.GraphPicard
attribute [local instance 2000] RightRigidCategory.rightDual
open DiagonalAlgebra
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]

/-- The genuine singleton-pair comparison respects genuine factor maps. -/
@[reassoc] lemma graphPairIso_naturality {X X' Y Y' : D}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (GraphLagrangian.graphFunctor α).map (capPairMap f g) ≫
        (graphPairIso α X' Y').hom =
      (graphPairIso α X Y).hom ≫
        ((Drinfeld.positive D).map f ⊗ₘ (Drinfeld.negative D).map (α.map g)) := by
  have h₁ : (DeligneProduct.map (𝟭 D) α).map (capPairMap f g) ≫
      (DeligneProduct.mapPairIso (𝟭 D) α X' Y').hom =
    (DeligneProduct.mapPairIso (𝟭 D) α X Y).hom ≫ capPairMap f (α.map g) := by
    simpa only [capPairMap, DeligneProduct.mapEmbeddingIso,
      linearMatLiftEmbeddingIso, NatIso.ofComponents_hom_app,
      DeligneProduct.mapPairIso, Functor.comp_map, LinearTensor.map_tmul,
      Functor.id_map] using
      (DeligneProduct.mapEmbeddingIso (𝟭 D) α).hom.naturality
        (show (⟨X,Y⟩ : LinearTensor D D) ⟶ ⟨X',Y'⟩ from f ⊗ₜ[ℂ] g)
  have h₂ := congrArg (Drinfeld.deligneFactorization D).map h₁
  simp only [Functor.map_comp] at h₂
  dsimp only [graphPairIso, Iso.trans_hom, Functor.mapIso_hom]
  change (Drinfeld.deligneFactorization D).map
      ((DeligneProduct.map (𝟭 D) α).map (capPairMap f g)) ≫ _ ≫ _ = _
  rw [reassoc_of% h₂]
  have h₃ := Drinfeld.deligneFactorizationPairIso_naturality
    (show (X ⟶ X') ⊗[ℂ] (α.obj Y ⟶ α.obj Y') from f ⊗ₜ[ℂ] α.map g)
  rw [Drinfeld.linearFactorization_map_tmul] at h₃
  simpa only [capPairMap, Category.assoc] using congrArg
    ((Drinfeld.deligneFactorization D).map
      (DeligneProduct.mapPairIso (𝟭 D) α X Y).hom ≫ ·) h₃

/-- Moving a genuine map through a graph cap takes its actual dual mate. -/
lemma graphCap_dinaturality {X Y : D} (f : X ⟶ Y) :
    ((Drinfeld.positive D).map (dualMap D f) ⊗ₘ
        𝟙 ((Drinfeld.negative D).obj (α.obj X))) ≫ graphCap S α X =
      (𝟙 ((Drinfeld.positive D).obj (dual D Y)) ⊗ₘ
        (Drinfeld.negative D).map (α.map f)) ≫ graphCap S α Y := by
  apply (cancel_epi (graphPairIso α (dual D Y) X).hom).mp
  unfold graphCap mappedGraphCap
  have hleft := graphPairIso_naturality α (dualMap D f) (𝟙 X)
  have hright := graphPairIso_naturality α (𝟙 (dual D Y)) f
  simp at hleft hright
  change (GraphLagrangian.graphFunctor α).map (capPairMap (𝟙 (dual D Y)) f) ≫
      (graphPairIso α (dual D Y) Y).hom =
    (graphPairIso α (dual D Y) X).hom ≫
      (Drinfeld.positive D).obj (dual D Y) ◁ (Drinfeld.negative D).map (α.map f) at hright
  simp only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom]
  rw [← reassoc_of% hleft, ← reassoc_of% hright]
  simp only [Functor.map_id, Iso.hom_inv_id_assoc, ← Functor.map_comp]
  exact congrArg (GraphLagrangian.graphFunctor α).map (capGenerator_dinaturality S f)

end Paper18.Category.GraphPicard
