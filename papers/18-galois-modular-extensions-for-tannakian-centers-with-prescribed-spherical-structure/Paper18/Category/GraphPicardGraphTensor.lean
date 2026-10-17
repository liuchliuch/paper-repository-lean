import Paper18.Category.GraphPicardGeneratorNaturality

/-! # Tensor normalization of the actual graph-pair comparison -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped TensorProduct
universe v u
namespace Paper18.Category.GraphPicard
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasFiniteBiproducts D]
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ]

/-- The actual graph functor on genuine linear pure pairs, before taking
its finite additive envelope. -/
def graphRaw : LinearTensor D D ⥤ Center D :=
  LinearTensor.map (𝟭 D) α ⋙ Drinfeld.linearFactorization D
instance graphRawMonoidal : (graphRaw α).Monoidal := by unfold graphRaw; infer_instance

/-- The genuine additive-envelope comparison on the actual graph functor. -/
def graphEmbeddingIso : Mat_.embedding (LinearTensor D D) ⋙
    GraphLagrangian.graphFunctor α ≅ graphRaw α :=
  (Functor.associator (Mat_.embedding (LinearTensor D D))
    (DeligneProduct.map (𝟭 D) α) (Drinfeld.deligneFactorization D)).symm ≪≫
    Functor.isoWhiskerRight (DeligneProduct.mapEmbeddingIso (𝟭 D) α)
      (Drinfeld.deligneFactorization D) ≪≫
    Functor.associator (LinearTensor.map (𝟭 D) α) (Mat_.embedding (LinearTensor D D))
      (Drinfeld.deligneFactorization D) ≪≫
    Functor.isoWhiskerLeft (LinearTensor.map (𝟭 D) α)
      (linearMatLiftEmbeddingIso (Drinfeld.linearFactorization D))

set_option synthInstance.maxSize 4096 in
instance graphEmbeddingIsoMonoidal : NatTrans.IsMonoidal (graphEmbeddingIso α).hom := by
  letI : NatTrans.IsMonoidal (DeligneProduct.mapEmbeddingIso (𝟭 D) α).hom :=
    inferInstanceAs (NatTrans.IsMonoidal
      (linearMatLiftEmbeddingIso
        (LinearTensor.map (𝟭 D) α ⋙ Mat_.embedding (LinearTensor D D))).hom)
  haveI h₁ : NatTrans.IsMonoidal ((Functor.associator (Mat_.embedding (LinearTensor D D))
    (DeligneProduct.map (𝟭 D) α) (Drinfeld.deligneFactorization D)).inv) := inferInstance
  haveI h₂ : NatTrans.IsMonoidal (Functor.whiskerRight
    (DeligneProduct.mapEmbeddingIso (𝟭 D) α).hom (Drinfeld.deligneFactorization D)) := inferInstance
  haveI h₃ : NatTrans.IsMonoidal ((Functor.associator (LinearTensor.map (𝟭 D) α)
    (Mat_.embedding (LinearTensor D D)) (Drinfeld.deligneFactorization D)).hom) := inferInstance
  haveI h₄ : NatTrans.IsMonoidal (Functor.whiskerLeft (LinearTensor.map (𝟭 D) α)
    (linearMatLiftEmbeddingIso (Drinfeld.linearFactorization D)).hom) := inferInstance
  dsimp only [graphEmbeddingIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

variable [RightRigidCategory D] [HasKernels D] [Simple (𝟙_ D)]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [α.IsEquivalence]

/-- The actual graph embedding comparison is precisely the actual pure
pair normalization used to define its genuine cap generators. -/
lemma graphEmbeddingIso_app (X Y : D) :
    (graphEmbeddingIso α).app (⟨X,Y⟩ : LinearTensor D D) = graphPairIso α X Y := by
  apply Iso.ext
  change (graphEmbeddingIso α).hom.app (⟨X,Y⟩ : LinearTensor D D) =
    (graphPairIso α X Y).hom
  simp only [graphEmbeddingIso, graphPairIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.mapIso_hom, Category.id_comp,
    Category.comp_id, Category.assoc]
  erw [Category.id_comp]
  change (Drinfeld.deligneFactorization D).map
      (DeligneProduct.mapPairIso (𝟭 D) α X Y).hom ≫
      (linearMatLiftEmbeddingIso (Drinfeld.linearFactorization D)).hom.app
        (⟨X,α.obj Y⟩ : LinearTensor D D) = _
  apply congrArg ((Drinfeld.deligneFactorization D).map
    (DeligneProduct.mapPairIso (𝟭 D) α X Y).hom ≫ ·)
  apply biproduct.hom_ext'
  rintro ⟨⟩
  simp [linearMatLiftEmbeddingIso, linearMatLiftSingletonIso,
    Drinfeld.deligneFactorizationPairIso, biproductUniqueIso, limitBiconeOfUnique]

/-- The actual graph tensorator on actual external pairs normalizes to
the actual tensorator of the explicit linear-pair graph functor. -/
@[reassoc] lemma graphPairIso_tensor (X Y X' Y' : D) :
    Functor.LaxMonoidal.μ (GraphLagrangian.graphFunctor α)
        (DeligneProduct.externalObject X Y) (DeligneProduct.externalObject X' Y') ≫
      (GraphLagrangian.graphFunctor α).map (DeligneProduct.externalTensorIso X X' Y Y').hom ≫
        (graphPairIso α (X ⊗ X') (Y ⊗ Y')).hom =
      ((graphPairIso α X Y).hom ⊗ₘ (graphPairIso α X' Y').hom) ≫
        Functor.LaxMonoidal.μ (graphRaw α)
          (⟨X,Y⟩ : LinearTensor D D) (⟨X',Y'⟩ : LinearTensor D D) := by
  have h := NatTrans.IsMonoidal.tensor (τ := (graphEmbeddingIso α).hom)
    (⟨X,Y⟩ : LinearTensor D D) (⟨X',Y'⟩ : LinearTensor D D)
  simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_obj] at h
  have he (A B : D) : (graphEmbeddingIso α).hom.app
      (⟨A,B⟩ : LinearTensor D D) = (graphPairIso α A B).hom :=
    congrArg Iso.hom (graphEmbeddingIso_app α A B)
  change (Functor.LaxMonoidal.μ (GraphLagrangian.graphFunctor α) _ _ ≫
      (GraphLagrangian.graphFunctor α).map (DeligneProduct.externalTensorIso X X' Y Y').hom) ≫
      (graphEmbeddingIso α).hom.app ⟨X ⊗ X',Y ⊗ Y'⟩ = _ at h
  rw [he, he, he] at h
  simpa only [Category.assoc] using h

end Paper18.Category.GraphPicard
