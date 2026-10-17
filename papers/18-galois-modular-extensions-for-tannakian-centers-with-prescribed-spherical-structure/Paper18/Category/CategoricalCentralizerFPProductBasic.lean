import Paper18.Category.CategoricalCentralizerGlobalDimensionFPTransport

/-! # FP dimension reciprocity transported through actual braided embeddings -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w v' u' w' v'' u'' w''
namespace Paper18.Category.FiniteSemisimpleSkeleton
attribute [local instance 2000] RightRigidCategory.rightDual
section Pullback
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {B : Type u'} [Category.{v'} B]
  {W : Type u''} [Category.{v''} W] [MonoidalCategory W] [BraidedCategory W]
  (H : B ⥤ C) (F : C ⥤ W) [F.Braided] [F.Faithful]

/-- The actual centralizer of a composite braided image pulls back to the
actual centralizer of the original image. -/
lemma centralizer_composite_image_pullback :
    dimensionPullbackProperty F (centralizerProperty ((H ⋙ F).essImage : Set W)) =
      centralizerProperty (Set.range H.obj) := by
  funext X
  apply propext
  change F.obj X ∈ centralizer ((H ⋙ F).essImage : Set W) ↔
    X ∈ centralizer (Set.range H.obj)
  rw [RelativeTensor.centralizer_essImage]
  constructor
  · intro h Y hY
    obtain ⟨Y, rfl⟩ := hY
    exact (centralizes_map_iff F X (H.obj Y)).mp (h _ ⟨Y, rfl⟩)
  · intro h Y hY
    obtain ⟨Y, rfl⟩ := hY
    exact (h _ ⟨Y, rfl⟩).map F

/-- The composite source objects centralizing the entire intermediate
image are precisely those whose intermediate images are transparent. -/
lemma centralizer_image_composite_pullback :
    dimensionPullbackProperty (H ⋙ F) (centralizerProperty (F.essImage : Set W)) =
      dimensionPullbackProperty H (centralizerProperty (Set.univ : Set C)) := by
  funext X
  apply propext
  change F.obj (H.obj X) ∈ centralizer (F.essImage : Set W) ↔
    H.obj X ∈ centralizer (Set.univ : Set C)
  rw [RelativeTensor.centralizer_essImage]
  constructor
  · intro h Y _
    exact (centralizes_map_iff F (H.obj X) Y).mp (h _ ⟨Y, rfl⟩)
  · intro h Y hY
    obtain ⟨Y, rfl⟩ := hY
    exact (h Y (Set.mem_univ _)).map F

end Pullback

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {B : Type u'} [Category.{v'} B] [MonoidalCategory B] [RightRigidCategory B]
  [Preadditive B] [Linear ℂ B] [MonoidalPreadditive B] [MonoidalLinear ℂ B]
  [HasKernels B] [HasFiniteBiproducts B] [Simple (𝟙_ B)] [BraidedCategory B]
  [∀ X Y : B, FiniteDimensional ℂ (X ⟶ Y)]
  {W : Type u''} [Category.{v''} W] [MonoidalCategory W] [RightRigidCategory W]
  [Preadditive W] [Linear ℂ W] [MonoidalPreadditive W] [MonoidalLinear ℂ W]
  [HasKernels W] [HasFiniteBiproducts W] [Simple (𝟙_ W)] [BraidedCategory W]
  [∀ X Y : W, FiniteDimensional ℂ (X ⟶ Y)]
  (H : B ⥤ C) [H.Braided] [H.Additive] [H.Linear ℂ] [H.Full] [H.Faithful]
  (F : C ⥤ W) [F.Braided] [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]

variable {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton B κ)
  {ν : Type w''} [Fintype ν] (R : FiniteSemisimpleSkeleton W ν)

include F R

/-- The general image-centralizer FP product follows from an actual fully
faithful braided embedding into an actual nondegenerate pivotal fusion
category. The two source categories require no pivotal structure. -/
theorem image_centralizerFPdim_mul_of_nondegenerate_embedding
    (J : PivotalStructure W) (hW : IsNondegenerate (C := W)) :
    T.fusionBasis.totalFPdim * S.centralizerFPdim (Set.range H.obj) =
      S.fusionBasis.totalFPdim *
        S.supportFPdim (fun X => H.essImage X ∧ X ∈ mugerCenter) := by
  have h := R.supportFPdim_centralizer_inter_reciprocity J hW F.essImage (H ⋙ F).essImage
  rw [RelativeTensor.supportFPdim_essImage T R (H ⋙ F),
    RelativeTensor.supportFPdim_essImage S R F,
    supportFPdim_inter_essImage F (centralizerProperty ((H ⋙ F).essImage : Set W)) S R,
    centralizer_composite_image_pullback H F,
    supportFPdim_inter_essImage (H ⋙ F) (centralizerProperty (F.essImage : Set W)) T R,
    centralizer_image_composite_pullback H F] at h
  rw [← supportFPdim_inter_essImage H (centralizerProperty (Set.univ : Set C)) T S] at h
  exact h

end Paper18.Category.FiniteSemisimpleSkeleton
