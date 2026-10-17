import Paper18.Category.TannakianBasic
import Paper18.Category.FusionSubcategoryFunctor
import Paper18.Category.CentralizerDoubleDimension
import Paper18.Category.RelativeTensorCentralImage

/-! # The actual Tannakian center of an ambient centralizer

In a genuinely nondegenerate ambient category, the transparent center of
the centralizer of an actual full braided image is the image of its
original transparent center. The actual double-centralizer theorem proves
the essential-image characterization used below.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u v' u' w'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C]
  [HasKernels C] [HasFiniteBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [BraidedCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D] [RightRigidCategory D] [Simple (𝟙_ D)]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Braided] [F.Full] [F.Faithful]
  {G : Type} [Group G] (T : TannakianCenter C G)

lemma TannakianCenter.image_in_centralizer (V : FDRep ℂ G) :
    F.obj (T.inclusion.obj V) ∈ centralizer (Set.range F.obj) := by
  intro Y hY
  obtain ⟨X,rfl⟩ := hY
  exact (T.centralizes V X).map F

def TannakianCenter.centralizerRepresentation :
    FDRep ℂ G ⥤ CentralizerCategory (Set.range F.obj) :=
  fullSubcategoryLift (centralizerProperty (Set.range F.obj)) (T.inclusion ⋙ F)
    (T.image_in_centralizer F)

instance TannakianCenter.centralizerRepresentation_braided :
    (T.centralizerRepresentation F).Braided := by
  dsimp [TannakianCenter.centralizerRepresentation]; infer_instance

instance TannakianCenter.centralizerRepresentation_additive :
    (T.centralizerRepresentation F).Additive := by
  dsimp [TannakianCenter.centralizerRepresentation]; infer_instance

instance TannakianCenter.centralizerRepresentation_linear :
    (T.centralizerRepresentation F).Linear ℂ := by
  dsimp [TannakianCenter.centralizerRepresentation]; infer_instance

instance TannakianCenter.centralizerRepresentation_full :
    (T.centralizerRepresentation F).Full := by
  dsimp [TannakianCenter.centralizerRepresentation]; infer_instance

instance TannakianCenter.centralizerRepresentation_faithful :
    (T.centralizerRepresentation F).Faithful := by
  dsimp [TannakianCenter.centralizerRepresentation]; infer_instance

variable {κ : Type w'} [Fintype κ] (S : FiniteSemisimpleSkeleton D κ)
  (J : PivotalStructure D) (hD : IsNondegenerate (C := D))

include S J hD in
lemma TannakianCenter.centralizerRepresentation_image_iff
    (Z : CentralizerCategory (Set.range F.obj)) :
    (T.centralizerRepresentation F).essImage Z ↔ Z ∈ mugerCenter := by
  constructor
  · rintro ⟨V, ⟨e⟩⟩ Y _
    apply Centralizes.of_iso_left e.symm
    apply (centralizes_map_iff (centralizerInclusion (Set.range F.obj)) _ _).mp
    exact (Y.property (F.obj (T.inclusion.obj V)) ⟨T.inclusion.obj V,rfl⟩).symm
  · intro hZ
    have hz : Z.obj ∈ centralizer (centralizer (Set.range F.obj)) := by
      intro Y hY
      exact (hZ (⟨Y,hY⟩ : CentralizerCategory (Set.range F.obj)) (Set.mem_univ _)).map
        (centralizerInclusion (Set.range F.obj))
    have he : centralizer (centralizer (Set.range F.obj)) = (F.essImage : Set D) := by
      rw [← RelativeTensor.centralizer_essImage F]
      exact S.double_centralizer_eq J hD F.essImage
    have hi : F.essImage Z.obj := by rwa [he] at hz
    have hc : hi.witness ∈ mugerCenter (C := C) := by
      intro X _
      apply (centralizes_map_iff F hi.witness X).mp
      exact (Z.property (F.obj X) ⟨X,rfl⟩).of_iso_left hi.getIso
    obtain ⟨V, ⟨e⟩⟩ := T.exists_representation _ hc
    exact ⟨V, ⟨(centralizerProperty (Set.range F.obj)).isoMk (F.mapIso e ≪≫ hi.getIso)⟩⟩

/-- The original actual Tannakian center transfers to the actual
centralizer of its full braided image in a nondegenerate pivotal ambient
fusion category. No center-identification field is received as input. -/
def TannakianCenter.centralizerCenter :
    TannakianCenter (CentralizerCategory (Set.range F.obj)) G where
  finite_group := T.finite_group
  inclusion := T.centralizerRepresentation F
  braided := inferInstance
  additive := inferInstance
  linear := inferInstance
  full := inferInstance
  faithful := inferInstance
  image_iff := T.centralizerRepresentation_image_iff F S J hD

end Paper18.Category
