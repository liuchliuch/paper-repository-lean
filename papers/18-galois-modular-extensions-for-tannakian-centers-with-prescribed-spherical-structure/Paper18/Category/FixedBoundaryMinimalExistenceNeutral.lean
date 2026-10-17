import Paper18.Category.FixedBoundaryMinimalExistenceEmbedding
import Paper18.Category.FusionSubcategoryFunctor
import Paper18.Category.RelativeTensorCentralImage

/-! # Actual neutral identification and nondegeneracy for existence assembly -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Functor.LaxMonoidal
open Paper18.Category.CrossedBraidedGauging
universe v u v' u' w
namespace Paper18.Category.FixedBoundary.MinimalExistence
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [HasFiniteBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [HasKernels D] [HasFiniteBiproducts D]
  {H : WeakAction G D} [∀ g : G, (H.ρ g).Monoidal] [H.IsMonoidal]
  [∀ g : G, (H.ρ g).Additive]
  {P : Grading G D} {Q : GradedAction P H} (B : CrossedBraiding P H Q)
  (J : C ⥤ D) [J.Monoidal] [J.Additive] [J.Linear ℂ] [J.Full] [J.Faithful]
  (hdeg : ∀ X : C, P.Homogeneous 1 (J.obj X))

def neutralLift : C ⥤ Neutral P := fullSubcategoryLift (neutralProperty P) J hdeg

instance neutralLift_monoidal : (neutralLift J hdeg).Monoidal := by
  dsimp [neutralLift]
  infer_instance
instance neutralLift_additive : (neutralLift J hdeg).Additive := by
  dsimp [neutralLift]
  infer_instance
instance neutralLift_linear : (neutralLift J hdeg).Linear ℂ := by
  dsimp [neutralLift]
  infer_instance
instance neutralLift_full : (neutralLift J hdeg).Full := by
  dsimp [neutralLift]
  infer_instance
instance neutralLift_faithful : (neutralLift J hdeg).Faithful := by
  dsimp [neutralLift]
  infer_instance

def neutralLiftBraided
    (hβ : ∀ X Y : C, μ J X Y ≫ J.map (β_ X Y).hom =
      (B.neutralIso (J.obj X) (hdeg X) (J.obj Y)).hom ≫ μ J Y X) :
    letI := B.neutralBraidedCategory
    (neutralLift J hdeg).Braided := by
  letI := B.neutralBraidedCategory
  refine { toMonoidal := inferInstance, braided := ?_ }
  intro X Y
  exact hβ X Y

/-- Actual coverage of neutral objects makes the actual neutral lift an
equivalence; no equivalence is included as a conclusion-valued input. -/
def neutralLiftEssSurj
    (hcover : ∀ Y : D, P.Homogeneous 1 Y → ∃ X : C, Nonempty (J.obj X ≅ Y)) :
    (neutralLift J hdeg).EssSurj where
  mem_essImage Y := by
    obtain ⟨X, ⟨e⟩⟩ := hcover Y.obj Y.property
    exact ⟨X, ⟨(neutralProperty P).isoMk e⟩⟩

/-- Genuine full neutral identification transports actual Müger
nondegeneracy to the constructed actual neutral category. -/
theorem neutral_nondegenerate
    (hβ : ∀ X Y : C, μ J X Y ≫ J.map (β_ X Y).hom =
      (B.neutralIso (J.obj X) (hdeg X) (J.obj Y)).hom ≫ μ J Y X)
    (hcover : ∀ Y : D, P.Homogeneous 1 Y → ∃ X : C, Nonempty (J.obj X ≅ Y))
    (hC : IsNondegenerate (C := C)) :
    letI := B.neutralBraidedCategory
    IsNondegenerate (C := Neutral P) := by
  letI := B.neutralBraidedCategory
  let K := neutralLift J hdeg
  letI : K.Braided := neutralLiftBraided B J hdeg hβ
  intro Y hY
  obtain ⟨X, ⟨e⟩⟩ := hcover Y.obj Y.property
  let ee : K.obj X ≅ Y := (neutralProperty P).isoMk e
  have hX : X ∈ mugerCenter := by
    intro Z _
    apply (centralizes_map_iff K X Z).mp
    exact (hY (K.obj Z) (Set.mem_univ _)).of_iso_left ee
  exact (RelativeTensor.unitSum_map K (hC X hX)).of_iso ee.symm

end Paper18.Category.FixedBoundary.MinimalExistence
