import Paper18.Category.FixedBoundaryMinimalExistenceDimensions
import Paper18.Category.FixedBoundaryMinimalExistenceNeutral
import Paper18.Category.FixedBoundaryBasic

/-! # Actual minimal extension assembled from genuine realized crossed data

This is an intermediate construction. It does not assert that an arbitrary
categorical action already has a crossed realization. When actual Picard
products instantiate the inputs, the ambient category, source embedding,
nondegeneracy and exact minimal dimension below are all constructed.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Functor.LaxMonoidal
open Paper18.Category.CrossedBraidedGauging
universe v₀ u₀ w₀ v₁ u₁ w₁ v₂ u₂ w₂
namespace Paper18.Category.FixedBoundary.MinimalExistence
variable {C : Type u₀} [Category.{v₀} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w₀} [Fintype ι] (SC : FiniteSemisimpleSkeleton C ι)
  {D : Type u₁} [Category.{v₁} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {κ : Type w₁} [Fintype κ] (SD : FiniteSemisimpleSkeleton D κ)
  {A : WeakAction C2 C} {H : WeakAction C2 D}
  [∀ g : C2, (A.ρ g).Monoidal] [A.IsMonoidal] [A.IsBraided]
  [∀ g : C2, (H.ρ g).Monoidal] [H.IsMonoidal]
  [∀ g : C2, (A.ρ g).Additive] [∀ g : C2, (A.ρ g).Linear ℂ]
  [∀ g : C2, (H.ρ g).Additive] [∀ g : C2, (H.ρ g).Linear ℂ]
  {P : Grading C2 D} {Q : GradedAction P H} (B : CrossedBraiding P H Q)
  (F : A.Intertwiner H) [F.functor.Monoidal] [F.IsMonoidal]
  [F.functor.Additive] [F.functor.Linear ℂ] [F.functor.Full] [F.functor.Faithful]
  (hdeg : ∀ X : C, P.Homogeneous 1 (F.functor.obj X))
  (hcover : ∀ Y : D, P.Homogeneous 1 Y → ∃ X : C, Nonempty (F.functor.obj X ≅ Y))

include hdeg hcover in
/-- Actual full identification with the neutral component identifies its
support dimension, by the genuine tensor-image dimension theorem. -/
theorem neutral_support_eq_source :
    SD.supportFPdim (neutralProperty P) = SC.fusionBasis.totalFPdim := by
  have he : F.functor.essImage = neutralProperty P := by
    ext Y
    constructor
    · intro hY
      exact P.homogeneous_iso hY.getIso.symm (hdeg hY.witness)
    · exact hcover Y
  rw [← he]
  exact RelativeTensor.supportFPdim_essImage SC SD F.functor

variable {R : Type u₂} [Category.{v₂} R] [Preadditive R] [Linear ℂ R]
  [HasKernels R] [HasFiniteBiproducts R]
  [∀ X Y : R, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory R] [BraidedCategory R] [MonoidalPreadditive R] [MonoidalLinear ℂ R]
  [RightRigidCategory R] [Simple (𝟙_ R)]
  {ν : Type w₂} [Fintype ν] (SR : FiniteSemisimpleSkeleton R ν)
  (E : R ⥤ A.Equivariant) [E.IsEquivalence] [E.Additive] [E.Linear ℂ] [E.Braided]

include SC SD SR hdeg hcover E in
/-- Actual descent of the source and actual index-two grading show that
the source dimension equals the entire un-gauged extension dimension. -/
theorem source_total_eq_graded (hf : P.Faithful) :
    SR.fusionBasis.totalFPdim = SD.fusionBasis.totalFPdim := by
  have hs := RelativeTensor.totalFPdim_eq_of_equivalence SR (A.equivariantSkeleton SC) E
  rw [A.totalFPdim_equivariant SC] at hs
  norm_num at hs
  have hd := totalFPdim_eq_twice_neutral P SD hf
  rw [neutral_support_eq_source SC SD F hdeg hcover] at hd
  linarith

/-- The actual source embedding is descent followed by the actual
equivariant functor induced by the neutral action intertwiner. -/
def sourceEmbedding : R ⥤ H.Equivariant := E ⋙ F.equivariantFunctor

instance sourceEmbedding_monoidal : (sourceEmbedding F E).Monoidal := by
  dsimp [sourceEmbedding]
  infer_instance

instance sourceEmbedding_full : (sourceEmbedding F E).Full := by
  dsimp [sourceEmbedding]
  infer_instance
instance sourceEmbedding_faithful : (sourceEmbedding F E).Faithful := by
  dsimp [sourceEmbedding]
  infer_instance
instance sourceEmbedding_additive : (sourceEmbedding F E).Additive := by
  dsimp [sourceEmbedding]
  infer_instance
instance sourceEmbedding_linear : (sourceEmbedding F E).Linear ℂ := by
  dsimp [sourceEmbedding]
  infer_instance

def sourceEmbeddingBraided
    (hβ : ∀ X Y : C, μ F.functor X Y ≫ F.functor.map (β_ X Y).hom =
      (B.neutralIso (F.functor.obj X) (hdeg X) (F.functor.obj Y)).hom ≫ μ F.functor Y X) :
    letI := B.equivariantBraidedCategory
    (sourceEmbedding F E).Braided := by
  letI := B.equivariantBraidedCategory
  letI := equivariantEmbeddingBraided F B hdeg hβ
  dsimp [sourceEmbedding]
  infer_instance

/-- Genuine realized crossed data yield an actual minimal nondegenerate
extension. Crossed realization existence is not asserted by this helper. -/
def minimalExtensionOfCrossedData (hf : P.Faithful)
    (hβ : ∀ X Y : C, μ F.functor X Y ≫ F.functor.map (β_ X Y).hom =
      (B.neutralIso (F.functor.obj X) (hdeg X) (F.functor.obj Y)).hom ≫ μ F.functor Y X)
    (hC : IsNondegenerate (C := C)) : MinimalBraidedExtension SR := by
  letI := B.equivariantBraidedCategory
  letI := sourceEmbeddingBraided B F hdeg E hβ
  refine
    { ambient := H.Equivariant
      index := H.SimpleIndex SD
      skeleton := H.equivariantSkeleton SD
      inclusion := sourceEmbedding F E
      nondegenerate := B.equivariant_nondegenerate SD hf
        (neutral_nondegenerate B F.functor hdeg hβ hcover hC)
      minimal := ?_ }
  rw [H.totalFPdim_equivariant SD]
  norm_num
  rw [← source_total_eq_graded SC SD F hdeg hcover SR E hf]

end Paper18.Category.FixedBoundary.MinimalExistence
