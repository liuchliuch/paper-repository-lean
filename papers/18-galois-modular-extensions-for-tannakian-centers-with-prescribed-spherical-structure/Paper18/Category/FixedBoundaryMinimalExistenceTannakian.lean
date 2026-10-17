import Paper18.Category.FixedBoundaryMinimalExistenceCentralizer
import Paper18.Category.TannakianDeequivariantNondegenerate

/-! # Actual C₂ Tannakian descent supplies the source of crossed assembly

This specializes the intermediate construction to the original category:
source descent, neutral fusion and neutral nondegeneracy are derived. The
actual crossed extension data still require Picard realization.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Functor.LaxMonoidal
open Paper18.Category.CrossedBraidedGauging
universe v u w v' u' w'
namespace Paper18.Category.FixedBoundary.MinimalExistence
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)] [HasCoequalizers C]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (T : TannakianCenter C C2)

local instance deeqRightRigid : RightRigidCategory T.Deequivariantization := T.deequivariantRightRigid
local instance deeqBraided : BraidedCategory T.Deequivariantization := T.deequivariantBraided
local instance deeqActionBraided : T.deequivariantAction.IsBraided := T.deequivariantActionBraided
local instance descentBraided : T.descentComparison.Braided := T.descentComparisonBraided

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {κ : Type w'} [Fintype κ] (SD : FiniteSemisimpleSkeleton D κ)
  {H : WeakAction C2 D}
  [∀ g : C2, (H.ρ g).Monoidal] [H.IsMonoidal]
  [∀ g : C2, (H.ρ g).Additive] [∀ g : C2, (H.ρ g).Linear ℂ]
  {P : Grading C2 D} {Q : GradedAction P H} (B : CrossedBraiding P H Q)
  (F : T.deequivariantAction.Intertwiner H) [F.functor.Monoidal] [F.IsMonoidal]
  [F.functor.Additive] [F.functor.Linear ℂ] [F.functor.Full] [F.functor.Faithful]
  (hdeg : ∀ X : T.Deequivariantization, P.Homogeneous 1 (F.functor.obj X))
  (hcover : ∀ Y : D, P.Homogeneous 1 Y →
    ∃ X : T.Deequivariantization, Nonempty (F.functor.obj X ≅ Y))

/-- Genuine realized C₂ crossed data over the actual Tannakian quotient
construct an actual original-source minimal extension. No ambient pivotal
structure, supplied embedding or supplied dimension identity is required. -/
def tannakianMinimalExtensionOfCrossedData (hf : P.Faithful)
    (hβ : ∀ X Y : T.Deequivariantization,
      μ F.functor X Y ≫ F.functor.map (β_ X Y).hom =
        (B.neutralIso (F.functor.obj X) (hdeg X) (F.functor.obj Y)).hom ≫ μ F.functor Y X) :
    MinimalBraidedExtension S := by
  letI := T.deequivariantSimpleUnit S
  exact minimalExtensionOfCrossedData (T.deequivariantSkeleton S) SD B F hdeg hcover
    S T.descentComparison hf hβ (T.deequivariant_isNondegenerate S)

include S SD hdeg hcover in
/-- Actual Tannakian descent identifies the original-source essential
image with the actual neutral equivariant sector. -/
theorem tannakianSourceEmbedding_essImage (hf : P.Faithful) :
    (sourceEmbedding F T.descentComparison).essImage =
      neutralProperty (equivariantGrading Q) := by
  letI := T.deequivariantSimpleUnit S
  exact sourceEmbedding_essImage (Q := Q) (T.deequivariantSkeleton S) SD F hdeg hcover
    S T.descentComparison hf

include S SD hdeg hcover in
/-- Actual neutral nondegeneracy and actual source reconstruction give
intrinsic integrality of the original-source centralizer. -/
theorem tannakianSourceEmbeddingCentralizerIntegral (hf : P.Faithful)
    (hβ : ∀ X Y : T.Deequivariantization,
      μ F.functor X Y ≫ F.functor.map (β_ X Y).hom =
        (B.neutralIso (F.functor.obj X) (hdeg X) (F.functor.obj Y)).hom ≫ μ F.functor Y X) :
    letI := B.equivariantBraidedCategory
    (gaugingSkeleton SD).CentralizerIntegral
      (Set.range (sourceEmbedding F T.descentComparison).obj) := by
  letI := T.deequivariantSimpleUnit S
  exact sourceEmbeddingCentralizerIntegral (T.deequivariantSkeleton S) SD B F hdeg hcover
    S T.descentComparison hf hβ (T.deequivariant_isNondegenerate S)

end Paper18.Category.FixedBoundary.MinimalExistence
