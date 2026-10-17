import Paper18.Category.CrossedBraidedGaugingCentralizerTransfer
import Paper18.Category.CrossedBraidedGaugingNondegenerate
import Paper18.Category.GaloisBraidedExtension

/-! # Actual Galois extension output from an actual crossed gauging

This construction supplies all ambient fusion, braiding, nondegeneracy
and centralizer-integrality data from genuine crossed maps and induced
neutral tests. It does not assert existence of those crossed data.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w t v₀ u₀
namespace Paper18.Category.GaloisBraidedExtension
open CrossedBraidedGauging
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {P : Grading G C} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]
  {Q : GradedAction P A} (B : CrossedBraiding P A Q)
  {ι : Type t} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {C₀ : Type u₀} [Category.{v₀} C₀] [Preadditive C₀] [Linear ℂ C₀]
  [MonoidalCategory C₀] [BraidedCategory C₀]

/-- The actual constructed gauging is an actual nondegenerate braided
extension with integral relative centralizer. The source embedding and
the neutral tests are genuine functors and objects, not dimension data. -/
def ofCrossedGauging (F : C₀ ⥤ A.Equivariant)
    [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]
    (hF : letI := B.equivariantBraidedCategory; F.Braided)
    (hfaithful : P.Faithful)
    (hN : letI := B.neutralBraidedCategory; IsNondegenerate (C := Neutral P))
    (hregular : regularUnit (A := A) ∈ Set.range F.obj)
    (U : Set (Neutral P))
    (hinduced : ∀ Y ∈ U, A.induction Y.obj ∈ Set.range F.obj)
    (hIntegral :
      letI := B.neutralBraidedCategory
      letI := S.fullSubcategoryHasKernels (neutralProperty P)
      letI := S.fullSubcategoryRightRigid (neutralProperty P)
      letI := S.fullSubcategorySimpleUnit (neutralProperty P)
      (S.fullSubcategorySkeleton (neutralProperty P)).CentralizerIntegral U) :
    GaloisBraidedExtension C₀ := by
  letI := B.equivariantBraidedCategory
  letI := hF
  exact {
    ambient := A.Equivariant
    index := A.SimpleIndex S
    skeleton := gaugingSkeleton S
    inclusion := F
    nondegenerate := B.equivariant_nondegenerate S hfaithful hN
    integralCentralizer := B.centralizerIntegral_of_induced_tests S
      (Set.range F.obj) hregular U hinduced hIntegral }

end Paper18.Category.GaloisBraidedExtension
