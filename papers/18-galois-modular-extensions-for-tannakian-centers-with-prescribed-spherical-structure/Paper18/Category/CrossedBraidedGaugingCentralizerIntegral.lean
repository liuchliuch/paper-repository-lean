import Paper18.Category.CrossedBraidedGaugingCentralizerBasic
import Paper18.Category.CrossedBraidedGaugingFusion
import Paper18.Category.CentralizerFusion

/-! # Integrality of the actual neutral equivariant centralizer -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w t
namespace Paper18.Category.CrossedBraidedGauging
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

/-- The actual forgetful tensor functor and actual unit-sum decomposition
give integral FP dimension, without requiring an equivariant unit sum. -/
theorem equivariant_fpdim_integer_of_underlying_unitSum (E : A.Equivariant)
    (hE : IsUnitSum E.obj) :
    ∃ n : ℤ, (gaugingSkeleton S).fpdim E = n := by
  obtain ⟨n, ⟨e⟩⟩ := hE
  refine ⟨n, ?_⟩
  rw [← (gaugingSkeleton S).fpdim_map S A.forget E]
  change S.fpdim E.obj = _
  rw [S.fpdim_iso e, S.fpdim_biproduct]
  simp

namespace CrossedBraiding

/-- Every actual object centralizing neutral equivariant objects has
integral intrinsic FP dimension when the actual neutral category is
nondegenerate. Faithfulness of the grading is unnecessary here. -/
theorem centralizer_fpdim_integer
    (hN : letI := B.neutralBraidedCategory; IsNondegenerate (C := Neutral P))
    (E : A.Equivariant) :
    letI := B.equivariantBraidedCategory
    E ∈ centralizer (neutralEquivariantObjects P A) →
      ∃ n : ℤ, (gaugingSkeleton S).fpdim E = n := by
  letI := B.equivariantBraidedCategory
  intro hE
  exact equivariant_fpdim_integer_of_underlying_unitSum S E
    (B.centralizer_underlying_unitSum hN E hE)

/-- The actual centralizer fusion category is integral; its skeleton and
all its categorical structures are the existing actual inherited ones. -/
theorem neutralEquivariantCentralizerIntegral
    (hN : letI := B.neutralBraidedCategory; IsNondegenerate (C := Neutral P)) :
    letI := B.equivariantBraidedCategory
    (gaugingSkeleton S).CentralizerIntegral (neutralEquivariantObjects P A) := by
  letI := B.equivariantBraidedCategory
  apply (gaugingSkeleton S).centralizerIntegral_iff _ |>.mpr
  intro i hi
  exact B.centralizer_fpdim_integer S hN _ hi

end CrossedBraiding
end Paper18.Category.CrossedBraidedGauging
