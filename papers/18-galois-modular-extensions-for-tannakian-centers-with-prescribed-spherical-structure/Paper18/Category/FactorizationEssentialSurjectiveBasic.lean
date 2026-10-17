import Paper18.Category.FunctorImage
import Mathlib.CategoryTheory.Equivalence

/-!
# Equal total dimension forces actual essential surjectivity

For an actual fully faithful linear tensor functor, its injection on actual
simple classes preserves positive FP dimensions. Equality of total dimensions
excludes every missing simple label, and actual biproduct decompositions then
construct preimages of all target objects.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w v' u' w'
namespace Paper18.Category.FiniteSemisimpleSkeleton
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Monoidal] [F.Full] [F.Faithful]

/-- Equality of total dimension makes the actual injection of simple
isomorphism classes surjective. -/
theorem simpleImageLabel_surjective_of_totalFPdim_eq
    (heq : S.fusionBasis.totalFPdim = T.fusionBasis.totalFPdim) :
    Function.Surjective (S.simpleImageLabel T F) := by
  let s : Finset κ := Finset.univ.image (S.simpleImageLabel T F)
  have hs : (∑ j ∈ s, T.fusionBasis.fpdim j ^ 2) = S.fusionBasis.totalFPdim := by
    dsimp only [s]
    rw [Finset.sum_image]
    · simp only [S.fpdim_simpleImageLabel T F]
      rfl
    · intro i _ j _ h
      exact S.simpleImageLabel_injective T F h
  intro q
  have hq : q ∈ s := by
    by_contra hn
    have hle : T.fusionBasis.fpdim q ^ 2 + (∑ j ∈ s, T.fusionBasis.fpdim j ^ 2) ≤
        T.fusionBasis.totalFPdim := by
      calc
        _ = ∑ j ∈ insert q s, T.fusionBasis.fpdim j ^ 2 := by
          exact (Finset.sum_insert (f := fun j : κ => T.fusionBasis.fpdim j ^ 2) hn).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => sq_nonneg _)
    have hp : 0 < T.fusionBasis.fpdim q ^ 2 := pow_pos (T.fusionBasis.fpdim_pos q) _
    rw [hs, heq] at hle
    linarith
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hq
  exact ⟨i, hi⟩

/-- The actual target decomposition lifts to a finite biproduct of source
simples, giving actual essential surjectivity. -/
def essSurjOfTotalFPdimEq
    (heq : S.fusionBasis.totalFPdim = T.fusionBasis.totalFPdim) : F.EssSurj where
  mem_essImage Y := by
    choose i hi using fun a : Fin (T.length Y) =>
      S.simpleImageLabel_surjective_of_totalFPdim_eq T F heq (T.label Y a)
    let f : Fin (T.length Y) → C := fun a => S.simpleObject (i a)
    refine ⟨⨁ f, ⟨F.mapBiproduct f ≪≫ ?_ ≪≫ (T.decomposition Y).symm⟩⟩
    exact biproduct.mapIso (fun a => S.simpleImageIso T F (i a) ≪≫
      eqToIso (congrArg T.simpleObject (hi a)))

/-- An actual fully faithful linear tensor functor of equal total dimension
is an actual equivalence. -/
def isEquivalenceOfTotalFPdimEq
    (heq : S.fusionBasis.totalFPdim = T.fusionBasis.totalFPdim) : F.IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := S.essSurjOfTotalFPdimEq T F heq

/-- The resulting equivalence retains the given actual functor as its
forward functor. -/
def equivalenceOfTotalFPdimEq
    (heq : S.fusionBasis.totalFPdim = T.fusionBasis.totalFPdim) : C ≌ D := by
  letI := S.isEquivalenceOfTotalFPdimEq T F heq
  exact F.asEquivalence

end Paper18.Category.FiniteSemisimpleSkeleton
