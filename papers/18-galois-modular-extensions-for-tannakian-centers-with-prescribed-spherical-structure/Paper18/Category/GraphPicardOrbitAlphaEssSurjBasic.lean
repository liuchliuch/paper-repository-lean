import Paper18.Category.FactorizationEssentialSurjectiveBasic

/-! # Essential surjectivity from actual simple dimensions

This version uses an actual objectwise FP-dimension calculation rather than
requiring the functor's tensor convention to agree with the target tensor.
It applies to native alpha induction, whose strong tensor structure lands in
the monoidal opposite of the native endofunctor category.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
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
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Full] [F.Faithful]

/-- An actual FP-preserving fully faithful linear functor of equal total
FP dimension reaches every actual simple class. -/
theorem simpleImageLabel_surjective_of_fpdim_eq
    (hF : ∀ X, T.fpdim (F.obj X) = S.fpdim X)
    (heq : S.fusionBasis.totalFPdim = T.fusionBasis.totalFPdim) :
    Function.Surjective (S.simpleImageLabel T F) := by
  have hd (i : ι) : T.fusionBasis.fpdim (S.simpleImageLabel T F i) =
      S.fusionBasis.fpdim i := by
    rw [← T.fpdim_simple, ← T.fpdim_iso (S.simpleImageIso T F i), hF, S.fpdim_simple]
  let s : Finset κ := Finset.univ.image (S.simpleImageLabel T F)
  have hs : (∑ j ∈ s, T.fusionBasis.fpdim j ^ 2) = S.fusionBasis.totalFPdim := by
    dsimp only [s]
    rw [Finset.sum_image]
    · simp only [hd]
      rfl
    · intro i _ j _ h
      exact S.simpleImageLabel_injective T F h
  intro q
  have hq : q ∈ s := by
    by_contra hn
    have hle : T.fusionBasis.fpdim q ^ 2 + (∑ j ∈ s, T.fusionBasis.fpdim j ^ 2) ≤
        T.fusionBasis.totalFPdim := by
      calc
        _ = ∑ j ∈ insert q s, T.fusionBasis.fpdim j ^ 2 :=
          (Finset.sum_insert hn).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun j _ _ => sq_nonneg _)
    have hp := pow_pos (T.fusionBasis.fpdim_pos q) 2
    rw [hs, heq] at hle
    linarith
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hq
  exact ⟨i, hi⟩

/-- Actual biproduct preimages give essential surjectivity from the proved
simple-class surjectivity. No tensor structure on this ordinary functor
is required. -/
def essSurjOfFPdimEq
    (hF : ∀ X, T.fpdim (F.obj X) = S.fpdim X)
    (heq : S.fusionBasis.totalFPdim = T.fusionBasis.totalFPdim) : F.EssSurj where
  mem_essImage Y := by
    choose i hi using fun a : Fin (T.length Y) =>
      S.simpleImageLabel_surjective_of_fpdim_eq T F hF heq (T.label Y a)
    let f : Fin (T.length Y) → C := fun a => S.simpleObject (i a)
    refine ⟨⨁ f, ⟨F.mapBiproduct f ≪≫ ?_ ≪≫ (T.decomposition Y).symm⟩⟩
    exact biproduct.mapIso (fun a => S.simpleImageIso T F (i a) ≪≫
      eqToIso (congrArg T.simpleObject (hi a)))

end Paper18.Category.FiniteSemisimpleSkeleton
