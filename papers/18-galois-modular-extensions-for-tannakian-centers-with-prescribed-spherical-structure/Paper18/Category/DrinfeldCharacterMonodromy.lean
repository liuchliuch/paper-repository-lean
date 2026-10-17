import Paper18.Category.DrinfeldCharacterMonodromyBasic

/-! # Actual monodromy representatives from the actual center factorization -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w t
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]

/-- The actual inverse supplied by the actual central factorization has
exactly the original monoidal natural character as its monodromy. -/
lemma inverseOfCharacterPair_monodromy {i j : ι}
    (e : (positive C).obj (S.simpleObject i) ⊗ (negative C).obj (S.simpleObject j) ≅
      characterObject χ) :
    (inverseOfCharacterPair S χ e).monodromyCharacter = χ :=
  characterPairInverse_monodromy χ e

/-- Existence of an actual invertible representative, using the proved
factorization for an explicitly given actual finite semisimple center skeleton.
The center skeleton's construction remains a separate categorical result. -/
theorem monodromyCharacter_surjective_of_centerSkeleton
    (J : PivotalStructure C)
    {κ : Type t} [Fintype κ] (T : FiniteSemisimpleSkeleton (Center C) κ)
    (hC : IsNondegenerate (C := C)) :
    ∃ i : ι, ∃ A : TensorInverse (S.simpleObject i), A.monodromyCharacter = χ := by
  obtain ⟨i,j,⟨e⟩⟩ := character_simple_pair S J T hC χ
  exact ⟨i, inverseOfCharacterPair S χ e, inverseOfCharacterPair_monodromy S χ e⟩

/-- Existence with the raw actual double-braiding equation exposed. -/
theorem monodromyRepresentative_of_centerSkeleton
    (J : PivotalStructure C)
    {κ : Type t} [Fintype κ] (T : FiniteSemisimpleSkeleton (Center C) κ)
    (hC : IsNondegenerate (C := C)) :
    ∃ i : ι, ∃ A : TensorInverse (S.simpleObject i),
      ∀ X : C, (S.simpleObject i) ◁ χ.hom.app X =
        (doubleBraiding (S.simpleObject i) X).hom := by
  obtain ⟨i,A,hA⟩ := monodromyCharacter_surjective_of_centerSkeleton S χ J T hC
  refine ⟨i,A,?_⟩
  intro X
  rw [← hA]
  exact A.monodromyCharacter_spec X

end Paper18.Category.Drinfeld
