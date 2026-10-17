import Paper18.Category.DrinfeldCharacter
import Paper18.Category.FactorizationEssentialSurjective
import Paper18.Category.InvertibleObjects

/-! # Actual simple factorizations of central tensor characters

The actual finite semisimple skeleton of the center is explicit here; this
file does not assume or assert that its existence has already been proved.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w t
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (J : PivotalStructure C)
  {κ : Type t} [Fintype κ] (T : FiniteSemisimpleSkeleton (Center C) κ)
  (hC : IsNondegenerate (C := C))
  (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]

include J T hC in
theorem character_simple_pair : ∃ i j : ι, Nonempty
    ((positive C).obj (S.simpleObject i) ⊗ (negative C).obj (S.simpleObject j) ≅
      characterObject χ) := by
  let E := factorizationEquivalenceOfCenterSkeleton S J T hC
  let F := deligneFactorization C
  let P := E.inverse.obj (characterObject χ)
  let D := DeligneProduct.skeleton S S
  letI := DeligneProduct.hasKernels S S
  letI := (deligneFactorizationFullyFaithful S hC).full
  letI := (deligneFactorizationFullyFaithful S hC).faithful
  letI : Simple (characterObject χ).1 := inferInstanceAs (Simple (𝟙_ C))
  letI : Simple (characterObject χ) := simple_of_underlying_simple _
  letI : Simple ((𝟭 (Center C)).obj (characterObject χ)) :=
    inferInstanceAs (Simple (characterObject χ))
  letI : Simple (F.obj P) := Simple.of_iso (E.counitIso.app (characterObject χ))
  letI : Simple P := by
    apply D.simple_of_finrank_end_eq_one
    exact (fullyFaithfulHomLinearEquiv F P P).finrank_eq.trans
      (finrank_endomorphism_simple_eq_one ℂ (F.obj P))
  obtain ⟨⟨i,j⟩, ⟨e⟩⟩ := D.simple_isomorphic_representative P
  exact ⟨i,j, ⟨(deligneFactorizationPairIso (S.simpleObject i) (S.simpleObject j)).symm ≪≫
    F.mapIso e.symm ≪≫ E.counitIso.app (characterObject χ)⟩⟩

/-- The two simple factors are actual tensor inverses, as witnessed by
forgetting their actual central isomorphism to the unit. -/
def inverseOfCharacterPair {i j : ι}
    (e : (positive C).obj (S.simpleObject i) ⊗ (negative C).obj (S.simpleObject j) ≅
      characterObject χ) : TensorInverse (S.simpleObject i) where
  inverse := S.simpleObject j
  right := (Center.forget C).mapIso e
  left := (β_ (S.simpleObject j) (S.simpleObject i)) ≪≫ (Center.forget C).mapIso e

end Paper18.Category.Drinfeld
