import Paper18.Category.FixedBoundaryGrading

/-! # The actual grading character of an order-two invertible object -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  {T : C} (B : TensorInverse T)

/-- The actual square isomorphism forces monodromy to be an involution
on every actual object. The proof uses the two braiding hexagons through
the previously derived monodromy tensor identity. -/
theorem TensorInverse.monodromy_involutive_of_square (q : T ⊗ T ≅ 𝟙_ C) (X : C) :
    B.monodromyCharacter.hom.app X ≫ B.monodromyCharacter.hom.app X = 𝟙 X := by
  letI := (B.tensor B).tensorLeftIsEquivalence
  apply (tensorLeft (T ⊗ T)).map_injective
  change (T ⊗ T) ◁ (B.monodromyCharacter.hom.app X ≫ B.monodromyCharacter.hom.app X) =
    (T ⊗ T) ◁ 𝟙 X
  rw [← B.monodromy_object_tensor B X]
  have h : Centralizes (T ⊗ T) X := (centralizes_unit_left X).of_iso_left q
  exact h.trans (MonoidalCategory.whiskerLeft_id _ _).symm

variable [Preadditive C] [Linear ℂ C]

/-- The neutral actual homogeneous category is precisely the actual
centralizer of the order-two object. -/
theorem TensorInverse.monodromy_neutral_iff (X : C) :
    FixedBoundary.Homogeneous B.monodromyCharacter 0 X ↔ Centralizes T X := by
  change B.monodromyCharacter.hom.app X = FixedBoundary.paritySign 0 • 𝟙 X ↔ _
  rw [FixedBoundary.paritySign_zero, one_smul]
  constructor
  · intro h
    change (doubleBraiding T X).hom = 𝟙 _
    rw [← B.monodromyCharacter_spec X, h]
    exact MonoidalCategory.whiskerLeft_id T X
  · intro h
    letI := B.tensorLeftIsEquivalence
    apply (tensorLeft T).map_injective
    change T ◁ B.monodromyCharacter.hom.app X = T ◁ 𝟙 X
    rw [B.monodromyCharacter_spec X, h]
    exact (MonoidalCategory.whiskerLeft_id T X).symm

variable [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

include S in
/-- A nontrivial actual invertible object in a nondegenerate category
has a nontrivial actual monodromy character. -/
theorem TensorInverse.monodromy_nontrivial (hC : IsNondegenerate (C := C))
    (hT : ¬ Nonempty (T ≅ 𝟙_ C)) : B.monodromyCharacter ≠ Iso.refl (𝟭 C) := by
  intro h
  letI := B.simple S
  have ht : T ∈ mugerCenter := B.monodromyCharacter_eq_refl_iff.mp h
  exact hT ⟨isoUnitOfTransparentSimple S hC T ht⟩

include S in
/-- Every actual object has an actual homogeneous simple decomposition
for the grading induced by the order-two invertible object. -/
theorem TensorInverse.orderTwo_homogeneous_decomposition (q : T ⊗ T ≅ 𝟙_ C) (X : C) :
    ∃ (n : ℕ) (Y : Fin n → C) (g : Fin n → ZMod 2),
      (∀ j, Simple (Y j) ∧ FixedBoundary.Homogeneous B.monodromyCharacter (g j) (Y j)) ∧
        Nonempty (X ≅ ⨁ Y) :=
  FixedBoundary.exists_homogeneous_decomposition B.monodromyCharacter
    (B.monodromy_involutive_of_square q) S X

end Paper18.Category
