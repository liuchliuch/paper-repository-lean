import Paper18.Category.FusionSubcategoryBasic
import Paper18.Category.RigidMultiplicity
import Paper18.Category.PivotalFunctor

/-!
# Nondegeneracy and modularity of actual braided categories

Nondegeneracy means that every actual transparent object is a finite direct
sum of tensor units. No invertibility of an externally supplied matrix is
part of this definition.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [HasFiniteBiproducts C] [MonoidalPreadditive C]

/-- An actual object is a finite direct sum of tensor units. -/
def IsUnitSum (X : C) : Prop :=
  ∃ n : ℕ, Nonempty (X ≅ ⨁ fun _ : Fin n => 𝟙_ C)

omit [BraidedCategory C] [MonoidalPreadditive C] in
lemma IsUnitSum.of_iso {X Y : C} (e : X ≅ Y) (hY : IsUnitSum Y) : IsUnitSum X := by
  obtain ⟨n, ⟨f⟩⟩ := hY
  exact ⟨n, ⟨e ≪≫ f⟩⟩

lemma unitSum_mem_mugerCenter {X : C} (hX : IsUnitSum X) : X ∈ mugerCenter := by
  obtain ⟨n, ⟨e⟩⟩ := hX
  intro Y _
  apply Centralizes.of_iso_left e
  exact centralizes_biproduct_left _ Y (fun _ => centralizes_unit_left Y)

/-- Actual Müger nondegeneracy. -/
def IsNondegenerate : Prop := ∀ X : C, X ∈ mugerCenter → IsUnitSum X

lemma nondegenerate_iff_mugerCenter : IsNondegenerate (C := C) ↔
    mugerCenter (C := C) = {X | IsUnitSum X} := by
  constructor
  · intro h
    ext X
    exact ⟨h X, unitSum_mem_mugerCenter⟩
  · intro h X hX
    simpa only [h, Set.mem_setOf_eq] using hX

/-- The actual Müger center inherits a symmetric category structure. -/
instance mugerCenter_symmetric : SymmetricCategory (CentralizerCategory (Set.univ : Set C)) where
  symmetry X Y := by
    change (β_ X.obj Y.obj).hom ≫ (β_ Y.obj X.obj).hom = 𝟙 _
    exact X.property Y.obj (Set.mem_univ _)

section Skeleton
variable [Linear ℂ C] [HasKernels C] [MonoidalLinear ℂ C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [Simple (𝟙_ C)] {ι : Type w} [Fintype ι]
  (S : FiniteSemisimpleSkeleton C ι)

omit [MonoidalLinear ℂ C] in
/-- For a semisimple category, Müger nondegeneracy can be checked on the
actual chosen simple objects. -/
lemma nondegenerate_iff_simple_center : IsNondegenerate (C := C) ↔
    ∀ i, S.simpleObject i ∈ mugerCenter → i = S.unitLabel := by
  constructor
  · intro h i hi
    obtain ⟨n, ⟨e⟩⟩ := h (S.simpleObject i) hi
    by_contra hne
    have hz : S.multiplicity (𝟙_ C) i = 0 := by
      rw [← S.multiplicity_iso S.unitIso i, S.multiplicity_simple]
      simp [hne]
    have he : S.multiplicity (S.simpleObject i) i =
        ∑ _ : Fin n, S.multiplicity (𝟙_ C) i := by
      rw [S.multiplicity_iso e, S.multiplicity_biproduct]
    simp [hz] at he
  · intro h X hX
    have hl (a : Fin (S.length X)) : S.label X a = S.unitLabel := by
      apply h
      have hp := S.property_label (centralizerProperty (Set.univ : Set C))
        (⟨X, hX⟩ : CentralizerCategory (Set.univ : Set C)) a
      exact hp
    refine ⟨S.length X, ⟨S.decomposition X ≪≫ biproduct.mapIso (fun a => ?_)⟩⟩
    exact eqToIso (congrArg S.simpleObject (hl a)) ≪≫ S.unitIso

end Skeleton

section Pivotal
variable [RightRigidCategory C]
/-- A prescribed spherical pivotal structure together with actual Müger
nondegeneracy is a modular structure in the sense used in the paper. -/
def IsModular (J : PivotalStructure C) : Prop := J.Spherical ∧ IsNondegenerate (C := C)

end Pivotal
end Paper18.Category
