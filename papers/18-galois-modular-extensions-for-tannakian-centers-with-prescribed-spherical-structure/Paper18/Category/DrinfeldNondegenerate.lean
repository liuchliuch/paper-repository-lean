import Paper18.Category.DrinfeldBiproducts
import Paper18.Category.NondegenerateBasic

/-!
# Nondegeneracy of the center of a nondegenerate category

The positive and negative canonical images detect every transparent object
of the center. Consequently a transparent central object lifts a transparent
underlying object. If the original category is nondegenerate, that object is
an actual finite sum of units; so is the object in the center.
-/
noncomputable section
universe v u
namespace Paper18.Category.Drinfeld

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits CategoryTheory.Functor.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C]

/-- The canonical positive embedding sends actual unit sums to actual unit
sums, using its proved additive and strong monoidal structures. -/
lemma positive_unitSum {X : C} (hX : IsUnitSum X) :
    IsUnitSum ((positive C).obj X) := by
  obtain ⟨n, ⟨e⟩⟩ := hX
  refine ⟨n, ⟨(positive C).mapIso e ≪≫ (positive C).mapBiproduct
    (fun _ : Fin n => 𝟙_ C) ≪≫ biproduct.mapIso (fun _ => (εIso (positive C)).symm)⟩⟩

omit [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C]
  [MonoidalLinear ℂ C] [HasFiniteBiproducts C] in
/-- Every object transparent in the center is canonically a positive lift,
and its underlying object is transparent in the original category. -/
theorem transparent_underlying (Z : Center C) (hZ : Z ∈ mugerCenter) :
    Z.1 ∈ mugerCenter := by
  intro Y _
  have hp := hZ ((positive C).obj Y) (Set.mem_univ _)
  have hn := hZ ((negative C).obj Y) (Set.mem_univ _)
  have hγ := (centralizes_negative_iff Z Y).mp hn
  have h := congrArg Center.Hom.f hp
  change (Z.2.β Y).hom ≫ (β_ Y Z.1).hom = 𝟙 _ at h
  rw [hγ] at h
  exact h

/-- Actual Müger nondegeneracy passes from a braided linear category
to its Drinfeld center. No factorization equivalence is an input. -/
theorem nondegenerate_of_nondegenerate (hC : IsNondegenerate (C := C)) :
    IsNondegenerate (C := Center C) := by
  intro Z hZ
  apply IsUnitSum.of_iso (isoPositiveOfCentralizes Z
    (fun Y => hZ ((negative C).obj Y) (Set.mem_univ _)))
  exact positive_unitSum (hC Z.1 (transparent_underlying Z hZ))

end Paper18.Category.Drinfeld
