import Paper18.Category.Braided
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.CategoryTheory.Retract

/-!
# Closure of actual categorical centralizers

These results use naturality and the hexagon equations of the braiding.
They concern actual morphisms and biproducts, with no scalar monodromy model.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Limits
open scoped BigOperators
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

@[reassoc]
lemma doubleBraiding_naturality_left {X X' : C} (f : X ⟶ X') (Y : C) :
    (f ▷ Y) ≫ (doubleBraiding X' Y).hom =
      (doubleBraiding X Y).hom ≫ (f ▷ Y) := by
  simp only [doubleBraiding, Iso.trans_hom, ← assoc]
  rw [braiding_naturality_left]
  simp only [assoc]
  rw [braiding_naturality_right]

/-- Centralization descends to an actual retract, without semisimplicity. -/
lemma Centralizes.of_retract_left {X X' Y : C} (r : Retract X X')
    (h : Centralizes X' Y) : Centralizes X Y := by
  have hnat := doubleBraiding_naturality_left r.i Y
  rw [h, comp_id] at hnat
  have hs := congrArg (fun f => f ≫ (r.r ▷ Y)) hnat
  simpa only [assoc, ← comp_whiskerRight, r.retract, id_whiskerRight, comp_id] using hs.symm

lemma Centralizes.of_retract_right {X Y Y' : C} (r : Retract Y Y')
    (h : Centralizes X Y') : Centralizes X Y :=
  (h.symm.of_retract_left r).symm

lemma centralizer_tensor {S : Set C} {X X' : C}
    (h : X ∈ centralizer S) (h' : X' ∈ centralizer S) :
    X ⊗ X' ∈ centralizer S := fun Y hY => (h Y hY).tensor_left (h' Y hY)

lemma centralizer_retract {S : Set C} {X X' : C} (r : Retract X X')
    (h : X' ∈ centralizer S) : X ∈ centralizer S :=
  fun Y hY => (h Y hY).of_retract_left r

/-- The full centralizer is an actual braided monoidal full subcategory. -/
def centralizerProperty (S : Set C) : ObjectProperty C := centralizer S

instance centralizerProperty_isMonoidal (S : Set C) :
    (centralizerProperty S).IsMonoidal where
  prop_unit := unit_mem_centralizer S
  prop_tensor _ _ := centralizer_tensor

abbrev CentralizerCategory (S : Set C) := (centralizerProperty S).FullSubcategory

/-- The fully faithful braided tensor inclusion of an actual centralizer. -/
abbrev centralizerInclusion (S : Set C) : CentralizerCategory S ⥤ C :=
  (centralizerProperty S).ι

section Additive
variable [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C]

/-- Centralization of a finite direct sum is determined by its summands. -/
lemma centralizes_biproduct_left {J : Type} [Fintype J] (f : J → C) (Y : C)
    (h : ∀ j, Centralizes (f j) Y) : Centralizes (⨁ f) Y := by
  have hj (j : J) : (biproduct.ι f j ▷ Y) ≫ (doubleBraiding (⨁ f) Y).hom =
      biproduct.ι f j ▷ Y := by
    rw [doubleBraiding_naturality_left, h j, id_comp]
  have hid : ∑ j : J, (biproduct.π f j ▷ Y) ≫ (biproduct.ι f j ▷ Y) =
      𝟙 ((⨁ f) ⊗ Y) := by
    simp only [← comp_whiskerRight, ← sum_whiskerRight]
    rw [biproduct.total, id_whiskerRight]
  change (doubleBraiding (⨁ f) Y).hom = _
  calc
    _ = (∑ j : J, (biproduct.π f j ▷ Y) ≫ (biproduct.ι f j ▷ Y)) ≫
        (doubleBraiding (⨁ f) Y).hom := by rw [hid, id_comp]
    _ = ∑ j : J, (biproduct.π f j ▷ Y) ≫ (biproduct.ι f j ▷ Y) := by
      simp only [Preadditive.sum_comp, assoc, hj]
    _ = _ := hid

lemma centralizes_biproduct_left_iff {J : Type} [Fintype J] (f : J → C) (Y : C) :
    Centralizes (⨁ f) Y ↔ ∀ j, Centralizes (f j) Y := by
  constructor
  · intro h j
    exact h.of_retract_left
      { i := biproduct.ι f j
        r := biproduct.π f j
        retract := by simp }
  · exact centralizes_biproduct_left f Y

lemma centralizer_biproduct {J : Type} [Fintype J] {S : Set C} (f : J → C)
    (h : ∀ j, f j ∈ centralizer S) : (⨁ f) ∈ centralizer S :=
  fun Y hY => centralizes_biproduct_left f Y (fun j => h j Y hY)

lemma centralizer_biproduct_iff {J : Type} [Fintype J] {S : Set C} (f : J → C) :
    (⨁ f) ∈ centralizer S ↔ ∀ j, f j ∈ centralizer S := by
  constructor
  · intro h j Y hY
    exact (centralizes_biproduct_left_iff f Y).mp (h Y hY) j
  · exact centralizer_biproduct f

end Additive
end Paper18.Category
