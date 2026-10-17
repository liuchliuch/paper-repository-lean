import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-!
# Centralization by the actual double braiding

Unlike the numerical fusion shadows, these definitions concern objects and morphisms
of a mathlib braided monoidal category. No nondegeneracy or modularity is assumed.
-/

universe v u v₁ u₁

namespace Paper18.Category

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Functor.LaxMonoidal
open CategoryTheory.Functor.OplaxMonoidal CategoryTheory.Functor.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The monodromy automorphism of `X ⊗ Y`. -/
def doubleBraiding (X Y : C) : X ⊗ Y ≅ X ⊗ Y := β_ X Y ≪≫ β_ Y X

/-- Two objects centralize one another when their double braiding is the identity. -/
def Centralizes (X Y : C) : Prop := (doubleBraiding X Y).hom = 𝟙 (X ⊗ Y)

lemma centralizes_iff (X Y : C) :
    Centralizes X Y ↔ (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 (X ⊗ Y) := Iff.rfl

lemma centralizes_iff_braiding_inv (X Y : C) :
    Centralizes X Y ↔ (β_ Y X).hom = (β_ X Y).inv := by
  change (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _ ↔ _
  constructor
  · intro h
    calc
      (β_ Y X).hom = (β_ X Y).inv ≫ ((β_ X Y).hom ≫ (β_ Y X).hom) := by simp
      _ = (β_ X Y).inv := by rw [h, comp_id]
  · intro h
    rw [h, Iso.hom_inv_id]

lemma Centralizes.symm {X Y : C} (h : Centralizes X Y) : Centralizes Y X := by
  rw [centralizes_iff] at h ⊢
  rw [(centralizes_iff_braiding_inv X Y).mp h, Iso.inv_hom_id]

lemma centralizes_comm (X Y : C) : Centralizes X Y ↔ Centralizes Y X :=
  ⟨Centralizes.symm, Centralizes.symm⟩

@[simp] lemma centralizes_unit_left (X : C) : Centralizes (𝟙_ C) X := by
  simp [Centralizes, doubleBraiding]

@[simp] lemma centralizes_unit_right (X : C) : Centralizes X (𝟙_ C) :=
  (centralizes_unit_left X).symm

/-- Centralization is closed under tensor product in the first argument. -/
lemma Centralizes.tensor_left {X Y Z : C} (hX : Centralizes X Z)
    (hY : Centralizes Y Z) : Centralizes (X ⊗ Y) Z := by
  rw [centralizes_iff_braiding_inv] at hX hY ⊢
  rw [braiding_tensor_right_hom, braiding_tensor_left_inv, hX, hY]

/-- Centralization is closed under tensor product in the second argument. -/
lemma Centralizes.tensor_right {X Y Z : C} (hY : Centralizes X Y)
    (hZ : Centralizes X Z) : Centralizes X (Y ⊗ Z) :=
  (hY.symm.tensor_left hZ.symm).symm

/-- The object set of the categorical centralizer of a collection of objects. -/
def centralizer (S : Set C) : Set C := {X | ∀ Y ∈ S, Centralizes X Y}

/-- The actual Müger center: objects centralizing every object. -/
def mugerCenter : Set C := centralizer Set.univ

@[simp] lemma mem_centralizer {S : Set C} {X : C} :
    X ∈ centralizer S ↔ ∀ Y ∈ S, Centralizes X Y := Iff.rfl

@[simp] lemma unit_mem_centralizer (S : Set C) : (𝟙_ C) ∈ centralizer S := by
  intro Y _
  exact centralizes_unit_left Y

lemma tensor_mem_centralizer {S : Set C} {X Y : C}
    (hX : X ∈ centralizer S) (hY : Y ∈ centralizer S) : X ⊗ Y ∈ centralizer S := by
  intro Z hZ
  exact (hX Z hZ).tensor_left (hY Z hZ)

@[simp] lemma centralizer_empty : centralizer (∅ : Set C) = Set.univ := by
  ext X
  simp [centralizer]

lemma centralizer_antitone {S T : Set C} (h : S ⊆ T) : centralizer T ⊆ centralizer S := by
  intro X hX Y hY
  exact hX Y (h hY)

lemma subset_double_centralizer (S : Set C) : S ⊆ centralizer (centralizer S) := by
  intro X hX Y hY
  exact (hY X hX).symm

lemma triple_centralizer (S : Set C) :
    centralizer (centralizer (centralizer S)) = centralizer S := by
  apply Set.Subset.antisymm
  · exact centralizer_antitone (subset_double_centralizer S)
  · exact subset_double_centralizer (centralizer S)

/-- Transparency is invariant under isomorphism in the first argument. -/
lemma Centralizes.of_iso_left {X X' Y : C} (i : X ≅ X')
    (h : Centralizes X' Y) : Centralizes X Y := by
  rw [centralizes_iff] at h ⊢
  apply (cancel_mono (i.hom ▷ Y)).1
  simp only [assoc, id_comp]
  rw [← braiding_naturality_right, ← assoc, ← braiding_naturality_left, assoc, h, comp_id]

lemma centralizes_iso_left {X X' Y : C} (i : X ≅ X') :
    Centralizes X Y ↔ Centralizes X' Y :=
  ⟨fun h => h.of_iso_left i.symm, fun h => h.of_iso_left i⟩

lemma centralizes_iso_right {X Y Y' : C} (i : Y ≅ Y') :
    Centralizes X Y ↔ Centralizes X Y' := by
  rw [centralizes_comm X Y, centralizes_comm X Y', centralizes_iso_left i]

variable {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [BraidedCategory D]

/-- The tensorator intertwines actual monodromy, for a braided strong monoidal functor. -/
lemma tensorator_map_doubleBraiding (F : C ⥤ D) [F.Braided] (X Y : C) :
    μ F X Y ≫ F.map (doubleBraiding X Y).hom =
      (doubleBraiding (F.obj X) (F.obj Y)).hom ≫ μ F X Y := by
  simp only [doubleBraiding, Iso.trans_hom, F.map_comp]
  rw [Functor.LaxBraided.braided_assoc, Functor.LaxBraided.braided]
  simp only [assoc]

lemma Centralizes.map {X Y : C} (h : Centralizes X Y) (F : C ⥤ D) [F.Braided] :
    Centralizes (F.obj X) (F.obj Y) := by
  apply (cancel_mono (μ F X Y)).1
  rw [← tensorator_map_doubleBraiding, h, F.map_id, comp_id, id_comp]

/-- Faithful braided tensor functors reflect centralization. Fullness is unnecessary. -/
lemma centralizes_map_iff (F : C ⥤ D) [F.Braided] [F.Faithful] (X Y : C) :
    Centralizes (F.obj X) (F.obj Y) ↔ Centralizes X Y := by
  constructor
  · intro h
    apply F.map_injective
    apply (cancel_epi (μ F X Y)).1
    rw [tensorator_map_doubleBraiding, h, F.map_id, comp_id, id_comp]
  · intro h
    exact h.map F

/-- Centralizing an image collection is exactly the original condition under a faithful
braided tensor functor. -/
lemma centralizer_image_iff (F : C ⥤ D) [F.Braided] [F.Faithful] (S : Set C) (X : C) :
    F.obj X ∈ centralizer (F.obj '' S) ↔ X ∈ centralizer S := by
  constructor
  · intro h Y hY
    exact (centralizes_map_iff F X Y).mp (h (F.obj Y) ⟨Y, hY, rfl⟩)
  · intro h Y hY
    obtain ⟨Z, hZ, rfl⟩ := hY
    exact (h Z hZ).map F

end Paper18.Category
