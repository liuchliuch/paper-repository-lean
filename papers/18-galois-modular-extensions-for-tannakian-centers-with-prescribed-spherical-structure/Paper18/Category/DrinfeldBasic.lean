import Paper18.Category.Braided
import Mathlib.CategoryTheory.Monoidal.Center

/-!
# The two canonical embeddings into the actual Drinfeld center

The positive embedding uses the given braiding and the negative embedding uses
its reverse. Their essential images are each other's categorical centralizers.
All assertions concern actual half-braidings and actual morphisms.
-/

noncomputable section
universe v u

namespace Paper18.Category.Drinfeld

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Functor.LaxMonoidal

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- The positive lift, with half-braiding `β X Y`. -/
abbrev positive : C ⥤ Center C := Center.ofBraided C

/-- The negative lift, with half-braiding `(β Y X)⁻¹`. -/
def negative : C ⥤ Center C :=
  @Center.ofBraided C _ _ (reverseBraiding C)

instance positive_faithful : (positive C).Faithful where
  map_injective h := congrArg Center.Hom.f h

instance positive_full : (positive C).Full where
  map_surjective f := ⟨f.f, by ext; rfl⟩

instance negative_faithful : (negative C).Faithful where
  map_injective h := congrArg Center.Hom.f h

instance negative_full : (negative C).Full where
  map_surjective f := ⟨f.f, by ext; rfl⟩

instance positive_braided : (positive C).Braided where
  braided X Y := by
    apply Center.ext
    change 𝟙 _ ≫ (β_ X Y).hom = (β_ X Y).hom ≫ 𝟙 _
    simp

instance negative_monoidal : (negative C).Monoidal :=
  by delta negative; infer_instance

@[simp] lemma positive_obj_fst (X : C) : ((positive C).obj X).1 = X := rfl
@[simp] lemma negative_obj_fst (X : C) : ((negative C).obj X).1 = X := rfl
@[simp] lemma positive_obj_halfBraiding (X Y : C) :
    (((positive C).obj X).2.β Y).hom = (β_ X Y).hom := rfl
@[simp] lemma negative_obj_halfBraiding (X Y : C) :
    (((negative C).obj X).2.β Y).hom = (β_ Y X).inv := rfl

@[simp] lemma positive_map_f {X Y : C} (f : X ⟶ Y) :
    ((positive C).map f).f = f := rfl
@[simp] lemma negative_map_f {X Y : C} (f : X ⟶ Y) :
    ((negative C).map f).f = f := rfl

@[simp] lemma negative_ε_f : (ε (negative C)).f = 𝟙 (𝟙_ C) := rfl

@[simp] lemma negative_μ_f (X Y : C) : (μ (negative C) X Y).f = 𝟙 (X ⊗ Y) := rfl

/-- Forgetting either canonical lift gives the identity functor. -/
def positiveForget : positive C ⋙ Center.forget C ≅ 𝟭 C := Iso.refl _

/-- Forgetting the negative lift gives the identity functor. -/
def negativeForget : negative C ⋙ Center.forget C ≅ 𝟭 C := Iso.refl _

variable {C}

omit [BraidedCategory C] in
/-- The unit component is forced by half-braiding coherence, even though it
is not a separately supplied field of `HalfBraiding`. -/
lemma halfBraiding_unit (X : C) (b : HalfBraiding X) :
    (b.β (𝟙_ C)).hom = (ρ_ X).hom ≫ (λ_ X).inv := by
  have h := congrArg Center.Hom.f
    (braiding_tensorUnit_right (C := Center C) (⟨X, b⟩ : Center C))
  simpa only [Center.comp_f, Center.rightUnitor_hom_f, Center.leftUnitor_inv_f] using h

/-- The two canonical images centralize each other. -/
lemma positive_centralizes_negative (X Y : C) :
    Centralizes ((positive C).obj X) ((negative C).obj Y) := by
  apply Center.ext
  change (β_ X Y).hom ≫ (β_ X Y).inv = 𝟙 _
  simp

/-- The centralization equation recovers the entire negative half-braiding. -/
lemma centralizes_positive_iff (Z : Center C) (Y : C) :
    Centralizes Z ((positive C).obj Y) ↔ (Z.2.β Y).hom = (β_ Y Z.1).inv := by
  constructor
  · intro h
    have h' := congrArg Center.Hom.f h
    change (Z.2.β Y).hom ≫ (β_ Y Z.1).hom = 𝟙 _ at h'
    calc
      (Z.2.β Y).hom = ((Z.2.β Y).hom ≫ (β_ Y Z.1).hom) ≫
          (β_ Y Z.1).inv := by simp
      _ = (β_ Y Z.1).inv := by rw [h', id_comp]
  · intro h
    apply Center.ext
    change (Z.2.β Y).hom ≫ (β_ Y Z.1).hom = 𝟙 _
    rw [h]
    simp

/-- The reverse equation recovers the positive half-braiding. -/
lemma centralizes_negative_iff (Z : Center C) (Y : C) :
    Centralizes Z ((negative C).obj Y) ↔ (Z.2.β Y).hom = (β_ Z.1 Y).hom := by
  constructor
  · intro h
    have h' := congrArg Center.Hom.f h
    change (Z.2.β Y).hom ≫ (β_ Z.1 Y).inv = 𝟙 _ at h'
    calc
      (Z.2.β Y).hom = ((Z.2.β Y).hom ≫ (β_ Z.1 Y).inv) ≫
          (β_ Z.1 Y).hom := by simp
      _ = (β_ Z.1 Y).hom := by rw [h', id_comp]
  · intro h
    apply Center.ext
    change (Z.2.β Y).hom ≫ (β_ Z.1 Y).inv = 𝟙 _
    rw [h]
    simp

/-- An object centralizing the entire positive image is canonically isomorphic
to the negative lift of its underlying object. -/
def isoNegativeOfCentralizes (Z : Center C)
    (h : ∀ Y : C, Centralizes Z ((positive C).obj Y)) :
    Z ≅ (negative C).obj Z.1 :=
  Center.isoMk ⟨𝟙 _, fun Y => by
    simpa using ((centralizes_positive_iff Z Y).mp (h Y)).symm⟩

/-- The corresponding canonical isomorphism for the other image. -/
def isoPositiveOfCentralizes (Z : Center C)
    (h : ∀ Y : C, Centralizes Z ((negative C).obj Y)) :
    Z ≅ (positive C).obj Z.1 :=
  Center.isoMk ⟨𝟙 _, fun Y => by
    simpa using ((centralizes_negative_iff Z Y).mp (h Y)).symm⟩

/-- An object lies in a canonical image up to actual categorical isomorphism. -/
def essentialImage (F : C ⥤ Center C) : Set (Center C) :=
  {Z | ∃ X : C, Nonempty (Z ≅ F.obj X)}

lemma negative_mem_centralizer_positive (X : C) :
    (negative C).obj X ∈ centralizer (Set.range (positive C).obj) := by
  rintro Y ⟨Y, rfl⟩
  exact (positive_centralizes_negative Y X).symm

/-- No finiteness or semisimplicity hypothesis is needed for the exact
centralizer of the positive image inside the Drinfeld center. -/
theorem centralizer_positive :
    centralizer (Set.range (positive C).obj) = essentialImage (negative C) := by
  ext Z
  constructor
  · intro h
    exact ⟨Z.1, ⟨isoNegativeOfCentralizes Z (fun Y => h _ ⟨Y, rfl⟩)⟩⟩
  · rintro ⟨X, ⟨e⟩⟩
    intro Y hY
    exact (negative_mem_centralizer_positive X Y hY).of_iso_left e

theorem centralizer_negative :
    centralizer (Set.range (negative C).obj) = essentialImage (positive C) := by
  ext Z
  constructor
  · intro h
    exact ⟨Z.1, ⟨isoPositiveOfCentralizes Z (fun Y => h _ ⟨Y, rfl⟩)⟩⟩
  · rintro ⟨X, ⟨e⟩⟩ Y ⟨Y, rfl⟩
    exact (positive_centralizes_negative X Y).of_iso_left e

/-- The two lifts agree up to an isomorphism with identity underlying map
exactly when the original object is transparent. -/
theorem positive_iso_negative_iff (X : C) :
    (∃ e : (positive C).obj X ≅ (negative C).obj X, e.hom.f = 𝟙 X) ↔
      X ∈ mugerCenter := by
  constructor
  · rintro ⟨e, he⟩ Y _
    have h := e.hom.comm Y
    have hi : (β_ Y X).inv = (β_ X Y).hom := by simpa [he] using h
    rw [centralizes_iff, ← hi]
    simp
  · intro h
    refine ⟨Center.isoMk ⟨𝟙 _, fun Y => ?_⟩, rfl⟩
    simpa using ((centralizes_iff_braiding_inv Y X).mp
      (h Y (Set.mem_univ Y)).symm).symm

/-- The qualification on the underlying identity can be removed: any
isomorphism between the two lifts detects transparency. -/
theorem positive_iso_negative_self_iff (X : C) :
    Nonempty ((positive C).obj X ≅ (negative C).obj X) ↔ X ∈ mugerCenter := by
  constructor
  · rintro ⟨e⟩
    apply (positive_iso_negative_iff X).mp
    refine ⟨e ≪≫ (negative C).mapIso ((Center.forget C).mapIso e).symm, ?_⟩
    change e.hom.f ≫ e.inv.f = 𝟙 X
    exact congrArg Center.Hom.f e.hom_inv_id
  · intro h
    obtain ⟨e, _⟩ := (positive_iso_negative_iff X).mpr h
    exact ⟨e⟩

/-- The intersection of the canonical images is exactly the image of the
Müger center of the original braided category. -/
theorem positive_mem_essentialImage_negative_iff (X : C) :
    (positive C).obj X ∈ essentialImage (negative C) ↔ X ∈ mugerCenter := by
  constructor
  · rintro ⟨Y, ⟨e⟩⟩
    apply (positive_iso_negative_self_iff X).mp
    exact ⟨e ≪≫ (negative C).mapIso ((Center.forget C).mapIso e).symm⟩
  · intro h
    exact ⟨X, (positive_iso_negative_self_iff X).mpr h⟩

/-- A half-braiding is an actual natural isomorphism between tensor functors. -/
def halfBraidingNatIso (Z : Center C) : tensorLeft Z.1 ≅ tensorRight Z.1 :=
  NatIso.ofComponents Z.2.β (fun f => Z.2.naturality f)

/-- Comparing a half-braiding with the reverse ambient braiding gives a
natural automorphism of the tensor-by-the-underlying-object functor. -/
def monodromyNatIso (Z : Center C) : tensorLeft Z.1 ≅ tensorLeft Z.1 :=
  NatIso.ofComponents (fun Y => Z.2.β Y ≪≫ β_ Y Z.1) (fun {Y Y'} f => by
    change (Z.1 ◁ f) ≫ ((Z.2.β Y').hom ≫ (β_ Y' Z.1).hom) =
      ((Z.2.β Y).hom ≫ (β_ Y Z.1).hom) ≫ (Z.1 ◁ f)
    rw [← assoc, HalfBraiding.naturality, assoc, braiding_naturality_left, ← assoc])

@[simp] lemma monodromyNatIso_hom_app (Z : Center C) (Y : C) :
    (monodromyNatIso Z).hom.app Y = (Z.2.β Y).hom ≫ (β_ Y Z.1).hom := rfl

@[simp] lemma monodromyNatIso_positive (X Y : C) :
    (monodromyNatIso ((positive C).obj X)).hom.app Y =
      (doubleBraiding X Y).hom := rfl

/-- The natural automorphism is trivial exactly on the opposite canonical
image; this is an equality of actual natural transformations. -/
theorem monodromyNatIso_identity_iff (Z : Center C) :
    (monodromyNatIso Z).hom = 𝟙 (tensorLeft Z.1) ↔
      Z ∈ essentialImage (negative C) := by
  rw [← centralizer_positive]
  constructor
  · intro h Y hY
    obtain ⟨Y, rfl⟩ := hY
    apply Center.ext
    exact NatTrans.congr_app h Y
  · intro h
    ext Y
    exact congrArg Center.Hom.f (h _ ⟨Y, rfl⟩)

end Paper18.Category.Drinfeld
