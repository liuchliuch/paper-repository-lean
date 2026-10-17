import Paper18.Category.CrossedBraidedGaugingCrossing
import Paper18.Category.CrossedBraidedGaugingComponents
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-! # The actual underlying gauging crossing

Actual homogeneous kernel images, actual biproduct preservation, and the
actual closed crossings construct an isomorphism on arbitrary objects.
Equivariance and the two braiding hexagons are proved separately.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w t
namespace Paper18.Category.CrossedBraidedGauging
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- Additivity preserves an actual finite biproduct in every indexing
universe, by the actual total identity of its bicone. -/
def preservesFiniteBiproductOfAdditive {J : Type t} [Fintype J]
    (F : C ⥤ C) [F.Additive] (f : J → C) : PreservesBiproduct f F where
  preserves hb := ⟨isBilimitOfTotal _ (by
    simp only [Functor.mapBicone_π, Functor.mapBicone_ι, ← F.map_comp]
    erw [← F.map_sum, IsBilimit.total hb, CategoryTheory.Functor.map_id]
    rfl)⟩

@[reassoc] theorem mapBiproduct_inclusion {J : Type t} [Fintype J]
    (F : C ⥤ C) [F.Additive] (f : J → C) [HasBiproduct f]
    [PreservesBiproduct f F] (j : J) :
    F.map (biproduct.ι f j) ≫ (F.mapBiproduct f).hom =
      biproduct.ι (F.obj ∘ f) j := by
  let e := F.mapBiproduct f
  have hi : biproduct.ι (F.obj ∘ f) j ≫ e.inv = F.map (biproduct.ι f j) := by
    rw [Functor.mapBiproduct_inv, biproduct.ι_desc]
  change F.map (biproduct.ι f j) ≫ e.hom = _
  rw [← hi, Category.assoc, e.inv_hom_id, Category.comp_id]


variable [MonoidalCategory C] [MonoidalPreadditive C]
  {G : Type w} [Group G] [Fintype G]
  {P : Grading G C} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  {Q : GradedAction P A} (B : CrossedBraiding P A Q)
  [HasKernels C] [HasFiniteBiproducts C]

/-- The genuine closed crossed isomorphisms on all actual degree images
assemble into an actual isomorphism on arbitrary objects. -/
def CrossedBraiding.halfSwapIso (X : C) (Y : A.Equivariant) :
    X ⊗ Y.obj ≅ Y.obj ⊗ X := by
  let f := fun g : G => P.component g X
  let R := (tensoringRight C).obj Y.obj
  let L := (tensoringLeft C).obj Y.obj
  letI : PreservesBiproduct f R := preservesFiniteBiproductOfAdditive R f
  letI : PreservesBiproduct f L := preservesFiniteBiproductOfAdditive L f
  exact whiskerRightIso (P.decompositionIso X) Y.obj ≪≫ R.mapBiproduct f ≪≫
    biproduct.mapIso (fun g : G => B.blockIso g (P.component g X) (P.component_homogeneous g X) Y) ≪≫
      (L.mapBiproduct f).symm ≪≫ whiskerLeftIso Y.obj (P.decompositionIso X).symm

namespace Grading
variable (P)

/-- The actual homogeneous summand inclusions are the actual inclusions
of the constructed complete biproduct decomposition. -/
@[reassoc] theorem componentInclusion_decompositionIso_hom (g : G) (X : C) :
    P.componentInclusion g X ≫ (P.decompositionIso X).hom =
      biproduct.ι (fun h : G => P.component h X) g := by
  apply biproduct.hom_ext
  intro h
  rw [Category.assoc, P.decompositionIso_hom, biproduct.lift_π]
  by_cases hgh : g = h
  · subst h
    simpa only [biproduct.ι_π_self] using P.componentInclusion_projection g X
  · rw [P.componentInclusion_projection_of_ne hgh, biproduct.ι_π_ne _ hgh]

/-- The actual tensor product preserves the total degree decomposition. -/
theorem component_tensorRight_total (X Y : C) :
    ∑ g : G, (P.componentProjection g X ▷ Y) ≫ (P.componentInclusion g X ▷ Y) =
      𝟙 (X ⊗ Y) := by
  simp only [← comp_whiskerRight, P.componentProjection_inclusion]
  rw [← sum_whiskerRight, P.total, id_whiskerRight]

/-- Equality of actual morphisms out of a tensor product is detected on
all actual homogeneous degree inclusions. -/
theorem tensorRight_hom_ext {X Y Z : C} {f h : X ⊗ Y ⟶ Z}
    (hh : ∀ g : G, (P.componentInclusion g X ▷ Y) ≫ f =
      (P.componentInclusion g X ▷ Y) ≫ h) : f = h := by
  calc
    f = (∑ g : G, (P.componentProjection g X ▷ Y) ≫
        (P.componentInclusion g X ▷ Y)) ≫ f := by
      rw [P.component_tensorRight_total]
      erw [Category.id_comp]
    _ = (∑ g : G, (P.componentProjection g X ▷ Y) ≫
        (P.componentInclusion g X ▷ Y)) ≫ h := by
      simp only [Preadditive.sum_comp, Category.assoc, hh]
    _ = h := by
      rw [P.component_tensorRight_total]
      erw [Category.id_comp]

end Grading
end Paper18.Category.CrossedBraidedGauging
