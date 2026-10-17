import Paper18.Category.RadfordBraidedTrace
import Paper18.Category.RadfordBraidedCoherence
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The actual Radford square category

The objects are precisely actual pivotalized objects satisfying the canonical
braided four-dual square equation. Their morphisms are the actual commuting
ambient morphisms. Equality of the two traces is derived from the square
equation, not included in the objects or in a category structure.
-/
noncomputable section
universe v u
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]

/-- The actual square condition cutting sphericalization out of pivotalization. -/
def radfordSquareProperty : ObjectProperty (Pivotalized C) := fun X =>
  X.phi.hom ≫ (doubleDualFunctor C).map X.phi.hom = (braidedFourDualIso X.obj).hom

/-- The category of actual square roots of the braided four-dual comparison. -/
abbrev Sphericalized (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RightRigidCategory C] [BraidedCategory C] :=
  (radfordSquareProperty (C := C)).FullSubcategory

/-- The square equation is invariant under actual isomorphisms of
pivotalized objects. -/
theorem radfordSquareProperty_of_iso {X Y : Pivotalized C} (e : X ≅ Y)
    (hX : radfordSquareProperty X) : radfordSquareProperty Y := by
  letI : IsIso e.hom.hom := by
    change IsIso (Pivotalized.forget.map e.hom)
    infer_instance
  apply (cancel_epi e.hom.hom).mp
  have hn := (braidedFourDualNatIso (C := C)).hom.naturality e.hom.hom
  change e.hom.hom ≫ (braidedFourDualIso Y.obj).hom =
    (braidedFourDualIso X.obj).hom ≫
      (doubleDualFunctor C).map ((doubleDualFunctor C).map e.hom.hom) at hn
  dsimp only [radfordSquareProperty] at hX ⊢
  calc
    _ = X.phi.hom ≫ (doubleDualFunctor C).map (e.hom.hom ≫ Y.phi.hom) := by
      rw [Functor.map_comp, ← assoc, e.hom.comm, assoc]
    _ = X.phi.hom ≫ (doubleDualFunctor C).map
        (X.phi.hom ≫ (doubleDualFunctor C).map e.hom.hom) := by rw [e.hom.comm]
    _ = (braidedFourDualIso X.obj).hom ≫
        (doubleDualFunctor C).map ((doubleDualFunctor C).map e.hom.hom) := by
      rw [Functor.map_comp, ← assoc, hX]
    _ = _ := hn.symm

/-- The square equation is closed under the actual right dual constructed
in pivotalization. -/
theorem radfordSquareProperty_dual {X : Pivotalized C}
    (hX : radfordSquareProperty X) :
    radfordSquareProperty (dual (Pivotalized C) X) := by
  change dualMap C X.phi.inv ≫
    (doubleDualFunctor C).map (dualMap C X.phi.inv) =
      (braidedFourDualIso (dual C X.obj)).hom
  rw [braidedFourDualIso_dual]
  apply (cancel_mono (dualMapIso (braidedFourDualIso X.obj)).hom).mp
  rw [Iso.inv_hom_id]
  have hd := congrArg (dualMap C) hX
  dsimp only [radfordSquareProperty, doubleDualFunctor, dualMapIso, dualMap] at hd ⊢
  rw [← hd]
  simp only [comp_rightAdjointMate, assoc, ← comp_rightAdjointMate_assoc,
    ← comp_rightAdjointMate, Iso.hom_inv_id, Iso.inv_hom_id, rightAdjointMate_id,
    id_comp, comp_id]

/-- The square condition implies equality of all the actual pivotal traces
on the object, including the traces of non-scalar endomorphisms. -/
theorem radfordSquareProperty_trace {X : Pivotalized C}
    (hX : radfordSquareProperty X) (f : X ⟶ X) :
    (Pivotalized.pivotalStructure (C := C)).leftTrace f =
      (Pivotalized.pivotalStructure (C := C)).rightTrace f := by
  apply Pivotalized.Hom.ext
  rw [Pivotalized.leftTrace_hom, Pivotalized.rightTrace_hom]
  exact braidedFourDual_trace_of_square X.obj X.phi hX f.hom

namespace Sphericalized

/-- The fully faithful inclusion into the actual pivotalized category. -/
def inclusion : Sphericalized C ⥤ Pivotalized C := radfordSquareProperty.ι

instance : (inclusion (C := C)).Full := inferInstanceAs radfordSquareProperty.ι.Full
instance : (inclusion (C := C)).Faithful := inferInstanceAs radfordSquareProperty.ι.Faithful

/-- The actual faithful forgetful functor to the original category. -/
def forget : Sphericalized C ⥤ C := inclusion ⋙ Pivotalized.forget

instance : (forget (C := C)).Faithful := inferInstanceAs (inclusion ⋙ Pivotalized.forget).Faithful

/-- Every actual endomorphism of a square object has equal left and right
traces under its tautological pivotal identification. -/
theorem trace_eq (X : Sphericalized C) (f : X ⟶ X) :
    (Pivotalized.pivotalStructure (C := C)).leftTrace (inclusion.map f) =
      (Pivotalized.pivotalStructure (C := C)).rightTrace (inclusion.map f) :=
  radfordSquareProperty_trace X.property f

end Sphericalized
end Paper18.Category
