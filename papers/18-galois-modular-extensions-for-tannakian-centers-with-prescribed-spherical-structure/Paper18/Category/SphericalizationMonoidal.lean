import Paper18.Category.SphericalizationSquare
import Paper18.Category.SphericalizationBraided
import Paper18.Category.RadfordBraidedMonoidal
import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Actual braided sphericalization

The canonical Radford square condition is closed under tensor product, the unit,
and right duals. Its full category consequently inherits actual monoidal,
braided, rigid and pivotal structures. Sphericality is proved from the actual
trace characterization of the Radford map.
-/
noncomputable section
universe v u
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]

lemma radfordSquareProperty_unit :
    radfordSquareProperty (𝟙_ (Pivotalized C)) := by
  change ε (doubleDualFunctor C) ≫
    (doubleDualFunctor C).map (ε (doubleDualFunctor C)) = (braidedFourDualIso (𝟙_ C)).hom
  rw [braidedFourDualIso_unit, Functor.LaxMonoidal.comp_ε]

lemma radfordSquareProperty_tensor {X Y : Pivotalized C}
    (hX : radfordSquareProperty X) (hY : radfordSquareProperty Y) :
    radfordSquareProperty (X ⊗ Y) := by
  change ((X.phi.hom ⊗ₘ Y.phi.hom) ≫ μ (doubleDualFunctor C) X.obj Y.obj) ≫
    (doubleDualFunctor C).map
      ((X.phi.hom ⊗ₘ Y.phi.hom) ≫ μ (doubleDualFunctor C) X.obj Y.obj) =
        (braidedFourDualIso (X.obj ⊗ Y.obj)).hom
  rw [Functor.map_comp, assoc, ← Functor.LaxMonoidal.μ_natural_assoc,
    ← assoc, tensorHom_comp_tensorHom, hX, hY]
  rw [braidedFourDualIso_tensor, Functor.LaxMonoidal.comp_μ]

/-- The actual Radford square property is a monoidal object property. -/
instance radfordSquareProperty_isMonoidal :
    (radfordSquareProperty (C := C)).IsMonoidal where
  prop_unit := radfordSquareProperty_unit
  prop_tensor _ _ := radfordSquareProperty_tensor

namespace Sphericalized

/-- The square category has the actual inherited braided monoidal structure. -/
instance inclusion_monoidal : (inclusion (C := C)).Monoidal :=
  inferInstanceAs (radfordSquareProperty (C := C)).ι.Monoidal

instance inclusion_braided : (inclusion (C := C)).Braided :=
  inferInstanceAs (radfordSquareProperty (C := C)).ι.Braided

/-- The actual forgetful functor is strong monoidal. -/
instance forget_monoidal : (forget (C := C)).Monoidal :=
  inferInstanceAs (inclusion ⋙ Pivotalized.forget).Monoidal

/-- The actual forgetful functor preserves the actual braiding. -/
instance forget_braided : (forget (C := C)).Braided :=
  inferInstanceAs (inclusion ⋙ Pivotalized.forget).Braided

/-- The inherited actual right pairing has exactly the ambient cup and cap. -/
def rightExactPairing (X : Sphericalized C) :
    ExactPairing X (⟨dual (Pivotalized C) X.obj,
      radfordSquareProperty_dual X.property⟩ : Sphericalized C) where
  coevaluation' := η_ X.obj (dual (Pivotalized C) X.obj)
  evaluation' := ε_ X.obj (dual (Pivotalized C) X.obj)
  coevaluation_evaluation' := ExactPairing.coevaluation_evaluation X.obj
    (dual (Pivotalized C) X.obj)
  evaluation_coevaluation' := ExactPairing.evaluation_coevaluation X.obj
    (dual (Pivotalized C) X.obj)

/-- The square category is actually right rigid, with no extra dual data. -/
instance rightRigidCategory : RightRigidCategory (Sphericalized C) where
  rightDual X :=
    { rightDual := ⟨dual (Pivotalized C) X.obj, radfordSquareProperty_dual X.property⟩
      exact := rightExactPairing X }

/-- The tautological actual pivotal structure restricts to the square
category. Its coherence equations are the ambient coherence equations. -/
def pivotalStructure : PivotalStructure (Sphericalized C) where
  j :=
    { hom :=
        { app X := Pivotalized.pivotalStructure.j.hom.app X.obj
          naturality _ _ f := Pivotalized.pivotalStructure.j.hom.naturality f }
      inv :=
        { app X := Pivotalized.pivotalStructure.j.inv.app X.obj
          naturality _ _ f := Pivotalized.pivotalStructure.j.inv.naturality f }
      hom_inv_id := by ext X; exact Pivotalized.pivotalStructure.j.hom_inv_id_app X.obj
      inv_hom_id := by ext X; exact Pivotalized.pivotalStructure.j.inv_hom_id_app X.obj }
  unit := Pivotalized.pivotalStructure.unit
  tensor X Y := Pivotalized.pivotalStructure.tensor X.obj Y.obj

/-- Sphericality is a theorem of the constructed category: both actual
traces agree on every actual endomorphism. -/
theorem pivotalStructure_spherical : (pivotalStructure (C := C)).Spherical := by
  intro X f
  exact radfordSquareProperty_trace X.property f

/-- The two actual traces in sphericalization are the ambient cap/cup
traces with the chosen square-root identification. -/
lemma rightTrace_forget (X : Sphericalized C) (f : X ⟶ X) :
    (forget.map ((pivotalStructure (C := C)).rightTrace f)) =
      η_ X.obj.obj (dual C X.obj.obj) ≫ f.hom ▷ dual C X.obj.obj ≫
        X.obj.phi.hom ▷ dual C X.obj.obj ≫
          ε_ (dual C X.obj.obj) (dual C (dual C X.obj.obj)) :=
  Pivotalized.rightTrace_hom X.obj f

end Sphericalized
end Paper18.Category
