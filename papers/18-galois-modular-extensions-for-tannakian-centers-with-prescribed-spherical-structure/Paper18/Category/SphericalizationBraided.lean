import Paper18.Category.SphericalizationRigid
import Paper18.Category.RadfordBraidedCoherence

/-! # The actual braiding on pivotalization -/
noncomputable section
universe v u
namespace Paper18.Category
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
namespace Pivotalized

/-- The actual ambient braiding commutes with the pivotalized
identifications because canonical double dualization is braided. -/
def braiding (X Y : Pivotalized C) : X ⊗ Y ≅ Y ⊗ X :=
  mkIso (β_ X.obj Y.obj) (by
    change (β_ X.obj Y.obj).hom ≫
      ((Y.phi.hom ⊗ₘ X.phi.hom) ≫ μ (doubleDualFunctor C) Y.obj X.obj) =
        ((X.phi.hom ⊗ₘ Y.phi.hom) ≫ μ (doubleDualFunctor C) X.obj Y.obj) ≫
          (doubleDualFunctor C).map (β_ X.obj Y.obj).hom
    rw [Category.assoc, Functor.Braided.braided]
    rw [← BraidedCategory.braiding_naturality_assoc])

/-- The hexagons and naturality hold on actual morphisms, reflected by the
faithful strong monoidal forgetful functor. -/
instance braidedCategory : BraidedCategory (Pivotalized C) :=
  BraidedCategory.ofFaithful forget braiding (by
    intro X Y
    simp only [forget_μ]
    erw [id_comp, comp_id]
    rfl)

/-- Pivotalization's actual forgetful functor preserves the braiding. -/
instance forget_braided : (forget (C := C)).Braided where
  braided X Y := by
    simp only [forget_μ]
    erw [id_comp, comp_id]
    rfl

@[simp] lemma braiding_hom (X Y : Pivotalized C) :
    (β_ X Y).hom.hom = (β_ X.obj Y.obj).hom := rfl
@[simp] lemma braiding_inv (X Y : Pivotalized C) :
    (β_ X Y).inv.hom = (β_ X.obj Y.obj).inv := rfl

end Pivotalized
end Paper18.Category
