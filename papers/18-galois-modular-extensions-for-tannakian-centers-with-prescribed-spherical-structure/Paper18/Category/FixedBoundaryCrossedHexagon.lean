import Paper18.Category.FixedBoundaryCrossedBraiding
import Paper18.Category.LocalModulesCoherence

/-! # The actual neutral/odd crossed hexagon

The positive ambient hexagon descends through the two actual balancing
quotients. The neutral factor crosses by the actual local braiding, while
the remaining factor crosses to the genuinely translated first module.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.FixedBoundary
open RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]
  (e : A ≅ A) [IsMonHom e.hom]

/-- The genuine crossed hexagon with a local neutral factor. -/
theorem translatedBraiding_hexagon (X Z N : Mod_ C A) (hZ : IsLocalModule Z)
    (hN : (doubleBraiding A N.X).hom = e.hom ▷ N.X)
    (hZN : (doubleBraiding A (Z ⊗ N).X).hom = e.hom ▷ (Z ⊗ N).X) :
    translatedBraidingHom e X (Z ⊗ N) hZN =
      (α_ X Z N).inv ≫ (localBraidingHom X Z hZ ▷ N) ≫
        (α_ Z X N).hom ≫ (Z ◁ translatedBraidingHom e X N hN) ≫
          (α_ Z N ((Mod_.comap e.hom).obj X)).inv := by
  apply triple_hom_ext'
  simp only [Mod_.comp_hom', Category.assoc]
  rw [π_translatedBraidingHom]
  rw [π_associator_inv_assoc, π_whiskerRight_assoc]
  rw [← comp_whiskerRight_assoc, π_localBraidingHom, comp_whiskerRight]
  simp only [Category.assoc]
  rw [π_associator_assoc, π_whiskerLeft_assoc]
  rw [← whiskerLeft_comp_assoc, π_translatedBraidingHom, whiskerLeft_comp]
  simp only [Category.assoc]
  rw [π_associator_inv]
  erw [braiding_naturality_right_assoc, braiding_tensor_right_hom]
  simp only [Category.assoc]
  rfl

end Paper18.Category.FixedBoundary
