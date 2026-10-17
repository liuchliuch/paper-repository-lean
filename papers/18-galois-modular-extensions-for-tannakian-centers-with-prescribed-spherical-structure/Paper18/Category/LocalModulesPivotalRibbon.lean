import Paper18.Category.LocalModulesPivotalDual
import Paper18.Category.PivotalBalancingDimensions
import Paper18.Category.SphericalizationTraceSeparation

/-! # Spherical pivotal structures have actual ribbon dual compatibility -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.PivotalStructure
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C] (J : PivotalStructure C)
include J

lemma dualMap_injective {X Y : C} : Function.Injective (dualMap C (X := X) (Y := Y)) := by
  intro f g h
  apply (cancel_mono (J.j.hom.app Y)).mp
  have hn₁ := J.j.hom.naturality f
  have hn₂ := J.j.hom.naturality g
  change f ≫ J.j.hom.app Y = J.j.hom.app X ≫ dualMap C (dualMap C f) at hn₁
  change g ≫ J.j.hom.app Y = J.j.hom.app X ≫ dualMap C (dualMap C g) at hn₂
  rw [hn₁, hn₂, h]

/-- The actual Radford square equation implies actual dual compatibility
of the twist. The proof uses the canonical four-dual formula and mates. -/
lemma twistSelfDual_of_radfordSquare
    (hs : ∀ X, J.j.hom.app X ≫ (doubleDualFunctor C).map (J.j.hom.app X) =
      (braidedFourDualIso X).hom) : J.TwistSelfDual := by
  intro X
  apply J.dualMap_injective
  have hδ : dualMap C (drinfeldIso (dual C X)).inv =
      (drinfeldIso X).inv ≫ J.j.hom.app X ≫
        (doubleDualFunctor C).map (J.j.hom.app X) := by
    have hh := hs X
    change J.j.hom.app X ≫ (doubleDualFunctor C).map (J.j.hom.app X) =
      (drinfeldIso X).hom ≫ dualMap C (drinfeldIso (dual C X)).inv at hh
    rw [hh]
    simp only [← assoc, Iso.inv_hom_id, id_comp]
  have hn := drinfeldIso_naturality (J.j.hom.app X)
  rw [drinfeldIso_doubleDual] at hn
  have hu := congrArg (fun t => (drinfeldIso X).inv ≫ t ≫
    (doubleDualFunctor C).map (drinfeldIso X).inv) hn
  simp only [assoc, ← Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, comp_id, Iso.inv_hom_id_assoc] at hu
  simp only [twistIso_hom, J.dual_component, dualMap, comp_rightAdjointMate]
  change dualMap C (drinfeldIso (dual C X)).inv ≫
    (doubleDualFunctor C).map (J.j.inv.app X) =
      (doubleDualFunctor C).map (J.j.hom.app X) ≫
        (doubleDualFunctor C).map (drinfeldIso X).inv
  rw [hδ]
  simp only [assoc, ← Functor.map_comp, J.j.hom_inv_id_app,
    CategoryTheory.Functor.map_id, comp_id]
  dsimp only [Functor.id_obj] at hu ⊢
  simp only [CategoryTheory.Functor.map_id, comp_id, Iso.inv_hom_id_assoc] at hu ⊢
  exact hu

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
include S

/-- Actual sphericality on a fusion category implies actual ribbon twist
duality on every object, through the proved trace characterization of Radford. -/
lemma twistSelfDual_of_spherical (hJ : J.Spherical) : J.TwistSelfDual :=
  J.twistSelfDual_of_radfordSquare (J.radfordSquare_of_spherical S hJ)

end Paper18.Category.PivotalStructure
