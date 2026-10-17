import Paper18.Category.SphericalizationAction

/-! # The actual square category as the canonical order-two equivariantization -/
noncomputable section
universe v u
namespace Paper18.Category
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]

/-- The nontrivial element of the canonical order-two group. -/
def sphericalizationGenerator : SphericalizationGroup := Multiplicative.ofAdd (1 : ZMod 2)

@[simp] lemma sphericalizationGenerator_ne_one : sphericalizationGenerator ≠ 1 := by decide
@[simp] lemma sphericalizationGenerator_mul :
    sphericalizationGenerator * sphericalizationGenerator = 1 := by decide

lemma radfordSquare_inverse (X : C) (phi : X ≅ (doubleDualFunctor C).obj X)
    (h : phi.hom ≫ (doubleDualFunctor C).map phi.hom = (braidedFourDualIso X).hom) :
    (doubleDualFunctor C).map phi.inv ≫ phi.inv = (braidedFourDualIso X).inv := by
  have hi : phi ≪≫ (doubleDualFunctor C).mapIso phi = braidedFourDualIso X := Iso.ext h
  exact congrArg Iso.inv hi

lemma radfordSquare_of_inverse (X : C) (phi : X ≅ (doubleDualFunctor C).obj X)
    (h : (doubleDualFunctor C).map phi.inv ≫ phi.inv = (braidedFourDualIso X).inv) :
    phi.hom ≫ (doubleDualFunctor C).map phi.hom = (braidedFourDualIso X).hom := by
  have hi : (doubleDualFunctor C).mapIso phi.symm ≪≫ phi.symm = (braidedFourDualIso X).symm :=
    Iso.ext h
  exact congrArg Iso.inv hi

namespace Sphericalized

/-- A square object has actual equivariant structure: the nontrivial
translate is identified by the inverse chosen pivotal identification. -/
def toEquivariantObj (X : Sphericalized C) : (sphericalizationAction C).Equivariant where
  obj := X.obj.obj
  structureIso g := by
    by_cases hg : g = 1
    · subst g
      exact Iso.refl _
    · simpa only [sphericalizationAction, sphericalizationRho, if_neg hg] using X.obj.phi.symm
  unit := by simp [sphericalizationAction, sphericalizationRho]
  mul g h := by
    fin_cases g <;> fin_cases h <;>
      simp [sphericalizationAction, sphericalizationRho, sphericalizationMulIso,
        SphericalizationGroup]
    exact radfordSquare_inverse X.obj.obj X.obj.phi X.property

/-- Actual commuting morphisms lift to equivariant morphisms. -/
def toEquivariant : Sphericalized C ⥤ (sphericalizationAction C).Equivariant where
  obj := toEquivariantObj
  map {X Y} f :=
    { hom := f.hom
      comm g := by
        fin_cases g
        · simp [toEquivariantObj, sphericalizationAction, sphericalizationRho, SphericalizationGroup]
        · change (doubleDualFunctor C).map f.hom ≫ Y.obj.phi.inv =
            X.obj.phi.inv ≫ f.hom
          apply (cancel_epi X.obj.phi.hom).mp
          simp only [← assoc, Iso.hom_inv_id, id_comp]
          rw [← f.comm, assoc, Iso.hom_inv_id, comp_id] }
  map_id _ := rfl
  map_comp _ _ := rfl

end Sphericalized

namespace WeakAction.Equivariant

/-- The actual generator structure is the square-root inverse. -/
def generatorIso (Y : (sphericalizationAction C).Equivariant) :
    (doubleDualFunctor C).obj Y.obj ≅ Y.obj := by
  simpa only [sphericalizationAction, sphericalizationRho,
    sphericalizationGenerator_ne_one, if_neg] using Y.structureIso sphericalizationGenerator

lemma generatorIso_square (Y : (sphericalizationAction C).Equivariant) :
    (doubleDualFunctor C).map Y.generatorIso.hom ≫ Y.generatorIso.hom =
      (braidedFourDualIso Y.obj).inv := by
  have h := Y.mul sphericalizationGenerator sphericalizationGenerator
  change (doubleDualFunctor C).map Y.generatorIso.hom ≫ Y.generatorIso.hom =
    (braidedFourDualIso Y.obj).inv ≫ (Y.structureIso 1).hom at h
  rw [Y.unit] at h
  simpa [sphericalizationAction, sphericalizationRho] using h

/-- An actual equivariant object yields the actual pivotalized square object. -/
def toSphericalizedObj (Y : (sphericalizationAction C).Equivariant) : Sphericalized C :=
  ⟨⟨Y.obj, Y.generatorIso.symm⟩,
    radfordSquare_of_inverse Y.obj Y.generatorIso.symm Y.generatorIso_square⟩

/-- Equivariant morphisms are precisely the actual square-commuting morphisms. -/
def toSphericalized : (sphericalizationAction C).Equivariant ⥤ Sphericalized C where
  obj := toSphericalizedObj
  map {X Y} f :=
    { hom := f.hom
      comm := by
        have h := f.comm sphericalizationGenerator
        change (doubleDualFunctor C).map f.hom ≫ Y.generatorIso.hom =
          X.generatorIso.hom ≫ f.hom at h
        change f.hom ≫ Y.generatorIso.inv =
          X.generatorIso.inv ≫ (doubleDualFunctor C).map f.hom
        apply (cancel_epi X.generatorIso.hom).mp
        simp only [← Category.assoc, Iso.hom_inv_id, id_comp]
        rw [← h, Category.assoc, Iso.hom_inv_id, comp_id] }
  map_id _ := rfl
  map_comp _ _ := rfl

end WeakAction.Equivariant

namespace Sphericalized

/-- Returning from the order-two equivariantization leaves the actual
square object unchanged. -/
def equivalenceUnitIso (X : Sphericalized C) :
    X ≅ WeakAction.Equivariant.toSphericalized.obj (toEquivariant.obj X) :=
  radfordSquareProperty.isoMk (Pivotalized.mkIso (Iso.refl X.obj.obj) (by
    change 𝟙 X.obj.obj ≫ X.obj.phi.hom =
      X.obj.phi.hom ≫ (doubleDualFunctor C).map (𝟙 X.obj.obj)
    simp))

/-- Returning from the square category recovers every actual equivariant
structure, including its forced identity component. -/
def equivalenceCounitIso (Y : (sphericalizationAction C).Equivariant) :
    toEquivariant.obj (WeakAction.Equivariant.toSphericalized.obj Y) ≅ Y :=
  WeakAction.Equivariant.mkIso (sphericalizationAction C) (Iso.refl Y.obj) (by
    intro g
    fin_cases g <;>
      simp [toEquivariant, toEquivariantObj, WeakAction.Equivariant.toSphericalized,
        WeakAction.Equivariant.toSphericalizedObj, WeakAction.Equivariant.generatorIso,
        sphericalizationAction, sphericalizationRho, sphericalizationGenerator,
        SphericalizationGroup, Y.unit])

/-- The actual square category is equivalent to the actual equivariant
category of the canonical monoidal order-two action. -/
def equivariantEquivalence : Sphericalized C ≌ (sphericalizationAction C).Equivariant where
  functor := toEquivariant
  inverse := WeakAction.Equivariant.toSphericalized
  unitIso := NatIso.ofComponents equivalenceUnitIso (fun f => by
    apply Pivotalized.Hom.ext
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    simp)
  counitIso := NatIso.ofComponents equivalenceCounitIso (fun f => by
    apply WeakAction.Equivariant.Hom.ext
    change f.hom ≫ 𝟙 _ = 𝟙 _ ≫ f.hom
    simp)
  functor_unitIso_comp X := by
    apply WeakAction.Equivariant.Hom.ext
    change 𝟙 X.obj.obj ≫ 𝟙 X.obj.obj = 𝟙 X.obj.obj
    simp

end Sphericalized
end Paper18.Category
