import Paper18.Category.EquivariantRigid

/-!
# Actual pivotal and spherical structures on equivariant objects

The action compatibility hypothesis is the canonical `PreservesPivotal`
equation. The pivotal natural isomorphism, all its coherence equations, and
the trace/sphericality statements on the equivariantization are constructed.
-/

noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
attribute [local instance 2000] RightRigidCategory.rightDual
universe v u w
namespace Paper18.Category.WeakAction
variable {G : Type w} [Group G] {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] (A : WeakAction G C) [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]

omit [RightRigidCategory C] in
@[simp] theorem forget_whiskerLeft (X : A.Equivariant) {Y Z : A.Equivariant} (f : Y ⟶ Z) :
    A.forget.map (X ◁ f) = X.obj ◁ f.hom := by
  change (𝟙 X.obj ⊗ₘ f.hom) = _
  simp

omit [RightRigidCategory C] in
@[simp] theorem forget_whiskerRight {X Y : A.Equivariant} (f : X ⟶ Y) (Z : A.Equivariant) :
    A.forget.map (f ▷ Z) = f.hom ▷ Z.obj := by
  change (f.hom ⊗ₘ 𝟙 Z.obj) = _
  simp

omit [RightRigidCategory C] in
@[simp] theorem forget_tensorHom {X X' Y Y' : A.Equivariant} (f : X ⟶ X') (h : Y ⟶ Y') :
    A.forget.map (f ⊗ₘ h) = f.hom ⊗ₘ h.hom := rfl

omit [RightRigidCategory C] in
@[simp] theorem forget_associator_hom (X Y Z : A.Equivariant) :
    A.forget.map (α_ X Y Z).hom = (α_ X.obj Y.obj Z.obj).hom := rfl
omit [RightRigidCategory C] in
@[simp] theorem forget_associator_inv (X Y Z : A.Equivariant) :
    A.forget.map (α_ X Y Z).inv = (α_ X.obj Y.obj Z.obj).inv := rfl
omit [RightRigidCategory C] in
@[simp] theorem forget_leftUnitor_hom (X : A.Equivariant) :
    A.forget.map (λ_ X).hom = (λ_ X.obj).hom := rfl
omit [RightRigidCategory C] in
@[simp] theorem forget_leftUnitor_inv (X : A.Equivariant) :
    A.forget.map (λ_ X).inv = (λ_ X.obj).inv := rfl
omit [RightRigidCategory C] in
@[simp] theorem forget_rightUnitor_hom (X : A.Equivariant) :
    A.forget.map (ρ_ X).hom = (ρ_ X.obj).hom := rfl
omit [RightRigidCategory C] in
@[simp] theorem forget_rightUnitor_inv (X : A.Equivariant) :
    A.forget.map (ρ_ X).inv = (ρ_ X.obj).inv := rfl

@[simp] theorem forget_evaluation (X : A.Equivariant) :
    A.forget.map (ε_ X (dual A.Equivariant X)) = ε_ X.obj (dual C X.obj) := rfl
@[simp] theorem forget_coevaluation (X : A.Equivariant) :
    A.forget.map (η_ X (dual A.Equivariant X)) = η_ X.obj (dual C X.obj) := rfl

omit [RightRigidCategory C] in
@[simp] theorem tensorObj_obj (X Y : A.Equivariant) : (X ⊗ Y).obj = X.obj ⊗ Y.obj := rfl
omit [RightRigidCategory C] in
@[simp] theorem tensorUnit_obj : (𝟙_ A.Equivariant).obj = 𝟙_ C := rfl

@[simp] theorem dual_obj (X : A.Equivariant) :
    (dual A.Equivariant X).obj = dual C X.obj := rfl
@[simp] theorem dual_structureIso (X : A.Equivariant) (g : G) :
    (dual A.Equivariant X).structureIso g = Equivariant.dualStructureIso A X g := rfl
omit [RightRigidCategory C] in
@[simp] theorem whiskerLeft_hom (X : A.Equivariant) {Y Z : A.Equivariant} (f : Y ⟶ Z) :
    (X ◁ f).hom = X.obj ◁ f.hom := forget_whiskerLeft A X f
omit [RightRigidCategory C] in
@[simp] theorem whiskerRight_hom {X Y : A.Equivariant} (f : X ⟶ Y) (Z : A.Equivariant) :
    (f ▷ Z).hom = f.hom ▷ Z.obj := forget_whiskerRight A f Z
omit [RightRigidCategory C] in
@[simp] theorem associator_hom_hom (X Y Z : A.Equivariant) :
    (α_ X Y Z).hom.hom = (α_ X.obj Y.obj Z.obj).hom := rfl
omit [RightRigidCategory C] in
@[simp] theorem associator_inv_hom (X Y Z : A.Equivariant) :
    (α_ X Y Z).inv.hom = (α_ X.obj Y.obj Z.obj).inv := rfl
omit [RightRigidCategory C] in
@[simp] theorem leftUnitor_hom_hom (X : A.Equivariant) :
    (λ_ X).hom.hom = (λ_ X.obj).hom := rfl
omit [RightRigidCategory C] in
@[simp] theorem leftUnitor_inv_hom (X : A.Equivariant) :
    (λ_ X).inv.hom = (λ_ X.obj).inv := rfl
omit [RightRigidCategory C] in
@[simp] theorem rightUnitor_hom_hom (X : A.Equivariant) :
    (ρ_ X).hom.hom = (ρ_ X.obj).hom := rfl
omit [RightRigidCategory C] in
@[simp] theorem rightUnitor_inv_hom (X : A.Equivariant) :
    (ρ_ X).inv.hom = (ρ_ X.obj).inv := rfl
@[simp] theorem evaluation_hom (X : A.Equivariant) :
    (ε_ X (dual A.Equivariant X)).hom = ε_ X.obj (dual C X.obj) := rfl
@[simp] theorem coevaluation_hom (X : A.Equivariant) :
    (η_ X (dual A.Equivariant X)).hom = η_ X.obj (dual C X.obj) := rfl

/-- Forgetting a categorical adjoint mate gives the actual ambient mate. -/
@[simp] theorem forget_dualMap {X Y : A.Equivariant} (f : X ⟶ Y) :
    A.forget.map (dualMap A.Equivariant f) = dualMap C f.hom := by
  simp only [dualMap, rightAdjointMate, Functor.map_comp, forget_whiskerLeft,
    forget_whiskerRight, forget_associator_inv, forget_rightUnitor_inv,
    forget_leftUnitor_hom, whiskerRight_hom, evaluation_hom,
    coevaluation_hom, dual_obj]

@[simp] theorem dualMap_hom {X Y : A.Equivariant} (f : X ⟶ Y) :
    (dualMap A.Equivariant f).hom = dualMap C f.hom := forget_dualMap A f


/-- The chosen duality on equivariant objects has exactly the ambient
canonical tensor comparison after forgetting. -/
@[simp] theorem forget_dualTensorTo (X Y : A.Equivariant) :
    A.forget.map (dualTensorTo A.Equivariant X Y) = dualTensorTo C X.obj Y.obj := by
  simp [dualTensorTo, tensorCoevaluation, Functor.map_comp]

@[simp] theorem dualTensorTo_hom (X Y : A.Equivariant) :
    (dualTensorTo A.Equivariant X Y).hom = dualTensorTo C X.obj Y.obj :=
  forget_dualTensorTo A X Y

@[simp] theorem forget_dualTensorFrom (X Y : A.Equivariant) :
    A.forget.map (dualTensorFrom A.Equivariant X Y) = dualTensorFrom C X.obj Y.obj := by
  simp [dualTensorFrom, tensorEvaluation, Functor.map_comp]

@[simp] theorem forget_doubleDualTensorHom (X Y : A.Equivariant) :
    A.forget.map (doubleDualTensorHom A.Equivariant X Y) = doubleDualTensorHom C X.obj Y.obj := by
  simp only [doubleDualTensorHom, Functor.map_comp, forget_dualTensorFrom,
    forget_dualMap, dual_obj, dualTensorTo_hom]

@[simp] theorem forget_doubleDualUnitHom :
    A.forget.map (doubleDualUnitHom A.Equivariant) = doubleDualUnitHom C := by
  simp [doubleDualUnitHom, dualUnitFrom, dualUnitTo, Functor.map_comp]

namespace Equivariant

/-- The actual structure map on the double dual factors through the
canonical strong-monoidal double-dual comparison. -/
theorem doubleDual_structureIso (X : A.Equivariant) (g : G) :
    ((dual A.Equivariant (dual A.Equivariant X)).structureIso g).hom =
      (doubleDualComparison (A.ρ g) X.obj).hom ≫
        (doubleDualFunctor C).map (X.structureIso g).hom := by
  simp [dual_structureIso, dualStructureIso, doubleDualComparison, dualMapIso,
    doubleDualFunctor, dualMap, comp_rightAdjointMate, Category.assoc]

variable (J : PivotalStructure C) (hJ : ∀ g : G, PreservesPivotal (A.ρ g) J J)

/-- The actual pivotal component is equivariant by the canonical pivotal
compatibility of each translating functor. -/
def pivotalComponent (X : A.Equivariant) : X ≅ (doubleDualFunctor A.Equivariant).obj X :=
  mkIso A (J.j.app X.obj) (by
    intro g
    change (A.ρ g).map (J.j.hom.app X.obj) ≫
      ((dual A.Equivariant (dual A.Equivariant X)).structureIso g).hom =
        (X.structureIso g).hom ≫ J.j.hom.app X.obj
    rw [doubleDual_structureIso, ← Category.assoc, hJ g X.obj]
    exact (J.j.hom.naturality (X.structureIso g).hom).symm)

/-- The actual pivotal natural isomorphism on equivariant objects. -/
def pivotalNatIso : 𝟭 A.Equivariant ≅ doubleDualFunctor A.Equivariant :=
  NatIso.ofComponents (pivotalComponent A J hJ) (by
    intro X Y f
    apply Hom.ext
    change f.hom ≫ J.j.hom.app Y.obj =
      J.j.hom.app X.obj ≫ A.forget.map ((doubleDualFunctor A.Equivariant).map f)
    simp only [doubleDualFunctor, forget_dualMap, dualMap_hom]
    exact J.j.hom.naturality f.hom)

/-- The inherited pivotal structure obeys the canonical unit and tensor
coherence equations, because its actual cups and caps forget to the originals. -/
def pivotalStructure : PivotalStructure A.Equivariant where
  j := pivotalNatIso A J hJ
  unit := by
    apply A.forget.map_injective
    change J.j.hom.app (𝟙_ C) = A.forget.map (doubleDualUnitHom A.Equivariant)
    rw [forget_doubleDualUnitHom]
    exact J.unit
  tensor X Y := by
    apply A.forget.map_injective
    change J.j.hom.app (X.obj ⊗ Y.obj) = A.forget.map
      (((pivotalNatIso A J hJ).hom.app X ⊗ₘ (pivotalNatIso A J hJ).hom.app Y) ≫
        doubleDualTensorHom A.Equivariant X Y)
    rw [Functor.map_comp, forget_tensorHom, forget_doubleDualTensorHom]
    exact J.tensor X.obj Y.obj

end Equivariant

/-- The canonical right-dual comparison of the actual forgetful functor is
the identity, as follows from its actual evaluation pairing. -/
theorem forget_dualComparison_hom (X : A.Equivariant) :
    (dualComparison A.forget X).hom = 𝟙 (dual C X.obj) := by
  apply pairing_hom_ext (inferInstanceAs (ExactPairing X.obj (dual C X.obj)))
  erw [id_whiskerRight, Category.id_comp]
  erw [dualComparison_evaluation A.forget X]
  simp only [forget_μ, forget_η]
  erw [Category.id_comp, Category.comp_id]
  exact forget_evaluation A X

@[simp] theorem forget_dualComparison_eq (X : A.Equivariant) :
    dualComparison A.forget X = Iso.refl (dual C X.obj) :=
  Iso.ext (forget_dualComparison_hom A X)

/-- The canonical double-dual comparison also agrees with the identity. -/
@[simp] theorem forget_doubleDualComparison_hom (X : A.Equivariant) :
    (doubleDualComparison A.forget X).hom = 𝟙 (dual C (dual C X.obj)) := by
  simp [doubleDualComparison, dualMapIso, dualMap]
  erw [rightAdjointMate_id, Category.comp_id]

variable (J : PivotalStructure C) (hJ : ∀ g : G, PreservesPivotal (A.ρ g) J J)

/-- The actual forgetful functor is pivotal for the inherited pivotal
structure, with the required canonical double-dual comparison. -/
theorem forget_preservesPivotal :
    PreservesPivotal A.forget (Equivariant.pivotalStructure A J hJ) J := by
  intro X
  rw [forget_doubleDualComparison_hom]
  erw [Category.comp_id]
  rfl

namespace Equivariant

/-- Preservation of every actual right trace by forgetting. -/
theorem forget_rightTrace {X : A.Equivariant} (f : X ⟶ X) :
    A.forget.map ((pivotalStructure A J hJ).rightTrace f) = J.rightTrace f.hom := by
  have h := (forget_preservesPivotal A J hJ).rightTrace f
  simp only [forget_ε, forget_η] at h
  erw [Category.id_comp, Category.comp_id] at h
  exact h

/-- Preservation of every actual left trace by forgetting. -/
theorem forget_leftTrace {X : A.Equivariant} (f : X ⟶ X) :
    A.forget.map ((pivotalStructure A J hJ).leftTrace f) = J.leftTrace f.hom := by
  have h := (forget_preservesPivotal A J hJ).leftTrace f
  simp only [forget_ε, forget_η] at h
  erw [Category.id_comp, Category.comp_id] at h
  exact h

/-- Sphericality of the inherited pivotal structure is a consequence of
actual equality of all ambient traces and faithfulness of forgetting. -/
theorem pivotalStructure_spherical (h : J.Spherical) :
    (pivotalStructure A J hJ).Spherical :=
  (forget_preservesPivotal A J hJ).spherical_of_faithful h

/-- A pivotal equivariantization is also left rigid, using the actual
pivotal left evaluation and coevaluation already constructed. -/
def pivotalLeftRigidCategory : LeftRigidCategory A.Equivariant where
  leftDual X :=
    { leftDual := dual A.Equivariant X
      exact := (pivotalStructure A J hJ).leftExactPairing X }

/-- The resulting actual two-sided rigid structure. -/
def pivotalRigidCategory : RigidCategory A.Equivariant where
  toRightRigidCategory := inferInstance
  toLeftRigidCategory := pivotalLeftRigidCategory A J hJ

end Equivariant
end Paper18.Category.WeakAction
