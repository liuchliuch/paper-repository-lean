import Paper18.Category.SphericalizationFusion
import Paper18.Category.RepresentationZ2Action
import Paper18.Category.NondegenerateBasic

/-! # The actual C₂ representation carried by unit-valued points of a square object

The generator acts on `Hom(1,X)` by the canonical double-dual unit map,
double dualization of the point, and the inverse square-root identification.
The Radford square equation proves that this operation is an involution.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal
universe v u
namespace Paper18.Category.Sphericalized
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The actual order-two operation on maps from the ambient tensor unit. -/
def unitHomInvolution (X : Sphericalized C) :
    (𝟙_ C ⟶ X.obj.obj) →ₗ[ℂ] (𝟙_ C ⟶ X.obj.obj) where
  toFun f := ε (doubleDualFunctor C) ≫ (doubleDualFunctor C).map f ≫ X.obj.phi.inv
  map_add' f g := by simp
  map_smul' c f := by simp

lemma unitHomInvolution_sq (X : Sphericalized C) (f : 𝟙_ C ⟶ X.obj.obj) :
    unitHomInvolution X (unitHomInvolution X f) = f := by
  change ε (doubleDualFunctor C) ≫
    (doubleDualFunctor C).map
      (ε (doubleDualFunctor C) ≫ (doubleDualFunctor C).map f ≫ X.obj.phi.inv) ≫
    X.obj.phi.inv = f
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  have hu := radfordSquareProperty_unit (C := C)
  change ε (doubleDualFunctor C) ≫ (doubleDualFunctor C).map (ε (doubleDualFunctor C)) =
    (braidedFourDualIso (𝟙_ C)).hom at hu
  rw [← Category.assoc (ε (doubleDualFunctor C)), hu]
  have hn := (braidedFourDualNatIso (C := C)).hom.naturality f
  change f ≫ (braidedFourDualIso X.obj.obj).hom =
    (braidedFourDualIso (𝟙_ C)).hom ≫
      (doubleDualFunctor C).map ((doubleDualFunctor C).map f) at hn
  rw [← Category.assoc, ← hn, Category.assoc,
    radfordSquare_inverse X.obj.obj X.obj.phi X.property, Iso.hom_inv_id, Category.comp_id]

lemma unitHomInvolution_natural {X Y : Sphericalized C} (f : X ⟶ Y)
    (g : 𝟙_ C ⟶ X.obj.obj) :
    unitHomInvolution X g ≫ f.hom = unitHomInvolution Y (g ≫ f.hom) := by
  change (ε (doubleDualFunctor C) ≫ (doubleDualFunctor C).map g ≫ X.obj.phi.inv) ≫ f.hom =
    ε (doubleDualFunctor C) ≫ (doubleDualFunctor C).map (g ≫ f.hom) ≫ Y.obj.phi.inv
  have hf : X.obj.phi.inv ≫ f.hom = (doubleDualFunctor C).map f.hom ≫ Y.obj.phi.inv := by
    apply (cancel_epi X.obj.phi.hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    rw [← f.comm, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc, hf]

variable [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]

/-- Finite coordinates keep the representation in the ordinary universe of
complex vector spaces even when the original category has large Hom types. -/
abbrev UnitHomVector (X : Sphericalized C) :=
  Fin (Module.finrank ℂ (𝟙_ C ⟶ X.obj.obj)) → ℂ

def unitHomCoordinate (X : Sphericalized C) :
    (𝟙_ C ⟶ X.obj.obj) ≃ₗ[ℂ] UnitHomVector X :=
  (Module.finBasis ℂ (𝟙_ C ⟶ X.obj.obj)).equivFun

/-- The generator on the actual finite-dimensional space of unit points. -/
def unitHomGenerator (X : Sphericalized C) :
    FGModuleCat.of ℂ (UnitHomVector X) ⟶ FGModuleCat.of ℂ (UnitHomVector X) :=
  FGModuleCat.ofHom ((unitHomCoordinate X).toLinearMap ∘ₗ unitHomInvolution X ∘ₗ
    (unitHomCoordinate X).symm.toLinearMap)

@[simp] lemma unitHomGenerator_apply (X : Sphericalized C) (x : UnitHomVector X) :
    (unitHomGenerator X).hom x =
      unitHomCoordinate X (unitHomInvolution X ((unitHomCoordinate X).symm x)) := rfl

lemma unitHomGenerator_sq (X : Sphericalized C) :
    unitHomGenerator X ≫ unitHomGenerator X = 𝟙 _ := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change unitHomCoordinate X (unitHomInvolution X
    ((unitHomCoordinate X).symm (unitHomCoordinate X
      (unitHomInvolution X ((unitHomCoordinate X).symm x))))) = x
  rw [LinearEquiv.symm_apply_apply, unitHomInvolution_sq, LinearEquiv.apply_symm_apply]

def unitHomCoordinateMap {X Y : Sphericalized C} (f : X ⟶ Y) :
    UnitHomVector X →ₗ[ℂ] UnitHomVector Y :=
  (unitHomCoordinate Y).toLinearMap ∘ₗ
    CategoryTheory.Linear.rightComp ℂ (𝟙_ C) f.hom ∘ₗ (unitHomCoordinate X).symm.toLinearMap

omit [MonoidalPreadditive C] [MonoidalLinear ℂ C] in
@[simp] lemma unitHomCoordinateMap_apply {X Y : Sphericalized C} (f : X ⟶ Y)
    (x : UnitHomVector X) :
    unitHomCoordinateMap f x = unitHomCoordinate Y ((unitHomCoordinate X).symm x ≫ f.hom) := rfl

/-- An actual finite-dimensional C₂ representation, functorial in every
actual square object. Its restriction to the forgetful kernel will be an
equivalence. -/
def unitHomRepresentation : Sphericalized C ⥤ FDRep ℂ RepresentationZ2.H where
  obj X := RepresentationZ2.actionOfInvolution (FGModuleCat.of ℂ (UnitHomVector X))
    (unitHomGenerator X) (unitHomGenerator_sq X)
  map {X Y} f := RepresentationZ2.mapOfInvolution _ _ _ _
    (FGModuleCat.ofHom (unitHomCoordinateMap f)) (by
      apply FGModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change unitHomCoordinate Y ((unitHomCoordinate X).symm
        (unitHomCoordinate X (unitHomInvolution X ((unitHomCoordinate X).symm x))) ≫ f.hom) =
        unitHomCoordinate Y (unitHomInvolution Y ((unitHomCoordinate Y).symm
          (unitHomCoordinate Y ((unitHomCoordinate X).symm x ≫ f.hom))))
      simp only [
        LinearEquiv.symm_apply_apply, unitHomInvolution_natural])
  map_id X := by
    apply Action.Hom.ext
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change unitHomCoordinate X ((unitHomCoordinate X).symm x ≫ 𝟙 X.obj.obj) = x
    simp only [Category.comp_id,
      LinearEquiv.apply_symm_apply]
  map_comp f g := by
    apply Action.Hom.ext
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change unitHomCoordinate _ ((unitHomCoordinate _).symm x ≫ (f.hom ≫ g.hom)) =
      unitHomCoordinate _ ((unitHomCoordinate _).symm
        (unitHomCoordinate _ ((unitHomCoordinate _).symm x ≫ f.hom)) ≫ g.hom)
    simp only [
      LinearEquiv.symm_apply_apply, Category.assoc]

instance unitHomRepresentation_additive : (unitHomRepresentation (C := C)).Additive where
  map_add := by
    intro X Y f g
    apply Action.Hom.ext
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change unitHomCoordinate Y ((unitHomCoordinate X).symm x ≫ (f.hom + g.hom)) =
      unitHomCoordinate Y ((unitHomCoordinate X).symm x ≫ f.hom) +
        unitHomCoordinate Y ((unitHomCoordinate X).symm x ≫ g.hom)
    simp only [Preadditive.comp_add, map_add]

instance unitHomRepresentation_linear : (unitHomRepresentation (C := C)).Linear ℂ where
  map_smul f c := by
    apply Action.Hom.ext
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change unitHomCoordinate _ ((unitHomCoordinate _).symm x ≫ (c • f.hom)) =
      c • unitHomCoordinate _ ((unitHomCoordinate _).symm x ≫ f.hom)
    simp only [Linear.comp_smul, map_smul]

@[simp] lemma unitHomRepresentation_generator (X : Sphericalized C) (g : 𝟙_ C ⟶ X.obj.obj) :
    (unitHomRepresentation.obj X).ρ RepresentationZ2.generator (unitHomCoordinate X g) =
      unitHomCoordinate X (unitHomInvolution X g) := by
  change (RepresentationZ2.actionOfInvolution (FGModuleCat.of ℂ (UnitHomVector X))
    (unitHomGenerator X) (unitHomGenerator_sq X)).ρ
    RepresentationZ2.generator (unitHomCoordinate X g) = _
  rw [RepresentationZ2.actionOfInvolution_generator]
  change unitHomCoordinate X (unitHomInvolution X
    ((unitHomCoordinate X).symm (unitHomCoordinate X g))) = _
  rw [LinearEquiv.symm_apply_apply]

end Paper18.Category.Sphericalized
