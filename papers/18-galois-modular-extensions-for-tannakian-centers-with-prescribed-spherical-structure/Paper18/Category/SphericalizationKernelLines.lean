import Paper18.Category.SphericalizationKernelFull
import Paper18.Category.SphericalizationNegative

/-! # The actual positive and negative lines in the sphericalization kernel -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
universe v u
namespace Paper18.Category.Sphericalized
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [CategoryTheory.Limits.HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [CategoryTheory.Limits.HasKernels C]
  [Simple (𝟙_ C)]

def signedUnit (b : Bool) : Sphericalized C := if b then negativeGenerator else 𝟙_ _

def signedUnitUnderlyingIso (b : Bool) : (signedUnit (C := C) b).obj.obj ≅ 𝟙_ C := by
  cases b <;> exact Iso.refl _

def kernelLine (b : Bool) : Kernel (C := C) :=
  ⟨signedUnit b, .of_iso (signedUnitUnderlyingIso b) IsUnitSum.unit⟩

def lineScalar (b : Bool) : UnitHomVector (signedUnit (C := C) b) ≃ₗ[ℂ] ℂ :=
  (unitHomCoordinate (signedUnit b)).symm.trans
    ((CategoryTheory.Linear.homCongr ℂ (Iso.refl (𝟙_ C)) (signedUnitUnderlyingIso b)).trans
      (unitScalarEquiv (C := C)))

def lineSign (b : Bool) : ℂ := if b then -1 else 1

omit [CategoryTheory.Limits.HasFiniteBiproducts C] in
lemma unitHomInvolution_unit (g : 𝟙_ C ⟶ 𝟙_ C) :
    unitHomInvolution (𝟙_ (Sphericalized C)) g = g := by
  obtain ⟨c, rfl⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ g
  change ε (doubleDualFunctor C) ≫ (doubleDualFunctor C).map (c • 𝟙 (𝟙_ C)) ≫
    η (doubleDualFunctor C) = c • 𝟙 (𝟙_ C)
  rw [Functor.map_smul]
  rw [CategoryTheory.Functor.map_id]
  simp only [Linear.comp_smul, Linear.smul_comp, Category.id_comp, ε_η]

omit [CategoryTheory.Limits.HasFiniteBiproducts C] in
lemma unitHomInvolution_negative (g : 𝟙_ C ⟶ 𝟙_ C) :
    unitHomInvolution (negativeGenerator (C := C)) g = -g := by
  change ε (doubleDualFunctor C) ≫ (doubleDualFunctor C).map g ≫
    (-η (doubleDualFunctor C)) = -g
  calc
    _ = -(ε (doubleDualFunctor C) ≫ (doubleDualFunctor C).map g ≫ η (doubleDualFunctor C)) := by
      simp only [Preadditive.comp_neg]
    _ = -g := congrArg Neg.neg (unitHomInvolution_unit g)

omit [CategoryTheory.Limits.HasFiniteBiproducts C] [MonoidalLinear ℂ C] in
lemma lineScalar_coordinate (b : Bool) (g : 𝟙_ C ⟶ (signedUnit (C := C) b).obj.obj) :
    lineScalar b (unitHomCoordinate (signedUnit b) g) =
      unitScalarEquiv (g ≫ (signedUnitUnderlyingIso b).hom) := by
  simp [lineScalar, CategoryTheory.Linear.homCongr]

lemma lineScalar_generator (b : Bool) (x : UnitHomVector (signedUnit (C := C) b)) :
    lineScalar b ((unitHomRepresentation.obj (signedUnit b)).ρ RepresentationZ2.generator x) =
      lineSign b * lineScalar b x := by
  have h := unitHomRepresentation_generator (signedUnit (C := C) b)
    ((unitHomCoordinate (signedUnit b)).symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  have hs := lineScalar_coordinate b ((unitHomCoordinate (signedUnit (C := C) b)).symm x)
  rw [LinearEquiv.apply_symm_apply] at hs
  rw [h, lineScalar_coordinate, hs]
  cases b
  · simp [signedUnit, signedUnitUnderlyingIso, lineSign]
    exact unitHomInvolution_unit _
  · simp [signedUnit, signedUnitUnderlyingIso, lineSign]
    erw [unitHomInvolution_negative]
    exact map_neg _ _

end Paper18.Category.Sphericalized
