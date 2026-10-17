import Paper18.Category.SphericalizationKernelLines
import Paper18.Category.SphericalizationKernelRepresentation

/-! # Every complex C₂ representation comes from an actual kernel object -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u
namespace Paper18.Category.Sphericalized
open RepresentationZ2
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C] [HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]

def eigenParity (V : FDRep ℂ H) : EigenIndex V → Bool := Sum.elim (fun _ => false) (fun _ => true)

lemma eigenParity_sign (V : FDRep ℂ H) (i : EigenIndex V) :
    lineSign (eigenParity V i) = eigenSign V i := by cases i <;> rfl

def eigenLine (V : FDRep ℂ H) (i : EigenIndex V) : Sphericalized C := signedUnit (eigenParity V i)

def eigenLineInclusion (V : FDRep ℂ H) (i : EigenIndex V) :
    unitHomRepresentation.obj (eigenLine (C := C) V i) ⟶ V where
  hom := FGModuleCat.ofHom
    ((LinearMap.toSpanSingleton ℂ V (eigenVector V i)).comp (lineScalar (eigenParity V i)).toLinearMap)
  comm g := by
    rcases eq_one_or_generator g with rfl | rfl
    · simp
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change lineScalar (eigenParity V i)
          ((unitHomRepresentation.obj (eigenLine (C := C) V i)).ρ generator x) • eigenVector V i =
        V.ρ generator (lineScalar (eigenParity V i) x • eigenVector V i)
      dsimp only [eigenLine]
      rw [lineScalar_generator, map_smul, eigenVector_generator, eigenParity_sign,
        smul_smul, mul_comm]

def eigenLineProjection (V : FDRep ℂ H) (i : EigenIndex V) :
    V ⟶ unitHomRepresentation.obj (eigenLine (C := C) V i) where
  hom := FGModuleCat.ofHom
    ((lineScalar (eigenParity V i)).symm.toLinearMap ∘ₗ
      (LinearMap.proj i) ∘ₗ (eigenCoordinates V).toLinearMap)
  comm g := by
    rcases eq_one_or_generator g with rfl | rfl
    · simp
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply (lineScalar (eigenParity V i)).injective
      change lineScalar (eigenParity V i) ((lineScalar (eigenParity V i)).symm
          (eigenCoordinates V (V.ρ generator x) i)) =
        lineScalar (eigenParity V i)
          ((unitHomRepresentation.obj (eigenLine (C := C) V i)).ρ generator
            ((lineScalar (eigenParity V i)).symm (eigenCoordinates V x i)))
      dsimp only [eigenLine]
      rw [lineScalar_generator, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
        eigenCoordinates_generator, eigenParity_sign]

lemma eigenLineInclusion_projection_self (V : FDRep ℂ H) (i : EigenIndex V) :
    eigenLineInclusion (C := C) V i ≫ eigenLineProjection V i = 𝟙 _ := by
  apply Action.Hom.ext
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (lineScalar (eigenParity V i)).symm
    (eigenCoordinates V (lineScalar (eigenParity V i) x • eigenVector V i) i) = x
  rw [map_smul, eigenCoordinates_eigenVector]
  simp

lemma eigenLineInclusion_projection_ne (V : FDRep ℂ H) (i j : EigenIndex V) (hij : i ≠ j) :
    eigenLineInclusion (C := C) V i ≫ eigenLineProjection (C := C) V j = 0 := by
  apply Action.Hom.ext
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (lineScalar (eigenParity V j)).symm
    (eigenCoordinates V (lineScalar (eigenParity V i) x • eigenVector V i) j) = 0
  rw [map_smul, eigenCoordinates_eigenVector]
  simp [hij]

def eigenLineBiproductIso (V : FDRep ℂ H) :
    (⨁ fun i : EigenIndex V => unitHomRepresentation.obj (eigenLine (C := C) V i)) ≅ V where
  hom := biproduct.desc (eigenLineInclusion V)
  inv := biproduct.lift (eigenLineProjection V)
  hom_inv_id := by
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    by_cases hij : i = j
    · subst j
      simp [eigenLineInclusion_projection_self]
    · simp [eigenLineInclusion_projection_ne V i j hij, hij]
  inv_hom_id := by
    rw [biproduct.lift_desc]
    apply Action.Hom.ext
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [Action.sum_hom, ModuleCat.hom_sum, LinearMap.sum_apply]
    change (∑ i : EigenIndex V, lineScalar (eigenParity V i)
      ((lineScalar (eigenParity V i)).symm (eigenCoordinates V x i)) • eigenVector V i) = x
    simp only [LinearEquiv.apply_symm_apply]
    exact eigenVector_resolution V x

/-- The actual finite sum of positive and negative unit objects indexed by
the two actual eigenspace bases. -/
def eigenKernelObject (V : FDRep ℂ H) : Kernel (C := C) :=
  ⟨⨁ (eigenLine (C := C) V), by
    apply IsUnitSum.of_iso ((forget (C := C)).mapBiproduct (eigenLine V))
    exact IsUnitSum.of_iso (biproduct.mapIso (fun i => signedUnitUnderlyingIso (eigenParity V i)))
      (IsUnitSum.biproduct_unit (EigenIndex V))⟩

def eigenKernelRepresentationIso (V : FDRep ℂ H) :
    kernelRepresentation.obj (eigenKernelObject (C := C) V) ≅ V :=
  (unitHomRepresentation (C := C)).mapBiproduct (eigenLine V) ≪≫ eigenLineBiproductIso V

instance kernelRepresentation_essSurj : (kernelRepresentation (C := C)).EssSurj where
  mem_essImage V := ⟨eigenKernelObject V, ⟨eigenKernelRepresentationIso V⟩⟩

instance kernelRepresentation_isEquivalence : (kernelRepresentation (C := C)).IsEquivalence where

def kernelEquivalence : Kernel (C := C) ≌ FDRep ℂ H := kernelRepresentation.asEquivalence

end Paper18.Category.Sphericalized
