import Paper18.Category.PointedCentralizer
import Paper18.Category.PointedPivotal
import Paper18.Category.PivotalModification
import Paper18.Category.PointedObstruction

noncomputable section

open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace Paper18.Category.AppendixBPointed

attribute [local instance 2000] RightRigidCategory.rightDual
attribute [local instance] PointedVec.simple_simpleObject

/-- The canonical positive pivotal structure on the ambient actual category. -/
abbrev canonicalPivotal : PivotalStructure Vec := PointedVec.pivotalStructure Paper18.PointedA

/-- Its restriction to the actual centralizer, using the inherited cups,
caps and the canonical dual comparison of the inclusion. -/
def bCanonicalPivotal : PivotalStructure B :=
  (PointedVec.skeleton Paper18.PointedA).fullSubcategoryPivotal
    (centralizerProperty centralizerSet) canonicalPivotal

theorem bCanonicalPivotal_spherical : bCanonicalPivotal.Spherical :=
  (PointedVec.skeleton Paper18.PointedA).fullSubcategoryPivotal_spherical
    (centralizerProperty centralizerSet) canonicalPivotal
    (PointedVec.pivotalStructure_spherical Paper18.PointedA)

/-- Restrict an actual degree-character automorphism to the centralizer. -/
def bCharacter (χ : AddChar Paper18.PointedA ℂ) : 𝟭 B ≅ 𝟭 B where
  hom :=
    { app X := PointedVec.degreeMap χ X.obj
      naturality := fun {X Y} f => PointedVec.degreeMap_naturality χ f }
  inv :=
    { app X := PointedVec.degreeMap (fun a => (χ a)⁻¹) X.obj
      naturality := fun {X Y} f => PointedVec.degreeMap_naturality _ f }
  hom_inv_id := by
    ext X
    exact (PointedVec.characterAutomorphism χ).hom_inv_id_app X.obj
  inv_hom_id := by
    ext X
    exact (PointedVec.characterAutomorphism χ).inv_hom_id_app X.obj

instance bCharacter_monoidal (χ : AddChar Paper18.PointedA ℂ) :
    (bCharacter χ).hom.IsMonoidal where
  unit := by
    change 𝟙 _ ≫ PointedVec.degreeMap χ (𝟙_ Vec) = 𝟙 _
    rw [Category.id_comp, PointedVec.characterMap_unit]
  tensor X Y := by
    change 𝟙 _ ≫ PointedVec.degreeMap χ (X.obj ⊗ Y.obj) =
      (PointedVec.degreeMap χ X.obj ⊗ₘ PointedVec.degreeMap χ Y.obj) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, PointedVec.characterMap_tensor]

lemma bCharacter_simple (χ : AddChar Paper18.PointedA ℂ) (a : evenSecond) :
    (bCharacter χ).hom.app (bSimple a) = χ a • 𝟙 (bSimple a) :=
  PointedVec.degreeMap_simple_eq_scalar χ a

lemma bCharacter_scalar (χ : AddChar Paper18.PointedA ℂ)
    (i : {a : Paper18.PointedA // PointedVec.simpleObject Paper18.PointedA a ∈
      centralizer centralizerSet}) :
    TensorAutomorphism.scalar (bCharacter χ) (bSkeleton.simpleObject i) = χ i.val := by
  change simpleScalarEquiv _ (PointedVec.degreeMap χ (PointedVec.simpleObject _ i.val)) = _
  rw [PointedVec.degreeMap_simple_eq_scalar]
  exact simpleScalarEquiv_smul_id _ _

lemma bCharacter_chi_involutive (X : B) :
    (bCharacter Paper18.chi).hom.app X ≫ (bCharacter Paper18.chi).hom.app X = 𝟙 X := by
  have he : bCharacter Paper18.chi = (bCharacter Paper18.chi).symm := by
    apply TensorAutomorphism.ext_simple _ _ bSkeleton
    intro i
    rw [TensorAutomorphism.inv_scalar, bCharacter_scalar]
    have hi : (2 : ℕ) • i.val.2 = 0 := (simple_mem_B_iff i.val).mp i.property
    have hs : Paper18.chi i.val ^ 2 = 1 := restrictedChi_sq ⟨i.val, hi⟩
    apply mul_right_cancel₀ (Paper18.chi.val_isUnit i.val).ne_zero
    simp only [← pow_two, hs, inv_mul_cancel₀ (Paper18.chi.val_isUnit i.val).ne_zero]
  have hh := congrArg (fun α : 𝟭 B ≅ 𝟭 B => α.hom.app X) he
  change (bCharacter Paper18.chi).hom.app X = (bCharacter Paper18.chi).inv.app X at hh
  exact (congrArg (fun f => f ≫ (bCharacter Paper18.chi).hom.app X) hh).trans
    ((bCharacter Paper18.chi).inv_hom_id_app X)

/-- The prescribed actual pivotal structure modifies the canonical one by
`i^b` on the actual centralizer. -/
def prescribedPivotal : PivotalStructure B :=
  bCanonicalPivotal.modify (bCharacter Paper18.chi)

/-- The prescribed structure is spherical on every actual endomorphism. -/
theorem prescribedPivotal_spherical : prescribedPivotal.Spherical :=
  bCanonicalPivotal.modify_spherical (bCharacter Paper18.chi)
    bCanonicalPivotal_spherical bCharacter_chi_involutive

@[simp] lemma bCanonicalPivotal_rightDimension_simple (a : evenSecond) :
    bCanonicalPivotal.rightDimension (bSimple a) = 𝟙 (𝟙_ B) :=
  PointedVec.pivotalStructure_rightDimension_simple Paper18.PointedA a

@[simp] lemma bCanonicalPivotal_rightDim_simple (a : evenSecond) :
    bCanonicalPivotal.rightDim (bSimple a) = 1 := by
  unfold PivotalStructure.rightDim
  rw [bCanonicalPivotal_rightDimension_simple, unitScalarEquiv_id]

@[simp] lemma bCharacter_scalar_simple (χ : AddChar Paper18.PointedA ℂ) (a : evenSecond) :
    TensorAutomorphism.scalar (bCharacter χ) (bSimple a) = χ a := by
  unfold TensorAutomorphism.scalar
  rw [bCharacter_simple, simpleScalarEquiv_smul_id]

/-- The prescribed categorical dimension on an actual homogeneous simple
is the specified sign character. -/
@[simp] theorem prescribedPivotal_dimension (a : evenSecond) :
    prescribedPivotal.rightDim (bSimple a) = Paper18.chi a := by
  rw [prescribedPivotal, PivotalStructure.modify_rightDim,
    bCanonicalPivotal_rightDim_simple, mul_one, bCharacter_scalar_simple]

def obstructionDegree : evenSecond := ⟨(0, 2), by
  change (2 : ℕ) • (2 : ZMod 4) = 0
  decide⟩

abbrev obstructionObject : B := bSimple obstructionDegree

@[simp] lemma prescribedPivotal_obstruction_dimension :
    prescribedPivotal.rightDim obstructionObject = -1 := by
  rw [prescribedPivotal_dimension]
  exact Paper18.appendixB_chi_at_zero_two

/-- The explicit all-degree pivotal modification really extends the
prescribed centralizer structure through the actual braided inclusion. -/
theorem nonsphericalPivotalExtension_preserves :
    PreservesPivotal BInclusion prescribedPivotal nonsphericalPivotalExtension := by
  intro X
  have h := (PointedVec.skeleton Paper18.PointedA).fullSubcategory_preservesPivotal
    (centralizerProperty centralizerSet) canonicalPivotal X
  change BInclusion.map (bCanonicalPivotal.j.hom.app X) ≫
    (doubleDualComparison BInclusion X).hom =
    canonicalPivotal.j.hom.app X.obj at h
  change (PointedVec.degreeMap Paper18.chi X.obj ≫
      BInclusion.map (bCanonicalPivotal.j.hom.app X)) ≫ (doubleDualComparison BInclusion X).hom =
    PointedVec.degreeMap Paper18.chi X.obj ≫ canonicalPivotal.j.hom.app X.obj
  rw [Category.assoc, h]

/-- No actual spherical pivotal structure on the fixed modular ambient
category can extend the prescribed spherical structure on its centralizer.
The contradiction uses preservation of an actual categorical dimension. -/
theorem prescribedPivotal_no_spherical_extension (J : PivotalStructure Vec)
    (hJ : J.Spherical) : ¬ PreservesPivotal BInclusion prescribedPivotal J := by
  intro hP
  have hp : prescribedPivotal.rightDimension obstructionObject =
      (-1 : ℂ) • 𝟙 (𝟙_ B) := by
    have hs := unitScalarEquiv_spec (prescribedPivotal.rightDimension obstructionObject)
    change prescribedPivotal.rightDim obstructionObject • 𝟙 (𝟙_ B) = _ at hs
    rw [prescribedPivotal_obstruction_dimension] at hs
    exact hs.symm
  have he := hP.rightDimension obstructionObject
  rw [hp, Functor.map_smul, CategoryTheory.Functor.map_id] at he
  have he' : (-1 : ℂ) • 𝟙 (𝟙_ Vec) =
      J.rightDimension (PointedVec.simpleObject Paper18.PointedA (0, 2)) := by
    simpa using he
  have hc := congrArg (unitScalarEquiv (C := Vec)) he'
  rw [unitScalarEquiv_smul_id] at hc
  change (-1 : ℂ) = J.rightDim (PointedVec.simpleObject Paper18.PointedA (0, 2)) at hc
  rw [spherical_dimension_zero_two J hJ] at hc
  norm_num at hc

end Paper18.Category.AppendixBPointed
