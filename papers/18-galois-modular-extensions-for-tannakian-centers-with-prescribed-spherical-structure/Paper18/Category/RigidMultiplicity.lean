import Paper18.Category.Multiplicity
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-! Actual linear Frobenius reciprocity and Hom-duality equivalences. -/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The left tensor adjunction is complex linear on actual Hom spaces. -/
def tensorLeftHomLinearEquiv (X Y Y' Z : C) [ExactPairing Y Y'] :
    (Y' ⊗ X ⟶ Z) ≃ₗ[ℂ] (X ⟶ Y ⊗ Z) where
  toEquiv := tensorLeftHomEquiv X Y Y' Z
  map_add' f g := by simp [tensorLeftHomEquiv]
  map_smul' r f := by simp [tensorLeftHomEquiv]

/-- The right tensor adjunction is complex linear on actual Hom spaces. -/
def tensorRightHomLinearEquiv (X Y Y' Z : C) [ExactPairing Y Y'] :
    (X ⊗ Y ⟶ Z) ≃ₗ[ℂ] (X ⟶ Z ⊗ Y') where
  toEquiv := tensorRightHomEquiv X Y Y' Z
  map_add' f g := by simp [tensorRightHomEquiv]
  map_smul' r f := by simp [tensorRightHomEquiv]

/-- Duality on actual Hom spaces is a linear equivalence. This derives the
needed bijection directly from the two rigid tensor adjunctions. -/
def rightDualHomLinearEquiv (X Y : C) [HasRightDual X] [HasRightDual Y] :
    (X ⟶ Y) ≃ₗ[ℂ] (Yᘁ ⟶ Xᘁ) :=
  (CategoryTheory.Linear.homCongr ℂ (Iso.refl X) (ρ_ Y).symm).trans
    ((tensorLeftHomLinearEquiv X Y (Yᘁ) (𝟙_ C)).symm.trans
      ((tensorRightHomLinearEquiv (Yᘁ) X (Xᘁ) (𝟙_ C)).trans
        (CategoryTheory.Linear.homCongr ℂ (Iso.refl (Yᘁ)) (λ_ (Xᘁ)))))

/-- Hom dimensions are reversed by the actual right-dual operation. -/
theorem finrank_rightDual_hom (X Y : C) [HasRightDual X] [HasRightDual Y] :
    Module.finrank ℂ (Yᘁ ⟶ Xᘁ) = Module.finrank ℂ (X ⟶ Y) :=
  (rightDualHomLinearEquiv X Y).finrank_eq.symm

/-- Linear Frobenius reciprocity on the left, stated as Hom dimension. -/
theorem finrank_tensorLeft_hom (X Y Y' Z : C) [ExactPairing Y Y'] :
    Module.finrank ℂ (Y' ⊗ X ⟶ Z) = Module.finrank ℂ (X ⟶ Y ⊗ Z) :=
  (tensorLeftHomLinearEquiv X Y Y' Z).finrank_eq

/-- Linear Frobenius reciprocity on the right, stated as Hom dimension. -/
theorem finrank_tensorRight_hom (X Y Y' Z : C) [ExactPairing Y Y'] :
    Module.finrank ℂ (X ⊗ Y ⟶ Z) = Module.finrank ℂ (X ⟶ Z ⊗ Y') :=
  (tensorRightHomLinearEquiv X Y Y' Z).finrank_eq

namespace FiniteSemisimpleSkeleton

variable [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- A right dual of an actual simple object is simple, derived from the
linear duality equivalence and finite semisimplicity. -/
theorem simple_rightDual (S : FiniteSemisimpleSkeleton C ι) (X : C) [Simple X] [HasRightDual X] : Simple (Xᘁ) := by
  apply S.simple_of_finrank_end_eq_one
  rw [finrank_rightDual_hom]
  exact CategoryTheory.finrank_endomorphism_simple_eq_one ℂ X

section RightRigid
variable [RightRigidCategory C]
attribute [local instance 2000] RightRigidCategory.rightDual

/-- Chosen label of the actual right dual of a simple representative. -/
def dualLabel (S : FiniteSemisimpleSkeleton C ι) (i : ι) : ι := by
  letI := S.simple_rightDual (S.simpleObject i)
  exact Classical.choose (S.simple_isomorphic_representative ((S.simpleObject i)ᘁ))

/-- The dual label is connected to the actual categorical dual by an isomorphism. -/
def dualIso (i : ι) : S.simpleObject (S.dualLabel i) ≅ (S.simpleObject i)ᘁ := by
  letI := S.simple_rightDual (S.simpleObject i)
  exact (Classical.choice
    (Classical.choose_spec (S.simple_isomorphic_representative ((S.simpleObject i)ᘁ)))).symm

/-- Left Frobenius reciprocity for actual Hom-defined fusion coefficients. -/
theorem fusionCoeff_dual (i j k : ι) :
    S.fusionCoeff i j k = S.fusionCoeff (S.dualLabel i) k j := by
  calc
    _ = Module.finrank ℂ (S.simpleObject k ⟶ S.simpleObject i ⊗ S.simpleObject j) := rfl
    _ = Module.finrank ℂ ((S.simpleObject i)ᘁ ⊗ S.simpleObject k ⟶ S.simpleObject j) :=
      (tensorLeftHomLinearEquiv (S.simpleObject k) (S.simpleObject i)
        ((S.simpleObject i)ᘁ) (S.simpleObject j)).finrank_eq.symm
    _ = Module.finrank ℂ (S.simpleObject j ⟶ (S.simpleObject i)ᘁ ⊗ S.simpleObject k) :=
      S.finrank_hom_comm _ _
    _ = S.fusionCoeff (S.dualLabel i) k j :=
      (finrank_hom_iso (Iso.refl (S.simpleObject j))
        (S.dualIso i ⊗ᵢ Iso.refl (S.simpleObject k))).symm

/-- Right Frobenius reciprocity for actual fusion coefficients. -/
theorem fusionCoeff_right (i j k : ι) :
    S.fusionCoeff i j k = S.fusionCoeff k (S.dualLabel j) i := by
  calc
    _ = Module.finrank ℂ (S.simpleObject i ⊗ S.simpleObject j ⟶ S.simpleObject k) :=
      S.finrank_hom_comm _ _
    _ = Module.finrank ℂ (S.simpleObject i ⟶ S.simpleObject k ⊗ (S.simpleObject j)ᘁ) :=
      (tensorRightHomLinearEquiv (S.simpleObject i) (S.simpleObject j)
        ((S.simpleObject j)ᘁ) (S.simpleObject k)).finrank_eq
    _ = S.fusionCoeff k (S.dualLabel j) i :=
      (finrank_hom_iso (Iso.refl (S.simpleObject i))
        (Iso.refl (S.simpleObject k) ⊗ᵢ S.dualIso j)).symm

variable [Simple (𝟙_ C)]

/-- Left and right dual labels coincide and duality is an involution; this
is derived from the two actual rigidity adjunctions and Schur's unit law. -/
theorem dualLabel_involutive (i : ι) : S.dualLabel (S.dualLabel i) = i := by
  have h1 : S.fusionCoeff (S.dualLabel i) i S.unitLabel = 1 := by
    rw [S.fusionCoeff_right, S.fusionCoeff_one_left S.unitLabel S.unitIso]
    simp
  have h2 : S.fusionCoeff (S.dualLabel i) i S.unitLabel =
      if S.dualLabel (S.dualLabel i) = i then 1 else 0 := by
    rw [S.fusionCoeff_dual, S.fusionCoeff_one_right S.unitLabel S.unitIso]
  by_contra hn
  rw [if_neg hn, h1] at h2
  contradiction

/-- The dual of the unit label is the unit label. -/
theorem dualLabel_unit : S.dualLabel S.unitLabel = S.unitLabel := by
  have h1 : S.fusionCoeff S.unitLabel S.unitLabel S.unitLabel = 1 := by
    rw [S.fusionCoeff_one_left S.unitLabel S.unitIso]
    simp
  have h2 : S.fusionCoeff S.unitLabel S.unitLabel S.unitLabel =
      if S.dualLabel S.unitLabel = S.unitLabel then 1 else 0 := by
    rw [S.fusionCoeff_dual, S.fusionCoeff_one_right S.unitLabel S.unitIso]
  by_contra hn
  rw [if_neg hn, h1] at h2
  contradiction

end RightRigid
end FiniteSemisimpleSkeleton

end Paper18.Category
