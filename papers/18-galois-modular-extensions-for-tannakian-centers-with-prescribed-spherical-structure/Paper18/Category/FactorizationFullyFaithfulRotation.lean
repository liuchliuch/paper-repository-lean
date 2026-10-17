import Paper18.Category.FactorizationFullyFaithfulCross

/-!
# Actual rigid Hom rotation for factorization

The tensor adjunctions move the positive target and negative source across
Hom. They produce a cross Hom between the canonical images. Combining this
actual linear equivalence with the proved cross Hom calculation yields the
factorization Hom dimension formula.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits CategoryTheory.Functor.Monoidal
universe v u w
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C]

/-- Actual linear Frobenius reciprocity turns a factored Hom into a cross
Hom of the positive and negative images. The pairings are transported by
the actual strong monoidal canonical embeddings. -/
def factorizationHomRotation (X X' Y Y' : C) :
    ((positive C).obj X ⊗ (negative C).obj Y ⟶
        (positive C).obj X' ⊗ (negative C).obj Y') ≃ₗ[ℂ]
      ((positive C).obj (X'ᘁ ⊗ X) ⟶ (negative C).obj (Y' ⊗ Yᘁ)) := by
  letI := mapExactPairing (positive C) X' X'ᘁ
  letI := mapExactPairing (negative C) Y Yᘁ
  exact (tensorLeftHomLinearEquiv
      ((positive C).obj X ⊗ (negative C).obj Y)
      ((positive C).obj X') ((positive C).obj X'ᘁ) ((negative C).obj Y')).symm.trans
    ((CategoryTheory.Linear.homCongr ℂ
      (α_ ((positive C).obj X'ᘁ) ((positive C).obj X) ((negative C).obj Y)).symm
      (Iso.refl _)).trans
    ((tensorRightHomLinearEquiv
      ((positive C).obj X'ᘁ ⊗ (positive C).obj X)
      ((negative C).obj Y) ((negative C).obj Yᘁ) ((negative C).obj Y')).trans
    (CategoryTheory.Linear.homCongr ℂ (μIso (positive C) X'ᘁ X)
      (μIso (negative C) Y' Yᘁ))))

variable [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
include S

/-- The actual unit multiplicity in a dual-source tensor is the actual
source-to-target Hom dimension, by semisimplicity and Frobenius reciprocity. -/
lemma multiplicity_unit_dual_tensor (X X' : C) :
    S.multiplicity (X'ᘁ ⊗ X) S.unitLabel = Module.finrank ℂ (X ⟶ X') := by
  calc
    _ = Module.finrank ℂ (X'ᘁ ⊗ X ⟶ S.simpleObject S.unitLabel) :=
      S.multiplicity_eq_finrank_hom _ _
    _ = Module.finrank ℂ (X'ᘁ ⊗ X ⟶ 𝟙_ C) :=
      finrank_hom_iso (Iso.refl _) S.unitIso
    _ = Module.finrank ℂ (X ⟶ X' ⊗ 𝟙_ C) := finrank_tensorLeft_hom X X' X'ᘁ (𝟙_ C)
    _ = _ := finrank_hom_iso (Iso.refl _) (ρ_ X')

/-- The analogous unit multiplicity is obtained directly from the right
actual tensor adjunction. -/
lemma multiplicity_unit_tensor_dual (Y Y' : C) :
    S.multiplicity (Y' ⊗ Yᘁ) S.unitLabel = Module.finrank ℂ (Y ⟶ Y') := by
  calc
    _ = Module.finrank ℂ (𝟙_ C ⟶ Y' ⊗ Yᘁ) := finrank_hom_iso S.unitIso (Iso.refl _)
    _ = Module.finrank ℂ ((𝟙_ C) ⊗ Y ⟶ Y') :=
      (finrank_tensorRight_hom (𝟙_ C) Y Yᘁ Y').symm
    _ = _ := finrank_hom_iso (λ_ Y) (Iso.refl _)

/-- Nondegeneracy yields the correct dimension of every actual factored
Hom space, without assuming simple-pair simplicity or full faithfulness. -/
lemma finrank_factorizationHom (hC : IsNondegenerate (C := C)) (X X' Y Y' : C) :
    Module.finrank ℂ
      ((positive C).obj X ⊗ (negative C).obj Y ⟶
        (positive C).obj X' ⊗ (negative C).obj Y') =
      Module.finrank ℂ (X ⟶ X') * Module.finrank ℂ (Y ⟶ Y') := by
  rw [(factorizationHomRotation X X' Y Y').finrank_eq,
    finrank_positive_negative S hC, multiplicity_unit_dual_tensor,
    multiplicity_unit_tensor_dual]

/-- In particular, pair images have the actual Kronecker-delta Hom law. -/
lemma finrank_factorization_simpleHom (hC : IsNondegenerate (C := C)) (i i' j j' : ι) :
    Module.finrank ℂ
      ((positive C).obj (S.simpleObject i) ⊗ (negative C).obj (S.simpleObject j) ⟶
        (positive C).obj (S.simpleObject i') ⊗ (negative C).obj (S.simpleObject j')) =
      (if i = i' then 1 else 0) * (if j = j' then 1 else 0) := by
  rw [finrank_factorizationHom S hC, S.finrank_simple_hom_simple,
    S.finrank_simple_hom_simple]

end Paper18.Category.Drinfeld
