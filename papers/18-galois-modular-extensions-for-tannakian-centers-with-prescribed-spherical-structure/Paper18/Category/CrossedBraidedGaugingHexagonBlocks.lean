import Paper18.Category.CrossedBraidedGaugingCrossing
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-! # Actual crossed hexagons after closing equivariant legs -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe v u w
namespace Paper18.Category.CrossedBraidedGauging.CrossedBraiding
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  {P : Grading G C} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  {Q : GradedAction P A} (B : CrossedBraiding P A Q)

/-- The genuine crossed tensor hexagon and actual equivariant tensor
structure give the ordinary right tensor hexagon on homogeneous blocks. -/
theorem blockIso_tensor_right (g : G) (X : C) (hX : P.Homogeneous g X)
    (Y Z : A.Equivariant) :
    (B.blockIso g X hX (Y ⊗ Z)).hom =
      (α_ X Y.obj Z.obj).inv ≫ ((B.blockIso g X hX Y).hom ▷ Z.obj) ≫
        (α_ Y.obj X Z.obj).hom ≫ (Y.obj ◁ (B.blockIso g X hX Z).hom) ≫
          (α_ Y.obj Z.obj X).inv := by
  rw [blockIso_hom]
  change (B.crossing g X hX (Y.obj ⊗ Z.obj)).hom ≫
    ((δ (A.ρ g) Y.obj Z.obj ≫
      ((Y.structureIso g).hom ⊗ₘ (Z.structureIso g).hom)) ▷ X) = _
  rw [B.hexagon_right]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← comp_whiskerRight_assoc, Functor.Monoidal.μ_δ, id_whiskerRight, Category.id_comp]
  simp only [blockIso_hom]
  simp only [tensorHom_def', comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [← associator_inv_naturality_middle_assoc,
    ← associator_inv_naturality_left,
    whisker_exchange_assoc, whisker_exchange_assoc,
    ← associator_naturality_left_assoc]

/-- The other genuine crossed hexagon closes using the actual weak
equivariance multiplication law of the object crossing both factors. -/
theorem blockIso_tensor_left (g h : G) (X Y : C)
    (hX : P.Homogeneous g X) (hY : P.Homogeneous h Y)
    (Z : A.Equivariant) :
    (B.blockIso (g * h) (X ⊗ Y) (P.homogeneous_tensor hX hY) Z).hom =
      (α_ X Y Z.obj).hom ≫ (X ◁ (B.blockIso h Y hY Z).hom) ≫
        (α_ X Z.obj Y).inv ≫ ((B.blockIso g X hX Z).hom ▷ Y) ≫
          (α_ Z.obj X Y).hom := by
  rw [blockIso_hom, B.hexagon_left]
  simp only [Category.assoc]
  rw [← comp_whiskerRight, ← Z.mul]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← associator_naturality_left_assoc,
    ← associator_naturality_left]
  rw [← comp_whiskerRight_assoc, ← B.naturality_right]
  simp only [comp_whiskerRight, blockIso_hom, whiskerLeft_comp, Category.assoc]
  rw [← associator_inv_naturality_middle_assoc]

end Paper18.Category.CrossedBraidedGauging.CrossedBraiding
