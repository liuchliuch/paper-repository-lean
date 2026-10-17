import Paper18.Category.CrossedBraidedGaugingGrading

/-! # Genuine crossed braiding data for a weak monoidal action

These are the structural unit, two crossed hexagon, and action-equivariance
squares. The entire graded category has no ordinary braiding. No
braided equivariantization, nondegeneracy, or extension-existence statement
is included in the structure.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.CrossedBraidedGauging
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  (P : Grading G C) (A : WeakAction G C)
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]

/-- The actual weak action permutes the actual grading projectors by
conjugation. -/
structure GradedAction where
  map_projection (a g : G) (X : C) :
    (A.ρ a).map ((P.projection g).app X) =
      (P.projection (a * g * a⁻¹)).app ((A.ρ a).obj X)

namespace GradedAction
variable {P A} (Q : GradedAction P A)

include Q in
/-- An actual translate has its actual conjugated homogeneous degree. -/
theorem homogeneous_map (a : G) {g : G} {X : C} (hX : P.Homogeneous g X) :
    P.Homogeneous (a * g * a⁻¹) ((A.ρ a).obj X) := by
  have h := Q.map_projection a g X
  rw [hX] at h
  erw [CategoryTheory.Functor.map_id] at h
  exact h.symm

end GradedAction

/-- The genuine weak-action conjugation comparison, using its specified
multiplication isomorphisms and the actual group identity. -/
def actionConjugationIso (a g : G) :
    A.ρ a ⋙ A.ρ (a * g * a⁻¹) ≅ A.ρ g ⋙ A.ρ a :=
  A.mulIso (a * g * a⁻¹) a ≪≫
    eqToIso (congrArg A.ρ (by simp [mul_assoc])) ≪≫ (A.mulIso a g).symm

/-- The structural axioms of a genuine G-crossed braiding. Every crossing
is an actual isomorphism, defined only when its first object has its
specified actual homogeneous degree. -/
structure CrossedBraiding (Q : GradedAction P A) where
  crossing (g : G) (X : C) (hX : P.Homogeneous g X) (Y : C) :
    X ⊗ Y ≅ (A.ρ g).obj Y ⊗ X
  naturality_left (g : G) {X X' : C}
      (hX : P.Homogeneous g X) (hX' : P.Homogeneous g X')
      (f : X ⟶ X') (Y : C) :
    (f ▷ Y) ≫ (crossing g X' hX' Y).hom =
      (crossing g X hX Y).hom ≫ ((A.ρ g).obj Y ◁ f)
  naturality_right (g : G) (X : C) (hX : P.Homogeneous g X)
      {Y Y' : C} (f : Y ⟶ Y') :
    (X ◁ f) ≫ (crossing g X hX Y').hom =
      (crossing g X hX Y).hom ≫ ((A.ρ g).map f ▷ X)
  unit_left (Y : C) :
    (crossing 1 (𝟙_ C) P.homogeneous_unit Y).hom =
      (λ_ Y).hom ≫ A.unitIso.inv.app Y ≫ (ρ_ ((A.ρ 1).obj Y)).inv
  unit_right (g : G) (X : C) (hX : P.Homogeneous g X) :
    (crossing g X hX (𝟙_ C)).hom =
      (ρ_ X).hom ≫ (λ_ X).inv ≫ (ε (A.ρ g) ▷ X)
  hexagon_right (g : G) (X : C) (hX : P.Homogeneous g X) (Y Z : C) :
    (crossing g X hX (Y ⊗ Z)).hom =
      (α_ X Y Z).inv ≫ ((crossing g X hX Y).hom ▷ Z) ≫
        (α_ ((A.ρ g).obj Y) X Z).hom ≫
          ((A.ρ g).obj Y ◁ (crossing g X hX Z).hom) ≫
            (α_ ((A.ρ g).obj Y) ((A.ρ g).obj Z) X).inv ≫
              (μ (A.ρ g) Y Z ▷ X)
  hexagon_left (g h : G) (X Y : C)
      (hX : P.Homogeneous g X) (hY : P.Homogeneous h Y) (Z : C) :
    (crossing (g * h) (X ⊗ Y) (P.homogeneous_tensor hX hY) Z).hom =
      (α_ X Y Z).hom ≫ (X ◁ (crossing h Y hY Z).hom) ≫
        (α_ X ((A.ρ h).obj Z) Y).inv ≫
          ((crossing g X hX ((A.ρ h).obj Z)).hom ▷ Y) ≫
            (α_ ((A.ρ g).obj ((A.ρ h).obj Z)) X Y).hom ≫
              ((A.mulIso g h).hom.app Z ▷ (X ⊗ Y))
  action_equivariance (a g : G) (X : C) (hX : P.Homogeneous g X) (Y : C) :
    μ (A.ρ a) X Y ≫ (A.ρ a).map (crossing g X hX Y).hom =
      (crossing (a * g * a⁻¹) ((A.ρ a).obj X) (Q.homogeneous_map a hX)
        ((A.ρ a).obj Y)).hom ≫
        ((actionConjugationIso A a g).hom.app Y ▷ (A.ρ a).obj X) ≫
          μ (A.ρ a) ((A.ρ g).obj Y) X

/-- Faithfulness of the actual grading means every degree contains an
actual nonzero object; it is not part of crossed-braiding coherence. -/
def Grading.Faithful : Prop :=
  ∀ g : G, ∃ X : C, P.Homogeneous g X ∧ ¬ IsZero X

end Paper18.Category.CrossedBraidedGauging
