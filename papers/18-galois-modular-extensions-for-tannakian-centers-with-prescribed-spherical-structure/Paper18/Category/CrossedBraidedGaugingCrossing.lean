import Paper18.Category.CrossedBraidedGaugingBasic

/-! # Actual homogeneous crossings against genuine equivariant objects

The actual equivariant structure closes the translated leg of each actual
crossing. Naturality uses precisely the actual equivariant morphism square.
-/
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

/-- An actual homogeneous crossing closes its translated leg using the
actual equivariant structure isomorphism. -/
def blockIso (g : G) (X : C) (hX : P.Homogeneous g X) (Y : A.Equivariant) :
    X ⊗ Y.obj ≅ Y.obj ⊗ X :=
  B.crossing g X hX Y.obj ≪≫ whiskerRightIso (Y.structureIso g) X

@[simp] theorem blockIso_hom (g : G) (X : C) (hX : P.Homogeneous g X)
    (Y : A.Equivariant) :
    (B.blockIso g X hX Y).hom =
      (B.crossing g X hX Y.obj).hom ≫ ((Y.structureIso g).hom ▷ X) := rfl

/-- Naturality in an actual homogeneous first argument. -/
@[reassoc] theorem blockIso_naturality_left (g : G) {X X' : C}
    (hX : P.Homogeneous g X) (hX' : P.Homogeneous g X') (f : X ⟶ X')
    (Y : A.Equivariant) :
    (f ▷ Y.obj) ≫ (B.blockIso g X' hX' Y).hom =
      (B.blockIso g X hX Y).hom ≫ (Y.obj ◁ f) := by
  simp only [blockIso_hom]
  rw [← Category.assoc, B.naturality_left g hX hX' f Y.obj, Category.assoc, whisker_exchange]
  simp only [Category.assoc]

/-- Naturality in an actual equivariant second argument. -/
@[reassoc] theorem blockIso_naturality_right (g : G) (X : C)
    (hX : P.Homogeneous g X) {Y Y' : A.Equivariant} (f : Y ⟶ Y') :
    (X ◁ f.hom) ≫ (B.blockIso g X hX Y').hom =
      (B.blockIso g X hX Y).hom ≫ (f.hom ▷ X) := by
  simp only [blockIso_hom]
  rw [← Category.assoc, B.naturality_right, Category.assoc,
    ← comp_whiskerRight, f.comm g, comp_whiskerRight]
  simp only [Category.assoc]

/-- The actual neutral crossing of the unit has the usual unit value. -/
@[simp] theorem blockIso_unit_left (Y : A.Equivariant) :
    (B.blockIso 1 (𝟙_ C) P.homogeneous_unit Y).hom =
      (λ_ Y.obj).hom ≫ (ρ_ Y.obj).inv := by
  rw [blockIso_hom, B.unit_left, Y.unit]
  simp only [Category.assoc]
  rw [← rightUnitor_inv_naturality]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

/-- The actual equivariant unit closes the actual crossed right-unit map. -/
@[simp] theorem blockIso_unit_right (g : G) (X : C) (hX : P.Homogeneous g X) :
    (B.blockIso g X hX (𝟙_ A.Equivariant)).hom =
      (ρ_ X).hom ≫ (λ_ X).inv := by
  rw [blockIso_hom]
  change (B.crossing g X hX (𝟙_ C)).hom ≫ (η (A.ρ g) ▷ X) = _
  rw [B.unit_right]
  change ((ρ_ X).hom ≫ (λ_ X).inv ≫ (ε (A.ρ g) ▷ X)) ≫ (η (A.ρ g) ▷ X) = _
  simp only [Category.assoc]
  rw [← comp_whiskerRight, Functor.Monoidal.ε_η, id_whiskerRight, Category.comp_id]

end Paper18.Category.CrossedBraidedGauging.CrossedBraiding
