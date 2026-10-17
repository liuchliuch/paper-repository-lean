import Paper18.Category.CrossedBraidedGaugingNeutral

/-! # The actual regular unit object detects the crossed degree -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Functor.LaxMonoidal Functor.OplaxMonoidal
universe v u w
namespace Paper18.Category.CrossedBraidedGauging
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasFiniteBiproducts C]
  {P : Grading G C} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  [∀ g : G, (A.ρ g).Additive]

/-- The actual regular object is induction of the tensor unit. -/
abbrev regularUnit : A.Equivariant := A.induction (𝟙_ C)

def regularUnitInjection (h : G) : (𝟙_ C) ⟶ (regularUnit (A := A)).obj :=
  ε (A.ρ h) ≫ biproduct.ι (fun k : G => (A.ρ k).obj (𝟙_ C)) h

def regularUnitProjection (h : G) : (regularUnit (A := A)).obj ⟶ (𝟙_ C) :=
  biproduct.π (fun k : G => (A.ρ k).obj (𝟙_ C)) h ≫ η (A.ρ h)

@[simp, reassoc] theorem regularUnitInjection_projection (h k : G) :
    regularUnitInjection (A := A) h ≫ regularUnitProjection (A := A) k =
      if h = k then 𝟙 (𝟙_ C) else 0 := by
  by_cases he : h = k
  · subst k
    simp only [regularUnitInjection, regularUnitProjection, Category.assoc,
      biproduct.ι_π_self_assoc, Functor.Monoidal.ε_η, if_pos rfl]
    rfl
  · simp only [regularUnitInjection, regularUnitProjection, Category.assoc,
      biproduct.ι_π_ne_assoc _ he, comp_zero, if_neg he]
    erw [zero_comp, comp_zero]

/-- The specified weak monoidal multiplication makes the normalized
unit summands transform by the actual left regular permutation. -/
@[reassoc] theorem regularUnitInjection_action (g h : G) :
    ε (A.ρ g) ≫ (A.ρ g).map (regularUnitInjection (A := A) h) ≫
        ((regularUnit (A := A)).structureIso g).hom =
      regularUnitInjection (A := A) (g * h) := by
  have hu := NatTrans.IsMonoidal.unit (τ := (A.mulIso g h).hom)
  change (ε (A.ρ g) ≫ (A.ρ g).map (ε (A.ρ h))) ≫
    (A.mulIso g h).hom.app (𝟙_ C) = ε (A.ρ (g * h)) at hu
  dsimp only [regularUnitInjection]
  change ε (A.ρ g) ≫ (A.ρ g).map (ε (A.ρ h) ≫
    biproduct.ι (fun k : G => (A.ρ k).obj (𝟙_ C)) h) ≫
    (A.inductionIso (𝟙_ C) g).hom = _
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [A.map_ι_inductionIso]
  rw [← Category.assoc, ← Category.assoc, hu]

namespace GradedAction
variable (Q : GradedAction P A)

include Q in
theorem induction_homogeneous {X : C} (hX : P.Homogeneous 1 X) :
    P.Homogeneous 1 (A.induction X).obj := by
  change P.Homogeneous 1 (⨁ fun h : G => (A.ρ h).obj X)
  apply P.homogeneous_biproduct
  intro h
  simpa only [mul_one, mul_inv_cancel] using Q.homogeneous_map h hX

include Q in
theorem regularUnit_homogeneous : P.Homogeneous 1 (regularUnit (A := A)).obj := by
  exact Q.induction_homogeneous P.homogeneous_unit

end GradedAction

namespace CrossedBraiding
variable {Q : GradedAction P A} (B : CrossedBraiding P A Q)

/-- On an actual degree-g object, crossing the regular unit moves the
actual h summand to gh. -/
@[reassoc] theorem blockIso_regularUnitInjection (g h : G) (X : C)
    (hX : P.Homogeneous g X) :
    (X ◁ regularUnitInjection (A := A) h) ≫
        (B.blockIso g X hX (regularUnit (A := A))).hom =
      (ρ_ X).hom ≫ (λ_ X).inv ≫ (regularUnitInjection (A := A) (g * h) ▷ X) := by
  rw [blockIso_hom, ← Category.assoc, B.naturality_right, B.unit_right]
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight,
    Category.assoc, regularUnitInjection_action]

/-- The actual double crossing with the regular unit is exactly the
regular permutation of its actual summands. -/
@[reassoc] theorem regularUnit_monodromy (g h : G) (X : C)
    (hX : P.Homogeneous g X) :
    (X ◁ regularUnitInjection (A := A) h) ≫
        (B.blockIso g X hX (regularUnit (A := A))).hom ≫
          (B.neutralIso (regularUnit (A := A)).obj Q.regularUnit_homogeneous X).hom =
      X ◁ regularUnitInjection (A := A) (g * h) := by
  rw [B.blockIso_regularUnitInjection_assoc]
  rw [B.neutralIso_naturality_left P.homogeneous_unit Q.regularUnit_homogeneous,
    B.neutralIso_unit_left]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]

end CrossedBraiding
end Paper18.Category.CrossedBraidedGauging
