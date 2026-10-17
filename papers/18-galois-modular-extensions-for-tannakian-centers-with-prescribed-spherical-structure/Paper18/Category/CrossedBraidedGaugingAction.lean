import Paper18.Category.CrossedBraidedGaugingCrossing

/-! # The genuine action square for closed homogeneous crossings -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal
universe v u w
namespace Paper18.Category.CrossedBraidedGauging
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  {P : Grading G C} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]

/-- Actual equivariance identifies the two conjugated action words. -/
theorem structureIso_conjugation (Y : A.Equivariant) (a g : G) :
    (actionConjugationIso A a g).hom.app Y.obj ≫
        (A.ρ a).map (Y.structureIso g).hom ≫ (Y.structureIso a).hom =
      (A.ρ (a * g * a⁻¹)).map (Y.structureIso a).hom ≫
        (Y.structureIso (a * g * a⁻¹)).hom := by
  have ht {k l : G} (e : k = l) :
      (eqToIso (congrArg A.ρ e)).hom.app Y.obj ≫ (Y.structureIso l).hom =
        (Y.structureIso k).hom := by
    subst l
    simp
  dsimp only [actionConjugationIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Category.assoc]
  rw [Y.mul a g, ← Category.assoc ((A.mulIso a g).inv.app Y.obj),
    Iso.inv_hom_id_app, Category.id_comp, ht]
  exact (Y.mul (a * g * a⁻¹) a).symm
  all_goals simp [mul_assoc]

namespace CrossedBraiding
variable {Q : GradedAction P A} (B : CrossedBraiding P A Q)

/-- A closed actual homogeneous crossing commutes with translation and
the actual equivariant structure of its second object. -/
@[reassoc] theorem blockIso_action (a g : G) (X : C) (hX : P.Homogeneous g X)
    (Y : A.Equivariant) :
    μ (A.ρ a) X Y.obj ≫ (A.ρ a).map (B.blockIso g X hX Y).hom ≫
        δ (A.ρ a) Y.obj X ≫ ((Y.structureIso a).hom ▷ (A.ρ a).obj X) =
      ((A.ρ a).obj X ◁ (Y.structureIso a).hom) ≫
        (B.blockIso (a * g * a⁻¹) ((A.ρ a).obj X)
          (Q.homogeneous_map a hX) Y).hom := by
  simp only [blockIso_hom, Functor.map_comp, Category.assoc]
  rw [← Category.assoc (μ (A.ρ a) X Y.obj), B.action_equivariance]
  simp only [Category.assoc]
  rw [← Functor.LaxMonoidal.μ_natural_left_assoc]
  rw [Functor.Monoidal.μ_δ_assoc]
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight,
    Category.assoc, structureIso_conjugation Y a g, comp_whiskerRight]
  rw [← Category.assoc, ← B.naturality_right]
  exact Category.assoc _ _ _

end CrossedBraiding
end Paper18.Category.CrossedBraidedGauging
