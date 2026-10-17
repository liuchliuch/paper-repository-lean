import Paper18.Category.ModuleAlphaInductionDensityDiagramBasic
import Paper18.Category.ModuleAlphaInductionCentral

/-! # The true half-braiding calculation for the density diagram

All crossings below are actual half-braidings of actual central objects.
There is no braiding on the ambient category.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.ModuleAlphaInduction
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {n p : D}

/-- The actual matrix action on the central object's left tensor image. -/
def centralCapAction (Z : Center D) (cap : p ⊗ n ⟶ 𝟙_ D) :
    (n ⊗ p) ⊗ (Z.1 ⊗ n) ⟶ Z.1 ⊗ n :=
  (centralLineator (M := D) Z (n ⊗ p) n).inv ≫ Z.1 ◁ capAction cap

/-- The actual positive/negative lineator formula, in the ambient tensor notation. -/
@[reassoc] theorem centralCapAction_def (Z : Center D) (cap : p ⊗ n ⟶ 𝟙_ D) :
    centralCapAction Z cap = (α_ (n ⊗ p) Z.1 n).inv ≫
      (Z.2.β (n ⊗ p)).inv ▷ n ≫ (α_ Z.1 (n ⊗ p) n).hom ≫ Z.1 ◁ capAction cap := by
  dsimp only [centralCapAction, centralLineator, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, MonoidalLeftAction.actionRight_map]
  simp only [Category.assoc]
  rfl

/-- Actual half-braiding naturality at the actual matrix action, together
with its hexagon, is the true neutral/odd crossing identity. -/
@[reassoc] theorem centralCapAction_braiding (Z : Center D)
    (cap : p ⊗ n ⟶ 𝟙_ D) :
    centralCapAction Z cap ≫ (Z.2.β n).hom =
      (n ⊗ p) ◁ (Z.2.β n).hom ≫
        (α_ (n ⊗ p) n Z.1).inv ≫ capAction cap ▷ Z.1 := by
  dsimp only [centralCapAction, centralLineator, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, MonoidalLeftAction.actionRight_map]
  simp only [Category.assoc]
  change (α_ (n ⊗ p) Z.1 n).inv ≫ (Z.2.β (n ⊗ p)).inv ▷ n ≫
    (α_ Z.1 (n ⊗ p) n).hom ≫ Z.1 ◁ capAction cap ≫ (Z.2.β n).hom = _
  rw [Z.2.naturality, Z.2.monoidal]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, inv_hom_whiskerRight_assoc,
    Iso.inv_hom_id_assoc]

/-- Solving the true crossing identity expresses the actual action by
conjugation with the actual half-braiding. -/
@[reassoc] theorem centralCapAction_eq (Z : Center D)
    (cap : p ⊗ n ⟶ 𝟙_ D) :
    centralCapAction Z cap = (n ⊗ p) ◁ (Z.2.β n).hom ≫
      (α_ (n ⊗ p) n Z.1).inv ≫ capAction cap ▷ Z.1 ≫ (Z.2.β n).inv := by
  calc
    _ = (centralCapAction Z cap ≫ (Z.2.β n).hom) ≫ (Z.2.β n).inv := by simp
    _ = _ := by rw [centralCapAction_braiding]; simp only [Category.assoc]

/-- Conjugating the genuine module/evaluation relation produces the
actual matrix-action intertwiner relation. -/
theorem capAction_intertwiner_of_central
    (Z W : Center D) (cap : p ⊗ n ⟶ 𝟙_ D)
    (f : Z.1 ⊗ n ⟶ W.1 ⊗ n)
    (h : centralCapAction Z cap ≫ f = (n ⊗ p) ◁ f ≫ centralCapAction W cap) :
    (α_ (n ⊗ p) n Z.1).inv ≫ capAction cap ▷ Z.1 ≫
      ((Z.2.β n).inv ≫ f ≫ (W.2.β n).hom) =
    (n ⊗ p) ◁ ((Z.2.β n).inv ≫ f ≫ (W.2.β n).hom) ≫
      (α_ (n ⊗ p) n W.1).inv ≫ capAction cap ▷ W.1 := by
  have hh := congrArg
    (fun k => (n ⊗ p) ◁ (Z.2.β n).inv ≫ k ≫ (W.2.β n).hom) h
  simpa only [centralCapAction_eq, whiskerLeft_comp, Category.assoc,
    whiskerLeft_inv_hom_assoc, Iso.inv_hom_id, Category.comp_id] using hh

/-- The genuine normalized density identity for the conjugated actual
morphism, using only true central half-braidings and actual module naturality. -/
theorem conjugated_eq_whiskerLeft_closure
    (Z W : Center D) (cup : 𝟙_ D ⟶ p ⊗ n) (cap : p ⊗ n ⟶ 𝟙_ D)
    (hnorm : cup ≫ cap = 𝟙 (𝟙_ D)) (f : Z.1 ⊗ n ⟶ W.1 ⊗ n)
    (h : centralCapAction Z cap ≫ f = (n ⊗ p) ◁ f ≫ centralCapAction W cap) :
    (Z.2.β n).inv ≫ f ≫ (W.2.β n).hom =
      n ◁ ModuleFunctor.leftClosure cup cap ((Z.2.β n).inv ≫ f ≫ (W.2.β n).hom) :=
  eq_whiskerLeft_leftClosure_of_capAction cup cap hnorm _
    (capAction_intertwiner_of_central Z W cap f h)

/-- Actual centrality of the extracted contraction recovers the original
morphism as actual right tensoring. In applications centrality is derived
by lifting through the actual full neutral inclusion. -/
theorem eq_closure_whiskerRight_of_central
    (Z W : Center D) (cup : 𝟙_ D ⟶ p ⊗ n) (cap : p ⊗ n ⟶ 𝟙_ D)
    (hnorm : cup ≫ cap = 𝟙 (𝟙_ D)) (f : Z.1 ⊗ n ⟶ W.1 ⊗ n)
    (h : centralCapAction Z cap ≫ f = (n ⊗ p) ◁ f ≫ centralCapAction W cap)
    (ha : let a := ModuleFunctor.leftClosure cup cap ((Z.2.β n).inv ≫ f ≫ (W.2.β n).hom)
      (a ▷ n) ≫ (W.2.β n).hom = (Z.2.β n).hom ≫ n ◁ a) :
    f = ModuleFunctor.leftClosure cup cap ((Z.2.β n).inv ≫ f ≫ (W.2.β n).hom) ▷ n := by
  let a := ModuleFunctor.leftClosure cup cap ((Z.2.β n).inv ≫ f ≫ (W.2.β n).hom)
  have hg := conjugated_eq_whiskerLeft_closure Z W cup cap hnorm f h
  apply (cancel_mono (W.2.β n).hom).mp
  calc
    f ≫ (W.2.β n).hom = (Z.2.β n).hom ≫
        ((Z.2.β n).inv ≫ f ≫ (W.2.β n).hom) := by simp
    _ = (Z.2.β n).hom ≫ n ◁ a := by rw [hg]
    _ = (a ▷ n) ≫ (W.2.β n).hom := ha.symm

end Paper18.Category.ModuleAlphaInduction
