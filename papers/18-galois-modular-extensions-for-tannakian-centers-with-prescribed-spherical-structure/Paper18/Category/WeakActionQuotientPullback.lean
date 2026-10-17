import Paper18.Category.WeakActionQuotientConstruction
import Paper18.Category.WeakActionQuotientKernel

/-! # Pullback of weak actions and their actual coherent isomorphisms -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category
universe v u w w'
namespace Paper18.Category.WeakAction
variable {Γ : Type w} [Group Γ] {G : Type w'} [Group G]
  {C : Type u} [Category.{v} C]

private lemma assoc_transport (B : WeakAction G C) (a b c d e l r : G)
    (hd : b * c = d) (he : a * b = e) (hl : a * d = l) (hr : e * c = r)
    (h : r = l) (X : C) :
    (B.ρ a).map ((B.mulIso b c).hom.app X ≫ (rhoEqIso B hd).hom.app X) ≫
      (B.mulIso a d).hom.app X ≫ (rhoEqIso B hl).hom.app X =
    ((B.mulIso a b).hom.app ((B.ρ c).obj X) ≫
      (rhoEqIso B he).hom.app ((B.ρ c).obj X)) ≫
      ((B.mulIso e c).hom.app X ≫ (rhoEqIso B hr).hom.app X) ≫
        eqToHom (congrArg (fun g => (B.ρ g).obj X) h) := by
  cases hd; cases he; cases hl; cases hr
  simpa only [rhoEqIso, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id] using B.assoc a b c X

private lemma one_mul_transport (B : WeakAction G C) (a b c : G)
    (hb : b = 1) (hc : b * a = c) (h : c = a) (X : C) :
    ((B.mulIso b a).hom.app X ≫ (rhoEqIso B hc).hom.app X) ≫
      eqToHom (congrArg (fun g => (B.ρ g).obj X) h) =
    (rhoEqIso B hb).hom.app ((B.ρ a).obj X) ≫ B.unitIso.hom.app ((B.ρ a).obj X) := by
  cases hb; cases hc
  simpa only [rhoEqIso, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id, Category.id_comp] using B.one_mul a X

private lemma mul_one_transport (B : WeakAction G C) (a b c : G)
    (hb : b = 1) (hc : a * b = c) (h : c = a) (X : C) :
    ((B.mulIso a b).hom.app X ≫ (rhoEqIso B hc).hom.app X) ≫
      eqToHom (congrArg (fun g => (B.ρ g).obj X) h) =
    (B.ρ a).map ((rhoEqIso B hb).hom.app X ≫ B.unitIso.hom.app X) := by
  cases hb; cases hc
  simpa only [rhoEqIso, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.comp_id, Category.id_comp] using B.mul_one a X

/-- Actual restriction of a weak action along a group homomorphism. -/
def pullback (B : WeakAction G C) (p : Γ →* G) : WeakAction Γ C where
  ρ x := B.ρ (p x)
  unitIso := eqToIso (congrArg B.ρ p.map_one) ≪≫ B.unitIso
  mulIso x y := B.mulIso (p x) (p y) ≪≫
    eqToIso (congrArg B.ρ (p.map_mul x y).symm)
  assoc x y z X := by
    exact assoc_transport B (p x) (p y) (p z) (p (y*z)) (p (x*y))
      (p (x*(y*z))) (p ((x*y)*z)) (p.map_mul y z).symm (p.map_mul x y).symm
      (p.map_mul x (y*z)).symm (p.map_mul (x*y) z).symm (congrArg p (mul_assoc x y z)) X
  one_mul x X := by
    exact one_mul_transport B (p x) (p 1) (p (1*x)) p.map_one
      (p.map_mul 1 x).symm (congrArg p (_root_.one_mul x)) X
  mul_one x X := by
    exact mul_one_transport B (p x) (p 1) (p (x*1)) p.map_one
      (p.map_mul x 1).symm (congrArg p (_root_.mul_one x)) X

/-- An actual isomorphism of weak actions on the same category. Its natural
isomorphisms respect the actual unit and multiplication maps. -/
structure ActionIso (A B : WeakAction Γ C) where
  iso : ∀ x, A.ρ x ≅ B.ρ x
  unit (X : C) : (iso 1).hom.app X ≫ B.unitIso.hom.app X = A.unitIso.hom.app X
  mul (x y : Γ) (X : C) :
    (A.mulIso x y).hom.app X ≫ (iso (x * y)).hom.app X =
      (A.ρ x).map ((iso y).hom.app X) ≫
        (iso x).hom.app ((B.ρ y).obj X) ≫ (B.mulIso x y).hom.app X

variable {p : Γ →* G} {A : WeakAction Γ C}
  (D : FiberComparisons p A) (s : QuotientSection p)

/-- The actual natural comparison between the original translating functor
and the chosen lift of its quotient image. -/
def quotientPullbackIso (x : Γ) :
    A.ρ x ≅ (pullback (quotientAction D s) p).ρ x :=
  D.iso x (s.lift (p x)) (s.map_lift (p x)).symm

lemma quotientPullbackIso_mul (x y : Γ) (X : C) :
    (A.mulIso x y).hom.app X ≫ (quotientPullbackIso D s (x * y)).hom.app X =
      (A.ρ x).map ((quotientPullbackIso D s y).hom.app X) ≫
        (quotientPullbackIso D s x).hom.app
          (((pullback (quotientAction D s) p).ρ y).obj X) ≫
            ((pullback (quotientAction D s) p).mulIso x y).hom.app X := by
  dsimp only [quotientPullbackIso, pullback, quotientAction, quotientMulIso,
    Iso.trans_hom, NatTrans.comp_app]
  simp only [Category.assoc, eqToIso.hom, eqToHom_app]
  rw [D.iso_comp_eqToHom _ (congrArg s.lift (p.map_mul x y).symm) X]
  rw [← D.iso_mul_assoc, D.iso_trans]

lemma quotientPullbackIso_unit (X : C) :
    (quotientPullbackIso D s 1).hom.app X ≫
      (pullback (quotientAction D s) p).unitIso.hom.app X = A.unitIso.hom.app X := by
  dsimp only [quotientPullbackIso, pullback, quotientAction,
    Iso.trans_hom, NatTrans.comp_app]
  simp only [eqToIso.hom, eqToHom_app]
  rw [D.iso_comp_eqToHom_assoc _ (congrArg s.lift p.map_one) X]
  rw [D.iso_comp_eqToHom_assoc _ s.lift_one X]
  rw [D.iso_refl, Category.id_comp]

/-- The original Γ-action is actually isomorphic to the pullback of the
constructed quotient action; each component is the canonical kernel comparison. -/
def quotientActionIso : ActionIso A (pullback (quotientAction D s) p) where
  iso := quotientPullbackIso D s
  unit := quotientPullbackIso_unit D s
  mul := quotientPullbackIso_mul D s

end Paper18.Category.WeakAction
