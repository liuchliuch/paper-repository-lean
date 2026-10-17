import Paper18.Category.WeakActionQuotientBasic

/-! # Constructing the actual weak quotient action -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category
universe v u w w'
namespace Paper18.Category.WeakAction
variable {Γ : Type w} [Group Γ] {G : Type w'} [Group G]
  {C : Type u} [Category.{v} C] {p : Γ →* G} {A : WeakAction Γ C}
  (D : FiberComparisons p A) (s : QuotientSection p)

/-- The quotient multiplication uses the actual original multiplication
and the actual kernel comparison between two lifts of the same product. -/
def quotientMulIso (g h : G) :
    A.ρ (s.lift h) ⋙ A.ρ (s.lift g) ≅ A.ρ (s.lift (g * h)) :=
  A.mulIso (s.lift g) (s.lift h) ≪≫
    D.iso _ _ (by simp only [map_mul, s.map_lift])

lemma quotient_left_unit (a b : Γ) (hb : b = 1) (hp : p (b * a) = p a) (X : C) :
    (A.mulIso b a).hom.app X ≫ (D.iso (b * a) a hp).hom.app X =
      eqToHom (congrArg (fun t => (A.ρ t).obj ((A.ρ a).obj X)) hb) ≫
        A.unitIso.hom.app ((A.ρ a).obj X) := by
  subst b
  rw [D.iso_of_eq (_root_.one_mul a)]
  simpa only [eqToHom_refl, Category.id_comp] using A.one_mul a X

lemma quotient_right_unit (a b : Γ) (hb : b = 1) (hp : p (a * b) = p a) (X : C) :
    (A.mulIso a b).hom.app X ≫ (D.iso (a * b) a hp).hom.app X =
      (A.ρ a).map (eqToHom (congrArg (fun t => (A.ρ t).obj X) hb) ≫ A.unitIso.hom.app X) := by
  subst b
  rw [D.iso_of_eq (_root_.mul_one a)]
  simpa only [eqToHom_refl, Category.id_comp] using A.mul_one a X

lemma quotient_assoc (g h k : G) (X : C) :
    (A.ρ (s.lift g)).map ((quotientMulIso D s h k).hom.app X) ≫
      (quotientMulIso D s g (h * k)).hom.app X =
    (quotientMulIso D s g h).hom.app ((A.ρ (s.lift k)).obj X) ≫
      (quotientMulIso D s (g * h) k).hom.app X ≫
      eqToHom (congrArg (fun t => (A.ρ (s.lift t)).obj X) (mul_assoc g h k)) := by
  dsimp only [quotientMulIso, Iso.trans_hom, NatTrans.comp_app]
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [D.transport_left]
  rw [← Category.assoc, A.assoc, Category.assoc, Category.assoc]
  rw [D.eqToHom_comp_iso]
  rw [D.iso_comp_eqToHom]
  rw [D.transport_right]
  all_goals simp only [_root_.mul_assoc]

/-- The descended weak action is constructed from the section. Its
associativity is proved from the original action and comparison equations. -/
def quotientAction : WeakAction G C where
  ρ g := A.ρ (s.lift g)
  unitIso := eqToIso (congrArg A.ρ s.lift_one) ≪≫ A.unitIso
  mulIso := quotientMulIso D s
  assoc := quotient_assoc D s
  one_mul g X := by
    dsimp only [quotientMulIso, Iso.trans_hom, NatTrans.comp_app]
    simp only [Category.assoc, eqToIso.hom, eqToHom_app]
    rw [D.iso_comp_eqToHom _ (congrArg s.lift (_root_.one_mul g)) X]
    exact quotient_left_unit D (s.lift g) (s.lift 1) s.lift_one _ X
  mul_one g X := by
    dsimp only [quotientMulIso, Iso.trans_hom, NatTrans.comp_app]
    simp only [Category.assoc, eqToIso.hom, eqToHom_app]
    rw [D.iso_comp_eqToHom _ (congrArg s.lift (_root_.mul_one g)) X]
    exact quotient_right_unit D (s.lift g) (s.lift 1) s.lift_one _ X

@[simp] lemma quotientAction_rho (g : G) : (quotientAction D s).ρ g = A.ρ (s.lift g) := rfl

end Paper18.Category.WeakAction
