import Paper18.Category.WeakActionQuotientPullback
import Paper18.Category.WeakActionQuotientKernel

/-! # Monoidal and linear structure of the actual quotient action -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u w w'
namespace Paper18.Category.WeakAction
variable {Γ : Type w} [Group Γ] {G : Type w'} [Group G]
  {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {p : Γ →* G} {A : WeakAction Γ C}
  [∀ g : Γ, (A.ρ g).Monoidal] [A.IsMonoidal]

/-- Monoidality of the actual fiber comparisons. -/
class FiberComparisons.IsMonoidal (D : FiberComparisons p A) : Prop where
  iso_monoidal : ∀ x y h, NatTrans.IsMonoidal (D.iso x y h).hom
attribute [instance] FiberComparisons.IsMonoidal.iso_monoidal

/-- The actual kernel trivializations are monoidal natural isomorphisms. -/
class KernelTrivialization.IsMonoidal (K : KernelTrivialization p A) : Prop where
  trivialization_monoidal : ∀ k, NatTrans.IsMonoidal (K.trivialization k).hom
attribute [instance] KernelTrivialization.IsMonoidal.trivialization_monoidal

instance kernelTrivialization_fiberComparisons_monoidal (K : KernelTrivialization p A)
    [K.IsMonoidal] : K.fiberComparisons.IsMonoidal where
  iso_monoidal x y h := kernelComparison_monoidal p A K.trivialization x y h

variable (D : FiberComparisons p A) [D.IsMonoidal] (s : QuotientSection p)

instance quotientAction_rho_monoidal (g : G) : ((quotientAction D s).ρ g).Monoidal :=
  inferInstanceAs (A.ρ (s.lift g)).Monoidal

instance quotientAction_monoidal : (quotientAction D s).IsMonoidal where
  unit_monoidal := by
    change NatTrans.IsMonoidal ((rhoEqIso A s.lift_one) ≪≫ A.unitIso).hom
    dsimp only [Iso.trans_hom]
    infer_instance
  mul_monoidal g h := by
    change NatTrans.IsMonoidal (quotientMulIso D s g h).hom
    dsimp only [quotientMulIso, Iso.trans_hom]
    infer_instance

section Linear
variable [Preadditive C] [Linear ℂ C]
  [∀ g : Γ, (A.ρ g).Additive] [∀ g : Γ, (A.ρ g).Linear ℂ]

instance quotientAction_rho_additive (g : G) : ((quotientAction D s).ρ g).Additive :=
  inferInstanceAs (A.ρ (s.lift g)).Additive

instance quotientAction_rho_linear (g : G) : ((quotientAction D s).ρ g).Linear ℂ :=
  inferInstanceAs (Functor.Linear ℂ (A.ρ (s.lift g)))

end Linear

instance pullback_rho_monoidal (B : WeakAction G C) [∀ g : G, (B.ρ g).Monoidal]
    (p : Γ →* G) (x : Γ) : ((pullback B p).ρ x).Monoidal :=
  inferInstanceAs (B.ρ (p x)).Monoidal

instance pullback_monoidal (B : WeakAction G C) [∀ g : G, (B.ρ g).Monoidal]
    [B.IsMonoidal] (p : Γ →* G) : (pullback B p).IsMonoidal where
  unit_monoidal := by
    change NatTrans.IsMonoidal ((rhoEqIso B p.map_one) ≪≫ B.unitIso).hom
    dsimp only [Iso.trans_hom]
    infer_instance
  mul_monoidal x y := by
    change NatTrans.IsMonoidal
      ((B.mulIso (p x) (p y)) ≪≫ rhoEqIso B (p.map_mul x y).symm).hom
    dsimp only [Iso.trans_hom]
    infer_instance

/-- The actual weak-action isomorphism has monoidal natural components. -/
class ActionIso.IsMonoidal {A B : WeakAction Γ C}
    [∀ x : Γ, (A.ρ x).Monoidal] [∀ x : Γ, (B.ρ x).Monoidal]
    (i : ActionIso A B) : Prop where
  iso_monoidal : ∀ x, NatTrans.IsMonoidal (i.iso x).hom
attribute [instance] ActionIso.IsMonoidal.iso_monoidal

instance quotientActionIso_monoidal : (quotientActionIso D s).IsMonoidal where
  iso_monoidal x := by
    change NatTrans.IsMonoidal (D.iso x (s.lift (p x)) (s.map_lift (p x)).symm).hom
    infer_instance

end Paper18.Category.WeakAction
