import Paper18.Category.WeakActionQuotientMonoidal

/-! # Genuine descent of weak monoidal actions through a group quotient

The normalized lifts are chosen from actual surjectivity. Kernel natural
isomorphisms with their original-action compatibility equations produce
the quotient action and its actual monoidal comparison with Γ-pullback.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category
universe v u w w'
namespace Paper18.Category.WeakAction
variable {Γ : Type w} [Group Γ] {G : Type w'} [Group G]
  {C : Type u} [Category.{v} C] {p : Γ →* G} {A : WeakAction Γ C}

/-- The actual quotient action from actual coherent kernel trivializations. -/
def KernelTrivialization.descend (K : KernelTrivialization p A)
    (hp : Function.Surjective p) : WeakAction G C :=
  quotientAction K.fiberComparisons (chosenQuotientSection p hp)

/-- The original Γ-action is actually isomorphic to the pullback of its descent. -/
def KernelTrivialization.descentIso (K : KernelTrivialization p A)
    (hp : Function.Surjective p) : ActionIso A (pullback (K.descend hp) p) :=
  quotientActionIso K.fiberComparisons (chosenQuotientSection p hp)

section Monoidal
variable [MonoidalCategory C] [∀ g : Γ, (A.ρ g).Monoidal] [A.IsMonoidal]
  (K : KernelTrivialization p A) [K.IsMonoidal] (hp : Function.Surjective p)

instance KernelTrivialization.descend_rho_monoidal (g : G) : ((K.descend hp).ρ g).Monoidal :=
  inferInstanceAs ((quotientAction K.fiberComparisons (chosenQuotientSection p hp)).ρ g).Monoidal

instance KernelTrivialization.descend_monoidal : (K.descend hp).IsMonoidal :=
  inferInstanceAs (quotientAction K.fiberComparisons (chosenQuotientSection p hp)).IsMonoidal

instance KernelTrivialization.descentIso_monoidal : (K.descentIso hp).IsMonoidal :=
  inferInstanceAs (quotientActionIso K.fiberComparisons (chosenQuotientSection p hp)).IsMonoidal

section Linear
variable [Preadditive C] [Linear ℂ C]
  [∀ g : Γ, (A.ρ g).Additive] [∀ g : Γ, (A.ρ g).Linear ℂ]

instance KernelTrivialization.descend_rho_additive (g : G) : ((K.descend hp).ρ g).Additive :=
  inferInstanceAs ((quotientAction K.fiberComparisons (chosenQuotientSection p hp)).ρ g).Additive

instance KernelTrivialization.descend_rho_linear (g : G) : ((K.descend hp).ρ g).Linear ℂ :=
  inferInstanceAs (Functor.Linear ℂ
    ((quotientAction K.fiberComparisons (chosenQuotientSection p hp)).ρ g))

end Linear
end Monoidal
end Paper18.Category.WeakAction
