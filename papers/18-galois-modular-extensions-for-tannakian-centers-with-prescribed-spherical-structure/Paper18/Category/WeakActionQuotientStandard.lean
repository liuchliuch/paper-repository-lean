import Paper18.Category.WeakActionQuotientStandardLeft

/-! # Descent from the standard unit, product, and conjugation laws

The three standard laws imply all canonical comparison coherences.
Thus the quotient weak action and its monoidal comparison are constructions,
not extra data supplied with the kernel trivialization.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category
universe v u w w'
namespace Paper18.Category.WeakAction
variable {Γ : Type w} [Group Γ] {G : Type w'} [Group G]
  {C : Type u} [Category.{v} C] (p : Γ →* G) (A : WeakAction Γ C)
  (D : StandardKernelTrivialization p A)

/-- The full multiplication comparison follows by first translating on the
left and then on the right. -/
lemma StandardKernelTrivialization.comparison_mul
    (x x' y y' : Γ) (hx : p x = p x') (hy : p y = p y') (X : C) :
    (A.mulIso x y).hom.app X ≫
      (kernelComparison p A D.trivialization (x*y) (x'*y')
        (by simp only [map_mul, hx, hy])).hom.app X =
    (A.ρ x).map ((kernelComparison p A D.trivialization y y' hy).hom.app X) ≫
      (kernelComparison p A D.trivialization x x' hx).hom.app ((A.ρ y').obj X) ≫
        (A.mulIso x' y').hom.app X := by
  have h₁ : p (x*y) = p (x*y') := by simp only [map_mul, hy]
  have h₂ : p (x*y') = p (x'*y') := by simp only [map_mul, hx]
  rw [← StandardKernelTrivialization.comparison_trans p A D (x*y) (x*y') (x'*y') h₁ h₂ X]
  rw [StandardKernelTrivialization.comparison_left_mul_assoc p A D x y y' hy X]
  rw [StandardKernelTrivialization.comparison_right_mul p A D x x' y' hx X]

/-- Actual comparison coherence derived solely from the three standard laws. -/
def StandardKernelTrivialization.toKernelTrivialization : KernelTrivialization p A where
  trivialization := D.trivialization
  comparison_refl := StandardKernelTrivialization.comparison_refl p A D
  comparison_trans := StandardKernelTrivialization.comparison_trans p A D
  comparison_mul := StandardKernelTrivialization.comparison_mul p A D

/-- Actual quotient action constructed from standard kernel trivializations. -/
def StandardKernelTrivialization.descend (hp : Function.Surjective p) : WeakAction G C :=
  (D.toKernelTrivialization p A).descend hp

/-- The original action is actually isomorphic to the pullback of this quotient action. -/
def StandardKernelTrivialization.descentIso (hp : Function.Surjective p) :
    ActionIso A (pullback (D.descend p A hp) p) :=
  (D.toKernelTrivialization p A).descentIso hp

section Monoidal
variable [MonoidalCategory C] [∀ g : Γ, (A.ρ g).Monoidal] [A.IsMonoidal]

/-- Each actual kernel trivialization is a monoidal natural isomorphism. -/
class StandardKernelTrivialization.IsMonoidal : Prop where
  trivialization_monoidal (k : p.ker) : NatTrans.IsMonoidal (D.trivialization k).hom

attribute [instance] StandardKernelTrivialization.IsMonoidal.trivialization_monoidal

instance StandardKernelTrivialization.toKernelTrivialization_monoidal [D.IsMonoidal p A] :
    (D.toKernelTrivialization p A).IsMonoidal where
  trivialization_monoidal k := inferInstanceAs (NatTrans.IsMonoidal (D.trivialization k).hom)

variable [D.IsMonoidal p A] (hp : Function.Surjective p)

instance StandardKernelTrivialization.descend_rho_monoidal (g : G) :
    ((D.descend p A hp).ρ g).Monoidal :=
  inferInstanceAs (((D.toKernelTrivialization p A).descend hp).ρ g).Monoidal

instance StandardKernelTrivialization.descend_monoidal : (D.descend p A hp).IsMonoidal :=
  inferInstanceAs ((D.toKernelTrivialization p A).descend hp).IsMonoidal

instance StandardKernelTrivialization.descentIso_monoidal : (D.descentIso p A hp).IsMonoidal :=
  inferInstanceAs ((D.toKernelTrivialization p A).descentIso hp).IsMonoidal

section Linear
variable [Preadditive C] [Linear ℂ C]
  [∀ g : Γ, (A.ρ g).Additive] [∀ g : Γ, (A.ρ g).Linear ℂ]

instance StandardKernelTrivialization.descend_rho_additive (g : G) :
    ((D.descend p A hp).ρ g).Additive :=
  inferInstanceAs (((D.toKernelTrivialization p A).descend hp).ρ g).Additive

instance StandardKernelTrivialization.descend_rho_linear (g : G) :
    ((D.descend p A hp).ρ g).Linear ℂ :=
  inferInstanceAs (Functor.Linear ℂ (((D.toKernelTrivialization p A).descend hp).ρ g))

end Linear
end Monoidal
end Paper18.Category.WeakAction
