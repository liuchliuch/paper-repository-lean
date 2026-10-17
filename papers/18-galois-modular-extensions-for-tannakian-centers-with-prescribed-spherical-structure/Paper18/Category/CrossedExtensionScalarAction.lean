import Paper18.Category.CrossedExtensionActionBasic

/-! # Actual graded actions from scalar cocycle identities -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
namespace Paper18.Category.CrossedExtension
variable {A : Type} [Fintype A] [AddGroup A]
  {Γ : Type*} [Group Γ]

omit [Fintype A] [AddGroup A] [Group Γ] in
lemma pointedEqToHom_apply {X Y : PointedVec A} (h : X = Y) (a : A) :
    (eqToHom h : X ⟶ Y) a = eqToHom (congrArg (fun Z : PointedVec A => Z a) h) := by
  subst Y
  rfl

/-- Actual pullback functors and actual scalar fiber isomorphisms form a
weak action whenever their explicitly stated degree and scalar equations
hold. No categorical action or categorical coherence is an input. -/
def scalarPullbackAction (q : Γ → A → A)
    (q₁ : ∀ a, q 1 a = a)
    (qm : ∀ g h a, q h (q g a) = q (g * h) a)
    (s : Γ → Γ → A → ℂˣ)
    (s₁ : ∀ g a, s 1 g a = 1) (s₂ : ∀ g a, s g 1 a = 1)
    (sm : ∀ g h j a, s h j (q g a) * s g (h * j) a =
      s g h a * s (g * h) j a) : WeakAction Γ (PointedVec A) where
  ρ g := GradedObject.comap (FGModuleCat ℂ) (q g)
  unitIso := pullbackScalarNatIso (q 1) id q₁ (fun _ => 1)
  mulIso g h := pullbackScalarNatIso (fun a => q h (q g a)) (q (g * h)) (qm g h) (s g h)
  assoc g h j X := by
    funext a
    dsimp only [GradedObject.comap, Pi.comap]
    simp only [pullbackScalarNatIso_hom_app, PointedVec.comp_apply,
      pointedEqToHom_apply, Linear.smul_comp, Linear.comp_smul,
      eqToHom_trans, smul_smul]
    congr 1
    simpa only [Units.val_mul, mul_comm] using
      congrArg (fun z : ℂˣ => (z : ℂ)) (sm g h j a)
  one_mul g X := by
    funext a
    dsimp only [GradedObject.comap, Pi.comap]
    simp only [pullbackScalarNatIso_hom_app, PointedVec.comp_apply,
      pointedEqToHom_apply, s₁, Units.val_one, one_smul, eqToHom_trans]
  mul_one g X := by
    funext a
    dsimp only [GradedObject.comap, Pi.comap]
    simp only [pullbackScalarNatIso_hom_app, PointedVec.comp_apply,
      pointedEqToHom_apply, s₂, Units.val_one, one_smul, eqToHom_trans]

end Paper18.Category.CrossedExtension
