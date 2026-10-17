import Paper18.Category.CrossedExtensionMonoidal
import Paper18.Category.CrossedExtensionActionCochain
import Paper18.Category.EquivariantBasic

/-! # Actual conjugation action on the kernel graded category -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling
variable {A : Type} [Fintype A] [AddGroup A]

/-- Actual scalar isomorphism between two propositionally equal fibers. -/
def scalarFiberIso (X : PointedVec A) {a b : A} (h : a = b) (s : ℂˣ) : X a ≅ X b where
  hom := (s : ℂ) • eqToHom (congrArg X h)
  inv := ((s⁻¹ : ℂˣ) : ℂ) • eqToHom (congrArg X h.symm)
  hom_inv_id := by
    simp only [Linear.smul_comp, Linear.comp_smul, eqToHom_trans,
      eqToHom_refl, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  inv_hom_id := by
    simp only [Linear.smul_comp, Linear.comp_smul, eqToHom_trans,
      eqToHom_refl, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

/-- An actual natural isomorphism of pullback functors, including actual
fiber transports rather than an equality of numerical degree labels. -/
def pullbackScalarNatIso (q r : A → A) (h : ∀ a, q a = r a) (s : A → ℂˣ) :
    GradedObject.comap (FGModuleCat ℂ) q ≅ GradedObject.comap (FGModuleCat ℂ) r :=
  NatIso.ofComponents (fun X => GradedObject.isoMk _ _ (fun a => scalarFiberIso X (h a) (s a)))
    (by
      intro X Y f
      funext a
      change f (q a) ≫ ((s a : ℂ) • eqToHom (congrArg Y (h a))) =
        ((s a : ℂ) • eqToHom (congrArg X (h a))) ≫ f (r a)
      rw [Linear.comp_smul, Linear.smul_comp]
      congr 1
      exact eqToHom_naturality f (h a))

omit [Fintype A] [AddGroup A] in
@[simp] lemma pullbackScalarNatIso_hom_app (q r : A → A) (h : ∀ a, q a = r a)
    (s : A → ℂˣ) (X : PointedVec A) (a : A) :
    (pullbackScalarNatIso q r h s).hom.app X a =
      (s a : ℂ) • eqToHom (congrArg X (h a)) := rfl

variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)

/-- The translating functor uses inverse conjugation so that the weak
action has the standard left-action composition order. -/
def kernelTranslation (g : KillingExtension G) :
    CocycleVec (kernelCocycle ω) ⥤ CocycleVec (kernelCocycle ω) :=
  kernelConjugationFunctor ω g⁻¹

@[simp] lemma kernelTranslation_obj_apply (g : KillingExtension G)
    (X : CocycleVec (kernelCocycle ω)) (a : Additive (KillingKernel G)) :
    (kernelTranslation ω g).obj X a = X (Additive.ofMul (conjugate g⁻¹ a.toMul)) := rfl

@[simp] lemma kernelTranslation_map_apply (g : KillingExtension G)
    {X Y : CocycleVec (kernelCocycle ω)} (f : X ⟶ Y) (a : Additive (KillingKernel G)) :
    (kernelTranslation ω g).map f a = f (Additive.ofMul (conjugate g⁻¹ a.toMul)) := rfl

instance kernelTranslation_monoidal (g : KillingExtension G) :
    (kernelTranslation ω g).Monoidal := kernelConjugationFunctor_monoidal ω g⁻¹

/-- Actual unit comparison, the canonical transport between equal fibers. -/
def kernelTranslationUnit : kernelTranslation ω 1 ≅ 𝟭 (CocycleVec (kernelCocycle ω)) :=
  pullbackScalarNatIso
    (fun a : Additive (KillingKernel G) => Additive.ofMul (conjugate (1 : KillingExtension G)⁻¹ a.toMul))
    id (fun a => by simp) (fun _ => 1)

/-- Actual multiplication comparison with the scalar constructed from the
finite primitive; it is natural for every actual linear graded morphism. -/
def kernelTranslationMul (g h : KillingExtension G) :
    kernelTranslation ω h ⋙ kernelTranslation ω g ≅ kernelTranslation ω (g * h) :=
  pullbackScalarNatIso
    (fun a : Additive (KillingKernel G) =>
      Additive.ofMul (conjugate h⁻¹ (conjugate g⁻¹ a.toMul)))
    (fun a : Additive (KillingKernel G) => Additive.ofMul (conjugate (g * h)⁻¹ a.toMul))
    (fun a => by simp only [conjugate_conjugate, mul_inv_rev])
    (fun a => conjugationComparison ω h⁻¹ g⁻¹ a.toMul)

set_option maxHeartbeats 1000000 in
@[simp] lemma kernelTranslationMul_hom_app (g h : KillingExtension G)
    (X : CocycleVec (kernelCocycle ω)) (a : Additive (KillingKernel G)) :
    (kernelTranslationMul ω g h).hom.app X a =
      (conjugationComparison ω h⁻¹ g⁻¹ a.toMul : ℂ) •
        eqToHom (congrArg X (show
          Additive.ofMul (conjugate h⁻¹ (conjugate g⁻¹ a.toMul)) =
          Additive.ofMul (conjugate (g * h)⁻¹ a.toMul) by
            simp only [conjugate_conjugate, mul_inv_rev])) := rfl

@[simp] lemma kernelTranslationUnit_hom_app (X : CocycleVec (kernelCocycle ω))
    (a : Additive (KillingKernel G)) :
    (kernelTranslationUnit ω).hom.app X a =
      eqToHom (congrArg X (show
        Additive.ofMul (conjugate (1 : KillingExtension G)⁻¹ a.toMul) = a by simp)) := by
  change (1 : ℂˣ).val • _ = _
  simp only [Units.val_one, one_smul]

end Paper18.Category.CrossedExtension
