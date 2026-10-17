import Paper18.Category.CrossedExtensionCoherence
import Paper18.Category.CrossedExtensionUnitCoherence

/-! # Actual strong tensor conjugation functors on the kernel fusion category -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling
variable {A : Type} [Fintype A] [AddGroup A]

/-- The actual convolution comparison maps satisfy every strong tensor
functor axiom, as a consequence of the proved scalar cochain equation. -/
def scalarRegradeCoreMonoidal (r : A → A → A → ℂˣ)
    (hr : ∀ a b c d, r b c d * r a (b + c) d * r a b c =
      r (a + b) c d * r a b (c + d)) (h₀ : ∀ a c, r a 0 c = 1)
    (e : A ≃+ A) (t : A → A → ℂˣ)
    (ht : ∀ a b c, t a b * t (a + b) c * r (e a) (e b) (e c) =
      r a b c * t b c * t a (b + c))
    (ht₀ : ∀ a, t 0 a = 1) (ht₁ : ∀ a, t a 0 = 1) :
    letI := scalarMonoidalCategory r hr h₀
    (regradeFunctor e).CoreMonoidal := by
  letI := scalarMonoidalCategory r hr h₀
  exact
    { εIso := regradeUnitIso e
      μIso := weightedRegradeTensorIso e t
      μIso_hom_natural_left := fun f Y => by
        simpa only [Functor.map_id, MonoidalCategory.tensorHom_id] using
          weightedRegradeTensorIso_naturality e t f (𝟙 Y)
      μIso_hom_natural_right := fun X f => by
        simpa only [Functor.map_id, MonoidalCategory.id_tensorHom] using
          weightedRegradeTensorIso_naturality e t (𝟙 X) f
      associativity := weightedRegrade_associativity e t r ht
      left_unitality := weightedRegrade_left_unitality e t ht₀
      right_unitality := weightedRegrade_right_unitality e t ht₁ }

def scalarRegradeMonoidal (r : A → A → A → ℂˣ)
    (hr : ∀ a b c d, r b c d * r a (b + c) d * r a b c =
      r (a + b) c d * r a b (c + d)) (h₀ : ∀ a c, r a 0 c = 1)
    (e : A ≃+ A) (t : A → A → ℂˣ)
    (ht : ∀ a b c, t a b * t (a + b) c * r (e a) (e b) (e c) =
      r a b c * t b c * t a (b + c))
    (ht₀ : ∀ a, t 0 a = 1) (ht₁ : ∀ a, t a 0 = 1) :
    letI := scalarMonoidalCategory r hr h₀
    (regradeFunctor e).Monoidal := by
  letI := scalarMonoidalCategory r hr h₀
  exact (scalarRegradeCoreMonoidal r hr h₀ e t ht ht₀ ht₁).toMonoidal

variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)

/-- Actual regrading by conjugation in the finite killing extension, on the
actual kernel fusion category. Pullback uses the inverse scalar tensorator. -/
def kernelConjugationFunctor (g : KillingExtension G) :
    CocycleVec (kernelCocycle ω) ⥤ CocycleVec (kernelCocycle ω) :=
  regradeFunctor ((conjugationAut g).toAdditive)

instance kernelConjugationFunctor_additive (g : KillingExtension G) :
    (kernelConjugationFunctor ω g).Additive :=
  inferInstanceAs ((regradeFunctor ((conjugationAut g).toAdditive)).Additive)

instance kernelConjugationFunctor_linear (g : KillingExtension G) :
    (kernelConjugationFunctor ω g).Linear ℂ :=
  inferInstanceAs ((regradeFunctor ((conjugationAut g).toAdditive)).Linear ℂ)

instance kernelConjugationFunctor_isEquivalence (g : KillingExtension G) :
    (kernelConjugationFunctor ω g).IsEquivalence :=
  inferInstanceAs ((regradeEquivalence ((conjugationAut g).toAdditive)).functor.IsEquivalence)

/-- Each conjugation functor carries an actual strong monoidal structure;
its coherence is derived from the actual fourth-cocycle primitive. -/
instance kernelConjugationFunctor_monoidal (g : KillingExtension G) :
    (kernelConjugationFunctor ω g).Monoidal :=
  scalarRegradeMonoidal
    (fun (a b c : Additive (KillingKernel G)) =>
      (kernelCocycle ω).val a.toMul b.toMul c.toMul)
    (fun (a b c d : Additive (KillingKernel G)) =>
      (kernelCocycle ω).pentagon a.toMul b.toMul c.toMul d.toMul)
    (fun (a c : Additive (KillingKernel G)) =>
      (kernelCocycle ω).one₂ a.toMul c.toMul)
    ((conjugationAut g).toAdditive)
    (fun (a b : Additive (KillingKernel G)) =>
      (conjugationTensorator ω g a.toMul b.toMul)⁻¹)
    (fun (a b c : Additive (KillingKernel G)) =>
      conjugationTensorator_inverse_coherence ω g a.toMul b.toMul c.toMul)
    (fun a => by simp)
    (fun a => by simp)

end Paper18.Category.CrossedExtension
