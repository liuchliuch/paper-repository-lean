import Paper06.Posterior
import Paper06.Mixtures
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open Real Set BigOperators MeasureTheory
open scoped Classical

namespace Paper06

/-- The k-coordinate marginal of the actual n-coordinate joint law. -/
noncomputable def marginal {α : Type*} [Fintype α] {n : ℕ}
    (P : FinProb (Fin n → α)) (k : ℕ) (hk : k ≤ n) : FinProb (Fin k → α) :=
  FinProb.map P (fun z i => z ⟨i.val, lt_of_lt_of_le i.isLt hk⟩)

/-- The original admissible data: a finite vector-valued linear constraint,
a joint law, exchangeability, and its lifted constraint at every site.
Exchangeability makes these equivalent to the paper's single constrained site. -/
structure Admissible (α : Type*) [Fintype α] (n : ℕ) where
  t : ℕ
  Γ : (α → ℝ) →ₗ[ℝ] (Fin t → ℝ)
  η : Fin t → ℝ
  law : FinProb (Fin n → α)
  exchangeable : Posterior.Exchangeable law
  cp : ∀ i, Posterior.LiftedCP Γ η law i

namespace Admissible
variable {α : Type*} [Fintype α] {n : ℕ}

/-- The nonempty affine slice specified by the original linear data. -/
def slice (A : Admissible α n) : Set (FinProb α) := Posterior.AffineSlice A.Γ A.η

/-- A single-coordinate CP identity suffices to form the original data. -/
def of_single (t : ℕ) (Γ : (α → ℝ) →ₗ[ℝ] (Fin t → ℝ)) (η : Fin t → ℝ)
    (P : FinProb (Fin n → α)) (hP : Posterior.Exchangeable P)
    (c : Fin n) (hCP : Posterior.LiftedCP Γ η P c) : Admissible α n where
  t := t
  Γ := Γ
  η := η
  law := P
  exchangeable := hP
  cp := Posterior.liftedCP_at_every_coordinate Γ η P hP c hCP

end Admissible

/-- Optimal relative-entropy error over all Borel probability mixing measures. -/
noncomputable def constrainedError {α : Type*} [Fintype α] {n : ℕ}
    (P : FinProb (Fin n → α)) (F : Set (FinProb α)) (k : ℕ) (hk : k ≤ n) : EReal :=
  ⨅ μ : ProbabilityMeasure F,
    FinProb.kl (marginal P k hk) (FinProb.feasibleProductMixture F (μ : Measure F) k)

/-- A finite d-symbol alphabet, without fixing its names or representation. -/
structure FiniteAlphabet (d : ℕ) where
  carrier : Type
  finite : Fintype carrier
  card_eq : @Fintype.card carrier finite = d

/-- The original worst-case error, including every d-symbol alphabet and
all linear maps, targets, and admissible n-coordinate laws. -/
noncomputable def worstConstrainedError (d n k : ℕ) (hk : k ≤ n) : EReal :=
  ⨆ alphabet : FiniteAlphabet d,
    letI := alphabet.finite
    ⨆ A : Admissible alphabet.carrier n, constrainedError A.law A.slice k hk

theorem constrainedError_le_worst {α : Type} [Fintype α] {n : ℕ}
    (A : Admissible α n) (k : ℕ) (hk : k ≤ n) :
    constrainedError A.law A.slice k hk ≤ worstConstrainedError (Fintype.card α) n k hk := by
  exact le_iSup_of_le (⟨α, inferInstance, rfl⟩ : FiniteAlphabet (Fintype.card α))
    (le_iSup (fun B : Admissible α n => constrainedError B.law B.slice k hk) A)

theorem constrainedError_nonneg {α : Type*} [Fintype α] {n : ℕ}
    (P : FinProb (Fin n → α)) (F : Set (FinProb α)) (k : ℕ) (hk : k ≤ n) :
    0 ≤ constrainedError P F k hk := by
  apply le_iInf
  intro μ
  exact FinProb.kl_nonneg _ _

theorem le_constrainedError {α : Type*} [Fintype α] {n : ℕ}
    (P : FinProb (Fin n → α)) (F : Set (FinProb α)) (k : ℕ) (hk : k ≤ n)
    (b : EReal) (h : ∀ μ : ProbabilityMeasure F,
      b ≤ FinProb.kl (marginal P k hk) (FinProb.feasibleProductMixture F (μ : Measure F) k)) :
    b ≤ constrainedError P F k hk := le_iInf h

theorem constrainedError_le {α : Type*} [Fintype α] {n : ℕ}
    (P : FinProb (Fin n → α)) (F : Set (FinProb α)) (k : ℕ) (hk : k ≤ n)
    (μ : ProbabilityMeasure F) :
    constrainedError P F k hk ≤
      FinProb.kl (marginal P k hk) (FinProb.feasibleProductMixture F (μ : Measure F) k) :=
  iInf_le _ μ

end Paper06
