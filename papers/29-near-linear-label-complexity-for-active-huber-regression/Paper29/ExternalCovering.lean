import Paper29.FiniteWeights
import Paper29.EndpointRegimes
import Paper29.LogTransfer
import Mathlib.Data.Int.Interval

/-! Precisely disclosed covering inputs from Jambulapati–Lee–Liu–Sidford,
arXiv:2311.18145v1, Definition1.8 and the metric-covering/Dudley argument in
Theorem3.14. These are the imported covering assertions (3.11) and (A.3) of
P29. They accept actual finite weight schemes; neither supplies a scheme,
all-radius Huber scores, centered transfer, an algorithm or a query bound.
No inhabitant of either Prop and no axiom is declared here. -/
noncomputable section
open scoped BigOperators ENNReal Classical
namespace Paper29.ExternalCovering
open WeightConstruction Chaining ProcessTools

def maxScore {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (s : Finset ℤ)
    (w : ℤ → PositiveWeights n) (i : Fin n) : ℝ :=
  supremum (fun j : {j : ℤ // j ∈ s} => Leverage.leverage A (w j) i)

structure HuberScheme {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (a b : ℤ) (α : ℝ) where
  w : ℤ → PositiveWeights n
  normalized : ∀ j ∈ Finset.Icc a b, ∀ i,
    (2:ℝ)^j / α ≤ huber (Leverage.radius A (w j) i) / Leverage.leverage A (w j) i ∧
      huber (Leverage.radius A (w j) i) / Leverage.leverage A (w j) i ≤ α*(2:ℝ)^j
  step : ∀ j, j ∈ Finset.Icc a b → j+1 ∈ Finset.Icc a b → ∀ i, w (j+1) i ≤ α*w j i

/-- Only the imported transition covering estimate. Exact trace mass and
finite deterministic construction are proved in local modules. -/
def HuberPrimitive (α C : ℝ) : Prop :=
  ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin d) ℝ), A.rank = d → (∀ i, A i ≠ 0) →
    ∀ (a b : ℤ), a ≤ b → 4 * Real.log (2*(n:ℝ)) ≤ ((Finset.Icc a b).card : ℝ) →
    ∀ scheme : HuberScheme A a b α,
      gamma2 (T := Ball A ((2:ℝ)^(b+1)))
        (fun h k => huberMetric A (maxScore A (Finset.Icc a b) scheme.w) h k) ≤
      ENNReal.ofReal (C * Real.sqrt ((2:ℝ)^(b+1)) * ProcessTools.logFactor n)

/-- Only the imported power-function covering estimate (A.3). -/
def PowerPrimitive (C : ℝ) : Prop :=
  ∀ (n d p : ℕ), (p = 1 ∨ p = 2) → ∀ (A : Matrix (Fin n) (Fin d) ℝ),
    A.rank = d → (∀ i, A i ≠ 0) → ∀ (a b : ℤ), a ≤ b →
    4 * Real.log (2*(n:ℝ)) ≤ ((Finset.Icc a b).card : ℝ) →
    ∀ w : ℤ → PositiveWeights n,
      (∀ j ∈ Finset.Icc a b, ∀ i,
        |Leverage.radius A (w j) i|^p / Leverage.leverage A (w j) i = (2:ℝ)^j) →
      (∀ j, j ∈ Finset.Icc a b → j+1 ∈ Finset.Icc a b → ∀ i, w (j+1) i ≤ w j i) →
      gamma2 (T := PowerBall A p ((2:ℝ)^(b+1)))
        (fun h k => powerMetric A p (maxScore A (Finset.Icc a b) w) h k) ≤
      ENNReal.ofReal (C * Real.sqrt ((2:ℝ)^(b+1)) * ProcessTools.logFactor n)

/-- Restrict the proved finite-prefix construction to any requested integer
interval. The imported primitive receives a genuine constructed scheme. -/
def constructedHuberScheme {n d : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin d) ℝ) (hA : A.rank = d) (hrows : ∀ i, A i ≠ 0)
    (external : RadiusLogNonexpansive) (a b : ℤ) : HuberScheme A a b 4 := by
  let w₀ := initialWeight A hA hrows external a
  let v := sequence A hA hrows a w₀
  have hw₀ := initialWeight_residual A hA hrows external a
  have hnorm (k : ℕ) (i : Fin n) := residual_scheme_bounds A hA hrows (a+(k:ℤ)) (v k)
    (sequence_residual A hA hrows external a w₀ hw₀ k) i
  have hstep := sequence_step_le A hA hrows external a w₀ hw₀
  refine ⟨fun j => v (j-a).toNat, ?_, ?_⟩
  · intro j hj i
    have hja := (Finset.mem_Icc.mp hj).1
    have he : a + ((j-a).toNat : ℤ) = j := by omega
    simpa only [he] using hnorm (j-a).toNat i
  · intro j hj hj' i
    have hja := (Finset.mem_Icc.mp hj).1
    have he : (j+1-a).toNat = (j-a).toNat+1 := by omega
    change v (j+1-a).toNat i ≤ 4 * v (j-a).toNat i
    rw [he]
    have h := hstep (j-a).toNat i
    have hv := (v (j-a).toNat).property i
    linarith

end Paper29.ExternalCovering
