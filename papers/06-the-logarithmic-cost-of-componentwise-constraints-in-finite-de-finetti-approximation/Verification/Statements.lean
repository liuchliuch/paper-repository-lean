import Paper06.Results
import Paper06.FullCorollaries
import Paper06.ResidueExamples
import Paper06.MatchingPairLaw
import Paper06.NonIIDMixtures
import Paper06.OptimalErrorLimit

/-! Fixed source-level specifications for the eight non-exempt numbered results.
Corollary 3.6 is explicitly exempt under the user's approved scope rule; it is
not replaced by an assumption and is not counted as proved here. -/
noncomputable section
open Real Set BigOperators MeasureTheory Filter Asymptotics
open scoped Classical Topology
open Paper06

namespace Paper06.Specification

def Lemma21_Posterior : Prop :=
  ∀ (κ α : Type) [Fintype κ] [DecidableEq κ] [Fintype α] (t : ℕ)
    (Γ : (α → ℝ) →ₗ[ℝ] (Fin t → ℝ)) (η : Fin t → ℝ)
    (P : FinProb (κ → α)), Posterior.Exchangeable P →
    ∀ c : κ, Posterior.LiftedCP Γ η P c →
    ∀ (i : κ) (I : Finset κ), i ∉ I → ∀ z : κ → α,
    ∀ hz : 0 < Posterior.observedMass P I z,
      Γ (Posterior.posterior P I z i hz).w = η

def Prop22_Conditioning : Prop :=
  ∀ (α : Type) [Fintype α] (t : ℕ)
    (Γ : (α → ℝ) →ₗ[ℝ] (Fin t → ℝ)) (η : Fin t → ℝ) (n k : ℕ)
    (P : FinProb (Fin n → α)), Posterior.Exchangeable P →
    ∀ c : Fin n, Posterior.LiftedCP Γ η P c →
    1 ≤ k → ∀ hn : k < n,
      ∃ μ : ProbabilityMeasure (Posterior.AffineSlice Γ η),
        FinProb.kl (marginal P k hn.le)
          (FinProb.feasibleProductMixture (Posterior.AffineSlice Γ η) (μ : Measure _) k) ≤
          ((((k : ℝ) * (k - 1) / (2 * ((n : ℝ) - k + 1))) *
            log (Fintype.card α) : ℝ) : EReal)

def Thm31_Logarithmic : Prop :=
  ∀ (θ : ℝ), 0 < θ → θ < 1 / 2 → ∀ n : ℕ, 6 ≤ n → Even n →
    ∀ (r : ℕ) (hr : Nat.Prime r),
    2 * Real.exp 1 * ((n : ℝ) - 1) ≤ (r : ℝ) ^ ((1 : ℝ) / 2 - θ) →
    letI : Fact (Nat.Prime r) := ⟨hr⟩
    ∃ P : FinProb (Fin n → ZMod r × ZMod r),
      Posterior.Exchangeable P ∧
      (∀ i, Posterior.LiftedCP (uniformInputLinear (ZMod r)) (uniformInputTarget (ZMod r)) P i) ∧
      ∀ k, 2 ≤ k → (hkk : k * k ≤ n) →
        ∀ μ : ProbabilityMeasure {q : FinProb (ZMod r × ZMod r) | UniformInput q},
          (((3 * θ * (k : ℝ) * (k - 1) * log ((r : ℝ) ^ 2)) /
            (16 * (n - 1)) : ℝ) : EReal) ≤
            FinProb.kl (marginal P k (by nlinarith))
              (FinProb.feasibleProductMixture {q : FinProb (ZMod r × ZMod r) | UniformInput q}
                (μ : Measure _) k) ∧
          (3 * θ / 32) * ((k : ℝ) * (k - 1) * log ((r : ℝ) ^ 2)) / (n - k + 1) ≤
            (3 * θ * (k : ℝ) * (k - 1) * log ((r : ℝ) ^ 2)) / (16 * (n - 1))

def Prop32_Matching : Prop :=
  ∀ (F : Type) [Fintype F] [Field F] (n : ℕ) (hEven : Even n),
    Posterior.Exchangeable (Matching.matchingLawFin (R := F) n hEven) ∧
      ∀ i, Posterior.LiftedCP (uniformInputLinear F) (uniformInputTarget F)
        (Matching.matchingLawFin (R := F) n hEven) i

def Lemma33_Incidence : Prop :=
  ∀ (F : Type) [Fintype F] [Field F] (q q' : FinProb (F × F)),
    UniformInput q → UniformInput q' →
    productWin q q' ≤ omegaR F ∧
      omegaR F ≤ betaR (Fintype.card F) ∧
      betaR (Fintype.card F) ≤ 3 / (2 * Real.sqrt (Fintype.card F))

def Prop34_MatchingWitness : Prop :=
  ∀ (F : Type) [Fintype F] [Field F] (n k : ℕ) (hEven : Even n)
    (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hkk : k * k ≤ n) (β : ℝ),
    omegaR F ≤ β → β < 3 / (4 * ((n : ℝ) - 1)) →
    ∀ μ : ProbabilityMeasure {q : FinProb (F × F) | UniformInput q},
      (((3 * (k : ℝ) * (k - 1) / (8 * (n - 1))) *
        log (3 / (4 * Real.exp 1 * (n - 1) * β)) : ℝ) : EReal) ≤
      FinProb.kl (marginal (Matching.matchingLawFin (R := F) n hEven) k (by nlinarith))
        (FinProb.feasibleProductMixture {q : FinProb (F × F) | UniformInput q} (μ : Measure _) k)

def Cor35_NoSublogarithmic : Prop :=
  ¬ ∃ C : ℝ, 0 < C ∧ ∃ h : ℕ → ℝ, (∀ d, 0 ≤ h d) ∧
    h =o[atTop] (fun d : ℕ => Real.log d) ∧
    ∀ (α : Type) [Fintype α] (n k : ℕ) (hkn : k ≤ n),
      1 < k → k < n → ∀ A : Admissible α n,
        constrainedError A.law A.slice k hkn ≤
          ((C * ((k : ℝ) * (k - 1) * h (Fintype.card α)) / (n - k + 1) : ℝ) : EReal)

def Prop41_ResponseTables : Prop :=
  ∀ (X : Type) [Fintype X] (A : X → Type) [∀ x, Fintype (A x)] [∀ x, Nonempty (A x)]
    (piLaw : FinProb X) (n : ℕ) (P : FinProb (Fin n → Sigma A)),
    Posterior.Exchangeable P → ∀ c : Fin n,
    Posterior.LiftedCP (Response.labelΓ (Sigma.fst : Sigma A → X)) piLaw.w P c →
    Fintype.card (SupportReduction.InputSupport piLaw) ≤ n →
    ∃ μ : ProbabilityMeasure (inputFiberSlice piLaw (Sigma.fst : Sigma A → X)),
      ∀ k, 1 ≤ k → (hk : k ≤ n / Fintype.card (SupportReduction.InputSupport piLaw)) →
        FinProb.kl (marginal P k (hk.trans (Nat.div_le_self _ _)))
          (FinProb.feasibleProductMixture (inputFiberSlice piLaw (Sigma.fst : Sigma A → X))
            (μ : Measure _) k) ≤
          (Sampling.cost (n / Fintype.card (SupportReduction.InputSupport piLaw)) k : EReal) ∧
        Sampling.cost (n / Fintype.card (SupportReduction.InputSupport piLaw)) k ≤
          (k * (k - 1) : ℝ) /
            (2 * (((n / Fintype.card (SupportReduction.InputSupport piLaw) : ℕ) : ℝ) - k + 1))

/-- S3.E10: the actual two-point marginal, both as a normalized-law
identity and with the two source coefficients displayed explicitly. -/
def Eq10_TwoPointLaw : Prop :=
  ∀ (F : Type) [Fintype F] [Field F] (n : ℕ) (hEven : Even n) (hn2 : 2 ≤ n)
    (i j : Fin n) (hij : i ≠ j),
    FinProb.map (Matching.matchingLawFin (R := F) n hEven) (fun z => (z i, z j)) =
      Matching.twoPointMixture (R := F) n hn2 ∧
    ∀ a b : F × F,
      (FinProb.map (Matching.matchingLawFin (R := F) n hEven) (fun z => (z i, z j))).w (a,b) =
        (1 / ((n : ℝ) - 1)) * (Matching.edgeLaw (R := F)).w (a,b) +
        (((n : ℝ) - 2) / ((n : ℝ) - 1)) *
          (prod (Matching.uniformSiteLaw (R := F)) (Matching.uniformSiteLaw (R := F))).w (a,b)

/-- S3.SS3.p6: the full symbolic witness against arbitrary Borel mixtures
of non-identical individually feasible factors. -/
def NonIID_MatchingWitness : Prop :=
  ∀ (F : Type) [Fintype F] [Field F] (n k : ℕ) (hEven : Even n)
    (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hkk : k * k ≤ n) (β : ℝ),
    omegaR F ≤ β → β < 3 / (4 * ((n : ℝ) - 1)) →
    ∀ μ : ProbabilityMeasure (Fin k → {q : FinProb (F × F) | UniformInput q}),
      (((3 * (k : ℝ) * (k - 1) / (8 * (n - 1))) *
        log (3 / (4 * Real.exp 1 * (n - 1) * β)) : ℝ) : EReal) ≤
      FinProb.kl (marginal (Matching.matchingLawFin (R := F) n hEven) k (by nlinarith))
        (FinProb.feasibleIndependentProductMixture {q : FinProb (F × F) | UniformInput q}
          k (μ : Measure _))

/-- S3.SS3.p6: both original logarithmic inequalities for the actual
matching law, with arbitrary Borel mixing on the full tuple of factors. -/
def NonIID_Logarithmic : Prop :=
  ∀ (F : Type) [Fintype F] [Field F] (n k : ℕ) (hEven : Even n)
    (hn : 6 ≤ n) (hk2 : 2 ≤ k) (hkk : k * k ≤ n) (θ : ℝ),
    0 < θ → θ < 1 / 2 →
    2 * Real.exp 1 * ((n : ℝ) - 1) ≤ (Fintype.card F : ℝ) ^ ((1 : ℝ) / 2 - θ) →
    ∀ μ : ProbabilityMeasure (Fin k → {q : FinProb (F × F) | UniformInput q}),
      (((3 * θ * (k : ℝ) * (k - 1) * log ((Fintype.card F : ℝ) ^ 2)) /
        (16 * (n - 1)) : ℝ) : EReal) ≤
        FinProb.kl (marginal (Matching.matchingLawFin (R := F) n hEven) k (by nlinarith))
          (FinProb.feasibleIndependentProductMixture {q : FinProb (F × F) | UniformInput q}
            k (μ : Measure _)) ∧
      (3 * θ / 32) * ((k : ℝ) * (k - 1) * log ((Fintype.card F : ℝ) ^ 2)) / (n - k + 1) ≤
        (3 * θ * (k : ℝ) * (k - 1) * log ((Fintype.card F : ℝ) ^ 2)) / (16 * (n - 1))

/-- The actual optimum over all Borel feasible iid mixtures tends to zero
on the ordinary atTop filter of even extension sizes. -/
def ActualOptimalErrorZero : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 / 2 →
    Tendsto (paperOptimalError θ) atTop (𝓝 (0 : EReal))

end Paper06.Specification
