import PsgEst.Basic
import PsgEst.Estimator
import PsgEst.GapsOfPowers
import PsgEst.HardPair
import PsgEst.Laplacian
import PsgEst.LowerBound
import PsgEst.Probability
import PsgEst.MinimaxUpper
import PsgEst.UpperDeterministic
import PsgEst.UpperProbability
import PsgEst.BipartiteSpectrum
import PsgEst.Concentration
import PsgEst.EstimatorExtras
import PsgEst.PaulinProof
import PsgEst.AppendixVisitClosed
import PsgEst.ConcentrationTheorems

/-!
# Paper-facing statements

Theorem 1 (uniform upper bound), Theorem 2 (minimax bounds),
Lemma 1, Proposition 1, Lemma 2 — independently written contracts.
Intermediate facts are proved from the `PsgEst` library.
-/

open Matrix BigOperators Real Classical

namespace PsgEst
namespace Paper

variable {d : ℕ}

/-! ## Intermediate contracts (proved) -/

theorem lhat_contraction' {m : ℕ} (Y : Fin (m + 1) → Fin d)
    (hpos : degPos Y) (u : Fin d → ℝ) :
    (∑ i, (lHat Y *ᵥ u) i ^ 2) ≤ ∑ i, u i ^ 2 :=
  lhat_contraction Y hpos u

theorem lhat_sigma1_one' {m : ℕ} (Y : Fin (m + 1) → Fin d) (hpos : degPos Y) :
    (lHat Y *ᵥ fun j => ((inDeg Y j : ℝ)) ^ ((1:ℝ) / 2))
      = (fun i => ((outDeg Y i : ℝ)) ^ ((1:ℝ) / 2))
    ∧ (∑ i, (((inDeg Y i : ℝ)) ^ ((1:ℝ) / 2)) ^ 2)
        = ∑ i, (((outDeg Y i : ℝ)) ^ ((1:ℝ) / 2)) ^ 2 :=
  lhat_sigma1_one Y hpos

theorem aHat_range' {m : ℕ} (Y : Fin (m + 1) → Fin d) : 0 ≤ aHat Y ∧ aHat Y ≤ 1 :=
  aHat_mem Y

theorem gammaHat_range' {n : ℕ} (X : Fin (n + 1) → Fin d) :
    0 ≤ gammaHat X ∧ gammaHat X ≤ 1 :=
  gammaHat_mem X

theorem lag_bound' {n : ℕ} (X : Fin (n + 1) → Fin d) (k : ℕ) (hk : 0 < k) :
    aHat (skipPath X k) / k ≤ 1 / k :=
  lag_bound X k hk

theorem bNorm_mul' (S : Stoch d) (st : Stationary S) (r s : ℕ) :
    bNorm S st (r + s) ≤ bNorm S st r * bNorm S st s :=
  bNorm_mul S st r s

theorem bNorm_mem' (S : Stoch d) (st : Stationary S) (t : ℕ) :
    0 ≤ bNorm S st t ∧ bNorm S st t ≤ 1 :=
  bNorm_mem S st t

theorem exists_max_lag' (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) :
    ∃ k0 : ℕ, 0 < k0 ∧ aK S st k0 / k0 = gammaPS S st
      ∧ (k0 : ℝ) ≤ 1 / gammaPS S st :=
  exists_max_lag S st hgap

theorem prop1_deterministic' (h τ η hhat : ℝ)
    (hη : 0 < η) (hη' : η ≤ 1 / 4) (hτ : 0 < τ) (hh : 0 ≤ h)
    (hlo : ((1 - 2 * η) * h - η * τ) / (1 + η) ≤ hhat)
    (hhi : hhat ≤ ((1 + 2 * η) * h + η * τ) / (1 - η)) :
    |hhat - h| ≤ η * (3 * h + τ) / (1 - η) :=
  prop1_deterministic h τ η hhat hη hη' hτ hh hlo hhi

theorem bernKL_le' (u v ε : ℝ) (hu : 0 < u) (hv : u < v) (hv' : v ≤ 1 / 3)
    (hrel : v = (1 + 8 * ε) * u) (hε : 0 < ε) :
    bernKL u v ≤ 128 * ε ^ 2 * u :=
  bernKL_le u v ε hu hv hv' hrel hε

theorem pathMeasure_init_le' {n : ℕ} (P : Matrix (Fin d) (Fin d) ℝ)
    (mu0 st : Fin d → ℝ) (hP : ∀ i j, 0 ≤ P i j) (hst : ∀ i, 0 < st i)
    (hmu : ∀ i, mu0 i ≤ st i / ⨅ j, st j)
    (E : Finset (Fin (n + 1) → Fin d)) :
    pathMeasure P mu0 E ≤ pathMeasure P st E / (⨅ j, st j) :=
  pathMeasure_init_le P mu0 st hP hst hmu E

/-! ## Lemma 1 (Gaps of powers) -/

theorem lemma_1_paper (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) :
    ∀ k : ℕ, 0 < k →
      (1 / 4 : ℝ) * min (k * gammaPS S st) 1
        ≤ gammaPS (S.pow k) (stationaryPow S st k)
      ∧ gammaPS (S.pow k) (stationaryPow S st k) ≤ min (k * gammaPS S st) 1 :=
  fun k hk => (lemma_1 S st hgap).1 k hk

theorem lemma_1_ergodic (E : Ergodic d) :
    (∀ k : ℕ, 0 < k →
      (1 / 4 : ℝ) * min (k * gammaPS E.S E.st) 1
        ≤ gammaPS (E.S.pow k) (stationaryPow E.S E.st k)
      ∧ gammaPS (E.S.pow k) (stationaryPow E.S E.st k) ≤ min (k * gammaPS E.S E.st) 1)
    ∧ (∀ t : ℕ, 0 < t → (1 / (gammaPS E.S E.st) : ℝ) ≤ t → (1 / 2 : ℝ) < aK E.S E.st t) :=
  lemma_1 E.S E.st E.gap_pos

/-! ## Proposition 1 and Lemma 2 -/

/-- Original unconditioned Proposition 1. Both original probability inputs
are proved, and every application-specific matrix and path argument is closed. -/
theorem proposition_1 (m : ℕ) (Q : Stoch d) (st : Stationary Q) [NeZero d]
    (τ η : ℝ) (mu0 : Fin d → ℝ)
    (hτ : 0 < τ) (hη : 0 < η) (hη' : η ≤ 1 / 4)
    (hm : (1 : ℝ) ≤ m * gammaPS Q st)
    (hmu : ∀ i, 0 ≤ mu0 i) (hsum : ∑ i, mu0 i = 1) :
    let p := Stationary.star st
    let Γ := gammaPS Q st
    let h := 1 - sigma2 (simil st.mu Q.P)
    pathMeasure Q.P mu0
      (Finset.univ.filter fun Y : Fin (m + 1) → Fin d =>
        ¬ (degPos Y ∧
          |(1 - sigma2 (lHat Y)) - h| ≤ η * (3 * h + τ) / (1 - η)))
      ≤ 4 * d / p * exp (-(m * p * Γ * η ^ 2) / 36)
        + 4 * (d : ℝ) * exp (-(3 * m * p * τ * η ^ 2) / 16) := by
  exact PsgEst.proposition_1_closed m Q st τ η mu0 hτ hη hη' hm hmu hsum

/-- Both original Appendix conclusions, now proved from the actual scalar
Freedman theorem rather than an external concentration input. -/
theorem lemma_2_paper (m : ℕ) (Q : Stoch d) (st : Stationary Q) [NeZero d]
    (η δ : ℝ) (mu0 : Fin d → ℝ)
    (hη : 0 < η) (hη' : η ≤ 1 / 4) (hδ : 0 < δ) (hδ' : δ < 1)
    (hmu : ∀ i, 0 ≤ mu0 i) (hsum : ∑ i, mu0 i = 1)
    (hΓ : 0 < gammaPS Q st) :
    let p := Stationary.star st
    let Γ := gammaPS Q st
    let b : ℕ := Nat.ceil ((1 + 2 * log (4 / (η * p))) / Γ)
    let fail : Finset (Fin (m + 1) → Fin d) :=
      Finset.univ.filter fun Y => ¬ degreeEvent st.mu η Y
    (((m : ℝ) ≥ 72 * b / (p * η ^ 2) * log (4 * (d : ℝ) * b / δ))
      → pathMeasure Q.P mu0 fail ≤ δ)
    ∧
    ((2 * b ≤ m ∧ (m : ℝ) * p / (2 * b) ≥ 2 / η)
      → pathMeasure Q.P mu0 fail
          ≤ 4 * (d : ℝ) * b * exp (-((m : ℝ) * p * η ^ 2) / (72 * b))) := by
  simpa only [neg_div] using
    PsgEst.lemma_2_closed m Q st η δ mu0 hη hη' hδ hδ' hmu hsum hΓ


/-! ## Theorem 1 (Uniform upper bound) -/

/-- Failure event of the estimator at relative precision `ε`. -/
def failEvent {n : ℕ} (X : Fin (n + 1) → Fin d) (γ ε : ℝ) : Prop :=
  ε * γ < |gammaHat X - γ|

/-- **Theorem 1** (Uniform upper bound).
There is a statistic `γ̂_n` (namely `gammaHat`) such that for every ergodic `P`,
every initial distribution, `0 < ε < 1/2`, `0 < δ < 1`,
`n ≥ 73728 / (π_⋆ γ ε²) · log(8d / (δ π_⋆ γ))` implies
`P(|γ̂_n - γ| > ε γ) ≤ δ`.
The statistic uses only the trajectory and the known state space. -/
theorem theorem_1 [NeZero d] (E : Ergodic d) (n : ℕ) (ε δ : ℝ)
    (hε : 0 < ε) (hε' : ε < 1 / 2) (hδ : 0 < δ) (hδ' : δ < 1)
    (mu0 : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu0 i) (hsum : ∑ i, mu0 i = 1)
    (hn : (n : ℝ) ≥ 73728 / (Stationary.star E.st * gammaPS E.S E.st * ε ^ 2)
          * log (8 * (d : ℝ) / (δ * Stationary.star E.st * gammaPS E.S E.st))) :
    pathMeasure E.S.P mu0
      (Finset.univ.filter (fun X : Fin (n + 1) → Fin d =>
        failEvent X (gammaPS E.S E.st) ε))
      ≤ δ := by
  have hprop : UpperProbability.Proposition1Bound d := by
    intro m Q st τ η mu0 hτ hη hη' hm hmu hsum
    exact proposition_1 m Q st τ η mu0 hτ hη hη' hm hmu hsum
  exact UpperProbability.uniform_upper_of_proposition1 hprop E n ε δ
    hε hε' hδ hδ' mu0 hmu hsum hn

/-! ## Theorem 2 (Minimax bounds) -/

/-- The uniform theorem, exposed as the input of the independent minimax reduction. -/
theorem uniformEstimationBound (S : Stoch d) (st : Stationary S) [NeZero d]
    (hgap : 0 < gammaPS S st) : UniformEstimationBound S st := by
  let E : Ergodic d := ⟨S, st, hgap, gammaPS_le_one_of_stationary S st⟩
  intro n ε δ hε hε' hδ hδ' mu0 hmu hsum hn
  exact theorem_1 E n ε δ hε hε' hδ hδ' mu0 hmu hsum hn

/-- Theorem 2, upper bound with one fixed universal constant. -/
theorem theorem_2_upper [NeZero d] (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2) :
    (nStar d p g ε : ℝ) ≤ 73729 / (p * g * ε ^ 2) * log (24 * d / (p * g)) := by
  exact minimax_upper_of_uniform hd p g ε hp hp' hg hg' hε hε'
    (fun S st _ hγ => uniformEstimationBound S st (hg.trans_le hγ))

/-- Theorem 2, lower bound.  Existence of a successful sample size follows from
Theorem 1; it is not added as a hypothesis of the paper theorem. -/
theorem theorem_2_lower [NeZero d] (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2) :
    (1 / 2048 : ℝ) / (p * g * ε ^ 2) ≤ nStar d p g ε := by
  have hAcc := exists_accurate_of_uniform hd p g ε hp hp' hg hg' hε hε'
    (fun S st _ hγ => uniformEstimationBound S st (hg.trans_le hγ))
  exact nStar_le_of_ne d hd p g ε hp hp' hg hg' hε hε' ⟨_, gammaHat, hAcc⟩

/-- Theorem 2 with explicit universal constants, hence with the source quantifiers. -/
theorem theorem_2 [NeZero d] (hd : 2 ≤ d) (p g ε : ℝ)
    (hp : 0 < p) (hp' : p ≤ 1 / d) (hg : 0 < g) (hg' : g ≤ 1 / 8)
    (hε : 0 < ε) (hε' : ε < 1 / 2) :
    (1 / 2048 : ℝ) / (p * g * ε ^ 2) ≤ nStar d p g ε ∧
    (nStar d p g ε : ℝ) ≤ 73729 / (p * g * ε ^ 2) * log (24 * d / (p * g)) :=
  ⟨theorem_2_lower hd p g ε hp hp' hg hg' hε hε',
    theorem_2_upper hd p g ε hp hp' hg hg' hε hε'⟩


end Paper
end PsgEst
