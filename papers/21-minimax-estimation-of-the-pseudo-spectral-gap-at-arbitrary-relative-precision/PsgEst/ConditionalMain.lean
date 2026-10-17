import PsgEst.RelativeConcentration
import PsgEst.UpperProbability
import PsgEst.MinimaxUpper
import PsgEst.ModelClass
import PsgEst.AppendixVisit

/-!
# Complete principal arguments with the original external inputs explicit

This module has no postulated instance of either cited concentration theorem.
It separates their mathematical statements from the paper's own contributions.
The unconditioned source contracts remain in `Main` and are not replaced by
these explicitly conditional results.
-/

open Matrix BigOperators Real Classical
namespace PsgEst

/-- Only the two probability theorems cited in Section 3. No instance is
postulated. The process assumptions of Freedman are checked by EdgeProcess. -/
structure ExternalConcentrationInputs (d : ℕ) [NeZero d] : Prop where
  paulin : ∀ (Q : Stoch d) (st : Stationary Q),
    0 < gammaPS Q st → PaulinOriginalInput Q st (gammaPS Q st)
  freedman : ∀ (Q : Stoch d) (mu : Fin d → ℝ),
    (∀ i, 0 ≤ mu i) → (∑ i, mu i = 1) → MatrixFreedmanInput Q mu

variable {d : ℕ} [NeZero d]

theorem proposition1Bound_of_external (h : ExternalConcentrationInputs d) :
    UpperProbability.Proposition1Bound d := by
  intro m Q st τ η mu hτ hη hη' hmΓ hmu hsum
  have hΓ : 0 < gammaPS Q st := by
    by_contra hh
    have hle := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) (le_of_not_gt hh)
    linarith
  have hpr := RelativeConcentration.proposition_1_of_external Q st τ η mu
    hτ hη hη' hmΓ hmu hsum (h.paulin Q st hΓ) (h.freedman Q mu hmu hsum)
  convert hpr using 1 <;> congr 1 <;> ext Y <;> simp [RelativeConcentration.good]

theorem uniform_upper_from_external (h : ExternalConcentrationInputs d)
    (E : Ergodic d) (n : ℕ) (ε δ : ℝ)
    (hε : 0 < ε) (hε' : ε < 1/2) (hδ : 0 < δ) (hδ' : δ < 1)
    (mu : Fin d → ℝ) (hmu : ∀ i, 0 ≤ mu i) (hsum : ∑ i, mu i = 1)
    (hn : 73728/(Stationary.star E.st*gammaPS E.S E.st*ε^2)*
      log (8*(d:ℝ)/(δ*Stationary.star E.st*gammaPS E.S E.st)) ≤ (n:ℝ)) :
    pathMeasure E.S.P mu (Finset.univ.filter fun X : Fin (n+1) → Fin d =>
      ε*gammaPS E.S E.st < |gammaHat X-gammaPS E.S E.st|) ≤ δ :=
  UpperProbability.uniform_upper_of_proposition1 (proposition1Bound_of_external h)
    E n ε δ hε hε' hδ hδ' mu hmu hsum hn

theorem uniformEstimationBound_from_external (h : ExternalConcentrationInputs d)
    (S : Stoch d) (st : Stationary S) (hgap : 0 < gammaPS S st) :
    UniformEstimationBound S st := by
  let E : Ergodic d := ⟨S, st, hgap, gammaPS_le_one_of_stationary S st⟩
  intro n ε δ hε hε' hδ hδ' mu hmu hsum hn
  exact uniform_upper_from_external h E n ε δ hε hε' hδ hδ' mu hmu hsum hn

/-- Theorem 2 on the actual irreducible, aperiodic source class, with a single
fixed universal upper constant and the explicit lower constant. -/
theorem minimax_bounds_from_external (h : ExternalConcentrationInputs d)
    (hd : 2 ≤ d) (p g ε : ℝ) (hp : 0 < p) (hp' : p ≤ 1/d)
    (hg : 0 < g) (hg' : g ≤ 1/8) (hε : 0 < ε) (hε' : ε < 1/2) :
    (1/2048 : ℝ)/(p*g*ε^2) ≤ standardNStar d p g ε ∧
    (standardNStar d p g ε : ℝ) ≤ 73729/(p*g*ε^2)*log (24*d/(p*g)) := by
  have hU : ∀ (S : Stoch d) (st : Stationary S),
      p ≤ Stationary.star st → g ≤ gammaPS S st → UniformEstimationBound S st :=
    fun S st _ hγ => uniformEstimationBound_from_external h S st (hg.trans_le hγ)
  have hAcc := exists_accurate_of_uniform hd p g ε hp hp' hg hg' hε hε' hU
  rw [standardNStar_eq_nStar d p g ε hg]
  exact ⟨nStar_le_of_ne d hd p g ε hp hp' hg hg' hε hε' ⟨_, gammaHat, hAcc⟩,
    minimax_upper_of_uniform hd p g ε hp hp' hg hg' hε hε' hU⟩

/-- Complete Appendix Lemma 2 from the original external Freedman input. -/
theorem lemma_2_from_external (h : ExternalConcentrationInputs d) (m : ℕ) (Q : Stoch d) (st : Stationary Q)
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
  have hf := lemma_2_paper_of_freedman m Q st η δ mu0 hη hη' hδ hδ' hmu hsum hΓ
    (fun r => h.freedman (Q.pow (mixingLag Q st η)) (shiftedLaw Q.P mu0 r)
      (shiftedLaw_nonneg Q mu0 hmu r) (shiftedLaw_sum Q mu0 hsum r))
  simpa only [neg_div] using hf

end PsgEst
