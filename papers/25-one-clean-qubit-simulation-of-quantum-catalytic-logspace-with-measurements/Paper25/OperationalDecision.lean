import Paper25.Main
import Paper25.OneCleanQubit
import Paper25.Resources

/-! The paper's signed decision-gap argument applied to the actual density
matrix circuit, after the normalized trace approximation has been established.
This conditional consequence does not assert the missing compiler existence.
-/
noncomputable section
namespace Paper25
open OneCleanQubit

/-- Equation (23) for the physical trace circuit. Its acceptance probability
is computed by Born measurement after `H controlled(𝒱) H`. -/
theorem operational_decision_gap {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (k : ℕ) (W : Matrix (Fin (2 ^ k) × n) (Fin (2 ^ k) × n) ℂ)
    (hW : OneCleanQubit.Unitary W) (lam K p : ℝ) (hlam : 0 < lam) (hK : 1 ≤ K)
    (herr : |(Matrix.trace (W.submatrix (fun i => (0, i)) (fun i => (0, i)))).re /
        Fintype.card n - lam * (2 * p - 1) / Real.sqrt K| ≤ lam / (100 * K)) :
    let P := ancillaryProjector (n := n) (Fin (2 ^ k)) (0 : Fin (2 ^ k))
    let pTarget := probZero (output (reflectedTraceUnitary P W))
    (2 / 3 ≤ p → 1 / 2 + lam / ((2 : ℝ) ^ (k + 3) * Real.sqrt K) ≤ pTarget) ∧
    (p ≤ 1 / 3 → pTarget ≤ 1 / 2 - lam / ((2 : ℝ) ^ (k + 3) * Real.sqrt K)) := by
  dsimp only
  let P := ancillaryProjector (n := n) (Fin (2 ^ k)) (0 : Fin (2 ^ k))
  let V := reflectedTraceUnitary P W
  let a : ℝ := (Matrix.trace (W.submatrix (fun i => (0, i)) (fun i => (0, i)))).re /
    Fintype.card n
  have hV := reflectedTraceUnitary_unitary P W (ancillaryProjector_hermitian _ _)
    (ancillaryProjector_idempotent _ _) hW
  have he := OneCleanQubit.lemma6 k W hW
  have hb := output_signedBias V hV
  have htarget : probZero (output V) = 1/2 + a / (2:ℝ)^(k+1) := by
    have hexp : expectationZ (output V) = a / (2:ℝ)^k := he
    rw [hexp] at hb
    have hdiv : a / (2:ℝ)^k = 2 * (a / (2:ℝ)^(k+1)) := by
      rw [pow_succ]
      field_simp
      <;> ring
    rw [hdiv] at hb
    linarith
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have gap (e b : ℝ) (he : (1/3:ℝ) ≤ |e|)
      (hepos : 0 < e) (h : |b-lam*e/Real.sqrt K| ≤ lam/(100*K)) :
      lam/(4*Real.sqrt K) ≤ b :=
    (theorem1_decision_gap lam K e b hlam hK he h).1 hepos
  change (2/3 ≤ p → _ ≤ probZero (output V)) ∧
    (p ≤ 1/3 → probZero (output V) ≤ _)
  rw [htarget]
  constructor
  · intro hp
    have he : (1/3:ℝ) ≤ 2*p-1 := by linarith
    have hepos : 0 < 2*p-1 := by linarith
    have habs : (1/3:ℝ) ≤ |2*p-1| := by rw [abs_of_pos hepos]; exact he
    exact theorem1_prob_gap lam K a k hlam hKpos (gap _ _ habs hepos herr)
  · intro hp
    have he : 2*p-1 ≤ -(1/3:ℝ) := by linarith
    have heneg : 2*p-1 < 0 := by linarith
    have habs : (1/3:ℝ) ≤ |2*p-1| := by rw [abs_of_neg heneg]; linarith
    have ha := (theorem1_decision_gap lam K (2*p-1) a hlam hK habs herr).2 heneg
    simp only [neg_div] at ha
    have hneg : lam/(4*Real.sqrt K) ≤ -a := by linarith
    have hg := theorem1_prob_gap lam K (-a) k hlam hKpos hneg
    simp only [neg_div] at hg
    linarith

end Paper25
