import Paper29.TransitionScores
import Paper29.EndpointCovering

noncomputable section
open scoped BigOperators Classical ENNReal
namespace Paper29.Chaining
open WeightConstruction ExternalCovering ProcessTools

/-- One label-independent score vector: a finite transition sum and two exact
endpoint leverage vectors. Summing the window changes only a universal constant. -/
def combinedScores {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w : ℤ → PositiveWeights n) (w₁ w₂ : PositiveWeights n) (i : Fin n) : ℝ :=
  windowScore A (transitionScales n) w i + Leverage.leverage A w₁ i + Leverage.leverage A w₂ i

/-- The complete own three-regime assembly of Lemma3.4. Only the two published
finite-scale covering primitives and the general radius stability theorem are
external inputs. Endpoints here are exact normalized Lewis/leverage solutions. -/
theorem all_radius_score_assembly {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hn : 1 ≤ n) (hA : A.rank = d) (hrows : ∀ i, A i ≠ 0)
    (scheme : HuberScheme A (-2-(transitionLength n:ℤ)) (2+transitionTop n) 4)
    (w₁ w₂ : PositiveWeights n)
    (hbase₁ : ∀ i, (Leverage.radius A w₁ i)^(1:ℝ) / Leverage.leverage A w₁ i = 1)
    (hbase₂ : ∀ i, (Leverage.radius A w₂ i)^(2:ℝ) / Leverage.leverage A w₂ i = 1)
    (Cₜ Cₑ : ℝ) (hCₜ : 0 ≤ Cₜ) (hCₑ : 0 ≤ Cₑ)
    (transition : HuberPrimitive 4 Cₜ) (endpoint : PowerPrimitive Cₑ) :
    let τ := combinedScores A scheme.w w₁ w₂
    (∀ i, 0 < τ i) ∧
      (∑ i, τ i) ≤ (4 + 11/Real.log 2) * d * Real.log (2*(n:ℝ)) ∧
      ScoreGeometry A τ ((2*Cₜ+4*Cₑ)*ProcessTools.logFactor n) := by
  dsimp only
  let τ := combinedScores A scheme.w w₁ w₂
  have hwin (i) := windowScore_nonneg A hA (transitionScales n) scheme.w i
  have h₁ (i) := leverage_pos A hA hrows w₁ i
  have h₂ (i) := leverage_pos A hA hrows w₂ i
  have hd₁ (i) : Leverage.leverage A w₁ i ≤ τ i := by dsimp [τ, combinedScores]; linarith [hwin i,h₂ i]
  have hd₂ (i) : Leverage.leverage A w₂ i ≤ τ i := by dsimp [τ, combinedScores]; linarith [hwin i,h₁ i]
  have hdwin (i) : windowScore A (transitionScales n) scheme.w i ≤ τ i := by
    dsimp [τ, combinedScores]; linarith [h₁ i,h₂ i]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact (h₁ i).trans_le (hd₁ i)
  · have hmass : (∑ i, τ i) = (((transitionScales n).card : ℝ)+2)*d := by
      simp only [τ, combinedScores, Finset.sum_add_distrib, windowScore_mass A hA,
        Leverage.leverage_sum_of_rank_eq A w₁ hA w₁.property,
        Leverage.leverage_sum_of_rank_eq A w₂ hA w₂.property]
      ring
    rw [hmass]
    have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hl : Real.log 2 ≤ Real.log (2*(n:ℝ)) := Real.log_le_log (by norm_num) (by linarith)
    have htwo : 2 ≤ (2/Real.log 2)*Real.log (2*(n:ℝ)) := by
      have hh : (2:ℝ) ≤ 2*Real.log (2*(n:ℝ))/Real.log 2 :=
        (le_div_iff₀ hlog).2 (by linarith)
      convert hh using 1 <;> ring
    have hc := transitionScales_card_le hn
    have hcoef : ((transitionScales n).card : ℝ)+2 ≤
        (4+11/Real.log 2)*Real.log (2*(n:ℝ)) := by
      calc
        _ ≤ (4+9/Real.log 2)*Real.log (2*(n:ℝ)) +
            (2/Real.log 2)*Real.log (2*(n:ℝ)) := add_le_add hc htwo
        _ = _ := by ring
    convert mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg d) using 1 <;> ring
  · have he₁ := (endpoint_cover_all_radii A hn hA hrows w₁ 1 (Or.inl rfl) (by simpa only [Nat.cast_one] using hbase₁) Cₑ hCₑ endpoint).2
    have he₂ := (endpoint_cover_all_radii A hn hA hrows w₂ 2 (Or.inr rfl) (by simpa only [Nat.cast_ofNat] using hbase₂) Cₑ hCₑ endpoint).2
    intro R hR
    have hlog : 0 ≤ ProcessTools.logFactor n := (ProcessTools.logFactor_pos hn).le
    have hrs : 0 ≤ ProcessTools.logFactor n * Real.sqrt R := by positivity
    by_cases hsmall : R ≤ 1/2
    · have hh := small_radius_cover A τ _ h₂ hd₂ (by positivity) he₂ hR hsmall
      apply hh.trans
      apply ENNReal.ofReal_le_ofReal
      have hp := mul_le_mul_of_nonneg_right (show 4*Cₑ ≤ 2*Cₜ+4*Cₑ by linarith) hrs
      convert hp using 1 <;> ring
    · by_cases hlarge : (n:ℝ)/2 ≤ R
      · have hh := large_radius_cover A τ _ h₁ hd₁ (by positivity) he₁ hR hlarge
        apply hh.trans
        apply ENNReal.ofReal_le_ofReal
        have hp := mul_le_mul_of_nonneg_right (show 4*Cₑ ≤ 2*Cₜ+4*Cₑ by linarith) hrs
        convert hp using 1 <;> ring
      · have hh := transition_radius_cover A hA hrows scheme τ hdwin Cₜ hCₜ transition
          (le_of_not_ge hsmall) (le_of_not_ge hlarge)
        apply hh.trans
        apply ENNReal.ofReal_le_ofReal
        have hp := mul_le_mul_of_nonneg_right (show 2*Cₜ ≤ 2*Cₜ+4*Cₑ by linarith) hrs
        convert hp using 1 <;> ring

end Paper29.Chaining
