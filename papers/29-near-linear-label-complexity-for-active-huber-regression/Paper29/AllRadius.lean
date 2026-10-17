import Paper29.ScoreAssembly
import Paper29.LewisInput

noncomputable section
open scoped BigOperators Classical ENNReal
namespace Paper29.Chaining
open WeightConstruction ExternalCovering ProcessTools

/-- The complete mathematical existence of all-radius scores, with each known
external theorem disclosed as a separate explicit input. The deterministic
finite approximation of the l1 endpoint remains a separate algorithmic item. -/
theorem all_radius_scores_exist {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hn : 1 ≤ n) (hA : A.rank = d) (hrows : ∀ i, A i ≠ 0)
    (Cₜ Cₑ : ℝ) (hCₜ : 0 ≤ Cₜ) (hCₑ : 0 ≤ Cₑ)
    (stability : RadiusLogNonexpansive) (transition : HuberPrimitive 4 Cₜ)
    (endpoint : PowerPrimitive Cₑ) (lewis : LewisOneNormalization) :
    ∃ τ : Fin n → ℝ, (∀ i, 0 < τ i) ∧
      (∑ i, τ i) ≤ (4+11/Real.log 2)*d*Real.log (2*(n:ℝ)) ∧
      ScoreGeometry A τ ((2*Cₜ+4*Cₑ)*ProcessTools.logFactor n) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let scheme := constructedHuberScheme A hA hrows stability
    (-2-(transitionLength n:ℤ)) (2+transitionTop n)
  obtain ⟨w₁, hw₁⟩ := lewis n d A hA hrows
  let w₂ : PositiveWeights n := ⟨fun _ => 1, fun _ => by norm_num⟩
  have hb₁ : ∀ i, (Leverage.radius A w₁ i)^(1:ℝ) / Leverage.leverage A w₁ i = 1 := by
    simpa only [Real.rpow_one] using hw₁
  have hb₂ : ∀ i, (Leverage.radius A w₂ i)^(2:ℝ) / Leverage.leverage A w₂ i = 1 := by
    intro i
    rw [Real.rpow_two, Leverage.radius_sq A w₂ (Leverage.mulVec_injective_of_rank_eq A hA) w₂.property]
    change Leverage.radiusSq A w₂ i / (1 * Leverage.radiusSq A w₂ i) = 1
    rw [one_mul, div_self (ne_of_gt (Leverage.radiusSq_pos A w₂
      (Leverage.mulVec_injective_of_rank_eq A hA) w₂.property i (hrows i)))]
  exact ⟨combinedScores A scheme.w w₁ w₂,
    all_radius_score_assembly A hn hA hrows scheme w₁ w₂ hb₁ hb₂ Cₜ Cₑ hCₜ hCₑ transition endpoint⟩

/-- A common universal constant for the source mass and geometry statement. -/
theorem all_radius_scores_statement (Cₜ Cₑ : ℝ) (hCₜ : 0 ≤ Cₜ) (hCₑ : 0 ≤ Cₑ)
    (stability : RadiusLogNonexpansive) (transition : HuberPrimitive 4 Cₜ)
    (endpoint : PowerPrimitive Cₑ) (lewis : LewisOneNormalization) : AllRadiusScoresStatement := by
  let C : ℝ := (4+11/Real.log 2) + (2*Cₜ+4*Cₑ) + 1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmass : 4+11/Real.log 2 ≤ C := by dsimp [C]; linarith
  have hgeom : 2*Cₜ+4*Cₑ ≤ C := by
    have hh : 0 ≤ 11/Real.log 2 := by positivity
    dsimp [C]
    linarith
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro n d A hA hrows
  have hrows' (i) : A i ≠ 0 := by
    intro hz
    obtain ⟨j,hj⟩ := hrows i
    have hh := congrFun hz j
    exact hj hh
  by_cases hn0 : n = 0
  · subst n
    refine ⟨fun i => Fin.elim0 i, (fun i => Fin.elim0 i), ?_, ?_⟩
    · simp
    · intro R hR
      have hd : (fun h k : ball A R => huberMetric A (fun i => Fin.elim0 i) h k) =
          fun _ _ => 0 := by funext h k; simp [huberMetric]
      rw [hd, gamma2_zero]
      exact bot_le
  · have hn : 1 ≤ n := by omega
    obtain ⟨τ, hτ, hT, hcover⟩ := all_radius_scores_exist A hn hA hrows' Cₜ Cₑ hCₜ hCₑ
      stability transition endpoint lewis
    refine ⟨τ, hτ, ?_, ?_⟩
    · have hlog : 0 ≤ Real.log (2*(n:ℝ)) := by
        have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
        exact (Real.log_pos (by linarith : (1:ℝ)<2*n)).le
      apply hT.trans
      have hp := mul_le_mul_of_nonneg_right hmass (mul_nonneg (Nat.cast_nonneg d) hlog)
      convert hp using 1 <;> ring
    · intro R hR
      have hc := hcover R hR
      apply hc.trans
      apply ENNReal.ofReal_le_ofReal
      rw [← ProcessTools.logFactor_eq_rpow hn]
      have hp := mul_le_mul_of_nonneg_right hgeom
        (mul_nonneg (Real.sqrt_nonneg R) (ProcessTools.logFactor_pos hn).le)
      convert hp using 1 <;> ring

end Paper29.Chaining
