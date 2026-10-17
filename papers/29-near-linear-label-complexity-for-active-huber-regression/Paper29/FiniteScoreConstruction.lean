import Paper29.AllRadius
import Paper29.FiniteEndpoint

noncomputable section
open scoped BigOperators Classical
namespace Paper29.Chaining
open WeightConstruction ExternalCovering ProcessTools

/-- All score coordinates use finitely stopped exact updates and matrix
inverses. The exact Lewis witness is used only in their correctness proof. -/
def finiteScores {n d : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin d) ℝ)
    (hA : A.rank = d) (hrows : ∀ i, A i ≠ 0) (stability : RadiusLogNonexpansive)
    (i : Fin n) : ℝ :=
  let scheme := constructedHuberScheme A hA hrows stability
    (-2-(transitionLength n:ℤ)) (2+transitionTop n)
  windowScore A (transitionScales n) scheme.w i +
    16*Leverage.leverage A (finiteOneWeight A hA hrows stability) i +
    Leverage.leverage A (fun _ => 1) i

/-- Finite construction portion of Lemma3.4, including safe endpoint inflation
and its exact trace mass. No endpoint algorithm or score correctness is assumed. -/
theorem finiteScores_spec {n d : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin d) ℝ)
    (hn : 1 ≤ n) (hA : A.rank = d) (hrows : ∀ i, A i ≠ 0)
    (Cₜ Cₑ : ℝ) (hCₜ : 0 ≤ Cₜ) (hCₑ : 0 ≤ Cₑ)
    (stability : RadiusLogNonexpansive) (transition : HuberPrimitive 4 Cₜ)
    (endpoint : PowerPrimitive Cₑ) (lewis : LewisOneNormalization) :
    let τ := finiteScores A hA hrows stability
    (∀ i, 0 < τ i) ∧
      (∑ i, τ i) ≤ (4+26/Real.log 2)*d*Real.log (2*(n:ℝ)) ∧
      ScoreGeometry A τ ((2*Cₜ+4*Cₑ)*ProcessTools.logFactor n) := by
  let scheme := constructedHuberScheme A hA hrows stability
    (-2-(transitionLength n:ℤ)) (2+transitionTop n)
  obtain ⟨w₁, hw₁⟩ := lewis n d A hA hrows
  let w₂ : PositiveWeights n := ⟨fun _ => 1, fun _ => by norm_num⟩
  have hb₁ : ∀ i, (Leverage.radius A w₁ i)^(1:ℝ) / Leverage.leverage A w₁ i = 1 := by
    simpa only [Real.rpow_one] using hw₁
  have hb₂ : ∀ i, (Leverage.radius A w₂ i)^(2:ℝ) / Leverage.leverage A w₂ i = 1 := by
    intro i
    rw [Real.rpow_two, Leverage.radius_sq A w₂ (Leverage.mulVec_injective_of_rank_eq A hA) w₂.property]
    change Leverage.radiusSq A w₂ i / (1*Leverage.radiusSq A w₂ i) = 1
    rw [one_mul, div_self (ne_of_gt (Leverage.radiusSq_pos A w₂
      (Leverage.mulVec_injective_of_rank_eq A hA) w₂.property i (hrows i)))]
  obtain ⟨hpos, _, hcover⟩ := all_radius_score_assembly A hn hA hrows scheme w₁ w₂ hb₁ hb₂
    Cₜ Cₑ hCₜ hCₑ transition endpoint
  have hdom (i) : combinedScores A scheme.w w₁ w₂ i ≤ finiteScores A hA hrows stability i := by
    have hh := finite_endpoint_dominates A hA hrows stability w₁ hw₁ i
    dsimp only [combinedScores, finiteScores, scheme, w₂]
    linarith
  dsimp only
  refine ⟨(fun i => (hpos i).trans_le (hdom i)), ?_, hcover.mono hpos hdom⟩
  have hmass : (∑ i, finiteScores A hA hrows stability i) =
      (((transitionScales n).card:ℝ)+17)*d := by
    simp only [finiteScores, Finset.sum_add_distrib, ← Finset.mul_sum,
      windowScore_mass A hA,
      Leverage.leverage_sum_of_rank_eq A _ hA (finiteOneWeight A hA hrows stability).property,
      Leverage.leverage_sum_of_rank_eq A (fun _ : Fin n => (1:ℝ)) hA (fun _ => by norm_num)]
    ring
  rw [hmass]
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ Real.log (2*(n:ℝ)) := Real.log_le_log (by norm_num) (by linarith)
  have h17 : (17:ℝ) ≤ (17/Real.log 2)*Real.log (2*(n:ℝ)) := by
    have hh : (17:ℝ) ≤ 17*Real.log (2*(n:ℝ))/Real.log 2 := (le_div_iff₀ hl2).2 (by linarith)
    convert hh using 1 <;> ring
  have hc := transitionScales_card_le hn
  have hcoef : ((transitionScales n).card:ℝ)+17 ≤ (4+26/Real.log 2)*Real.log (2*(n:ℝ)) := by
    calc
      _ ≤ (4+9/Real.log 2)*Real.log (2*(n:ℝ)) + (17/Real.log 2)*Real.log (2*(n:ℝ)) :=
        add_le_add hc h17
      _ = _ := by ring
  convert mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg d) using 1 <;> ring

end Paper29.Chaining
