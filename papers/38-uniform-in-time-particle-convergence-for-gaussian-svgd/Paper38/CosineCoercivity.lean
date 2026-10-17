import Paper38.CosineExample
import Mathlib.Topology.Order.Compact

noncomputable section

open Real Set

namespace Paper38.Cosine

lemma perturbation_lower {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 ≤ s) (μ : ℝ) :
    -ε ≤ ε * attenuation s * Real.cos μ := by
  have h₁ := mul_le_mul_of_nonneg_left (Real.neg_one_le_cos μ)
    (mul_nonneg hε (attenuation_pos s).le)
  have h₂ := mul_le_mul_of_nonneg_left (attenuation_le_one hs) hε
  nlinarith

lemma energy_base_lower {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 < s) (μ : ℝ) :
    (μ ^ 2 + s - Real.log s) / 2 - ε ≤ energy ε μ s := by
  have := perturbation_lower hε hs.le μ
  unfold energy
  linarith

lemma log_le_half {s : ℝ} (hs : 0 < s) : Real.log s ≤ s / 2 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < s / 2 by positivity)
  have h₂ := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have heq : Real.log (s / 2) = Real.log s - Real.log 2 :=
    Real.log_div hs.ne' (by norm_num)
  rw [heq] at h
  linarith

/-- Every energy sublevel stays away from the singular boundary and is bounded
in both coordinates. These explicit bounds establish the coercivity claimed
in Example 9.1 without an extra analytic hypothesis. -/
lemma energy_sublevel_bounds {ε R μ s : ℝ} (hε : 0 ≤ ε) (hs : 0 < s)
    (hE : energy ε μ s ≤ R) :
    μ ^ 2 ≤ 2 * (R + ε) ∧
      Real.exp (-2 * (R + ε)) ≤ s ∧ s ≤ 4 * (R + ε) := by
  have hbase := energy_base_lower hε hs μ
  have hlog := Real.log_le_sub_one_of_pos hs
  have hhalf := log_le_half hs
  have hμsq := sq_nonneg μ
  refine ⟨by linarith, ?_, by linarith⟩
  rw [← Real.exp_log hs, Real.exp_le_exp]
  linarith

/-- Compactness of the actual energy sublevel, viewed as a subset of `ℝ²`. -/
lemma energy_sublevel_compact {ε : ℝ} (hε : 0 ≤ ε) (R : ℝ) :
    IsCompact {q : ℝ × ℝ | 0 < q.2 ∧ energy ε q.1 q.2 ≤ R} := by
  let l : ℝ := Real.exp (-2 * (R + ε))
  let B : ℝ := 2 * |R + ε| + 1
  let U : ℝ := 4 * |R + ε| + 1
  have hl : 0 < l := Real.exp_pos _
  have hclamp : Continuous (fun q : ℝ × ℝ => energy ε q.1 (max l q.2)) := by
    unfold energy attenuation
    apply Continuous.add
    · apply Continuous.div_const
      apply Continuous.sub
      · fun_prop
      · apply Continuous.log
        · fun_prop
        · intro q
          exact ne_of_gt (lt_of_lt_of_le hl (le_max_left _ _))
    · fun_prop
  have hset : {q : ℝ × ℝ | 0 < q.2 ∧ energy ε q.1 q.2 ≤ R} =
      {q : ℝ × ℝ | l ≤ q.2} ∩ {q : ℝ × ℝ | energy ε q.1 (max l q.2) ≤ R} := by
    ext q
    constructor
    · intro hq
      change 0 < q.2 ∧ energy ε q.1 q.2 ≤ R at hq
      change l ≤ q.2 ∧ energy ε q.1 (max l q.2) ≤ R
      have hb := energy_sublevel_bounds hε hq.1 hq.2
      have hlq : l ≤ q.2 := hb.2.1
      refine ⟨hlq, ?_⟩
      rw [max_eq_right hlq]
      exact hq.2
    · intro hq
      change l ≤ q.2 ∧ energy ε q.1 (max l q.2) ≤ R at hq
      change 0 < q.2 ∧ energy ε q.1 q.2 ≤ R
      rw [max_eq_right hq.1] at hq
      exact ⟨lt_of_lt_of_le hl hq.1, hq.2⟩
  have hclosed : IsClosed {q : ℝ × ℝ | 0 < q.2 ∧ energy ε q.1 q.2 ≤ R} := by
    rw [hset]
    exact (isClosed_le continuous_const continuous_snd).inter
      (isClosed_le hclamp continuous_const)
  have hsubset : {q : ℝ × ℝ | 0 < q.2 ∧ energy ε q.1 q.2 ≤ R} ⊆
      (Icc (-B) B) ×ˢ (Icc l U) := by
    intro q hq
    obtain ⟨hm, hlq, hu⟩ := energy_sublevel_bounds hε hq.1 hq.2
    have habs : R + ε ≤ |R + ε| := le_abs_self _
    have habs' : 0 ≤ |R + ε| := abs_nonneg _
    have hm' : -B ≤ q.1 ∧ q.1 ≤ B := by
      dsimp [B]
      constructor <;> nlinarith [sq_nonneg (q.1 - 1), sq_nonneg (q.1 + 1)]
    exact ⟨hm', hlq, by dsimp [U]; linarith⟩
  exact ((isCompact_Icc).prod isCompact_Icc).of_isClosed_subset hclosed hsubset

end Paper38.Cosine
