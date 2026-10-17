import CalibrationDistance.Core

/-! The actual least Lipschitz constant and supremum norm on the source domain
`[0,1]`, with admissibility proved from a Lipschitz hypothesis. -/

open scoped BigOperators NNReal

namespace CalibrationDistance

noncomputable section

def UnitLipschitz (f : ℝ → ℝ) (L : ℝ) : Prop :=
  0 ≤ L ∧ ∀ a ∈ Set.Icc (0 : ℝ) 1, ∀ b ∈ Set.Icc (0 : ℝ) 1,
    |f a - f b| ≤ L * |a - b|

def unitLipschitzConstants (f : ℝ → ℝ) : Set ℝ := {L | UnitLipschitz f L}

def leastLip (f : ℝ → ℝ) : ℝ := sInf (unitLipschitzConstants f)

def unitNormValues (f : ℝ → ℝ) : Set ℝ :=
  {v | ∃ x ∈ Set.Icc (0 : ℝ) 1, v = |f x|}

def unitSupNorm (f : ℝ → ℝ) : ℝ := sSup (unitNormValues f)

lemma unitLipschitzConstants_bddBelow (f : ℝ → ℝ) :
    BddBelow (unitLipschitzConstants f) :=
  ⟨0, fun _ hL => hL.1⟩

theorem leastLip_nonneg {f : ℝ → ℝ} (hf : ∃ C, UnitLipschitz f C) :
    0 ≤ leastLip f := by
  apply le_csInf hf
  intro C hC
  exact hC.1

theorem leastLip_le {f : ℝ → ℝ} {C : ℝ} (hC : UnitLipschitz f C) :
    leastLip f ≤ C := csInf_le (unitLipschitzConstants_bddBelow f) hC

/-- The infimum is itself a valid Lipschitz constant, with no best-constant
existence hypothesis. Every pair of distinct points supplies a lower bound. -/
theorem leastLip_admissible {f : ℝ → ℝ} (hf : ∃ C, UnitLipschitz f C) :
    UnitLipschitz f (leastLip f) := by
  refine ⟨leastLip_nonneg hf, ?_⟩
  intro a ha b hb
  by_cases hab : a = b
  · simp [hab]
  · have hd : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hab)
    have hlower : |f a - f b| / |a - b| ≤ leastLip f := by
      apply le_csInf hf
      intro C hC
      exact (div_le_iff₀ hd).mpr (hC.2 a ha b hb)
    exact (div_le_iff₀ hd).mp hlower

theorem leastLip_isLeast {f : ℝ → ℝ} (hf : ∃ C, UnitLipschitz f C) :
    IsLeast (unitLipschitzConstants f) (leastLip f) :=
  ⟨leastLip_admissible hf, fun _ hC => leastLip_le hC⟩

lemma unitNormValues_nonempty (f : ℝ → ℝ) : (unitNormValues f).Nonempty :=
  ⟨|f 0|, 0, by constructor <;> norm_num, rfl⟩

lemma norm_bound_of_unitLipschitz {f : ℝ → ℝ} {C : ℝ} (hC : UnitLipschitz f C)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : |f x| ≤ C + |f 0| := by
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  calc
    |f x| = |(f x - f 0) + f 0| := by rw [sub_add_cancel]
    _ ≤ |f x - f 0| + |f 0| := abs_add_le _ _
    _ ≤ C * |x - 0| + |f 0| := add_le_add_right (hC.2 x hx 0 hzero) _
    _ ≤ C + |f 0| := by
      rw [sub_zero, abs_of_nonneg hx.1]
      nlinarith [hC.1, hx.2]

lemma unitNormValues_bddAbove {f : ℝ → ℝ} (hf : ∃ C, UnitLipschitz f C) :
    BddAbove (unitNormValues f) := by
  obtain ⟨C, hC⟩ := hf
  refine ⟨C + |f 0|, ?_⟩
  rintro v ⟨x, hx, rfl⟩
  exact norm_bound_of_unitLipschitz hC hx

theorem abs_le_unitSupNorm {f : ℝ → ℝ} (hf : ∃ C, UnitLipschitz f C)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : |f x| ≤ unitSupNorm f :=
  le_csSup (unitNormValues_bddAbove hf) ⟨x, hx, rfl⟩

theorem unitSupNorm_nonneg {f : ℝ → ℝ} (hf : ∃ C, UnitLipschitz f C) :
    0 ≤ unitSupNorm f :=
  (abs_nonneg (f 0)).trans (abs_le_unitSupNorm hf (by constructor <;> norm_num))

theorem unitSupNorm_le {f : ℝ → ℝ} {C : ℝ} (hC : UnitLipschitz f C) :
    unitSupNorm f ≤ C + |f 0| := by
  apply csSup_le (unitNormValues_nonempty f)
  rintro v ⟨x, hx, rfl⟩
  exact norm_bound_of_unitLipschitz hC hx

theorem unitSupNorm_isLUB {f : ℝ → ℝ} (hf : ∃ C, UnitLipschitz f C) :
    IsLUB (unitNormValues f) (unitSupNorm f) :=
  isLUB_csSup (unitNormValues_nonempty f) (unitNormValues_bddAbove hf)

/-- Lemma 4.1 with precisely the source's least Lipschitz constant and
supremum norm. Their existence and admissibility are derived above. -/
theorem witness_comparison_least {α : Type*} [Fintype α] {p y : α → ℝ}
    (hp : Valid p) (hy : Valid y) (f : ℝ → ℝ) (hf : ∃ C, UnitLipschitz f C) :
    |∑ t, f (p t) * (y t - p t)| ≤
      (leastLip f + unitSupNorm f) * calDist p y :=
  witness_comparison hp hy f (leastLip_nonneg hf) (unitSupNorm_nonneg hf)
    (leastLip_admissible hf).2 (fun _ hx => abs_le_unitSupNorm hf hx)

theorem unitLipschitz_of_lipschitzOnWith {f : ℝ → ℝ} {C : ℝ≥0}
    (hf : LipschitzOnWith C f (Set.Icc (0 : ℝ) 1)) : UnitLipschitz f C := by
  refine ⟨C.coe_nonneg, ?_⟩
  intro a ha b hb
  simpa only [Real.dist_eq] using hf.dist_le_mul a ha b hb

theorem witness_comparison_least_of_lipschitzOnWith {α : Type*} [Fintype α]
    {p y : α → ℝ} (hp : Valid p) (hy : Valid y) (f : ℝ → ℝ) {C : ℝ≥0}
    (hf : LipschitzOnWith C f (Set.Icc (0 : ℝ) 1)) :
    |∑ t, f (p t) * (y t - p t)| ≤
      (leastLip f + unitSupNorm f) * calDist p y :=
  witness_comparison_least hp hy f ⟨C, unitLipschitz_of_lipschitzOnWith hf⟩

end

end CalibrationDistance
