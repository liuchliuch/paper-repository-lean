import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic.Linarith

/-! Source-semantic definitions for Definition 2.1. Parameter values, rather than
points in the image of a probe, are counted. Counts take values in `ℝ≥0∞`. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace Paper35

/-- Strict opposite signs on the two punctured sides of a parameter value. -/
def SignChanges (f : ℝ → ℝ) (s : ℝ) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧
    ((∀ t ∈ Ioo (s - δ) s, f t < 0) ∧
      (∀ t ∈ Ioo s (s + δ), 0 < f t) ∨
     (∀ t ∈ Ioo (s - δ) s, 0 < f t) ∧
      (∀ t ∈ Ioo s (s + δ), f t < 0))

/-- Exactly two candidates attain the maximum, and their difference changes sign.
No differentiability assumption is inserted in the definition. -/
def ActiveSwitch {K : ℕ} (f : Fin K → ℝ → ℝ) (L s : ℝ) : Prop :=
  0 < s ∧ s < L ∧ ∃ i j : Fin K, i ≠ j ∧ f i s = f j s ∧
    (∀ k, k ≠ i → k ≠ j → f k s < f i s) ∧
    SignChanges (fun t => f i t - f j t) s

def switchSet {K : ℕ} (f : Fin K → ℝ → ℝ) (L : ℝ) : Set ℝ :=
  {s | ActiveSwitch f L s}

def switchCount {K : ℕ} (f : Fin K → ℝ → ℝ) (L : ℝ) : ℝ≥0∞ :=
  (switchSet f L).encard

def switchDensity {K : ℕ} (f : Fin K → ℝ → ℝ) (L : ℝ) : ℝ≥0∞ :=
  switchCount f L / ENNReal.ofReal L

/-- The random switch count is integrated as a nonnegative extended variable. -/
def expectedSwitchCount {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (μ : Measure Ω) (f : Ω → Fin K → ℝ → ℝ) (L : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, switchCount (f ω) L ∂μ

/-- Affine candidate scores along the original parameterization of a path. -/
def affineScores {d K : ℕ} (W : Fin K → Fin d → ℝ) (β : Fin K → ℝ)
    (γ : ℝ → Fin d → ℝ) : Fin K → ℝ → ℝ :=
  fun j s => (∑ a : Fin d, W j a * γ s a) + β j

theorem activeSwitch_interior {K : ℕ} {f : Fin K → ℝ → ℝ} {L s : ℝ}
    (h : ActiveSwitch f L s) : s ∈ Ioo 0 L := ⟨h.1, h.2.1⟩

theorem switchSet_subset_interior {K : ℕ} (f : Fin K → ℝ → ℝ) (L : ℝ) :
    switchSet f L ⊆ Ioo 0 L := fun _ h => activeSwitch_interior h

theorem no_switch_rank_one (f : Fin 1 → ℝ → ℝ) (L s : ℝ) :
    ¬ ActiveSwitch f L s := by
  rintro ⟨_, _, i, j, hij, _⟩
  exact hij (Subsingleton.elim i j)

theorem switchCount_rank_one (f : Fin 1 → ℝ → ℝ) (L : ℝ) :
    switchCount f L = 0 := by
  have : switchSet f L = ∅ := Set.eq_empty_iff_forall_notMem.mpr
    (fun s => no_switch_rank_one f L s)
  simp [switchCount, this]

theorem no_switch_nonpositive_length {K : ℕ} (f : Fin K → ℝ → ℝ)
    {L : ℝ} (hL : L ≤ 0) (s : ℝ) : ¬ ActiveSwitch f L s := by
  intro h
  have := h.1
  have := h.2.1
  linarith

theorem switchCount_nonpositive_length {K : ℕ} (f : Fin K → ℝ → ℝ)
    {L : ℝ} (hL : L ≤ 0) : switchCount f L = 0 := by
  have : switchSet f L = ∅ := Set.eq_empty_iff_forall_notMem.mpr
    (fun s => no_switch_nonpositive_length f hL s)
  simp [switchCount, this]

theorem signChanges_neg {f : ℝ → ℝ} {s : ℝ} :
    SignChanges (fun t => -f t) s ↔ SignChanges f s := by
  constructor <;> rintro ⟨δ, hδ, h⟩ <;> refine ⟨δ, hδ, ?_⟩
  · rcases h with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact Or.inr ⟨fun t ht => by simpa using hl t ht,
        fun t ht => by simpa using hr t ht⟩
    · exact Or.inl ⟨fun t ht => by simpa using hl t ht,
        fun t ht => by simpa using hr t ht⟩
  · rcases h with ⟨hl, hr⟩ | ⟨hl, hr⟩
    · exact Or.inr ⟨fun t ht => by simpa using hl t ht,
        fun t ht => by simpa using hr t ht⟩
    · exact Or.inl ⟨fun t ht => by simpa using hl t ht,
        fun t ht => by simpa using hr t ht⟩

theorem signChanges_zero (s : ℝ) : ¬ SignChanges (fun _ => 0) s := by
  rintro ⟨δ, hδ, h⟩
  have ht : s - δ / 2 ∈ Ioo (s - δ) s := by constructor <;> linarith
  rcases h with ⟨hl, _⟩ | ⟨hl, _⟩ <;> have := hl _ ht <;> linarith

theorem no_switch_constant {K : ℕ} (v : Fin K → ℝ) (L s : ℝ) :
    ¬ ActiveSwitch (fun i _ => v i) L s := by
  rintro ⟨_, _, i, j, _, hij, _, hsign⟩
  have hz : (fun _ : ℝ => v i - v j) = (fun _ => 0) := by
    funext t
    exact sub_eq_zero.mpr hij
  rw [hz] at hsign
  exact signChanges_zero s hsign

/-- Visibility explicitly excludes a third candidate strictly above the pair. -/
theorem inactive_pair_not_switch_witness {K : ℕ} {f : Fin K → ℝ → ℝ}
    {s : ℝ} {i j k : Fin K} (hki : k ≠ i) (hkj : k ≠ j)
    (h : f i s < f k s) :
    ¬ (∀ a, a ≠ i → a ≠ j → f a s < f i s) := by
  intro hvis
  exact (lt_asymm h) (hvis k hki hkj)

end Paper35
