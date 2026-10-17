import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import MEJF.OrderStatistics

/-!
# Finite interval efficiency statements

This file treats the actual finite order statistics of the prediction and score
arrays. All ranks are zero based; rank `k` is paper rank `k + 1`. In particular
`k.rev` is paper rank `m + 1 - ℓ` when `k` is paper rank `ℓ`.
-/

namespace MEJF.Efficiency

open Finset Set
open MEJF.OrderStatistics

noncomputable section

/-- The finite endpoint-quantile interval, with ties counted by `stat`. -/
def endpointInterval {m : ℕ} (p S : Fin (m+1) → ℝ) (k : Fin (m+1)) : Set ℝ :=
  Set.Icc (stat (fun i => p i - S i) k) (stat (fun i => p i + S i) k.rev)

/-- The finite jackknife-minmax envelope. `d` is its score-quantile index. -/
def minmaxInterval {m : ℕ} (p Sα : Fin (m+1) → ℝ) (d : Fin (m+1)) : Set ℝ :=
  Set.Icc (stat p 0 - stat Sα d) (stat p (Fin.last m) + stat Sα d)

/-- Proposition 7.3. Its only numerical premises are the paper's two prediction
 gaps. The necessary endpoint inequalities are proved using monotonicity of the
 actual order statistics, rather than assumed as replacement hypotheses. -/
theorem strict_containment {m : ℕ} (p Sa Sα : Fin (m+1) → ℝ)
    (k d : Fin (m+1))
    (_hne : (endpointInterval p Sa k).Nonempty)
    (hlo : stat Sa (Fin.last m) - stat Sα d < stat p k - stat p 0)
    (hhi : stat Sa (Fin.last m) - stat Sα d <
      stat p (Fin.last m) - stat p k.rev) :
    endpointInterval p Sa k ⊆ interior (minmaxInterval p Sα d) := by
  have hS (i : Fin (m+1)) : Sa i ≤ stat Sa (Fin.last m) := le_stat_last Sa i
  have hleft : stat p k - stat Sa (Fin.last m) ≤ stat (fun i => p i-Sa i) k := by
    rw [← stat_sub_const]
    exact stat_mono (fun i => sub_le_sub_left (hS i) (p i)) k
  have hright : stat (fun i => p i+Sa i) k.rev ≤
      stat p k.rev + stat Sa (Fin.last m) := by
    rw [← stat_add_const]
    exact stat_mono (fun i => add_le_add_left (hS i) (p i)) k.rev
  have hstrictL : stat p 0-stat Sα d < stat (fun i => p i-Sa i) k := by linarith
  have hstrictU : stat (fun i => p i+Sa i) k.rev <
      stat p (Fin.last m)+stat Sα d := by linarith
  rw [minmaxInterval, interior_Icc]
  exact Set.Icc_subset_Ioo hstrictL hstrictU

/-- The sorted prediction multiset at the exceptional coordinate in (7.6).
It has exactly one `-K`, seventeen zeros, and one `K`. -/
def predictions19 (K : ℝ) (i : Fin 19) : ℝ :=
  if i = 0 then -K else if i = 18 then K else 0

/-- The paper's cyclic pairwise prediction table, equation (7.6). -/
def cyclicPrediction20 (K : ℝ) (u v : ZMod 20) : ℝ :=
  if v-u = 1 then -K else if v-u = -1 then K else 0

/-- Enumerate exactly the nineteen calibration types other than `u`, in cyclic
order starting at `u+1`. -/
def otherType20 (u : ZMod 20) (i : Fin 19) : ZMod 20 := u + ((i.val+1 : ℕ) : ZMod 20)

lemma otherType20_ne (u : ZMod 20) (i : Fin 19) : otherType20 u i ≠ u := by
  intro h
  have hc : ((i.val+1 : ℕ) : ZMod 20) = 0 := by
    have := congrArg (fun v => v-u) h
    simpa [otherType20] using this
  have hv := congrArg ZMod.val hc
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : i.val+1 < 20)] at hv
  norm_num at hv

lemma otherType20_injective (u : ZMod 20) : Function.Injective (otherType20 u) := by
  intro i j hij
  have hc : ((i.val+1 : ℕ) : ZMod 20) = ((j.val+1 : ℕ) : ZMod 20) := add_left_cancel hij
  have hv := congrArg ZMod.val hc
  rw [ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (by omega : i.val+1 < 20),
    Nat.mod_eq_of_lt (by omega : j.val+1 < 20)] at hv
  exact Fin.ext (by omega)

lemma otherType20_surjective (u v : ZMod 20) (hv : v ≠ u) :
    ∃ i : Fin 19, otherType20 u i = v := by
  have hd : v-u ≠ 0 := sub_ne_zero.mpr hv
  have hdpos : 0 < (v-u).val := ZMod.val_pos.mpr hd
  have hdlt : (v-u).val < 20 := ZMod.val_lt _
  let i : Fin 19 := ⟨(v-u).val-1, by omega⟩
  refine ⟨i, ?_⟩
  have he : i.val+1 = (v-u).val := by dsimp [i]; omega
  simp only [otherType20, he, ZMod.natCast_zmod_val]
  ring

/-- This is a bijective enumeration of the calibration types. -/
def otherType20Equiv (u : ZMod 20) : Fin 19 ≃ {v : ZMod 20 // v ≠ u} :=
  Equiv.ofBijective (fun i => ⟨otherType20 u i, otherType20_ne u i⟩) (by
    constructor
    · intro i j hij
      exact otherType20_injective u (congrArg Subtype.val hij)
    · intro v
      obtain ⟨i, hi⟩ := otherType20_surjective u v.val v.property
      exact ⟨i, Subtype.ext hi⟩)

/-- The row of the actual cyclic table is exactly the finite sorted tuple used
in the quantile computation; no row-shape hypothesis is required. -/
theorem cyclicPrediction20_row (K : ℝ) (u : ZMod 20) (i : Fin 19) :
    cyclicPrediction20 K u (otherType20 u i) = predictions19 K i := by
  have hd : otherType20 u i-u = ((i.val+1 : ℕ) : ZMod 20) := by simp [otherType20]
  unfold cyclicPrediction20
  rw [hd]
  have h₁ : (((i.val+1 : ℕ) : ZMod 20) = 1) ↔ i = 0 := by
    change (((i.val+1 : ℕ) : ZMod 20) = ((1 : ℕ) : ZMod 20)) ↔ i = 0
    rw [ZMod.natCast_eq_natCast_iff']
    rw [Nat.mod_eq_of_lt (by omega : i.val+1 < 20)]
    change i.val+1 = 1 ↔ i = 0
    constructor
    · intro h
      exact Fin.ext (by omega)
    · intro h
      subst i
      rfl
  have h₂ : (((i.val+1 : ℕ) : ZMod 20) = -1) ↔ i = 18 := by
    rw [show (-1 : ZMod 20) = ((19 : ℕ) : ZMod 20) by decide,
      ZMod.natCast_eq_natCast_iff']
    rw [Nat.mod_eq_of_lt (by omega : i.val+1 < 20)]
    change i.val+1 = 19 ↔ i = 18
    constructor
    · intro h
      exact Fin.ext (by change i.val = 18; omega)
    · intro h
      subst i
      rfl
  simp only [h₁, h₂, predictions19]

lemma predictions19_monotone {K : ℝ} (hK : 0 ≤ K) : Monotone (predictions19 K) := by
  intro i j hij
  unfold predictions19
  split_ifs <;> first | linarith | omega

/-- A calibration block has eighteen ordinary residuals equal to one; the
exceptional residual is allowed to be any nonnegative real. -/
def residuals19 (z : ℝ) (j : Fin 19) : ℝ := if j = 0 then |z| else 1

lemma residuals19_middle (z : ℝ) (k : Fin 19) (hk₁ : 1 ≤ k.val) (hk₂ : k.val < 18) :
    stat (residuals19 z) k = 1 := by
  classical
  apply le_antisymm
  · apply (stat_le_iff_count _ _ _).mpr
    have hc : 18 ≤ count (residuals19 z) (· ≤ (1 : ℝ)) := by
      have hsub : (Finset.univ.erase (0 : Fin 19)) ⊆
          Finset.univ.filter (fun j => residuals19 z j ≤ (1 : ℝ)) := by
        intro j hj
        simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hj
        simp [residuals19, hj]
      have hh := Finset.card_mono hsub
      simpa [count] using hh
    omega
  · by_contra hn
    have hs : stat (residuals19 z) k < 1 := lt_of_not_ge hn
    have hc := count_le_self_stat (residuals19 z) k
    have hsub : Finset.univ.filter (fun j => residuals19 z j ≤ stat (residuals19 z) k) ⊆
        {(0 : Fin 19)} := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      by_contra hj0
      have hj0' : j ≠ 0 := by simpa using hj0
      simp only [residuals19, if_neg hj0'] at hj
      linarith
    have hcard := Finset.card_mono hsub
    simp only [Finset.card_singleton] at hcard
    change count (residuals19 z) (· ≤ stat (residuals19 z) k) ≤ 1 at hcard
    omega

/-- The paper's two inner quantiles (paper ranks 18 and 16) are exactly one. -/
theorem inner_scores19 (z : ℝ) :
    stat (residuals19 z) (⟨17, by omega⟩ : Fin 19) = 1 ∧
    stat (residuals19 z) (⟨15, by omega⟩ : Fin 19) = 1 := by
  constructor <;> apply residuals19_middle <;> norm_num

/-- Actual endpoint quantiles discard the two tails of the prediction array. -/
theorem endpoint_interval19 {K : ℝ} (hK : 0 < K) :
    endpointInterval (predictions19 K) (fun _ => 1) (⟨1, by omega⟩ : Fin 19) =
      Set.Icc (-1) 1 := by
  have hp := predictions19_monotone (le_of_lt hK)
  simp only [endpointInterval, stat_sub_const, stat_add_const,
    stat_of_monotone _ hp]
  congr 1 <;> norm_num [predictions19, Fin.rev, Fin.ext_iff]

/-- The genuine score quantile and the extrema give the long minmax envelope. -/
theorem minmax_interval19 {K : ℝ} (hK : 0 < K) (d : Fin 19) :
    minmaxInterval (predictions19 K) (fun _ => 1) d = Set.Icc (-K-1) (K+1) := by
  have hp := predictions19_monotone (le_of_lt hK)
  simp [minmaxInterval, stat_of_monotone _ hp, predictions19]

/-- At the other eighteen coordinates both order-statistic rules return [0,2]. -/
theorem ordinary_coordinate19 (k d : Fin 19) :
    endpointInterval (fun _ : Fin 19 => (1 : ℝ)) (fun _ => 1) k = Set.Icc 0 2 ∧
    minmaxInterval (fun _ : Fin 19 => (1 : ℝ)) (fun _ => 1) d = Set.Icc 0 2 := by
  norm_num [endpointInterval, minmaxInterval]

/-- Lebesgue length of a bounded closed real interval, including a crossed pair. -/
def intervalLength (lower upper : ℝ) : ℝ := max (upper - lower) 0

@[simp] theorem intervalLength_eq {l u : ℝ} (h : l ≤ u) :
    intervalLength l u = u - l := max_eq_left (sub_nonneg.mpr h)

@[simp] theorem intervalLength_nonneg (l u : ℝ) : 0 ≤ intervalLength l u :=
  le_max_right _ _

/-- The length definition agrees with one-dimensional Lebesgue measure. -/
theorem intervalLength_volume (l u : ℝ) :
    ENNReal.ofReal (intervalLength l u) = MeasureTheory.volume (Set.Icc l u) := by
  rw [Real.volume_Icc]
  simp [intervalLength]

/-- Endpoint movement by `ξ` changes interval length by at most `2ξ`, even if
one of the intervals has crossed endpoints. -/
theorem intervalLength_perturb {l u l₀ u₀ ξ : ℝ}
    (hl : |l - l₀| ≤ ξ) (hu : |u - u₀| ≤ ξ) :
    |intervalLength l u - intervalLength l₀ u₀| ≤ 2 * ξ := by
  apply (abs_max_sub_max_le_abs (u - l) (u₀ - l₀) 0).trans
  calc
    |(u - l) - (u₀ - l₀)| = |(u - u₀) - (l - l₀)| := by congr 1 <;> ring
    _ ≤ |u - u₀| + |l - l₀| := by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le (u-u₀) 0 (l-l₀)
    _ ≤ 2 * ξ := by linarith

/-- Scores are computed from residuals; response perturbations pass through
absolute values and their finite quantile without amplification. -/
theorem score_lipschitz {n : ℕ} (p y y₀ : Fin n → ℝ) (k : Fin n) (ξ : ℝ)
    (hy : ∀ j, |y j-y₀ j| ≤ ξ) :
    |stat (fun j => |y j-p j|) k - stat (fun j => |y₀ j-p j|) k| ≤ ξ := by
  apply stat_lipschitz
  intro j
  calc
    abs (abs (y j-p j) - abs (y₀ j-p j)) ≤ |(y j-p j)-(y₀ j-p j)| := abs_abs_sub_abs_le_abs_sub _ _
    _ = |y j-y₀ j| := by congr 1 <;> ring
    _ ≤ ξ := hy j

/-- Length of the actual finite endpoint-quantile rule. -/
def endpointLength {m : ℕ} (p S : Fin (m+1) → ℝ) (k : Fin (m+1)) : ℝ :=
  intervalLength (stat (fun i => p i-S i) k) (stat (fun i => p i+S i) k.rev)

/-- Length of the actual finite minmax rule. -/
def minmaxLength {m : ℕ} (p Sα : Fin (m+1) → ℝ) (d : Fin (m+1)) : ℝ :=
  intervalLength (stat p 0-stat Sα d) (stat p (Fin.last m)+stat Sα d)

theorem endpointLength_lipschitz {m : ℕ} (p S S₀ : Fin (m+1) → ℝ)
    (k : Fin (m+1)) (ξ : ℝ) (hS : ∀ i, |S i-S₀ i| ≤ ξ) :
    |endpointLength p S k-endpointLength p S₀ k| ≤ 2*ξ := by
  apply intervalLength_perturb
  · apply stat_lipschitz
    intro i
    have heq : (p i-S i)-(p i-S₀ i) = -(S i-S₀ i) := by ring
    simpa only [heq, abs_neg] using hS i
  · apply stat_lipschitz
    intro i
    have heq : (p i+S i)-(p i+S₀ i) = S i-S₀ i := by ring
    simpa only [heq] using hS i

theorem minmaxLength_lipschitz {m : ℕ} (p S S₀ : Fin (m+1) → ℝ)
    (d : Fin (m+1)) (ξ : ℝ) (hS : ∀ i, |S i-S₀ i| ≤ ξ) :
    |minmaxLength p S d-minmaxLength p S₀ d| ≤ 2*ξ := by
  have hQ := stat_lipschitz S S₀ d ξ hS
  apply intervalLength_perturb
  · have heq : (stat p 0-stat S d)-(stat p 0-stat S₀ d) = -(stat S d-stat S₀ d) := by ring
    simpa only [heq, abs_neg] using hQ
  · have heq : (stat p (Fin.last m)+stat S d)-(stat p (Fin.last m)+stat S₀ d) =
        stat S d-stat S₀ d := by ring
    simpa only [heq] using hQ

/-- Pathwise average over the 19 coordinates in Proposition 7.2. -/
def average19 (f : Fin 19 → ℝ) : ℝ := (∑ j, f j) / 19

theorem average19_mono {f g : Fin 19 → ℝ} (h : ∀ j, f j ≤ g j) :
    average19 f ≤ average19 g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ => h j) (by norm_num)

@[simp] theorem average19_const (c : ℝ) : average19 (fun _ => c) = c := by
  simp [average19]

theorem average19_sub (f g : Fin 19 → ℝ) :
    average19 (fun j => f j - g j) = average19 f - average19 g := by
  simp [average19, Finset.sum_sub_distrib, sub_div]

/-- The single long coordinate and the 18 ordinary coordinates of the paper. -/
def baseMinmaxLength (K : ℝ) (j : Fin 19) : ℝ := if j = 0 then 2 * K + 2 else 2

theorem baseMinmaxLength_sum (K : ℝ) :
    (∑ j, baseMinmaxLength K j) = 2 * K + 38 := by
  classical
  rw [Fin.sum_univ_succ]
  simp [baseMinmaxLength]
  ring

@[simp] theorem baseMinmaxLength_average (K : ℝ) :
    average19 (baseMinmaxLength K) = (2 * K + 38) / 19 := by
  rw [average19, baseMinmaxLength_sum]

/-- Arithmetic part of (7.2)--(7.3), stated for the actual finite interval lengths. -/
theorem zero_response_lengths (K : ℝ) (hK : 0 < K) :
    average19 (fun _ => intervalLength (-1) 1) = 2 ∧
    average19 (fun j : Fin 19 =>
      if j = 0 then intervalLength (-K-1) (K+1) else intervalLength 0 2) =
      (2*K+38)/19 ∧
    average19 (fun j : Fin 19 =>
      (if j = 0 then intervalLength (-K-1) (K+1) else intervalLength 0 2) -
      intervalLength (-1) 1) = 2*K/19 := by
  have hlong : intervalLength (-K-1) (K+1) = 2*K+2 := by
    rw [intervalLength_eq (by linarith)]
    ring
  have hshort : intervalLength (-1) 1 = 2 := by norm_num [intervalLength]
  have hother : intervalLength 0 2 = 2 := by norm_num [intervalLength]
  simp only [hlong, hshort, hother]
  change average19 (fun _ => (2 : ℝ)) = 2 ∧
    average19 (baseMinmaxLength K) = (2*K+38)/19 ∧
    average19 (fun j => baseMinmaxLength K j - 2) = 2*K/19
  rw [average19_const, baseMinmaxLength_average, average19_sub,
    baseMinmaxLength_average, average19_const]
  constructor
  · rfl
  constructor
  · rfl
  · ring

/-- Coordinate-wise prediction tuples of the explicit finite construction. -/
def coordinatePredictions19 (K : ℝ) (j i : Fin 19) : ℝ :=
  if j = 0 then predictions19 K i else 1

/-- The actual inner quantiles of the construction, with arbitrary exceptional
calibration predictions `z i`. -/
def scores19 (z : Fin 19 → ℝ) (k : Fin 19) (i : Fin 19) : ℝ :=
  stat (residuals19 (z i)) k

lemma scores19_eq_one (z : Fin 19 → ℝ) (k : Fin 19)
    (hk₁ : 1 ≤ k.val) (hk₂ : k.val < 18) : scores19 z k = fun _ => 1 := by
  funext i
  exact residuals19_middle (z i) k hk₁ hk₂

lemma endpointLength19 {K : ℝ} (hK : 0 < K) (j : Fin 19) :
    endpointLength (coordinatePredictions19 K j) (fun _ => 1) (⟨1, by omega⟩ : Fin 19) = 2 := by
  have hp := predictions19_monotone (le_of_lt hK)
  by_cases hj : j = 0
  · subst j
    change endpointLength (predictions19 K) (fun _ => 1) (⟨1, by omega⟩ : Fin 19) = 2
    unfold endpointLength
    rw [stat_sub_const, stat_add_const, stat_of_monotone _ hp, stat_of_monotone _ hp]
    norm_num [predictions19, Fin.rev, Fin.ext_iff, intervalLength]
  · have hpj : coordinatePredictions19 K j = fun _ => 1 := by
      funext i
      simp [coordinatePredictions19, hj]
    rw [hpj]
    norm_num [endpointLength, intervalLength]

lemma minmaxLength19 {K : ℝ} (hK : 0 < K) (j : Fin 19) (d : Fin 19) :
    minmaxLength (coordinatePredictions19 K j) (fun _ => 1) d = baseMinmaxLength K j := by
  have hp := predictions19_monotone (le_of_lt hK)
  by_cases hj : j = 0
  · subst j
    change minmaxLength (predictions19 K) (fun _ => 1) d = 2*K+2
    unfold minmaxLength
    rw [stat_const, stat_of_monotone _ hp, stat_of_monotone _ hp]
    norm_num [predictions19, Fin.ext_iff, Fin.last]
    rw [intervalLength_eq (by linarith)]
    ring
  · have hpj : coordinatePredictions19 K j = fun _ => 1 := by
      funext i
      simp [coordinatePredictions19, hj]
    rw [hpj]
    norm_num [minmaxLength, baseMinmaxLength, hj, intervalLength]

/-- Equations (7.2)--(7.3) from actual residual and outer endpoint order statistics.
The exceptional calibration prediction can be any real, so in particular each
of the cyclic table's `-K`, `0`, and `K` cases is covered. -/
theorem finite_construction19 {K : ℝ} (hK : 0 < K) (z : Fin 19 → ℝ) (d : Fin 19) :
    let Sa := scores19 z (⟨17, by omega⟩ : Fin 19)
    let Sα := scores19 z (⟨15, by omega⟩ : Fin 19)
    let ep := fun j => endpointLength (coordinatePredictions19 K j) Sa (⟨1, by omega⟩ : Fin 19)
    let mm := fun j => minmaxLength (coordinatePredictions19 K j) Sα d
    average19 ep = 2 ∧ average19 mm = (2*K+38)/19 ∧
    average19 (fun j => mm j-ep j) = 2*K/19 ∧
    average19 ep / average19 mm = 38/(2*K+38) := by
  dsimp only
  rw [scores19_eq_one z ⟨17, by omega⟩ (by norm_num) (by norm_num),
    scores19_eq_one z ⟨15, by omega⟩ (by norm_num) (by norm_num)]
  simp only [endpointLength19 hK, minmaxLength19 hK, average19_const,
    baseMinmaxLength_average, average19_sub]
  refine ⟨trivial, trivial, ?_, ?_⟩
  · ring
  · have hd : 2*K+38 ≠ 0 := by linarith
    field_simp [hd]
    <;> ring

/-- Calibration predictions at all nineteen coordinates. -/
def calibrationPredictions19 (z : Fin 19 → ℝ) (i j : Fin 19) : ℝ :=
  if j = 0 then z i else 1

/-- Quantiles are recomputed from perturbed responses, rather than postulated
as perturbed endpoint arrays. -/
def responseScores19 (z : Fin 19 → ℝ) (Y : Fin 19 → Fin 19 → ℝ)
    (k : Fin 19) (i : Fin 19) : ℝ :=
  stat (fun j => |Y i j-calibrationPredictions19 z i j|) k

lemma responseScores19_zero (z : Fin 19 → ℝ) (k : Fin 19) :
    responseScores19 z (fun _ _ => 0) k = scores19 z k := by
  funext i
  unfold responseScores19 scores19
  congr 1
  funext j
  by_cases hj : j = 0 <;>
    simp [residuals19, calibrationPredictions19, hj]

lemma responseScores19_bound (z : Fin 19 → ℝ) (Y : Fin 19 → Fin 19 → ℝ)
    (k : Fin 19) (hk₁ : 1 ≤ k.val) (hk₂ : k.val < 18) (ξ : ℝ)
    (hY : ∀ i j, |Y i j| ≤ ξ) (i : Fin 19) : |responseScores19 z Y k i-1| ≤ ξ := by
  have h := score_lipschitz (calibrationPredictions19 z i) (Y i) (fun _ => 0) k ξ
    (fun j => by simpa using hY i j)
  change |responseScores19 z Y k i-responseScores19 z (fun _ _ => 0) k i| ≤ ξ at h
  rw [responseScores19_zero, scores19_eq_one z k hk₁ hk₂] at h
  exact h

/-- The bounded perturbation estimates (7.4)--(7.5) are pathwise finite-sum
statements: every interval may move in both endpoints. -/
theorem noisy_length_bounds {K ξ : ℝ} (hK : 0 < K) (hξ : 0 ≤ ξ)
    (hsmall : ξ < K / 38)
    (ep mm : Fin 19 → ℝ)
    (hep : ∀ j, |ep j - 2| ≤ 2*ξ)
    (hmm : ∀ j, |mm j - baseMinmaxLength K j| ≤ 2*ξ) :
    (2*K-76*ξ)/19 ≤ average19 (fun j => mm j - ep j) ∧
    0 < (2*K-76*ξ)/19 ∧
    average19 ep ≤ 2+2*ξ ∧
    (2*K+38-38*ξ)/19 ≤ average19 mm ∧
    average19 ep / average19 mm ≤ 38*(1+ξ)/(2*K+38-38*ξ) := by
  have heup : average19 ep ≤ 2+2*ξ := by
    calc
      _ ≤ average19 (fun _ => 2+2*ξ) := average19_mono fun j => by
        have := (abs_le.mp (hep j)).2
        linarith
      _ = _ := average19_const _
  have hmlow : (2*K+38-38*ξ)/19 ≤ average19 mm := by
    have hh : average19 (fun j => baseMinmaxLength K j - 2*ξ) ≤ average19 mm :=
      average19_mono fun j => by
        have := (abs_le.mp (hmm j)).1
        linarith
    rw [average19_sub, baseMinmaxLength_average, average19_const] at hh
    linarith
  have hd : 0 < 2*K+38-38*ξ := by linarith
  have hmpos : 0 < average19 mm := lt_of_lt_of_le (div_pos hd (by norm_num)) hmlow
  have havg : (2*K-76*ξ)/19 ≤ average19 (fun j => mm j - ep j) := by
    rw [average19_sub]
    linarith
  refine ⟨havg, ?_, heup, hmlow, ?_⟩
  · apply div_pos _ (by norm_num)
    linarith
  · calc
      average19 ep / average19 mm ≤ (2+2*ξ) / average19 mm :=
        div_le_div_of_nonneg_right heup (le_of_lt hmpos)
      _ ≤ (2+2*ξ) / ((2*K+38-38*ξ)/19) :=
        div_le_div_of_nonneg_left (by linarith) (div_pos hd (by norm_num)) hmlow
      _ = 38*(1+ξ)/(2*K+38-38*ξ) := by field_simp; ring

/-- The pathwise inequalities in Proposition 7.2 for arbitrary bounded response
noise, proved all the way from residuals through both levels of order statistics. -/
theorem finite_noisy_construction19 {K ξ : ℝ} (hK : 0 < K) (hξ : 0 ≤ ξ)
    (hsmall : ξ < K/38) (z : Fin 19 → ℝ) (Y : Fin 19 → Fin 19 → ℝ)
    (hY : ∀ i j, |Y i j| ≤ ξ) (d : Fin 19) :
    let Sa := responseScores19 z Y (⟨17, by omega⟩ : Fin 19)
    let Sα := responseScores19 z Y (⟨15, by omega⟩ : Fin 19)
    let ep := fun j => endpointLength (coordinatePredictions19 K j) Sa (⟨1, by omega⟩ : Fin 19)
    let mm := fun j => minmaxLength (coordinatePredictions19 K j) Sα d
    (2*K-76*ξ)/19 ≤ average19 (fun j => mm j-ep j) ∧
    0 < (2*K-76*ξ)/19 ∧ average19 ep ≤ 2+2*ξ ∧
    (2*K+38-38*ξ)/19 ≤ average19 mm ∧
    average19 ep / average19 mm ≤ 38*(1+ξ)/(2*K+38-38*ξ) := by
  dsimp only
  apply noisy_length_bounds hK hξ hsmall
  · intro j
    have h := endpointLength_lipschitz (coordinatePredictions19 K j)
      (responseScores19 z Y ⟨17, by omega⟩) (fun _ => 1) ⟨1, by omega⟩ ξ
      (responseScores19_bound z Y ⟨17, by omega⟩ (by norm_num) (by norm_num) ξ hY)
    rwa [endpointLength19 hK] at h
  · intro j
    have h := minmaxLength_lipschitz (coordinatePredictions19 K j)
      (responseScores19 z Y ⟨15, by omega⟩) (fun _ => 1) d ξ
      (responseScores19_bound z Y ⟨15, by omega⟩ (by norm_num) (by norm_num) ξ hY)
    rwa [minmaxLength19 hK] at h

/-- Both the noiseless ratio (ξ = 0) and the fixed-noise bound tend to zero. -/
theorem length_ratio_tendsto_zero (ξ : ℝ) :
    Filter.Tendsto (fun K : ℝ => 38*(1+ξ)/(2*K+38-38*ξ))
      Filter.atTop (nhds 0) := by
  apply Filter.Tendsto.const_div_atTop
  have hmul : Filter.Tendsto (fun K : ℝ => 2*K) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) Filter.tendsto_id
  have hadd := Filter.tendsto_atTop_add_const_right Filter.atTop (38-38*ξ) hmul
  convert hadd using 1 <;> ext K <;> ring

end
end MEJF.Efficiency
