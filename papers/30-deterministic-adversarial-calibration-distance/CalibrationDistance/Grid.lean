import CalibrationDistance.Core
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace CalibrationDistance

noncomputable section

/-- The equally spaced grid used in (6.1). -/
def gridPoint (m j : ℕ) : ℝ := (j : ℝ) / m

@[simp] theorem gridPoint_zero (m : ℕ) : gridPoint m 0 = 0 := by
  simp [gridPoint]

@[simp] theorem gridPoint_last {m : ℕ} (hm : 0 < m) : gridPoint m m = 1 := by
  simp [gridPoint, ne_of_gt hm]

theorem gridPoint_mem {m j : ℕ} (hm : 0 < m) (hj : j ≤ m) :
    0 ≤ gridPoint m j ∧ gridPoint m j ≤ 1 := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hmr)
  · apply (div_le_one hmr).2
    exact_mod_cast hj

/-- A state stores the actual unshifted proxy residuals.  The remaining fields
are the inductive certificates proved by `gridStep`, not assumptions on play. -/
structure GridState (m : ℕ) where
  bias : ℕ → ℝ
  bias_lower : ∀ j, j ≤ m → -(1 / 2 : ℝ) ≤ bias j
  bias_upper : ∀ j, j ≤ m → bias j ≤ (1 / 2 : ℝ)
  zero_bias : bias 0 = 0
  last_bias : bias m = 0

/-- Shift (6.1). -/
def shiftedBias {m : ℕ} (s : GridState m) (j : ℕ) : ℝ :=
  s.bias j + gridPoint m j - 1 / 2

noncomputable def firstNonnegative {m : ℕ} (hm : 0 < m) (s : GridState m) : ℕ :=
  Nat.find (show ∃ j, j ≤ m ∧ 0 ≤ shiftedBias s j from
    ⟨m, le_refl _, by simp [shiftedBias, s.last_bias, gridPoint_last hm]; norm_num⟩)

theorem firstNonnegative_spec {m : ℕ} (hm : 0 < m) (s : GridState m) :
    firstNonnegative hm s ≤ m ∧ 0 ≤ shiftedBias s (firstNonnegative hm s) := by
  unfold firstNonnegative
  exact Nat.find_spec (p := fun j => j ≤ m ∧ 0 ≤ shiftedBias s j) _

theorem firstNonnegative_pos {m : ℕ} (hm : 0 < m) (s : GridState m) :
    0 < firstNonnegative hm s := by
  have h := (firstNonnegative_spec hm s).2
  by_contra hn
  have hz : firstNonnegative hm s = 0 := by omega
  rw [hz] at h
  simp [shiftedBias, s.zero_bias] at h
  norm_num at h

theorem firstNonnegative_min {m : ℕ} (hm : 0 < m) (s : GridState m)
    {k : ℕ} (hk : k < firstNonnegative hm s) : shiftedBias s k < 0 := by
  have hkm : k ≤ m := le_trans (le_of_lt hk) (firstNonnegative_spec hm s).1
  have hn : ¬(k ≤ m ∧ 0 ≤ shiftedBias s k) := Nat.find_min _ hk
  exact lt_of_not_ge (fun h => hn ⟨hkm, h⟩)

noncomputable def leftNeighbor {m : ℕ} (hm : 0 < m) (s : GridState m) : ℕ :=
  firstNonnegative hm s - 1

theorem leftNeighbor_succ {m : ℕ} (hm : 0 < m) (s : GridState m) :
    leftNeighbor hm s + 1 = firstNonnegative hm s := by
  have := firstNonnegative_pos hm s
  simp only [leftNeighbor]
  omega

theorem leftNeighbor_lt {m : ℕ} (hm : 0 < m) (s : GridState m) :
    leftNeighbor hm s < firstNonnegative hm s := by
  rw [← leftNeighbor_succ hm s]
  exact Nat.lt_succ_self _

theorem leftNeighbor_le {m : ℕ} (hm : 0 < m) (s : GridState m) :
    leftNeighbor hm s ≤ m :=
  le_trans (le_of_lt (leftNeighbor_lt hm s)) (firstNonnegative_spec hm s).1

def binaryValue (y : Bool) : ℝ := if y then 1 else 0

noncomputable def proxyIndex {m : ℕ} (hm : 0 < m) (s : GridState m) (y : Bool) : ℕ :=
  if y then firstNonnegative hm s else leftNeighbor hm s

/-- The announced midpoint (6.3) depends only on the current state. -/
noncomputable def gridForecast {m : ℕ} (hm : 0 < m) (s : GridState m) : ℝ :=
  (gridPoint m (leftNeighbor hm s) + gridPoint m (firstNonnegative hm s)) / 2

/-- The proxy is assigned after the outcome, as required by (6.4). -/
noncomputable def gridProxy {m : ℕ} (hm : 0 < m) (s : GridState m) (y : Bool) : ℝ :=
  gridPoint m (proxyIndex hm s y)

noncomputable def nextBias {m : ℕ} (hm : 0 < m) (s : GridState m) (y : Bool)
    (k : ℕ) : ℝ :=
  s.bias k + if k = proxyIndex hm s y then gridPoint m k - binaryValue y else 0

/-- One round preserves Lemma 6.1 and both zero endpoint residuals. -/
noncomputable def gridStep {m : ℕ} (hm : 0 < m) (s : GridState m) (y : Bool) :
    GridState m where
  bias := nextBias hm s y
  bias_lower := by
    intro k hk
    have hl := s.bias_lower k hk
    have hx := gridPoint_mem hm hk
    cases y with
    | false =>
      simp only [nextBias, proxyIndex, Bool.false_eq_true, ↓reduceIte, binaryValue]
      split_ifs <;> linarith
    | true =>
      simp only [nextBias, proxyIndex, ↓reduceIte, binaryValue]
      split_ifs with he
      · have hs := (firstNonnegative_spec hm s).2
        rw [← he] at hs
        unfold shiftedBias at hs
        linarith
      · simpa using hl
  bias_upper := by
    intro k hk
    have hu := s.bias_upper k hk
    have hx := gridPoint_mem hm hk
    cases y with
    | false =>
      simp only [nextBias, proxyIndex, Bool.false_eq_true, ↓reduceIte, binaryValue]
      split_ifs with he
      · have hs := firstNonnegative_min hm s (leftNeighbor_lt hm s)
        rw [← he] at hs
        unfold shiftedBias at hs
        linarith
      · simpa using hu
    | true =>
      simp only [nextBias, proxyIndex, ↓reduceIte, binaryValue]
      split_ifs <;> linarith
  zero_bias := by
    cases y with
    | false => simp [nextBias, proxyIndex, binaryValue, s.zero_bias]
    | true =>
      have hn : 0 ≠ firstNonnegative hm s := ne_of_lt (firstNonnegative_pos hm s)
      simp [nextBias, proxyIndex, binaryValue, s.zero_bias, hn]
  last_bias := by
    cases y with
    | false =>
      have hn : m ≠ leftNeighbor hm s := by
        have h := leftNeighbor_lt hm s
        have h' := (firstNonnegative_spec hm s).1
        omega
      simp [nextBias, proxyIndex, binaryValue, s.last_bias, hn]
    | true => simp [nextBias, proxyIndex, binaryValue, s.last_bias, gridPoint_last hm]

/-- Initial zero residual state. -/
def initialGridState (m : ℕ) : GridState m where
  bias := fun _ => 0
  bias_lower := by intros; norm_num
  bias_upper := by intros; norm_num
  zero_bias := rfl
  last_bias := rfl

/-- The deterministic recursion uses only outcomes strictly before the current round. -/
noncomputable def gridRun {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) : ℕ → GridState m
  | 0 => initialGridState m
  | t + 1 => gridStep hm (gridRun hm y t) (y t)

/-- Lemma 6.1, including the equivalent shifted formulation. -/
theorem shifted_bias_invariant {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t j : ℕ)
    (hj : j ≤ m) :
    -(1 / 2 : ℝ) ≤ (gridRun hm y t).bias j ∧
    (gridRun hm y t).bias j ≤ (1 / 2 : ℝ) ∧
    gridPoint m j - 1 ≤ shiftedBias (gridRun hm y t) j ∧
    shiftedBias (gridRun hm y t) j ≤ gridPoint m j := by
  have hl := (gridRun hm y t).bias_lower j hj
  have hu := (gridRun hm y t).bias_upper j hj
  unfold shiftedBias
  exact ⟨hl, hu, by linarith, by linarith⟩

theorem gridRun_bias_sum {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t k : ℕ) :
    (gridRun hm y t).bias k =
      ∑ s ∈ Finset.range t, if k = proxyIndex hm (gridRun hm y s) (y s)
        then gridPoint m k - binaryValue (y s) else 0 := by
  induction t with
  | zero => simp [gridRun, initialGridState]
  | succ t ih =>
    simp only [gridRun, gridStep, nextBias, Finset.sum_range_succ]
    exact congrArg (fun z => z + _) ih

theorem gridRun_nonanticipating {m : ℕ} (hm : 0 < m) (y z : ℕ → Bool) (t : ℕ)
    (h : ∀ s, s < t → y s = z s) : gridRun hm y t = gridRun hm z t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp only [gridRun]
    rw [ih (fun s hs => h s (by omega)), h t (by omega)]

theorem gridForecast_nonanticipating {m : ℕ} (hm : 0 < m) (y z : ℕ → Bool) (t : ℕ)
    (h : ∀ s, s < t → y s = z s) :
    gridForecast hm (gridRun hm y t) = gridForecast hm (gridRun hm z t) := by
  rw [gridRun_nonanticipating hm y z t h]


theorem gridPoint_injective {m : ℕ} (hm : 0 < m) : Function.Injective (gridPoint m) := by
  intro i j h
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  have h' : (i : ℝ) = j := (div_left_inj' hm0).mp h
  exact_mod_cast h'

theorem grid_gap {m : ℕ} (hm : 0 < m) (s : GridState m) :
    gridPoint m (firstNonnegative hm s) - gridPoint m (leftNeighbor hm s) = 1 / m := by
  have hc : (firstNonnegative hm s : ℝ) = (leftNeighbor hm s : ℝ) + 1 := by
    exact_mod_cast (leftNeighbor_succ hm s).symm
  unfold gridPoint
  rw [hc]
  ring

theorem gridForecast_mem {m : ℕ} (hm : 0 < m) (s : GridState m) :
    gridForecast hm s ∈ Set.Icc (0 : ℝ) 1 := by
  have hl := gridPoint_mem hm (leftNeighbor_le hm s)
  have hr := gridPoint_mem hm (firstNonnegative_spec hm s).1
  unfold gridForecast
  constructor <;> linarith

theorem gridProxy_mem {m : ℕ} (hm : 0 < m) (s : GridState m) (y : Bool) :
    gridProxy hm s y ∈ Set.Icc (0 : ℝ) 1 := by
  cases y with
  | false => exact gridPoint_mem hm (leftNeighbor_le hm s)
  | true => exact gridPoint_mem hm (firstNonnegative_spec hm s).1

theorem gridForecast_proxy_distance {m : ℕ} (hm : 0 < m) (s : GridState m) (y : Bool) :
    |gridForecast hm s - gridProxy hm s y| = 1 / (2 * (m : ℝ)) := by
  have hg := grid_gap hm s
  have hp : (0 : ℝ) < m := by exact_mod_cast hm
  have hd : (0 : ℝ) ≤ 1 / m := by positivity
  have he : (1 / (m : ℝ)) / 2 = 1 / (2 * (m : ℝ)) := by ring
  cases y with
  | false =>
    change |(gridPoint m (leftNeighbor hm s) + gridPoint m (firstNonnegative hm s)) / 2 -
      gridPoint m (leftNeighbor hm s)| = _
    rw [abs_of_nonneg (by linarith)]
    rw [← he]
    linarith
  | true =>
    change |(gridPoint m (leftNeighbor hm s) + gridPoint m (firstNonnegative hm s)) / 2 -
      gridPoint m (firstNonnegative hm s)| = _
    rw [abs_of_nonpos (by linarith)]
    rw [← he]
    linarith

theorem gridState_sum_abs_bias_le {m : ℕ} (hm : 0 < m) (s : GridState m) :
    (∑ j ∈ Finset.range (m + 1), |s.bias j|) ≤ ((m : ℝ) - 1) / 2 := by
  have hcast : (m - 1 : ℕ) + 1 = m := by omega
  have hb : ∀ j ∈ Finset.range (m - 1), |s.bias (j + 1)| ≤ (1 / 2 : ℝ) := by
    intro j hj
    have hle : j + 1 ≤ m := by have := Finset.mem_range.mp hj; omega
    exact abs_le.mpr ⟨s.bias_lower _ hle, s.bias_upper _ hle⟩
  rw [Finset.sum_range_succ, s.last_bias, abs_zero, add_zero]
  rw [show Finset.range m = Finset.range ((m - 1) + 1) from congrArg Finset.range hcast.symm,
    Finset.sum_range_succ']
  rw [s.zero_bias, abs_zero, add_zero]
  calc
    (∑ j ∈ Finset.range (m - 1), |s.bias (j + 1)|) ≤
        ∑ _j ∈ Finset.range (m - 1), (1 / 2 : ℝ) := Finset.sum_le_sum hb
    _ = ((m : ℝ) - 1) / 2 := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sub (by omega)]
      norm_num
      ring


/-- The first `T` announced predictions along an arbitrary infinite binary path. -/
noncomputable def runForecast {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (T : ℕ) : Fin T → ℝ :=
  fun t => gridForecast hm (gridRun hm y t.val)

noncomputable def runProxy {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (T : ℕ) : Fin T → ℝ :=
  fun t => gridProxy hm (gridRun hm y t.val) (y t.val)

def runOutcomes (y : ℕ → Bool) (T : ℕ) : Fin T → ℝ :=
  fun t => binaryValue (y t.val)

theorem runForecast_mem {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (T : ℕ) (t : Fin T) :
    runForecast hm y T t ∈ Set.Icc (0 : ℝ) 1 := gridForecast_mem hm _

theorem runProxy_mem {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (T : ℕ) (t : Fin T) :
    runProxy hm y T t ∈ Set.Icc (0 : ℝ) 1 := gridProxy_mem hm _ _

theorem runOutcomes_mem (y : ℕ → Bool) (T : ℕ) (t : Fin T) :
    runOutcomes y T t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold runOutcomes binaryValue
  split_ifs <;> constructor <;> norm_num

theorem runForecast_proxy_sum {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (T : ℕ) :
    (∑ t : Fin T, |runForecast hm y T t - runProxy hm y T t|) =
      (T : ℝ) / (2 * (m : ℝ)) := by
  simp only [runForecast, runProxy, gridForecast_proxy_distance]
  simp [div_eq_mul_inv]


theorem proxyIndex_le {m : ℕ} (hm : 0 < m) (s : GridState m) (y : Bool) :
    proxyIndex hm s y ≤ m := by
  cases y with
  | false => exact leftNeighbor_le hm s
  | true => exact (firstNonnegative_spec hm s).1

/-- The stored residual is exactly the residual in the corresponding proxy bin. -/
theorem runProxy_binResidual {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (T k : ℕ) :
    binResidual (runProxy hm y T) (runOutcomes y T) (gridPoint m k) =
      -(gridRun hm y T).bias k := by
  classical
  unfold binResidual bucket
  rw [Finset.sum_filter, gridRun_bias_sum, Finset.sum_range, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  change (if gridPoint m (proxyIndex hm (gridRun hm y t.val) (y t.val)) = gridPoint m k
    then binaryValue (y t.val) - gridPoint m (proxyIndex hm (gridRun hm y t.val) (y t.val))
    else 0) = -(if k = proxyIndex hm (gridRun hm y t.val) (y t.val)
    then gridPoint m k - binaryValue (y t.val) else 0)
  simp only [(gridPoint_injective hm).eq_iff]
  by_cases h : k = proxyIndex hm (gridRun hm y t.val) (y t.val)
  · simp [← h]
  · simp [h, Ne.symm h]

/-- Only grid-valued proxy bins can occur; the endpoint bins contribute zero. -/
theorem runProxy_ece_le {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (T : ℕ) :
    ece (runProxy hm y T) (runOutcomes y T) ≤ ((m : ℝ) - 1) / 2 := by
  classical
  have hsub : Finset.univ.image (runProxy hm y T) ⊆
      (Finset.range (m + 1)).image (gridPoint m) := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
    refine Finset.mem_image.mpr ⟨proxyIndex hm (gridRun hm y t.val) (y t.val), ?_, rfl⟩
    exact Finset.mem_range.mpr (by have := proxyIndex_le hm (gridRun hm y t.val) (y t.val); omega)
  calc
    ece (runProxy hm y T) (runOutcomes y T) ≤
        ∑ z ∈ (Finset.range (m + 1)).image (gridPoint m),
          |binResidual (runProxy hm y T) (runOutcomes y T) z| := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
    _ = ∑ j ∈ Finset.range (m + 1), |(gridRun hm y T).bias j| := by
      rw [Finset.sum_image (gridPoint_injective hm).injOn]
      simp only [runProxy_binResidual, abs_neg]
    _ ≤ ((m : ℝ) - 1) / 2 := gridState_sum_abs_bias_le hm _

/-- Proposition 6.3: the actual causal midpoint construction satisfies the
finite-horizon bound on every binary path, including every truncated prefix. -/
theorem fixed_grid_pathwise_bound {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (T : ℕ) :
    calDist (runForecast hm y T) (runOutcomes y T) ≤
      (T : ℝ) / (2 * (m : ℝ)) + ((m : ℝ) - 1) / 2 := by
  have hy : Valid (runOutcomes y T) := runOutcomes_mem y T
  calc
    calDist (runForecast hm y T) (runOutcomes y T) ≤
        l1Dist (runForecast hm y T) (runProxy hm y T) +
          ece (runProxy hm y T) (runOutcomes y T) :=
      calDist_le_l1_add_ece _ _ hy
    _ ≤ (T : ℝ) / (2 * (m : ℝ)) + ((m : ℝ) - 1) / 2 := by
      rw [l1Dist, runForecast_proxy_sum]
      exact add_le_add_left (runProxy_ece_le hm y T) _


/-- Exact signed integer residual storage: this is `2*m*b`, with no growing
round counter in a stored coordinate. -/
noncomputable def gridNumerator {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) : ℕ → ℕ → ℤ
  | 0, _ => 0
  | t + 1, k => gridNumerator hm y t k +
      if k = proxyIndex hm (gridRun hm y t) (y t) then
        2 * (k : ℤ) - if y t then 2 * (m : ℤ) else 0
      else 0

theorem gridNumerator_cast {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t k : ℕ) :
    ((gridNumerator hm y t k : ℤ) : ℝ) = 2 * (m : ℝ) * (gridRun hm y t).bias k := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  induction t with
  | zero => simp [gridNumerator, gridRun, initialGridState]
  | succ t ih =>
    simp only [gridNumerator, gridRun, gridStep, nextBias, Int.cast_add, ih]
    by_cases hk : k = proxyIndex hm (gridRun hm y t) (y t)
    · simp only [hk, ↓reduceIte]
      cases hy : y t <;> simp [hy, binaryValue, gridPoint] <;> field_simp <;> ring
    · simp [hk]

/-- The exact signed integer in each coordinate stays in [-m,m]. -/
theorem gridNumerator_bounds {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t k : ℕ)
    (hk : k ≤ m) : -(m : ℤ) ≤ gridNumerator hm y t k ∧
      gridNumerator hm y t k ≤ (m : ℤ) := by
  have hs := gridNumerator_cast hm y t k
  have hl := (gridRun hm y t).bias_lower k hk
  have hu := (gridRun hm y t).bias_upper k hk
  have hp : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  constructor
  · have : -(m : ℝ) ≤ ((gridNumerator hm y t k : ℤ) : ℝ) := by nlinarith
    exact_mod_cast this
  · have : ((gridNumerator hm y t k : ℤ) : ℝ) ≤ (m : ℝ) := by nlinarith
    exact_mod_cast this

/-- Equation (B.3): the shifted-bias numerator uses the same bounded integers. -/
theorem gridShiftNumerator_cast {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t k : ℕ) :
    (((gridNumerator hm y t k + 2 * (k : ℤ) - (m : ℤ) : ℤ) : ℝ)) =
      (2 * (m : ℝ)) * shiftedBias (gridRun hm y t) k := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  push_cast
  rw [gridNumerator_cast]
  unfold shiftedBias gridPoint
  field_simp

/-- The signed numerators used for sign tests have magnitude at most `2*m`. -/
theorem gridShiftNumerator_bounds {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t k : ℕ)
    (hk : k ≤ m) :
    -(2 * (m : ℤ)) ≤ gridNumerator hm y t k + 2 * (k : ℤ) - (m : ℤ) ∧
      gridNumerator hm y t k + 2 * (k : ℤ) - (m : ℤ) ≤ 2 * (m : ℤ) := by
  have hn := gridNumerator_bounds hm y t k hk
  have hk0 : (0 : ℤ) ≤ k := Int.natCast_nonneg k
  have hkm : (k : ℤ) ≤ m := by exact_mod_cast hk
  omega

/-- A round changes a single residual coordinate, hence at most one sign-set key. -/
theorem gridNumerator_update_local {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t k : ℕ)
    (hk : k ≠ proxyIndex hm (gridRun hm y t) (y t)) :
    gridNumerator hm y (t + 1) k = gridNumerator hm y t k := by
  simp [gridNumerator, hk]

/-- Integer signs implement the shifted-bias query without real arithmetic. -/
theorem integer_shift_sign {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t k : ℕ) :
    0 ≤ gridNumerator hm y t k + 2 * (k : ℤ) - (m : ℤ) ↔
      0 ≤ shiftedBias (gridRun hm y t) k := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  have hp : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : (((gridNumerator hm y t k + 2 * (k : ℤ) - (m : ℤ) : ℤ) : ℝ)) =
      (2 * (m : ℝ)) * shiftedBias (gridRun hm y t) k := by
    push_cast
    rw [gridNumerator_cast]
    unfold shiftedBias gridPoint
    field_simp
  have hcast : (0 : ℤ) ≤ gridNumerator hm y t k + 2 * (k : ℤ) - (m : ℤ) ↔
      (0 : ℝ) ≤ ((gridNumerator hm y t k + 2 * (k : ℤ) - (m : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast Iff.rfl
  rw [hcast, hs]
  exact mul_nonneg_iff_of_pos_left (by positivity)

/-- Selection can be performed by a search entirely on bounded signed integers. -/
noncomputable def integerFirstNonnegative {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t : ℕ) : ℕ :=
  Nat.find (show ∃ k, k ≤ m ∧ 0 ≤ gridNumerator hm y t k + 2 * (k : ℤ) - (m : ℤ) from
    ⟨firstNonnegative hm (gridRun hm y t), (firstNonnegative_spec hm _).1,
      (integer_shift_sign hm y t _).2 (firstNonnegative_spec hm _).2⟩)

theorem integerFirstNonnegative_eq {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t : ℕ) :
    integerFirstNonnegative hm y t = firstNonnegative hm (gridRun hm y t) := by
  unfold integerFirstNonnegative firstNonnegative
  apply Nat.find_congr'
  intro k
  exact and_congr_right (fun _ => integer_shift_sign hm y t k)

/-- The announced forecast has the exact rational representation in Proposition 6.5. -/
noncomputable def gridForecastRational {m : ℕ} (hm : 0 < m) (s : GridState m) : ℚ :=
  ((leftNeighbor hm s : ℚ) + (firstNonnegative hm s : ℚ)) / (2 * (m : ℚ))

theorem gridForecastRational_cast {m : ℕ} (hm : 0 < m) (s : GridState m) :
    (gridForecastRational hm s : ℝ) = gridForecast hm s := by
  simp only [gridForecastRational, Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat,
    Rat.cast_natCast, gridForecast, gridPoint]
  ring

/-- The numerator and denominator stated in (B.4). -/
theorem gridForecast_exact_rational {m : ℕ} (hm : 0 < m) (s : GridState m) :
    gridForecast hm s =
      (2 * (firstNonnegative hm s : ℝ) - 1) / (2 * (m : ℝ)) := by
  have hc : (leftNeighbor hm s : ℝ) + 1 = (firstNonnegative hm s : ℝ) := by
    exact_mod_cast leftNeighbor_succ hm s
  unfold gridForecast gridPoint
  rw [show (leftNeighbor hm s : ℝ) = (firstNonnegative hm s : ℝ) - 1 by linarith]
  ring

/-- This quantifies the bounded-word representation without a horizon-dependent term. -/
theorem exact_integer_implementation {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) :
    (∀ t k, k ≤ m → -(m : ℤ) ≤ gridNumerator hm y t k ∧
      gridNumerator hm y t k ≤ (m : ℤ)) ∧
    (∀ t, integerFirstNonnegative hm y t = firstNonnegative hm (gridRun hm y t)) ∧
    (∀ t, (gridForecastRational hm (gridRun hm y t) : ℝ) =
      gridForecast hm (gridRun hm y t)) :=
  ⟨gridNumerator_bounds hm y, integerFirstNonnegative_eq hm y,
    fun t => gridForecastRational_cast hm _⟩


end

section

/-- The sign set can be built and searched using only signed integer comparisons. -/
def integerEligible (m : ℕ) (v : ℕ → ℤ) : Finset ℕ :=
  (Finset.range (m + 1)).filter (fun k => 0 ≤ v k + 2 * (k : ℤ) - (m : ℤ))

/-- A concrete finite search; balanced-tree refinement may use the same sign set. -/
def boundedIntegerQuery (m : ℕ) (v : ℕ → ℤ) : ℕ :=
  if h : (integerEligible m v).Nonempty then (integerEligible m v).min' h else m

theorem boundedIntegerQuery_eq {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t : ℕ) :
    boundedIntegerQuery m (gridNumerator hm y t) = firstNonnegative hm (gridRun hm y t) := by
  have hmem : firstNonnegative hm (gridRun hm y t) ∈ integerEligible m (gridNumerator hm y t) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr (by have := (firstNonnegative_spec hm (gridRun hm y t)).1; omega),
      (integer_shift_sign hm y t _).2 (firstNonnegative_spec hm _).2⟩
  unfold boundedIntegerQuery
  rw [dif_pos ⟨_, hmem⟩]
  apply (Finset.min'_eq_iff _ _ _).mpr
  refine ⟨hmem, ?_⟩
  intro k hk
  by_contra hn
  have hlt : k < firstNonnegative hm (gridRun hm y t) := by omega
  have hs := firstNonnegative_min hm (gridRun hm y t) hlt
  have hi := (integer_shift_sign hm y t k).1 (Finset.mem_filter.mp hk).2
  linarith

/-- A round of an independent implementation uses only integers and the current bit. -/
def boundedIntegerStep (m : ℕ) (v : ℕ → ℤ) (y : Bool) (k : ℕ) : ℤ :=
  let j := boundedIntegerQuery m v
  let i := j - 1
  let a := if y then j else i
  v k + if k = a then 2 * (k : ℤ) - if y then 2 * (m : ℤ) else 0 else 0

/-- This recursion executes without real-number state or future outcomes. -/
def boundedIntegerRun (m : ℕ) (y : ℕ → Bool) : ℕ → ℕ → ℤ
  | 0 => fun _ => 0
  | t + 1 => boundedIntegerStep m (boundedIntegerRun m y t) (y t)

/-- The integer implementation exactly simulates the mathematical grid construction. -/
theorem boundedIntegerRun_correct {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t : ℕ) :
    boundedIntegerRun m y t = gridNumerator hm y t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext k
    simp only [boundedIntegerRun, boundedIntegerStep, ih, boundedIntegerQuery_eq,
      gridNumerator, proxyIndex, leftNeighbor]

theorem gridNumerator_zero_outside {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t k : ℕ)
    (hk : m < k) : gridNumerator hm y t k = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hn : k ≠ proxyIndex hm (gridRun hm y t) (y t) := by
      have := proxyIndex_le hm (gridRun hm y t) (y t)
      omega
    rw [gridNumerator_update_local hm y t k hn, ih]

/-- Only the fixed `m+1` grid coordinates require storage. -/
theorem boundedIntegerRun_zero_outside {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t k : ℕ)
    (hk : m < k) : boundedIntegerRun m y t k = 0 := by
  rw [boundedIntegerRun_correct hm y t]
  exact gridNumerator_zero_outside hm y t k hk


/-- Exact rational output of the integer-only algorithm. -/
def boundedIntegerForecast (m : ℕ) (v : ℕ → ℤ) : ℚ :=
  (2 * (boundedIntegerQuery m v : ℚ) - 1) / (2 * (m : ℚ))

theorem boundedIntegerForecast_correct {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t : ℕ) :
    (boundedIntegerForecast m (boundedIntegerRun m y t) : ℝ) =
      gridForecast hm (gridRun hm y t) := by
  unfold boundedIntegerForecast
  push_cast
  rw [boundedIntegerRun_correct hm y t, boundedIntegerQuery_eq hm y t]
  exact (gridForecast_exact_rational hm _).symm


/-- The initial sign set is the sorted interval in Appendix B.1. -/
theorem integerEligible_initial (m : ℕ) :
    integerEligible m (fun _ => 0) = Finset.Icc ((m + 1) / 2) m := by
  ext k
  simp only [integerEligible, Finset.mem_filter, Finset.mem_range, Finset.mem_Icc, zero_add]
  omega

/-- A round changes sign-set membership at only the updated coordinate. -/
theorem integerEligible_update_local {m : ℕ} (hm : 0 < m) (y : ℕ → Bool) (t k : ℕ)
    (hk : k ≠ proxyIndex hm (gridRun hm y t) (y t)) :
    (k ∈ integerEligible m (gridNumerator hm y (t + 1)) ↔
      k ∈ integerEligible m (gridNumerator hm y t)) := by
  simp only [integerEligible, Finset.mem_filter]
  rw [gridNumerator_update_local hm y t k hk]

/-- The exact sign-set data contain at most `m+1` keys, at every time. -/
theorem integerEligible_card_le (m : ℕ) (v : ℕ → ℤ) :
    (integerEligible m v).card ≤ m + 1 := by
  calc
    (integerEligible m v).card ≤ (Finset.range (m + 1)).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = m + 1 := Finset.card_range _

end
end CalibrationDistance
