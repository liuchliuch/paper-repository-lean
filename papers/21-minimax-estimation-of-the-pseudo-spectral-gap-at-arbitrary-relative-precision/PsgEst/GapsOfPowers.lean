import PsgEst.Basic
import PsgEst.Estimator
import Mathlib.Data.Nat.Choose.Sum

/-!
# Lemma 1: gaps of powers

`1/4 · min{k γ_ps(P), 1} ≤ γ_ps(P^k) ≤ min{k γ_ps(P), 1}`,
and `a_t > 1/2` for every `t ≥ 1/γ_ps(P)`.
-/

open Matrix BigOperators Real

namespace PsgEst

variable {d : ℕ}

/-! ## Real / Nat helpers -/

/-- Bernoulli-type bound used in Lemma 1: `(1 + 1/q)^q ≥ 2` for `q ≥ 1`. -/
theorem one_add_inv_nat_pow_two_le (q : ℕ) (hq : 0 < q) :
    (2 : ℝ) ≤ (1 + 1 / (q : ℝ)) ^ q := by
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hq)
  have hmem_q : q ∈ Finset.range (q + 1) := Finset.mem_range.mpr (Nat.lt_succ_self q)
  have hmem_qm1 : q - 1 ∈ Finset.range (q + 1) := by
    refine Finset.mem_range.mpr ?_
    have : q - 1 < q := Nat.sub_lt hq (by omega)
    omega
  rw [add_pow (1 : ℝ) (1 / q) q]
  rw [Finset.sum_eq_sum_diff_singleton_add hmem_q]
  have hqterm : (1 : ℝ) ^ q * (1 / q) ^ (q - q) * q.choose q = 1 := by
    rw [tsub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one, mul_one, one_pow]
  rw [hqterm]
  have hss : q - 1 ∈ Finset.range (q + 1) \ {q} := by
    refine Finset.mem_sdiff.mpr ⟨hmem_qm1, ?_⟩
    simp only [Finset.mem_singleton]
    omega
  rw [Finset.sum_eq_sum_diff_singleton_add hss]
  have hqm1term : (1 : ℝ) ^ (q - 1) * (1 / q) ^ (q - (q - 1)) * q.choose (q - 1) = 1 := by
    have hsub : q - (q - 1) = 1 := by omega
    have h1 : (1 : ℝ) ^ (q - 1) = 1 := one_pow _
    have h3 : q.choose (q - 1) = q := by
      cases q with
      | zero => exact absurd hq (by omega)
      | succ n =>
        show (n + 1).choose ((n + 1) - 1) = n + 1
        rw [Nat.add_sub_cancel, Nat.choose_succ_self_right]
    rw [hsub, h1, h3]
    have h2 : ((1 : ℝ) / q) ^ (1 : ℕ) = 1 / q := by simp
    rw [h2, one_mul, div_mul_cancel₀ 1 hq0]
  rw [hqm1term]
  have hrest_nonneg : (0 : ℝ) ≤
      ∑ m ∈ (Finset.range (q + 1) \ {q}) \ {q - 1},
        (1 : ℝ) ^ m * (1 / q) ^ (q - m) * q.choose m := by
    apply Finset.sum_nonneg
    intro m _
    apply mul_nonneg
    · apply mul_nonneg
      · exact pow_nonneg (by norm_num) _
      · exact pow_nonneg (div_nonneg zero_le_one (Nat.cast_nonneg q)) _
    · exact Nat.cast_nonneg _
  have h2 : (2 : ℝ) = 1 + 1 + 0 := by norm_num
  rw [h2]
  have : ((∑ m ∈ (Finset.range (q + 1) \ {q}) \ {q - 1},
        (1 : ℝ) ^ m * (1 / q) ^ (q - m) * q.choose m) + 1) + 1
      = 1 + 1 + ∑ m ∈ (Finset.range (q + 1) \ {q}) \ {q - 1},
        (1 : ℝ) ^ m * (1 / q) ^ (q - m) * q.choose m := by
    abel
  rw [this]
  exact add_le_add le_rfl hrest_nonneg

/-- `(1-a)^{⌊1/a⌋} < 1/2` for `0 < a < 1`. -/
theorem one_sub_pow_floor_lt_half {a : ℝ} (ha : 0 < a) (ha' : a < 1) :
    (1 - a) ^ (⌊(1 : ℝ) / a⌋₊ : ℕ) < 1 / 2 := by
  set q : ℕ := ⌊(1 : ℝ) / a⌋₊ with hqdef
  have hq_pos : 0 < q := by
    rw [hqdef, Nat.floor_pos]
    have : (1:ℝ) ≤ 1/a := by
      rw [le_div_iff₀ ha]
      linarith
    linarith
  have hfloor_le : (q : ℝ) ≤ 1 / a := Nat.floor_le (by positivity)
  have hfloor_lt : (1 : ℝ) / a < q + 1 := Nat.lt_floor_add_one _
  have hq1 : (0 : ℝ) < q + 1 := by positivity
  have ha_gt : (1 : ℝ) / (q + 1) < a := by
    have : (1 : ℝ) < a * (q + 1) := by
      have h := hfloor_lt
      rw [div_lt_iff₀ ha] at h
      linarith
    rw [div_lt_iff₀ hq1]
    linarith
  have h1ma : (1 - a) < (q : ℝ) / (q + 1) := by
    have h2 : (1 : ℝ) - 1 / (q + 1) = q / (q + 1) := by
      field_simp; ring
    have : (1 - a) < (1 : ℝ) - 1 / (q + 1) := by linarith
    rwa [h2] at this
  have hqz : (0 : ℝ) < q := Nat.cast_pos.mpr hq_pos
  have hbase : 0 ≤ 1 - a := le_of_lt (sub_pos.mpr ha')
  have hpow : (1 - a) ^ q < ((q : ℝ) / (q + 1)) ^ q := by
    gcongr
  have key : ((q : ℝ) / (q + 1)) ^ q = 1 / (1 + 1 / (q : ℝ)) ^ q := by
    have h1 : (q : ℝ) / (q + 1) = 1 / (1 + 1 / q) := by
      field_simp
    rw [h1, _root_.one_div_pow]
  have h2 : (1 : ℝ) / (1 + 1 / q) ^ q ≤ 1 / 2 := by
    have hbig := one_add_inv_nat_pow_two_le q (Nat.cast_pos.mp hq_pos)
    have hpos : (0 : ℝ) < (1 + 1 / q) ^ q := by positivity
    rw [div_le_div_iff_of_pos_left zero_lt_one hpos zero_lt_two]
    linarith
  exact lt_of_lt_of_le hpow (key.trans_le h2)

/-! ## Abstract gap sequences -/

/-- Paper's structural properties of `a_t = 1 - b_t^2`:
`0 ≤ a_t ≤ 1` and `b_{r+s} ≤ b_r b_s` i.e. `1 - a_{r+s} ≤ (1 - a_r)(1 - a_s)`. -/
structure GapAx (a : ℕ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ a t
  le_one : ∀ t, a t ≤ 1
  b_sub : ∀ r s, 1 - a (r + s) ≤ (1 - a r) * (1 - a s)

/-- Paulin-style gap of an abstract sequence: `γ = ⨆_{k≥1} a_k / k`. -/
noncomputable def gapGamma (a : ℕ → ℝ) : ℝ :=
  ⨆ k : ℕ, if 0 < k then a k / k else 0

theorem gapGamma_bddAbove (a : ℕ → ℝ) (h : ∀ t, a t ≤ 1) :
    BddAbove (Set.range fun k : ℕ => if 0 < k then a k / k else 0) := by
  refine ⟨1, fun x hx => ?_⟩
  obtain ⟨k, rfl⟩ := hx
  by_cases hk : 0 < k
  · show (if 0 < k then a k / k else 0) ≤ 1
    rw [if_pos hk]
    have h1 : a k / k ≤ 1 / k := div_le_div_of_nonneg_right (h k) (Nat.cast_nonneg k)
    have h2 : (1 : ℝ) / k ≤ 1 :=
      div_le_self zero_le_one (by exact_mod_cast Nat.one_le_of_lt hk)
    linarith
  · show (if 0 < k then a k / k else 0) ≤ 1
    rw [if_neg hk]
    norm_num

theorem gapGamma_le_one (a : ℕ → ℝ) (h : ∀ t, a t ≤ 1) : gapGamma a ≤ 1 := by
  apply ciSup_le
  intro k
  by_cases hk : 0 < k
  · show (if 0 < k then a k / k else 0) ≤ 1
    rw [if_pos hk]
    have h1 : a k / k ≤ 1 / k := div_le_div_of_nonneg_right (h k) (Nat.cast_nonneg k)
    have h2 : (1 : ℝ) / k ≤ 1 :=
      div_le_self zero_le_one (by exact_mod_cast Nat.one_le_of_lt hk)
    linarith
  · show (if 0 < k then a k / k else 0) ≤ 1
    rw [if_neg hk]
    norm_num

theorem gapGamma_nonneg (a : ℕ → ℝ) (h : ∀ t, a t ≤ 1) : 0 ≤ gapGamma a := by
  have h0 : (if 0 < (0:ℕ) then a 0 / (0:ℕ) else 0) = 0 := by simp
  calc (0:ℝ) = (if 0 < (0:ℕ) then a 0 / (0:ℕ) else 0) := by simp
    _ ≤ gapGamma a := le_ciSup (gapGamma_bddAbove a h) 0

theorem le_gapGamma (a : ℕ → ℝ) {k : ℕ} (hk : 0 < k) (h : ∀ t, a t ≤ 1) :
    a k / k ≤ gapGamma a := by
  have : (if 0 < k then a k / k else 0) = a k / k := if_pos hk
  rw [← this]
  exact le_ciSup (f := fun k : ℕ => if 0 < k then a k / k else 0) (gapGamma_bddAbove a h) k

/-- Contraction sequence `b_t = sqrt(1 - a_t)`. -/
noncomputable def gapB (a : ℕ → ℝ) (t : ℕ) : ℝ := Real.sqrt (max 0 (1 - a t))

theorem gapB_nonneg (a : ℕ → ℝ) (t : ℕ) : 0 ≤ gapB a t := Real.sqrt_nonneg _

theorem gapB_sq {a : ℕ → ℝ} (h : ∀ t, a t ≤ 1) (t : ℕ) :
    gapB a t ^ 2 = 1 - a t := by
  have : max 0 (1 - a t) = 1 - a t := max_eq_right (sub_nonneg.mpr (h t))
  rw [gapB, this, Real.sq_sqrt (sub_nonneg.mpr (h t))]

theorem gapB_le_one {a : ℕ → ℝ} (h : GapAx a) (t : ℕ) : gapB a t ≤ 1 := by
  have h1 : 0 ≤ 1 - a t := sub_nonneg.mpr (h.le_one t)
  have h2 : 1 - a t ≤ 1 := sub_le_self _ (h.nonneg t)
  have : max 0 (1 - a t) = 1 - a t := max_eq_right h1
  rw [gapB, this]
  exact (Real.sqrt_le_one).2 h2

/-- Submultiplicativity `gapB (r+s) ≤ gapB r * gapB s` under `GapAx`. -/
theorem gapB_mul {a : ℕ → ℝ} (hax : GapAx a) (r s : ℕ) :
    gapB a (r + s) ≤ gapB a r * gapB a s := by
  have h1 : 0 ≤ 1 - a (r + s) := sub_nonneg.mpr (hax.le_one _)
  have hr : 0 ≤ 1 - a r := sub_nonneg.mpr (hax.le_one _)
  have hs : 0 ≤ 1 - a s := sub_nonneg.mpr (hax.le_one _)
  have e1 : max 0 (1 - a (r + s)) = 1 - a (r + s) := max_eq_right h1
  have e2 : max 0 (1 - a r) = 1 - a r := max_eq_right hr
  have e3 : max 0 (1 - a s) = 1 - a s := max_eq_right hs
  have hmul : gapB a r * gapB a s = Real.sqrt ((1 - a r) * (1 - a s)) := by
    rw [gapB, gapB, e2, e3, Real.sqrt_mul hr]
  rw [gapB, e1, hmul]
  exact Real.sqrt_le_sqrt (hax.b_sub r s)

/-- `b_{q * k0} ≤ b_{k0}^q`. -/
theorem gapB_pow {a : ℕ → ℝ} (hax : GapAx a) (k0 : ℕ) :
    ∀ q : ℕ, gapB a (q * k0) ≤ gapB a k0 ^ q
  | 0 => by
    simp only [zero_mul, pow_zero]
    exact gapB_le_one hax 0
  | q + 1 => by
    have hstep : (q + 1) * k0 = q * k0 + k0 := by rw [Nat.succ_mul]
    rw [hstep]
    have hmul := gapB_mul hax (q * k0) k0
    have ih := gapB_pow hax k0 q
    have : gapB a (q * k0 + k0) ≤ gapB a k0 ^ q * gapB a k0 :=
      le_trans hmul (mul_le_mul_of_nonneg_right ih (gapB_nonneg a k0))
    rw [pow_succ]
    exact this

/-- If `a_{k0} = 1` then `a_t = 1` for `t ≥ k0`. -/
theorem gapAx_eq_one_of {a : ℕ → ℝ} (hax : GapAx a) {k0 : ℕ} (h : a k0 = 1)
    {t : ℕ} (ht : k0 ≤ t) : a t = 1 := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le ht
  have h1 : 1 - a (k0 + q) ≤ (1 - a k0) * (1 - a q) := hax.b_sub k0 q
  rw [h, sub_self, zero_mul] at h1
  have h2 : 0 ≤ 1 - a (k0 + q) := sub_nonneg.mpr (hax.le_one _)
  have h3 : 1 - a (k0 + q) = 0 := le_antisymm h1 h2
  linarith

/-- A maximizing lag exists and satisfies `k0 ≤ 1/γ`. -/
theorem gapGamma_exists_max {a : ℕ → ℝ} (hax : GapAx a) (hγ : 0 < gapGamma a) :
    ∃ k0 : ℕ, 0 < k0 ∧ a k0 / k0 = gapGamma a ∧ (k0 : ℝ) ≤ 1 / gapGamma a := by
  have hle : ∀ t, a t ≤ 1 := hax.le_one
  set K : ℕ := ⌈(2:ℝ) / gapGamma a⌉₊ with hKdef
  have hKpos : 0 < K := by
    rw [hKdef, Nat.ceil_pos]
    positivity
  have hKge : (2:ℝ) / gapGamma a ≤ K := by rw [hKdef]; exact Nat.le_ceil _
  have hpos : (0:ℝ) < K := Nat.cast_pos.mpr hKpos
  have hγpos : (0:ℝ) < gapGamma a := hγ
  have h1K : (1:ℝ) / K ≤ gapGamma a / 2 := by
    rw [div_le_iff₀ hpos]
    -- 1 ≤ gapGamma a / 2 * K  ↔  2 ≤ gapGamma a * K
    have h2 : (2:ℝ) ≤ gapGamma a * K := by
      have hmul := mul_le_mul_of_nonneg_left hKge (le_of_lt hγpos)
      have hcancel : gapGamma a * ((2:ℝ) / gapGamma a) = 2 :=
        mul_div_cancel₀ _ (ne_of_gt hγpos)
      linarith
    linarith
  have h1Klt : (1:ℝ) / K < gapGamma a := by linarith
  have hIcc : (Finset.Icc 1 K : Finset ℕ).Nonempty :=
    ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, Nat.one_le_of_lt hKpos⟩⟩
  obtain ⟨k0, hk0mem, hk0max⟩ :=
    Finset.exists_max_image (Finset.Icc 1 K) (fun k => a k / k) hIcc
  have hk0le : 1 ≤ k0 ∧ k0 ≤ K := Finset.mem_Icc.mp hk0mem
  have hk0pos : 0 < k0 := by omega
  have hmax_le : gapGamma a ≤ a k0 / k0 := by
    by_contra hnc
    push_neg at hnc
    have hmax : a k0 / k0 < gapGamma a := hnc
    have hle_fin : ∀ k : ℕ, k ∈ Finset.Icc 1 K → a k / k ≤ a k0 / k0 :=
      fun k hk => hk0max k hk
    have : gapGamma a ≤ max (a k0 / k0) (gapGamma a / 2) := by
      apply ciSup_le
      intro k
      by_cases hk : 0 < k
      · show (if 0 < k then a k / k else 0) ≤ max (a k0 / k0) (gapGamma a / 2)
        rw [if_pos hk]
        by_cases hkK : k ≤ K
        · exact le_max_of_le_left (hle_fin k (Finset.mem_Icc.mpr ⟨hk, hkK⟩))
        · have h1 : a k / k ≤ 1 / k := div_le_div_of_nonneg_right (hle k) (Nat.cast_nonneg k)
          have h2 : (1:ℝ)/k ≤ gapGamma a / 2 := by
            have h3 : (1:ℝ)/k ≤ 1/K := by
              apply div_le_div_of_nonneg_left zero_le_one (by positivity)
              exact_mod_cast (Nat.le_of_lt (by omega : K < k))
            linarith
          exact le_max_of_le_right (le_trans h1 h2)
      · show (if 0 < k then a k / k else 0) ≤ max (a k0 / k0) (gapGamma a / 2)
        rw [if_neg hk]
        exact le_max_of_le_right (by linarith)
    have hlt : max (a k0 / k0) (gapGamma a / 2) < gapGamma a := max_lt hmax (by linarith)
    linarith
  have hle_max : a k0 / k0 ≤ gapGamma a := le_gapGamma a hk0pos hle
  have heq : a k0 / k0 = gapGamma a := le_antisymm hle_max hmax_le
  refine ⟨k0, hk0pos, heq, ?_⟩
  have hk0eq : a k0 = k0 * gapGamma a := by
    have := heq
    rw [div_eq_iff (Nat.cast_ne_zero.mpr (ne_of_gt hk0pos))] at this
    rw [this]
    ring
  have : a k0 ≤ 1 := hle k0
  rw [hk0eq] at this
  rw [le_div_iff₀ hγpos]
  nlinarith

/-- If `γ > 0` and `a` satisfies `GapAx`, then `a_t > 1/2` for `t ≥ 1/γ`. -/
theorem gapAx_gt_half_of_gap {a : ℕ → ℝ} (hax : GapAx a) (hγ : 0 < gapGamma a) :
    ∀ t : ℕ, 0 < t → (1 / gapGamma a : ℝ) ≤ t → (1 / 2 : ℝ) < a t := by
  obtain ⟨k0, hk0pos, hk0eq, hk0le⟩ := gapGamma_exists_max hax hγ
  have ha_eq : a k0 = k0 * gapGamma a := by
    have := hk0eq
    rw [div_eq_iff (Nat.cast_ne_zero.mpr (ne_of_gt hk0pos))] at this
    rw [this]
    ring
  have hαpos : 0 < a k0 := by
    rw [ha_eq]
    positivity
  have hαle : a k0 ≤ 1 := hax.le_one k0
  have hγeq : gapGamma a = a k0 / k0 := hk0eq.symm
  have hk0r : (0:ℝ) < k0 := Nat.cast_pos.mpr hk0pos
  have hk0ne : (k0:ℝ) ≠ 0 := ne_of_gt hk0r
  have h1γ : (1:ℝ) / gapGamma a = k0 / a k0 := by
    rw [hγeq, one_div_div]
  intro t htpos htge
  by_cases hα1 : a k0 = 1
  · have hk0 : (k0 : ℝ) = 1 / gapGamma a := by
      have h1 : (1:ℝ) = k0 * gapGamma a := hα1.symm.trans ha_eq
      rw [eq_div_iff hγ.ne']
      nlinarith
    have ht : k0 ≤ t := by
      have := htge
      rw [← hk0] at this
      exact_mod_cast this
    have := gapAx_eq_one_of hax hα1 ht
    rw [this]
    norm_num
  · have hαlt : a k0 < 1 := lt_of_le_of_ne hαle hα1
    have htge' : (k0 : ℝ) / a k0 ≤ t := by
      rw [← h1γ]
      exact htge
    have h1 : (1:ℝ) / a k0 ≤ (t:ℝ) / (k0:ℝ) := by
      have h := div_le_div_of_nonneg_right htge' (le_of_lt hk0r)
      have heq' : (k0 : ℝ) / a k0 / k0 = 1 / a k0 := by
        field_simp
      rw [heq'] at h
      exact h
    have hfloor : (⌊(1:ℝ) / a k0⌋₊ : ℕ) ≤ t / k0 := by
      have hnonneg : 0 ≤ (1:ℝ)/a k0 := by positivity
      have h2 : (⌊(1:ℝ)/a k0⌋₊ : ℝ) ≤ 1 / a k0 := Nat.floor_le hnonneg
      have h3 : (⌊(1:ℝ)/a k0⌋₊ : ℝ) * k0 ≤ t := by
        have : (⌊(1:ℝ)/a k0⌋₊ : ℝ) * k0 ≤ (1 / a k0) * k0 :=
          mul_le_mul_of_nonneg_right h2 (le_of_lt hk0r)
        have heq : (1 / a k0 : ℝ) * k0 = k0 / a k0 := by ring
        rw [heq] at this
        have : (k0:ℝ) / a k0 ≤ t := htge'
        linarith
      rw [Nat.le_div_iff_mul_le (by omega : 0 < k0)]
      exact_mod_cast h3
    have hbt : gapB a t ≤ gapB a k0 ^ (t / k0) := by
      have hkey : (t / k0) * k0 + t % k0 = t := by
        rw [mul_comm]
        exact Nat.div_add_mod t k0
      have hmod : gapB a t ≤ gapB a ((t / k0) * k0) * gapB a (t % k0) := by
        have h := gapB_mul hax ((t / k0) * k0) (t % k0)
        rwa [hkey] at h
      have hble : gapB a (t % k0) ≤ 1 := gapB_le_one hax _
      have hstep : gapB a t ≤ gapB a ((t / k0) * k0) :=
        le_trans hmod (le_trans (mul_le_mul_of_nonneg_left hble (gapB_nonneg _ _))
          (mul_one _).le)
      exact le_trans hstep (gapB_pow hax k0 _)
    have hb0 : gapB a k0 = Real.sqrt (1 - a k0) := by
      rw [gapB]
      congr 1
      exact max_eq_right (sub_nonneg.mpr hαle)
    have hsq : gapB a t ^ 2 = 1 - a t := gapB_sq hax.le_one t
    have hpow : gapB a t ^ 2 ≤ (1 - a k0) ^ (⌊(1:ℝ) / a k0⌋₊ : ℕ) := by
      have h2 : gapB a t ^ 2 ≤ (gapB a k0 ^ (t / k0)) ^ 2 :=
        pow_le_pow_left₀ (gapB_nonneg _ _) hbt 2
      have h3 : (gapB a k0 ^ (t / k0)) ^ 2 = (gapB a k0 ^ 2) ^ (t / k0) := by
        calc (gapB a k0 ^ (t / k0)) ^ 2 = gapB a k0 ^ ((t / k0) * 2) := (pow_mul _ _ _).symm
          _ = gapB a k0 ^ (2 * (t / k0)) := by rw [mul_comm]
          _ = (gapB a k0 ^ 2) ^ (t / k0) := pow_mul _ _ _
      have h4 : gapB a k0 ^ 2 = 1 - a k0 := by
        rw [hb0, Real.sq_sqrt (le_of_lt (sub_pos.mpr hαlt))]
      rw [h3, h4] at h2
      have hbase : 0 ≤ 1 - a k0 := le_of_lt (sub_pos.mpr hαlt)
      have hbase1 : 1 - a k0 ≤ 1 := by linarith
      have h5 : (1 - a k0) ^ (t / k0) ≤ (1 - a k0) ^ (⌊(1:ℝ) / a k0⌋₊ : ℕ) :=
        pow_le_pow_of_le_one hbase hbase1 (by exact_mod_cast hfloor)
      exact le_trans h2 h5
    have hhalf : (1 - a k0) ^ (⌊(1:ℝ) / a k0⌋₊ : ℕ) < 1 / 2 :=
      one_sub_pow_floor_lt_half hαpos hαlt
    have : gapB a t ^ 2 < 1 / 2 := lt_of_le_of_lt hpow hhalf
    rw [hsq] at this
    linarith


/-- Abstract Lemma 1 for a `GapAx` sequence. -/
theorem gapAx_lemma_1 {a : ℕ → ℝ} (hax : GapAx a) (hγ : 0 < gapGamma a) :
    (∀ k : ℕ, 0 < k →
      (1 / 4 : ℝ) * min (k * gapGamma a) 1 ≤ gapGamma (fun j => a (k * j))
        ∧ gapGamma (fun j => a (k * j)) ≤ min (k * gapGamma a) 1)
    ∧ (∀ t : ℕ, 0 < t → (1 / gapGamma a : ℝ) ≤ t → (1 / 2 : ℝ) < a t) := by
  refine ⟨?_, gapAx_gt_half_of_gap hax hγ⟩
  intro k hk
  have hle : ∀ t, a t ≤ 1 := hax.le_one
  have hkpos : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hkne : (k:ℝ) ≠ 0 := ne_of_gt hkpos
  -- upper bound
  have hup : gapGamma (fun j => a (k * j)) ≤ min (k * gapGamma a) 1 := by
    apply le_min
    · apply ciSup_le
      intro j
      by_cases hj : 0 < j
      · show (if 0 < j then a (k * j) / j else 0) ≤ k * gapGamma a
        rw [if_pos hj]
        have hjne : (j:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hj)
        have h : a (k * j) / (j:ℝ) = k * (a (k * j) / (k * j : ℝ)) := by
          field_simp
        rw [h]
        have hle' : a (k * j) / (k * j : ℝ) ≤ gapGamma a := by
          have hmul : ((k * j : ℕ) : ℝ) = (k:ℝ) * j := by norm_cast
          rw [← hmul]
          refine le_gapGamma a ?_ hle
          positivity
        exact mul_le_mul_of_nonneg_left hle' (le_of_lt hkpos)
      · show (if 0 < j then a (k * j) / j else 0) ≤ k * gapGamma a
        rw [if_neg hj]
        positivity
    · apply ciSup_le
      intro j
      by_cases hj : 0 < j
      · show (if 0 < j then a (k * j) / j else 0) ≤ 1
        rw [if_pos hj]
        have h1 : a (k * j) / (j:ℝ) ≤ 1 / j :=
          div_le_div_of_nonneg_right (hle _) (Nat.cast_nonneg _)
        have h2 : (1:ℝ) / j ≤ 1 :=
          div_le_self zero_le_one (by exact_mod_cast Nat.one_le_of_lt hj)
        linarith
      · show (if 0 < j then a (k * j) / j else 0) ≤ 1
        rw [if_neg hj]
        norm_num
  -- lower bound
  have hlo : (1 / 4 : ℝ) * min (k * gapGamma a) 1 ≤ gapGamma (fun j => a (k * j)) := by
    by_cases hkg : k * gapGamma a ≤ 1
    · -- kγ ≤ 1: take j = ⌈1/(kγ)⌉
      have hkgpos : 0 < k * gapGamma a := by positivity
      set j : ℕ := ⌈(1 : ℝ) / (k * gapGamma a)⌉₊ with hjdef
      have hjpos : 0 < j := by
        rw [hjdef, Nat.ceil_pos]
        positivity
      have hjge : (1 : ℝ) / (k * gapGamma a) ≤ j := by
        rw [hjdef]
        exact Nat.le_ceil _
      have hjlt : (j : ℝ) < 1 / (k * gapGamma a) + 1 := by
        have hjne : j ≠ 0 := ne_of_gt hjpos
        have := (Nat.ceil_eq_iff hjne).mp rfl
        obtain ⟨hlt, _⟩ := this
        have hlt' : (j:ℝ) - 1 < 1 / (k * gapGamma a) := by
          have : ((j - 1 : ℕ) : ℝ) = (j:ℝ) - 1 := by
            rw [Nat.cast_sub (Nat.succ_le_of_lt hjpos)]
            simp
          linarith
        linarith
      -- kj ≥ 1/γ
      have hkj : (1 / gapGamma a : ℝ) ≤ ((k * j : ℕ) : ℝ) := by
        have hmul : ((k * j : ℕ) : ℝ) = (k:ℝ) * j := by norm_cast
        rw [hmul]
        have : (1 : ℝ) ≤ (k * gapGamma a) * j := by
          have hcancel : (k * gapGamma a : ℝ) * (1 / (k * gapGamma a)) = 1 :=
            mul_div_cancel₀ _ (ne_of_gt hkgpos)
          have := mul_le_mul_of_nonneg_left hjge (le_of_lt hkgpos)
          rw [hcancel] at this
          exact this
        rw [div_le_iff₀ hγ]
        nlinarith
      have hakj : (1/2 : ℝ) < a (k * j) :=
        gapAx_gt_half_of_gap hax hγ (k * j) (by positivity) hkj
      have hge : a (k * j) / j ≤ gapGamma (fun j => a (k * j)) :=
        le_gapGamma (fun j => a (k * j)) hjpos (fun t => hle _)
      have hj2 : (1 : ℝ) / (2 * j) < a (k * j) / j := by
        have hj0 : (0:ℝ) < j := Nat.cast_pos.mpr hjpos
        have h1 : (1:ℝ) / (2 * j) = (1 / 2) / j := by field_simp
        rw [h1]
        exact div_lt_div_of_pos_right hakj hj0
      have hfinal : (k * gapGamma a : ℝ) / 4 ≤ a (k * j) / j := by
        have hstep1 : (k * gapGamma a : ℝ) / 4 ≤ 1 / (2 * j) := by
          have hjle : (j : ℝ) ≤ 1 / (k * gapGamma a) + 1 := le_of_lt hjlt
          have hj2' : (k * gapGamma a : ℝ) * j ≤ 1 + k * gapGamma a := by
            have h := mul_le_mul_of_nonneg_left hjle (le_of_lt hkgpos)
            have hcancel : (k * gapGamma a : ℝ) * (1 / (k * gapGamma a)) = 1 :=
              mul_div_cancel₀ _ (ne_of_gt hkgpos)
            nlinarith
          have : (k * gapGamma a : ℝ) * j ≤ 2 := by linarith
          rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 4) (by positivity)]
          ring_nf at this ⊢
          linarith
        exact le_trans hstep1 (le_of_lt hj2)
      have hmin : (1 / 4 : ℝ) * min (k * gapGamma a) 1 = (k * gapGamma a) / 4 := by
        rw [min_eq_left hkg]
        ring
      rw [hmin]
      exact le_trans hfinal hge
    · -- kγ ≥ 1: min = 1, take j = 1
      have hkg' : 1 ≤ k * gapGamma a := le_of_not_ge hkg
      have hkge : (1 / gapGamma a : ℝ) ≤ k := by
        rw [div_le_iff₀ hγ]
        nlinarith
      have hak : (1/2 : ℝ) < a k := gapAx_gt_half_of_gap hax hγ k hk hkge
      have hge : a k / 1 ≤ gapGamma (fun j => a (k * j)) := by
        have := le_gapGamma (fun j => a (k * j)) (show (0:ℕ) < 1 by norm_num)
          (fun t => hle _)
        simpa using this
      have hmin : (1 / 4 : ℝ) * min (k * gapGamma a) 1 = 1 / 4 := by
        rw [min_eq_right hkg']
        ring
      rw [hmin]
      have : (1 / 4 : ℝ) ≤ a k / 1 := by
        rw [div_one]
        linarith
      exact le_trans this hge
  exact ⟨hlo, hup⟩


/-! ## Structural lemmas for Markov chains -/

/-- The stationary law of `S` is also stationary for `S.pow k`. -/
noncomputable def stationaryPow (S : Stoch d) (st : Stationary S) (k : ℕ) :
    Stationary (S.pow k) where
  mu := st.mu
  pos := st.pos
  sum_one := st.sum_one
  station := by
    intro j
    dsimp [Stoch.pow]
    induction k with
    | zero =>
      classical
      simp [pow_zero, Matrix.one_apply]
    | succ k ih =>
      have hpow : S.P ^ (k + 1) = S.P * S.P ^ k := pow_succ' _ _
      erw [hpow]
      show ∑ i, st.mu i * (∑ l, S.P i l * (S.P ^ k) l j) = st.mu j
      calc ∑ i, st.mu i * ∑ l, S.P i l * (S.P ^ k) l j
          = ∑ i, ∑ l, st.mu i * (S.P i l * (S.P ^ k) l j) := by
            simp_rw [Finset.mul_sum]
        _ = ∑ i, ∑ l, (st.mu i * S.P i l) * (S.P ^ k) l j := by
            simp_rw [mul_assoc]
        _ = ∑ l, ∑ i, (st.mu i * S.P i l) * (S.P ^ k) l j := Finset.sum_comm
        _ = ∑ l, (∑ i, st.mu i * S.P i l) * (S.P ^ k) l j := by
            simp_rw [← Finset.sum_mul]
        _ = ∑ l, st.mu l * (S.P ^ k) l j := by
            simp_rw [st.station]
        _ = st.mu j := ih

/-- Diagonal `D^{-1/2} * D^{1/2} = I`. -/
theorem dpi_half_inv_mul (mu : Fin d → ℝ) (hpos : ∀ i, 0 < mu i) :
    diagonal (fun i => (mu i) ^ (-(1 / 2 : ℝ))) *
      diagonal (fun i => (mu i) ^ (1 / 2 : ℝ)) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have h : (fun i => (mu i) ^ (-(1 / 2 : ℝ)) * (mu i) ^ (1 / 2 : ℝ))
      = fun _ => (1 : ℝ) := by
    funext i
    rw [← Real.rpow_add (hpos i)]
    have : (-(1 / 2 : ℝ) + 1 / 2) = 0 := by ring
    rw [this, Real.rpow_zero]
  rw [h]
  exact Matrix.diagonal_one

/-- Diagonal `D^{1/2} * D^{-1/2} = I`. -/
theorem dpi_half_mul_inv (mu : Fin d → ℝ) (hpos : ∀ i, 0 < mu i) :
    diagonal (fun i => (mu i) ^ (1 / 2 : ℝ)) *
      diagonal (fun i => (mu i) ^ (-(1 / 2 : ℝ))) = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  have h : (fun i => (mu i) ^ (1 / 2 : ℝ) * (mu i) ^ (-(1 / 2 : ℝ)))
      = fun _ => (1 : ℝ) := by
    funext i
    rw [← Real.rpow_add (hpos i)]
    have : ((1 / 2 : ℝ) + -(1 / 2)) = 0 := by ring
    rw [this, Real.rpow_zero]
  rw [h]
  exact Matrix.diagonal_one

/-- `L_{r+s} = L_r * L_s`.
Proof: `L_r L_s = D^{1/2} P^r (D^{-1/2} D^{1/2}) P^s D^{-1/2} = D^{1/2} P^{r+s} D^{-1/2}`. -/
theorem Lk_add (S : Stoch d) (st : Stationary S) (r s : ℕ) :
    Lk S st (r + s) = Lk S st r * Lk S st s := by
  have hmid : diagonal (fun i => (st.mu i) ^ (-(1 / 2 : ℝ))) *
      diagonal (fun i => (st.mu i) ^ (1 / 2 : ℝ)) = 1 :=
    dpi_half_inv_mul st.mu st.pos
  set dh : Matrix (Fin d) (Fin d) ℝ := diagonal (fun i => (st.mu i) ^ (1 / 2 : ℝ))
  set di : Matrix (Fin d) (Fin d) ℝ := diagonal (fun i => (st.mu i) ^ (-(1 / 2 : ℝ)))
  have hmidS : di * dh = 1 := hmid
  have hmidS' : dh * di = 1 := dpi_half_mul_inv st.mu st.pos
  show dh * (S.P ^ (r + s)) * di = (dh * S.P ^ r * di) * (dh * S.P ^ s * di)
  rw [pow_add]
  have hmid1 : di * ((dh * S.P ^ s) * di) = S.P ^ s * di := by
    calc di * ((dh * S.P ^ s) * di)
        = ((di * dh) * S.P ^ s) * di := by simp only [mul_assoc]
      _ = (1 * S.P ^ s) * di := by rw [hmidS]
      _ = S.P ^ s * di := by rw [one_mul]
  have hrew : (dh * S.P ^ r * di) * (dh * S.P ^ s * di)
      = (dh * (S.P ^ r * S.P ^ s)) * di := by
    calc (dh * S.P ^ r * di) * (dh * S.P ^ s * di)
        = (dh * S.P ^ r) * (di * ((dh * S.P ^ s) * di)) := by
          simp only [mul_assoc]
      _ = (dh * S.P ^ r) * (S.P ^ s * di) := by rw [hmid1]
      _ = dh * (S.P ^ r * (S.P ^ s * di)) := by simp only [mul_assoc]
      _ = dh * ((S.P ^ r * S.P ^ s) * di) := by simp only [mul_assoc]
      _ = (dh * (S.P ^ r * S.P ^ s)) * di := by simp only [mul_assoc]
  rw [hrew]

/-- `L_j` of `S.pow k` equals `L_{k*j}` of `S`. -/
theorem Lk_pow (S : Stoch d) (st : Stationary S) (k j : ℕ) :
    Lk (S.pow k) (stationaryPow S st k) j = Lk S st (k * j) := by
  have h : (S.P ^ k) ^ j = S.P ^ (k * j) := by rw [← pow_mul, mul_comm]
  simp only [Lk, simil, Stoch.pow, stationaryPow]
  rw [h]

/-- `aK` of powers. -/
theorem aK_pow [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S) (k j : ℕ) :
    aK (S.pow k) (stationaryPow S st k) j = aK S st (k * j) := by
  simp only [aK]
  rw [Lk_pow]

/-- `gammaPS` equals the abstract gap of `aK`. -/
theorem gammaPS_eq_gapGamma [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S) :
    gammaPS S st = gapGamma (aK S st) := rfl


/-! ## Concrete statements for Markov chains -/

/-- Stationary square-root vector `v_i = √π_i`. -/
noncomputable def stVec {d : ℕ} {S : Stoch d} (st : Stationary S) : Fin d → ℝ :=
  fun i => (st.mu i) ^ ((1 : ℝ) / 2)

theorem stVec_nonneg {d : ℕ} {S : Stoch d} (st : Stationary S) (i : Fin d) :
    0 ≤ stVec st i := by
  simp only [stVec]
  exact Real.rpow_nonneg (st.nonneg i) _

theorem stVec_pos {d : ℕ} {S : Stoch d} (st : Stationary S) (i : Fin d) :
    0 < stVec st i := by
  simp only [stVec]
  exact Real.rpow_pos_of_pos (st.pos i) _

theorem stVec_sq {d : ℕ} {S : Stoch d} (st : Stationary S) (i : Fin d) :
    stVec st i * stVec st i = st.mu i := by
  simp only [stVec]
  exact rpow_half_sq _ (st.pos i)

theorem stVec_sq_sum {d : ℕ} {S : Stoch d} (st : Stationary S) :
    ∑ i, stVec st i * stVec st i = 1 := by
  simp_rw [stVec_sq]
  exact st.sum_one

/-- Expansion of `L_t *ᵥ u` in terms of `f = D^{-1/2} u`. -/
theorem Lk_mulVec_apply (S : Stoch d) (st : Stationary S) (t : ℕ)
    (u : Fin d → ℝ) (i : Fin d) :
    (Lk S st t *ᵥ u) i
      = (st.mu i) ^ ((1 : ℝ) / 2) *
          ∑ k, (S.P ^ t) i k * ((st.mu k) ^ (-(1 / 2 : ℝ)) * u k) := by
  have h1 : Lk S st t *ᵥ u
      = diagonal (fun j => (st.mu j) ^ ((1 : ℝ) / 2)) *ᵥ
          ((S.P ^ t) *ᵥ (diagonal (fun j => (st.mu j) ^ (-(1 / 2 : ℝ))) *ᵥ u)) := by
    simp only [Lk, simil]
    rw [← Matrix.mulVec_mulVec]
    simp only [Matrix.mul_assoc, Matrix.mulVec_mulVec]
  calc (Lk S st t *ᵥ u) i
      = (diagonal (fun j => (st.mu j) ^ ((1 : ℝ) / 2)) *ᵥ
          ((S.P ^ t) *ᵥ (diagonal (fun j => (st.mu j) ^ (-(1 / 2 : ℝ))) *ᵥ u))) i := by rw [h1]
    _ = (st.mu i) ^ ((1 : ℝ) / 2) *
          ((S.P ^ t) *ᵥ (diagonal (fun j => (st.mu j) ^ (-(1 / 2 : ℝ))) *ᵥ u)) i :=
        Matrix.mulVec_diagonal _ _ _
    _ = (st.mu i) ^ ((1 : ℝ) / 2) *
          ∑ k, (S.P ^ t) i k * ((st.mu k) ^ (-(1 / 2 : ℝ)) * u k) := by
          congr 1
          have hdi : (diagonal (fun j => (st.mu j) ^ (-(1 / 2 : ℝ))) *ᵥ u)
              = fun k => (st.mu k) ^ (-(1 / 2 : ℝ)) * u k := by
            funext k
            exact Matrix.mulVec_diagonal _ _ _
          rw [hdi]
          rfl

/-- `L_t` is a Euclidean contraction: `∑ (L_t u)² ≤ ∑ u²`. -/
theorem Lk_contraction (S : Stoch d) (st : Stationary S) (t : ℕ)
    (u : Fin d → ℝ) : ∑ i, (Lk S st t *ᵥ u) i ^ 2 ≤ ∑ i, u i ^ 2 := by
  classical
  have hpos : ∀ i, 0 < st.mu i := st.pos
  set w : Fin d → ℝ := fun k => (st.mu k) ^ (-(1 / 2 : ℝ))
  set f : Fin d → ℝ := fun k => w k * u k
  have hvec : ∀ i, (Lk S st t *ᵥ u) i
      = (st.mu i) ^ ((1 : ℝ) / 2) * ∑ k, (S.P ^ t) i k * f k := by
    intro i
    rw [Lk_mulVec_apply S st t u i]
  have hj : ∀ i, (∑ k, (S.P ^ t) i k * f k) ^ 2
      ≤ ∑ k, (S.P ^ t) i k * f k ^ 2 := by
    intro i
    have hwc := weighted_cauchy (a := fun k => (S.P ^ t) i k) (v := f)
      (fun k => S.pow_nonneg t i k)
    have hrow : ∑ k, (S.P ^ t) i k = 1 := S.pow_row_stoch t i
    have := hwc
    rw [hrow, one_mul] at this
    exact this
  have hsum : ∑ i, (Lk S st t *ᵥ u) i ^ 2
      ≤ ∑ i, st.mu i * ∑ k, (S.P ^ t) i k * f k ^ 2 := by
    calc ∑ i, (Lk S st t *ᵥ u) i ^ 2
        = ∑ i, ((st.mu i) ^ ((1 : ℝ) / 2) * ∑ k, (S.P ^ t) i k * f k) ^ 2 :=
          Finset.sum_congr rfl fun i _ => congrArg (fun z => z ^ 2) (hvec i)
      _ = ∑ i, ((st.mu i) ^ ((1 : ℝ) / 2)) ^ 2 * (∑ k, (S.P ^ t) i k * f k) ^ 2 := by
          simp_rw [mul_pow]
      _ = ∑ i, st.mu i * (∑ k, (S.P ^ t) i k * f k) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hi : 0 < st.mu i := hpos i
          have h2 : ((st.mu i) ^ ((1 : ℝ) / 2)) ^ 2 = st.mu i := by
            rw [pow_two, rpow_half_sq _ hi]
          rw [h2]
      _ ≤ ∑ i, st.mu i * ∑ k, (S.P ^ t) i k * f k ^ 2 := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hj i) (st.nonneg i)
  have hswap : ∑ i, st.mu i * ∑ k, (S.P ^ t) i k * f k ^ 2
      = ∑ k, (∑ i, st.mu i * (S.P ^ t) i k) * f k ^ 2 := by
    have h1 : ∑ i, st.mu i * ∑ k, (S.P ^ t) i k * f k ^ 2
        = ∑ i, ∑ k, st.mu i * ((S.P ^ t) i k * f k ^ 2) := by
      simp_rw [Finset.mul_sum]
    have h2 : ∑ i, ∑ k, st.mu i * ((S.P ^ t) i k * f k ^ 2)
        = ∑ k, ∑ i, st.mu i * ((S.P ^ t) i k * f k ^ 2) := Finset.sum_comm
    have h3 : ∑ k, ∑ i, st.mu i * ((S.P ^ t) i k * f k ^ 2)
        = ∑ k, (∑ i, st.mu i * (S.P ^ t) i k) * f k ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      have hassoc : ∀ i, st.mu i * ((S.P ^ t) i k * f k ^ 2)
          = (st.mu i * (S.P ^ t) i k) * f k ^ 2 := fun i => by ring
      rw [Finset.sum_congr rfl (fun i _ => hassoc i)]
      exact (Finset.sum_mul Finset.univ (fun i => st.mu i * (S.P ^ t) i k) (f k ^ 2)).symm
    rw [h1, h2, h3]
  have hstat : ∀ k, ∑ i, st.mu i * (S.P ^ t) i k = st.mu k := by
    intro k
    have := (stationaryPow S st t).station k
    simpa [Stoch.pow] using this
  have hcancel : ∀ k, st.mu k * f k ^ 2 = u k ^ 2 := by
    intro k
    have hk : 0 < st.mu k := hpos k
    have hw2 : w k * w k = (st.mu k) ^ (-1 : ℝ) := by
      simp only [w]
      exact rpow_neg_half_sq _ hk
    have hsq : f k ^ 2 = w k * w k * u k ^ 2 := by
      simp only [f]
      rw [pow_two]
      ring
    rw [hsq, hw2]
    have hinv : (st.mu k) ^ (-1 : ℝ) * st.mu k = 1 := by
      rw [Real.rpow_neg_one, inv_mul_cancel₀ (ne_of_gt hk)]
    nlinarith
  have hfinal : ∑ k, (∑ i, st.mu i * (S.P ^ t) i k) * f k ^ 2 = ∑ k, u k ^ 2 := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hstat, hcancel]
  linarith

/-- `L_t v = v` for `v = stVec st`. -/
theorem Lk_mulVec_stVec (S : Stoch d) (st : Stationary S) (t : ℕ) :
    Lk S st t *ᵥ stVec st = stVec st := by
  classical
  have hpos : ∀ i, 0 < st.mu i := st.pos
  funext i
  rw [Lk_mulVec_apply S st t (stVec st) i]
  have h1 : ∀ k, (st.mu k) ^ (-(1 / 2 : ℝ)) * stVec st k = 1 := by
    intro k
    simp only [stVec]
    have hk : 0 < st.mu k := hpos k
    have h := Real.rpow_add hk (-(1 / 2 : ℝ)) ((1 : ℝ) / 2)
    rw [show (-(1 / 2 : ℝ) + 1 / 2) = 0 by ring, Real.rpow_zero] at h
    rw [← h]
  have h2 : ∑ k, (S.P ^ t) i k * ((st.mu k) ^ (-(1 / 2 : ℝ)) * stVec st k) = 1 := by
    have h : ∀ k, (S.P ^ t) i k * ((st.mu k) ^ (-(1 / 2 : ℝ)) * stVec st k)
        = (S.P ^ t) i k * 1 := fun k => by rw [h1 k]
    rw [Finset.sum_congr rfl (fun k _ => h k)]
    simp_rw [mul_one]
    exact S.pow_row_stoch t i
  rw [h2, mul_one]
  simp only [stVec]

/-- `L_tᵀ v = v` (left stationarity of `L_t`). -/
theorem Lk_transpose_mulVec_stVec (S : Stoch d) (st : Stationary S) (t : ℕ) :
    (Lk S st t).transpose *ᵥ stVec st = stVec st := by
  classical
  have hpos : ∀ i, 0 < st.mu i := st.pos
  have hL : (Lk S st t).transpose
      = (diagonal (fun j => (st.mu j) ^ (-(1 / 2 : ℝ))) * (S.P ^ t).transpose) *
          diagonal (fun j => (st.mu j) ^ ((1 : ℝ) / 2)) := by
    show ((diagonal (fun j => (st.mu j) ^ ((1 : ℝ) / 2)) * S.P ^ t) *
        diagonal (fun j => (st.mu j) ^ (-(1 / 2 : ℝ))))ᵀ = _
    rw [Matrix.transpose_mul, Matrix.transpose_mul]
    simp only [Matrix.diagonal_transpose, Matrix.transpose_transpose, Matrix.mul_assoc]
  have hdh : (diagonal (fun j => (st.mu j) ^ ((1 : ℝ) / 2)) *ᵥ stVec st) = st.mu := by
    funext k
    simp only [Matrix.mulVec_diagonal, stVec]
    have hk : 0 < st.mu k := hpos k
    have h := Real.rpow_add hk ((1 : ℝ) / 2) ((1 : ℝ) / 2)
    rw [show ((1 : ℝ) / 2 + 1 / 2) = 1 by ring, Real.rpow_one] at h
    exact h.symm
  have hstatT : (S.P ^ t).transpose *ᵥ st.mu = st.mu := by
    funext j
    have h := (stationaryPow S st t).station j
    simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct, Stoch.pow] at h ⊢
    simpa [mul_comm] using h
  have hdi : (diagonal (fun j => (st.mu j) ^ (-(1 / 2 : ℝ))) *ᵥ st.mu) = stVec st := by
    funext k
    simp only [Matrix.mulVec_diagonal, stVec]
    have hk : 0 < st.mu k := hpos k
    have h := Real.rpow_add hk (-(1 / 2 : ℝ)) (1 : ℝ)
    rw [show (-(1 / 2 : ℝ) + 1) = 1 / 2 by ring] at h
    rw [Real.rpow_one] at h
    exact h.symm
  have h1 : (Lk S st t).transpose *ᵥ stVec st
      = (diagonal (fun j => (st.mu j) ^ (-(1 / 2 : ℝ))) * (S.P ^ t).transpose) *ᵥ
          (diagonal (fun j => (st.mu j) ^ ((1 : ℝ) / 2)) *ᵥ stVec st) := by
    rw [hL, ← Matrix.mulVec_mulVec]
  rw [h1, hdh]
  have h2 : (diagonal (fun j => (st.mu j) ^ (-(1 / 2 : ℝ))) * (S.P ^ t).transpose) *ᵥ st.mu
      = diagonal (fun j => (st.mu j) ^ (-(1 / 2 : ℝ))) *ᵥ ((S.P ^ t).transpose *ᵥ st.mu) := by
    rw [← Matrix.mulVec_mulVec]
  rw [h2, hstatT, hdi]

/-- `0 ≤ aK t ≤ 1`. Requires the π-norm contraction
(`‖P^t f‖_π ≤ ‖f‖_π` via Jensen + stationarity) and Rayleigh quotients of `gram (L_t)`. -/
theorem aK_mem [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S) (t : ℕ) :
    0 ≤ aK S st t ∧ aK S st t ≤ 1 := by
  have hcontr : ∀ u : Fin d → ℝ, (∑ i, (Lk S st t *ᵥ u) i ^ 2) ≤ ∑ i, u i ^ 2 :=
    fun u => Lk_contraction S st t u
  have hσ := sigma2_mem_of_contraction (Lk S st t) hcontr
  have hsq : 0 ≤ (sigma2 (Lk S st t)) ^ 2 ∧ (sigma2 (Lk S st t)) ^ 2 ≤ 1 := by
    refine ⟨sq_nonneg _, ?_⟩
    nlinarith [hσ.1, hσ.2]
  unfold aK aOf
  constructor <;> linarith

/-- Contraction norm `b_t = ‖P^t - Π‖_π = sqrt(1 - a_t)`. -/
noncomputable def bNorm [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S) (t : ℕ) : ℝ :=
  gapB (aK S st) t

theorem bNorm_nonneg [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S) (t : ℕ) :
    0 ≤ bNorm S st t := gapB_nonneg _ _

/-! ### Rank-one projection and `σ₂ = ‖L - vvᵀ‖` -/

/-- Rank-one projection `vvᵀ`. -/
noncomputable def piProj {d : ℕ} {S : Stoch d} (st : Stationary S) :
    Matrix (Fin d) (Fin d) ℝ := fun i j => stVec st i * stVec st j

/-- `M_t = L_t - vvᵀ`. -/
noncomputable def LkSub {d : ℕ} [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S)
    (t : ℕ) : Matrix (Fin d) (Fin d) ℝ := Lk S st t - piProj st

theorem piProj_mulVec {d : ℕ} {S : Stoch d} (st : Stationary S) (x : Fin d → ℝ) :
    piProj st *ᵥ x = fun i => stVec st i * ∑ j, stVec st j * x j := by
  funext i
  simp only [Matrix.mulVec, dotProduct, piProj]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem LkSub_mulVec {d : ℕ} [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S)
    (t : ℕ) (x : Fin d → ℝ) :
    LkSub S st t *ᵥ x = fun i => (Lk S st t *ᵥ x) i - stVec st i * ∑ j, stVec st j * x j := by
  funext i
  simp only [LkSub, Matrix.sub_mulVec, Pi.sub_apply]
  rw [piProj_mulVec]

/-- `M_t v = 0` and `M_tᵀ v = 0`. -/
theorem LkSub_mulVec_stVec {d : ℕ} [DecidableEq (Fin d)] (S : Stoch d)
    (st : Stationary S) (t : ℕ) : LkSub S st t *ᵥ stVec st = 0 := by
  funext i
  simp only [LkSub, Matrix.sub_mulVec, Pi.sub_apply, Pi.zero_apply]
  rw [Lk_mulVec_stVec, piProj_mulVec]
  simp only [stVec_sq_sum, mul_one, sub_self]

/-- `M_{r+s} = M_r * M_s`. -/
theorem LkSub_add [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S) (r s : ℕ) :
    LkSub S st (r + s) = LkSub S st r * LkSub S st s := by
  have hL : Lk S st (r + s) = Lk S st r * Lk S st s := Lk_add S st r s
  have hPP : piProj st * piProj st = piProj st := by
    ext i j
    simp only [piProj, Matrix.mul_apply]
    have hsum : ∑ k, (stVec st i * stVec st k) * (stVec st k * stVec st j)
        = stVec st i * stVec st j * ∑ k, stVec st k * stVec st k := by
      have h : ∀ k, (stVec st i * stVec st k) * (stVec st k * stVec st j)
          = stVec st i * stVec st j * (stVec st k * stVec st k) := by
        intro k; ring
      rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.mul_sum]
    rw [hsum, stVec_sq_sum st, mul_one]
  have hLproj : Lk S st r * piProj st = piProj st := by
    ext i j
    simp only [piProj, Matrix.mul_apply]
    have hcol : ∀ i, ∑ k, Lk S st r i k * stVec st k = stVec st i := by
      intro i
      have := congrFun (Lk_mulVec_stVec S st r) i
      simpa [Matrix.mulVec, dotProduct] using this
    have h : ∑ x, Lk S st r i x * (stVec st x * stVec st j)
        = (∑ x, Lk S st r i x * stVec st x) * stVec st j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [h, hcol]
  have hprojL : piProj st * Lk S st s = piProj st := by
    ext i j
    simp only [piProj, Matrix.mul_apply]
    have hrow : ∀ j, ∑ k, stVec st k * Lk S st s k j = stVec st j := by
      intro j
      have h := congrFun (Lk_transpose_mulVec_stVec S st s) j
      -- (Lᵀ *ᵥ v) j = ∑ k, Lᵀ j k * v k = ∑ k, L k j * v k = v j
      simpa [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using h
    have h : ∑ x, stVec st i * stVec st x * Lk S st s x j
        = stVec st i * (∑ x, stVec st x * Lk S st s x j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [h, hrow]
  calc LkSub S st (r + s)
      = Lk S st (r + s) - piProj st := rfl
    _ = Lk S st r * Lk S st s - piProj st := by rw [hL]
    _ = (Lk S st r - piProj st) * (Lk S st s - piProj st) := by
        have h1 : (Lk S st r - piProj st) * (Lk S st s - piProj st)
            = Lk S st r * Lk S st s - Lk S st r * piProj st
                - piProj st * Lk S st s + piProj st * piProj st := by
          rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
          abel
        rw [h1, hLproj, hprojL, hPP]
        abel

/-! ### Finite optimization: second-largest Rayleigh quotient -/

/-- Split `∑ i, f i = f 0 + ∑ i ≠ 0, f i`. -/
theorem sum_fin_eq_zero_add_rest {d : ℕ} [NeZero d] (f : Fin d → ℝ) :
    ∑ i, f i = f 0 + ∑ i ∈ (Finset.univ : Finset (Fin d)) \ {(0 : Fin d)}, f i := by
  conv_lhs => rw [Finset.sum_eq_sum_diff_singleton_add (i := (0 : Fin d)) (Finset.mem_univ 0)]
  rw [add_comm]

/-- Indicator vector `e_a`. -/
def eVec {d : ℕ} (a : Fin d) : Fin d → ℝ := fun i => if i = a then 1 else 0

theorem eVec_sq_sum {d : ℕ} [NeZero d] (a : Fin d) : ∑ i, eVec a i * eVec a i = 1 := by
  simp [eVec, Finset.sum_ite_eq']

theorem eVec_dot {d : ℕ} [NeZero d] (a : Fin d) (v : Fin d → ℝ) : ∑ i, eVec a i * v i = v a := by
  simp [eVec, Finset.sum_ite_eq']

theorem eVec_rayleigh {d : ℕ} [NeZero d] (lam : Fin d → ℝ) (a : Fin d) :
    ∑ i, lam i * (eVec a i * eVec a i) = lam a := by
  simp [eVec, Finset.sum_ite_eq']

/-- Second-largest eigenvalue characterization. -/
theorem second_rayleigh {d : ℕ} [NeZero d] (lam w : Fin d → ℝ)
    (hanti : Antitone lam) (hw : ∑ i, w i * w i = 1) (hle : lam 0 ≤ 1)
    (hmem : ∀ i, w i ≠ 0 → lam i = 1) (hd : 1 < d) :
    (∀ y : Fin d → ℝ, ∑ i, y i * y i = 1 → ∑ i, y i * w i = 0 →
        ∑ i, lam i * (y i * y i) ≤ lam 1)
    ∧ (∃ y : Fin d → ℝ, ∑ i, y i * y i = 1 ∧ ∑ i, y i * w i = 0
        ∧ ∑ i, lam i * (y i * y i) = lam 1) := by
  have hex : ∃ i, w i ≠ 0 := by
    by_contra hall
    push_neg at hall
    have : ∑ i, w i * w i = 0 := by
      simp_rw [hall, mul_zero]; exact Finset.sum_const_zero
    linarith
  obtain ⟨i0, hi0w⟩ := hex
  have h01 : lam 0 = 1 := by
    have hlami : lam i0 = 1 := hmem i0 hi0w
    have h0 : lam 0 ≥ lam i0 := hanti (Fin.zero_le i0)
    exact le_antisymm hle (by linarith)
  have hle1 : ∀ i, i ≠ (0 : Fin d) → lam i ≤ lam 1 := fun i hi =>
    hanti (Fin.one_le_of_ne_zero hi)
  have hsplit : ∀ (f : Fin d → ℝ), ∑ i, f i
      = f 0 + ∑ i ∈ (Finset.univ : Finset (Fin d)) \ {(0 : Fin d)}, f i :=
    fun f => sum_fin_eq_zero_add_rest f
  refine ⟨?_, ?_⟩
  · intro y hy hyw
    have hrest : ∑ i ∈ (Finset.univ : Finset (Fin d)) \ {(0 : Fin d)},
        lam i * (y i * y i) ≤ lam 1 * (1 - y 0 * y 0) := by
      have h1 : ∑ i ∈ (Finset.univ : Finset (Fin d)) \ {(0 : Fin d)},
          lam i * (y i * y i)
          ≤ ∑ i ∈ (Finset.univ : Finset (Fin d)) \ {(0 : Fin d)}, lam 1 * (y i * y i) := by
        apply Finset.sum_le_sum
        intro i hi
        have hi0 : i ≠ 0 := by
          simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton,
            true_and, not_false_eq_true] at hi
          exact hi
        exact mul_le_mul_of_nonneg_right (hle1 i hi0) (mul_self_nonneg _)
      have h2 : ∑ i ∈ (Finset.univ : Finset (Fin d)) \ {(0 : Fin d)}, lam 1 * (y i * y i)
          = lam 1 * ∑ i ∈ (Finset.univ : Finset (Fin d)) \ {(0 : Fin d)}, (y i * y i) :=
        (Finset.mul_sum ..).symm
      have h3 : ∑ i ∈ (Finset.univ : Finset (Fin d)) \ {(0 : Fin d)}, (y i * y i)
          = 1 - y 0 * y 0 := by
        conv_rhs => rw [← hy, hsplit]
        ring
      calc ∑ i ∈ (Finset.univ : Finset (Fin d)) \ {(0 : Fin d)}, lam i * (y i * y i)
          ≤ ∑ i ∈ (Finset.univ : Finset (Fin d)) \ {(0 : Fin d)}, lam 1 * (y i * y i) := h1
        _ = lam 1 * ∑ i ∈ (Finset.univ : Finset (Fin d)) \ {(0 : Fin d)}, (y i * y i) := h2
        _ = lam 1 * (1 - y 0 * y 0) := by rw [h3]
    rw [hsplit (fun i => lam i * (y i * y i))]
    by_cases heq : (lam 0 : ℝ) = lam 1
    · have h2 : (lam 0 : ℝ) * (y 0 * y 0) = lam 1 * (y 0 * y 0) := by rw [heq]
      have hsum : (lam 1 : ℝ) * (y 0 * y 0) + lam 1 * (1 - y 0 * y 0) = lam 1 := by ring
      have h1 := hrest
      nlinarith [h2, hsum]
    · have hlt : lam 1 < (lam 0 : ℝ) := lt_of_le_of_ne
        (hanti (show (0 : Fin d) ≤ (1 : Fin d) by simp)) (Ne.symm heq)
      have hy00 : y 0 = 0 := by
        by_contra hny
        have hw0 : w 0 ≠ 0 := by
          by_contra hw0
          obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
            by_contra hall
            push_neg at hall
            have : ∑ i, w i * w i = 0 := by
              simp_rw [hall, mul_zero]; exact Finset.sum_const_zero
            linarith
          have hj0 : j ≠ 0 := by rintro rfl; exact absurd hw0 hj
          have hj1 : (1 : Fin d) ≤ j := Fin.one_le_of_ne_zero hj0
          have := hmem j hj
          have := hanti hj1
          linarith
        have hwi0 : ∀ i, i ≠ (0 : Fin d) → w i = 0 := by
          intro i hi
          by_contra hwi
          have := hmem i hwi
          have := hle1 i hi
          linarith
        have hrest0 : ∑ i ∈ (Finset.univ : Finset (Fin d)) \ {(0 : Fin d)},
            y i * w i = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hi0 : i ≠ 0 := by
            simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton,
              true_and, not_false_eq_true] at hi
            exact hi
          rw [hwi0 i hi0, mul_zero]
        have hyw' : ∑ i, y i * w i = y 0 * w 0
            + ∑ i ∈ (Finset.univ : Finset (Fin d)) \ {(0 : Fin d)}, y i * w i := hsplit _
        rw [hyw', hrest0, add_zero] at hyw
        exact hny ((mul_eq_zero.mp hyw).resolve_right hw0)
      have hz : (lam 0 : ℝ) * (y 0 * y 0) = 0 := by rw [hy00]; ring
      have hrest' : ∑ i ∈ (Finset.univ : Finset (Fin d)) \ {(0 : Fin d)},
          lam i * (y i * y i) ≤ lam 1 := by
        have := hrest
        have : (1 : ℝ) - y 0 * y 0 = 1 := by rw [hy00]; ring
        rw [this] at hrest
        simpa using hrest
      nlinarith
  · by_cases hw0 : w 0 = 0
    · refine ⟨eVec 0, eVec_sq_sum 0, ?_, ?_⟩
      · rw [eVec_dot, hw0]
      · rw [eVec_rayleigh, h01]
        have hwn : ∃ j, j ≠ (0 : Fin d) ∧ w j ≠ 0 := by
          by_contra hall
          push_neg at hall
          have hall' : ∀ i, w i = 0 := by
            intro i
            by_cases hi : i = (0 : Fin d)
            · exact hi ▸ hw0
            · exact hall i hi
          have : ∑ i, w i * w i = 0 := by
            simp_rw [hall', mul_zero]; exact Finset.sum_const_zero
          linarith
        obtain ⟨j, hj0, hj⟩ := hwn
        have hj1 : (1 : Fin d) ≤ j := Fin.one_le_of_ne_zero hj0
        have hlamj : lam j = 1 := hmem j hj
        have hlej : lam j ≤ lam 1 := hanti hj1
        have hge : (1 : ℝ) ≤ lam 1 := by linarith
        have hup : lam 1 ≤ 1 := by
          have : lam 1 ≤ lam 0 := hanti (show (0 : Fin d) ≤ (1 : Fin d) by simp)
          linarith
        linarith
    · by_cases hw1 : w 1 = 0
      · refine ⟨eVec 1, eVec_sq_sum 1, ?_, ?_⟩
        · rw [eVec_dot, hw1]
        · rw [eVec_rayleigh]
      · set c : ℝ := Real.sqrt (w 1 * w 1 + w 0 * w 0)
        have hcpos : 0 < c := by
          simp only [c]
          apply Real.sqrt_pos.mpr
          nlinarith [sq_pos_of_ne_zero hw0, sq_pos_of_ne_zero hw1]
        have hc2 : c * c = w 1 * w 1 + w 0 * w 0 := by
          have hnn : 0 ≤ w 1 * w 1 + w 0 * w 0 := add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
          exact Real.mul_self_sqrt hnn
        set y0 : Fin d → ℝ := fun i =>
          if i = 0 then w 1 else if i = (1 : Fin d) then -w 0 else 0
        have h01' : (0 : Fin d) ≠ 1 := by
          intro hh
          have hval' : (0 : ℕ) = 1 := by
            have hval := congrArg Fin.val hh
            have h1 : ((1 : Fin d) : ℕ) = 1 := by
              rw [Fin.val_one' d, Nat.mod_eq_of_lt hd]
            rwa [Fin.val_zero, h1] at hval
          exact absurd hval' (by omega)
        have h10 : (1 : Fin d) ≠ 0 := fun hh => h01' hh.symm
        have hy0sq : ∑ i, y0 i * y0 i = w 1 * w 1 + w 0 * w 0 := by
          have h : ∀ i, y0 i * y0 i
              = (if i = (0 : Fin d) then w 1 * w 1 else 0)
                + (if i = (1 : Fin d) then w 0 * w 0 else 0) := by
            intro i
            by_cases h0 : i = 0
            · subst h0; simp [y0, h01']
            · by_cases h1 : i = 1
              · subst h1; simp [y0, h0, h10]
              · simp [y0, h0, h1]
          simp_rw [h, Finset.sum_add_distrib]
          rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp [Finset.mem_univ]
        have hy0w : ∑ i, y0 i * w i = 0 := by
          have h : ∀ i, y0 i * w i
              = (if i = (0 : Fin d) then w 1 * w 0 else 0)
                + (if i = (1 : Fin d) then (-w 0) * w 1 else 0) := by
            intro i
            by_cases h0 : i = 0
            · subst h0; simp [y0, h01']
            · by_cases h1 : i = 1
              · subst h1; simp [y0, h0, h10]
              · simp [y0, h0, h1]
          simp_rw [h, Finset.sum_add_distrib]
          rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp [Finset.mem_univ]
          ring
        have hy0ray : ∑ i, lam i * (y0 i * y0 i) = w 1 * w 1 + w 0 * w 0 := by
          have h : ∀ i, lam i * (y0 i * y0 i)
              = (if i = (0 : Fin d) then lam 0 * (w 1 * w 1) else 0)
                + (if i = (1 : Fin d) then lam 1 * (w 0 * w 0) else 0) := by
            intro i
            by_cases h0 : i = 0
            · subst h0; simp [y0, h01']
            · by_cases h1 : i = 1
              · subst h1; simp [y0, h0, h10]
              · simp [y0, h0, h1]
          simp_rw [h, Finset.sum_add_distrib]
          rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
          simp [Finset.mem_univ]
          have hlam1 : lam 1 = 1 := hmem 1 hw1
          rw [h01, hlam1]
          ring
        set y : Fin d → ℝ := fun i => y0 i / c
        have hnorm : ∑ i, y i * y i = 1 := by
          have h : ∀ i, (y0 i / c) * (y0 i / c) = (y0 i * y0 i) / (c * c) := by
            intro i; field_simp
          simp only [y]; simp_rw [h]
          rw [← Finset.sum_div, hy0sq, hc2]
          exact div_self (ne_of_gt (by nlinarith [sq_pos_of_ne_zero hw0, sq_pos_of_ne_zero hw1]))
        have horth : ∑ i, y i * w i = 0 := by
          have h : ∀ i, (y0 i / c) * w i = (y0 i * w i) / c := by
            intro i; field_simp
          simp only [y]; simp_rw [h]
          rw [← Finset.sum_div, hy0w, zero_div]
        have hray : ∑ i, lam i * (y i * y i) = lam 1 := by
          have h : ∀ i, lam i * ((y0 i / c) * (y0 i / c))
              = (lam i * (y0 i * y0 i)) / (c * c) := by
            intro i; field_simp
          simp only [y]; simp_rw [h]
          rw [← Finset.sum_div, hy0ray, hc2]
          have hlam1 : lam 1 = 1 := hmem 1 hw1
          rw [hlam1]
          exact div_self (ne_of_gt (by nlinarith [sq_pos_of_ne_zero hw0, sq_pos_of_ne_zero hw1]))
        exact ⟨y, hnorm, horth, hray⟩


private theorem spectral_repr_dot {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin d)))
    (x y : EuclideanSpace ℝ (Fin d)) :
    ∑ i, b.repr x i * b.repr y i = ∑ j, x j * y j := by
  simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct, mul_comm] using
    b.repr.inner_map_map x y

private theorem spectral_gram_dot (L : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℝ) :
    ∑ i, x i * (gram L *ᵥ x) i = ∑ i, (L *ᵥ x) i ^ 2 := by
  change x ⬝ᵥ ((L.transpose * L) *ᵥ x) = _
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.transpose_transpose]
  simp [dotProduct, pow_two]

/-- Rayleigh characterization of the second sorted Gram eigenvalue on the complement
of a fixed unit singular vector, with no simplicity assumption on the top eigenvalue. -/
theorem sigma2_rayleigh_fixed [DecidableEq (Fin d)] (L : Matrix (Fin d) (Fin d) ℝ)
    (v : Fin d → ℝ) (hd : 1 < d)
    (hv : ∑ i, v i * v i = 1)
    (hLv : L *ᵥ v = v) (hLTv : L.transpose *ᵥ v = v)
    (hcon : ∀ x : Fin d → ℝ, ∑ i, (L *ᵥ x) i ^ 2 ≤ ∑ i, x i ^ 2) :
    (∀ x : Fin d → ℝ, ∑ i, x i ^ 2 = 1 → ∑ i, x i * v i = 0 →
      ∑ i, (L *ᵥ x) i ^ 2 ≤ sigma2 L ^ 2) ∧
    (∃ x : Fin d → ℝ, (∑ i, x i ^ 2 = 1) ∧ (∑ i, x i * v i = 0) ∧
      ∑ i, (L *ᵥ x) i ^ 2 = sigma2 L ^ 2) := by
  classical
  let n := Fintype.card (Fin d)
  have hn : 1 < n := by simpa [n] using hd
  letI : NeZero n := ⟨by omega⟩
  let hT := Matrix.isHermitian_iff_isSymmetric.mp (gram_isHermitian L)
  let b := hT.eigenvectorBasis finrank_euclideanSpace
  let lam : Fin n → ℝ := gramEig₀ L
  let w : Fin n → ℝ := fun i => b.repr (WithLp.toLp 2 v) i
  have hdiag (x : EuclideanSpace ℝ (Fin d)) (i : Fin n) :
      b.repr (Matrix.toEuclideanLin (gram L) x) i = lam i * b.repr x i :=
    hT.eigenvectorBasis_apply_self_apply finrank_euclideanSpace x i
  have hnorm (x : EuclideanSpace ℝ (Fin d)) :
      ∑ i, b.repr x i * b.repr x i = ∑ j, x j * x j := spectral_repr_dot b x x
  have hray (x : Fin d → ℝ) :
      ∑ i, lam i * (b.repr (WithLp.toLp 2 x) i * b.repr (WithLp.toLp 2 x) i) =
        ∑ i, (L *ᵥ x) i ^ 2 := by
    calc
      _ = ∑ i, b.repr (WithLp.toLp 2 x) i *
          b.repr (Matrix.toEuclideanLin (gram L) (WithLp.toLp 2 x)) i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hdiag]
        ring
      _ = ∑ j, x j * (gram L *ᵥ x) j := spectral_repr_dot b _ _
      _ = _ := spectral_gram_dot L x
  have hw : ∑ i, w i * w i = 1 := (hnorm (WithLp.toLp 2 v)).trans hv
  have hAv : Matrix.toEuclideanLin (gram L) (WithLp.toLp 2 v) = WithLp.toLp 2 v := by
    change WithLp.toLp 2 ((L.transpose * L) *ᵥ v) = _
    rw [← Matrix.mulVec_mulVec, hLv, hLTv]
  have hmem (i : Fin n) (hi : w i ≠ 0) : lam i = 1 := by
    have hh := hdiag (WithLp.toLp 2 v) i
    rw [hAv] at hh
    have hh' : (lam i - 1) * w i = 0 := by change b.repr _ i = _ at hh; dsimp [w]; nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh').resolve_right hi)
  have hle : lam 0 ≤ 1 := gramEig₀_le_one L hcon 0
  have hanti : Antitone lam := (gram_isHermitian L).eigenvalues₀_antitone
  have hsecond := second_rayleigh lam w hanti hw hle hmem hn
  have hsigma : sigma2 L ^ 2 = lam 1 := by
    rw [sigma2, dif_pos hd, Real.sq_sqrt (le_max_left _ _),
      max_eq_right (gramEig₀_nonneg L _)]
    congr 2
    exact (Nat.mod_eq_of_lt hn).symm
  constructor
  · intro x hx hxv
    rw [hsigma, ← hray x]
    apply hsecond.1 (fun i => b.repr (WithLp.toLp 2 x) i)
    · simpa only [pow_two] using (hnorm (WithLp.toLp 2 x)).trans (by simpa [pow_two] using hx)
    · exact (spectral_repr_dot b (WithLp.toLp 2 x) (WithLp.toLp 2 v)).trans hxv
  · obtain ⟨y, hy, hyw, hyray⟩ := hsecond.2
    let x : Fin d → ℝ := WithLp.ofLp (b.repr.symm (WithLp.toLp 2 y))
    have hrepr : b.repr (WithLp.toLp 2 x) = WithLp.toLp 2 y := by simp [x]
    refine ⟨x, ?_, ?_, ?_⟩
    · have hh := hnorm (WithLp.toLp 2 x)
      rw [hrepr] at hh
      simpa only [pow_two] using hh.symm.trans hy
    · have hh := spectral_repr_dot b (WithLp.toLp 2 x) (WithLp.toLp 2 v)
      rw [hrepr] at hh
      exact hh.symm.trans hyw
    · rw [hsigma, ← hray x, hrepr]
      exact hyray


/-- The second singular value bounds the action on every vector perpendicular to `v`. -/
theorem sigma2_bound_fixed [DecidableEq (Fin d)] (L : Matrix (Fin d) (Fin d) ℝ)
    (v : Fin d → ℝ) (hd : 1 < d)
    (hv : ∑ i, v i * v i = 1)
    (hLv : L *ᵥ v = v) (hLTv : L.transpose *ᵥ v = v)
    (hcon : ∀ x : Fin d → ℝ, ∑ i, (L *ᵥ x) i ^ 2 ≤ ∑ i, x i ^ 2)
    (x : Fin d → ℝ) (hxv : ∑ i, x i * v i = 0) :
    ∑ i, (L *ᵥ x) i ^ 2 ≤ sigma2 L ^ 2 * ∑ i, x i ^ 2 := by
  classical
  let q : ℝ := ∑ i, x i ^ 2
  have hq : 0 ≤ q := Finset.sum_nonneg fun _ _ => sq_nonneg _
  by_cases hq0 : q = 0
  · have hx0 : x = 0 := by
      funext i
      have hi : x i ^ 2 ≤ q := Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      have : x i ^ 2 = 0 := le_antisymm (hq0 ▸ hi) (sq_nonneg _)
      exact sq_eq_zero_iff.mp this
    simp [hx0]
  · let c := Real.sqrt q
    have hc : 0 < c := Real.sqrt_pos.mpr (lt_of_le_of_ne hq (Ne.symm hq0))
    have hc2 : c ^ 2 = q := Real.sq_sqrt hq
    let y : Fin d → ℝ := fun i => x i / c
    have hy : ∑ i, y i ^ 2 = 1 := by
      simp only [y, div_pow, ← Finset.sum_div]
      rw [hc2]
      exact div_self hq0
    have hyv : ∑ i, y i * v i = 0 := by
      simp only [y, div_mul_eq_mul_div, ← Finset.sum_div, hxv, zero_div]
    have hyL (i : Fin d) : (L *ᵥ y) i = (L *ᵥ x) i / c := by
      simp only [Matrix.mulVec, dotProduct, y, ← mul_div_assoc, ← Finset.sum_div]
    have hbound := (sigma2_rayleigh_fixed L v hd hv hLv hLTv hcon).1 y hy hyv
    simp only [hyL, div_pow, ← Finset.sum_div] at hbound
    have hbound' := (div_le_iff₀ (sq_pos_of_pos hc)).mp hbound
    simpa only [hc2, mul_comm] using hbound'

/-- Squared second singular values are submultiplicative for the Markov powers. -/
theorem sigma2_Lk_submul [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S) (r s : ℕ) :
    sigma2 (Lk S st (r+s)) ^ 2 ≤
      sigma2 (Lk S st r) ^ 2 * sigma2 (Lk S st s) ^ 2 := by
  classical
  by_cases hd : 1 < d
  · have hfixed (t : ℕ) := sigma2_rayleigh_fixed (Lk S st t) (stVec st) hd
        (stVec_sq_sum st) (Lk_mulVec_stVec S st t)
        (Lk_transpose_mulVec_stVec S st t) (Lk_contraction S st t)
    obtain ⟨x, hx, hxv, hxr⟩ := (hfixed (r+s)).2
    have horth : ∑ i, (Lk S st s *ᵥ x) i * stVec st i = 0 := by
      change (Lk S st s *ᵥ x) ⬝ᵥ stVec st = 0
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
        Lk_transpose_mulVec_stVec]
      exact (dotProduct_comm (stVec st) x).trans hxv
    have hr := sigma2_bound_fixed (Lk S st r) (stVec st) hd (stVec_sq_sum st)
      (Lk_mulVec_stVec S st r) (Lk_transpose_mulVec_stVec S st r)
      (Lk_contraction S st r) (Lk S st s *ᵥ x) horth
    have hs := (hfixed s).1 x hx hxv
    calc
      sigma2 (Lk S st (r+s)) ^ 2 = ∑ i, (Lk S st r *ᵥ (Lk S st s *ᵥ x)) i ^ 2 := by
        rw [← hxr, Lk_add, Matrix.mulVec_mulVec]
      _ ≤ sigma2 (Lk S st r) ^ 2 * ∑ i, (Lk S st s *ᵥ x) i ^ 2 := hr
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
  · simp [sigma2, hd]


/-- GapAx for `aK`: the range is `[0,1]`, and the squared second singular
value contracts multiplicatively by its exact Rayleigh characterization on `v⊥`. -/
theorem aK_gapAx [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S) :
    GapAx (aK S st) := by
  have hmem := aK_mem S st
  refine ⟨fun t => (hmem t).1, fun t => (hmem t).2, ?_⟩
  intro r s
  simpa only [aK, aOf, sub_sub_cancel] using sigma2_Lk_submul S st r s

/-- Submultiplicativity `b_{r+s} ≤ b_r b_s`. -/
theorem bNorm_mul [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S) (r s : ℕ) :
    bNorm S st (r + s) ≤ bNorm S st r * bNorm S st s :=
  gapB_mul (aK_gapAx S st) r s

/-- Range `0 ≤ b_t ≤ 1`. -/
theorem bNorm_mem [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S) (t : ℕ) :
    0 ≤ bNorm S st t ∧ bNorm S st t ≤ 1 :=
  ⟨gapB_nonneg _ _, gapB_le_one (aK_gapAx S st) t⟩

/-- Relation `a_t = 1 - b_t^2`. -/
theorem aK_eq_one_sub_bNorm_sq [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S)
    (t : ℕ) : aK S st t = 1 - bNorm S st t ^ 2 := by
  have h : bNorm S st t ^ 2 = 1 - aK S st t :=
    gapB_sq (aK_gapAx S st).le_one t
  linarith

/-- Maximizing lag `k0` satisfies `k0 ≤ ⌊1/γ⌋`. -/
theorem exists_max_lag [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) :
    ∃ k0 : ℕ, 0 < k0 ∧ aK S st k0 / k0 = gammaPS S st
      ∧ (k0 : ℝ) ≤ 1 / gammaPS S st := by
  have hax := aK_gapAx S st
  simpa [gammaPS_eq_gapGamma] using gapGamma_exists_max hax (by simpa [gammaPS_eq_gapGamma] using hgap)

/-- Lemma 1, upper and lower gaps of powers, plus `a_t > 1/2` beyond the inverse gap. -/
theorem lemma_1 [DecidableEq (Fin d)] (S : Stoch d) (st : Stationary S)
    (hgap : 0 < gammaPS S st) :
    (∀ k : ℕ, 0 < k →
      (1 / 4 : ℝ) * min (k * gammaPS S st) 1 ≤
          gammaPS (S.pow k) (stationaryPow S st k)
        ∧ gammaPS (S.pow k) (stationaryPow S st k) ≤ min (k * gammaPS S st) 1)
    ∧ (∀ t : ℕ, 0 < t → (1 / (gammaPS S st) : ℝ) ≤ t → (1 / 2 : ℝ) < aK S st t) := by
  have hax := aK_gapAx S st
  have hγ : 0 < gapGamma (aK S st) := by simpa [gammaPS_eq_gapGamma] using hgap
  have := gapAx_lemma_1 hax hγ
  refine ⟨?_, this.2⟩
  intro k hk
  have h := this.1 k hk
  -- `gammaPS (S.pow k) (stationaryPow ...) = gapGamma (fun j => aK S st (k * j))`
  have hgamma : gammaPS (S.pow k) (stationaryPow S st k)
      = gapGamma (fun j => aK S st (k * j)) := by
    rw [gammaPS_eq_gapGamma]
    congr 1
    funext j
    exact aK_pow S st k j
  rw [hgamma, gammaPS_eq_gapGamma]
  exact h

end PsgEst
