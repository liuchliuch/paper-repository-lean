import Paper17.Support
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.MetricSpace.Closeds
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.Convex.Segment
import Mathlib.LinearAlgebra.Pi

/-!
# Comparison of the Hausdorff and symmetric-difference metrics (paper §2.1)

Proposition 2.5.  The Hausdorff metric and the volume-of-symmetric-difference
metric induce the same topology on `𝒞_p(n)`.

We realize the symmetric-difference volume `d_V(K, L) = vol (K ∆ L)` via
`MeasureTheory.volume` on the ambient space `V n = Fin n → ℝ`, and follow the
two inequalities of the paper:

* If `d_H(K,L) = δ < r` and `r • B ⊂ K`, then
  `(1 - δ/r) • K ⊂ L ⊂ (1 + δ/r) • K` and
  `d_V(K,L) ≤ ((1 + δ/r)^n - (1 - δ/r)^n) • Vol(K)`.
* Conversely, from `d_V(K, L_j) → 0` one gets an interior ball
  `r₀ • B ⊂ L_j` eventually, and the ball-inside estimate
  `d_V ≥ κ_n • (r₀ • d_H / (2(R + r₀)))^n` forces `d_H(K, L_j) → 0`.

Sequences converge for one metric iff for the other; since these are metric
(hence sequential) spaces, this identifies the two topologies.
-/

noncomputable section

open scoped Pointwise Topology BigOperators symmDiff ENNReal

open MeasureTheory Set Metric Filter Finset

namespace Paper17

variable {n : ℕ}

/-! ## The symmetric-difference volume -/

/-- Volume of the symmetric difference of two sets in `V n`.
This is the paper's `d_V` (unnormalized). -/
def symmDiffVol (K L : Set (V n)) : ℝ :=
  ENNReal.toReal (MeasureTheory.volume (K ∆ L))

/-- The volume of the unit ball of `V n`; this is the paper's `κ_n`. -/
def kappa (n : ℕ) : ℝ :=
  ENNReal.toReal (MeasureTheory.volume (Metric.ball (0 : V n) 1))

theorem kappa_nonneg (n : ℕ) : 0 ≤ kappa n :=
  ENNReal.toReal_nonneg

theorem symmDiffVol_nonneg (K L : Set (V n)) : 0 ≤ symmDiffVol K L :=
  ENNReal.toReal_nonneg

theorem symmDiffVol_comm (K L : Set (V n)) : symmDiffVol K L = symmDiffVol L K := by
  unfold symmDiffVol
  rw [symmDiff_comm]

theorem symmDiffVol_self (K : Set (V n)) : symmDiffVol K K = 0 := by
  unfold symmDiffVol
  have h : (K : Set (V n)) ∆ K = ∅ := by
    rw [symmDiff_self]
    simp
  rw [h, measure_empty, ENNReal.toReal_zero]

theorem symmDiffVol_eq_toReal (K L : Set (V n)) :
    symmDiffVol K L = ENNReal.toReal (MeasureTheory.volume (K ∆ L)) := rfl

/-- Finiteness of the symmetric-difference volume for compact sets:
`K ∆ L ⊆ K ∪ L` has finite measure. -/
theorem volume_symmDiff_ne_top_of_isCompact {K L : Set (V n)}
    (hK : IsCompact K) (hL : IsCompact L) :
    MeasureTheory.volume (K ∆ L) ≠ ∞ := by
  have h1 : K ∆ L ⊆ K ∪ L := by
    intro x hx
    have hx' : x ∈ K ∆ L := hx
    rw [mem_symmDiff] at hx'
    rw [mem_union]
    tauto
  have h2 : MeasureTheory.volume (K ∪ L) < ∞ :=
    (hK.union hL).measure_lt_top
  exact ne_top_of_le_ne_top h2.ne (measure_mono h1)

/-- Triangle inequality for the symmetric-difference volume.
This is the pseudometric axiom of `d_V` on sets of finite measure. -/
theorem symmDiffVol_triangle (s t u : Set (V n))
    (hs : MeasureTheory.volume s ≠ ∞)
    (ht : MeasureTheory.volume t ≠ ∞)
    (hu : MeasureTheory.volume u ≠ ∞) :
    symmDiffVol s u ≤ symmDiffVol s t + symmDiffVol t u := by
  unfold symmDiffVol
  have htri : MeasureTheory.volume (s ∆ u)
      ≤ MeasureTheory.volume (s ∆ t) + MeasureTheory.volume (t ∆ u) :=
    measure_symmDiff_le _ _ _
  have h1 : MeasureTheory.volume (s ∆ t) ≤ MeasureTheory.volume s + MeasureTheory.volume t := by
    calc MeasureTheory.volume (s ∆ t) ≤ MeasureTheory.volume (s ∪ t) :=
        measure_mono Set.symmDiff_subset_union
      _ ≤ MeasureTheory.volume s + MeasureTheory.volume t := measure_union_le _ _
  have h2 : MeasureTheory.volume (t ∆ u) ≤ MeasureTheory.volume t + MeasureTheory.volume u := by
    calc MeasureTheory.volume (t ∆ u) ≤ MeasureTheory.volume (t ∪ u) :=
        measure_mono Set.symmDiff_subset_union
      _ ≤ MeasureTheory.volume t + MeasureTheory.volume u := measure_union_le _ _
  have hf1 : MeasureTheory.volume (s ∆ t) ≠ ∞ :=
    ne_top_of_le_ne_top
      (ne_of_lt (ENNReal.add_lt_top.mpr
        ⟨lt_top_iff_ne_top.mpr hs, lt_top_iff_ne_top.mpr ht⟩)) h1
  have hf2 : MeasureTheory.volume (t ∆ u) ≠ ∞ :=
    ne_top_of_le_ne_top
      (ne_of_lt (ENNReal.add_lt_top.mpr
        ⟨lt_top_iff_ne_top.mpr ht, lt_top_iff_ne_top.mpr hu⟩)) h2
  have hsum_ne : MeasureTheory.volume (s ∆ t) + MeasureTheory.volume (t ∆ u) ≠ ∞ :=
    ENNReal.add_ne_top.mpr ⟨hf1, hf2⟩
  have hleft_ne : MeasureTheory.volume (s ∆ u) ≠ ∞ :=
    ne_top_of_le_ne_top hsum_ne htri
  have hadd : (MeasureTheory.volume (s ∆ t) + MeasureTheory.volume (t ∆ u)).toReal
      = (MeasureTheory.volume (s ∆ t)).toReal + (MeasureTheory.volume (t ∆ u)).toReal :=
    ENNReal.toReal_add hf1 hf2
  have hle : (MeasureTheory.volume (s ∆ u)).toReal
      ≤ (MeasureTheory.volume (s ∆ t) + MeasureTheory.volume (t ∆ u)).toReal :=
    (ENNReal.toReal_le_toReal hleft_ne hsum_ne).mpr htri
  linarith

/-! ## Volume of dilations -/

/-- The dimension of `V n` as a real vector space. -/
theorem finrank_V : Module.finrank ℝ (V n) = n := by
  have h := Module.finrank_fintype_fun_eq_card (R := ℝ) (η := Fin n)
  simp [V, Fintype.card_fin] at h ⊢

/-- Lebesgue measure scales by `t ^ n` under dilation by `t ≥ 0`. -/
theorem volume_smul_of_nonneg {t : ℝ} (ht : 0 ≤ t) (s : Set (V n)) :
    MeasureTheory.volume (t • s)
      = ENNReal.ofReal (t ^ n) * MeasureTheory.volume s := by
  have h := MeasureTheory.Measure.addHaar_smul_of_nonneg
    (μ := (MeasureTheory.volume : Measure (V n))) ht s
  rw [h, finrank_V]

/-- `toReal` form of dilation scaling, when the original volume is finite. -/
theorem volume_smul_toReal {t : ℝ} (ht : 0 ≤ t) {s : Set (V n)}
    (hs : MeasureTheory.volume s ≠ ∞) :
    (MeasureTheory.volume (t • s)).toReal
      = t ^ n * (MeasureTheory.volume s).toReal := by
  rw [volume_smul_of_nonneg ht s]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- n = 0: t ^ 0 = 1
    have h1 : t ^ n = 1 := by rw [hn, pow_zero]
    rw [h1, ENNReal.ofReal_one, one_mul, one_mul]
  · by_cases ht0 : t = 0
    · subst ht0
      have hz : (0 : ℝ) ^ n = 0 := zero_pow hn.ne'
      rw [hz, ENNReal.ofReal_zero, zero_mul, ENNReal.toReal_zero, zero_mul]
    · have hmul : ENNReal.ofReal (t ^ n) * MeasureTheory.volume s ≠ ∞ :=
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hs
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg ht n)]

/-! ## Dilated inclusions and the volume bound (paper, first inequality) -/

/-- Convexity helper: if `0 ∈ K`, `K` is convex, and `0 ≤ t ≤ 1`, then
`t • K ⊆ K`. -/
theorem smul_subset_self {K : Set (V n)} {t : ℝ} (h0 : (0 : V n) ∈ K)
    (hconv : Convex ℝ K) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t • K ⊆ K := by
  have hsc : StarConvex ℝ 0 K := hconv.starConvex h0
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.mp hx
  exact hsc.smul_mem hy ht0 ht1

/-- Convexity helper: if `0 ∈ K`, `K` is convex, and `t ≥ 1`, then
`K ⊆ t • K`. -/
theorem subset_smul_self {K : Set (V n)} {t : ℝ} (h0 : (0 : V n) ∈ K)
    (hconv : Convex ℝ K) (ht : 1 ≤ t) :
    K ⊆ t • K := by
  have hsc : StarConvex ℝ 0 K := hconv.starConvex h0
  intro x hx
  exact hsc.mem_smul hx ht

/-- If `(1-t) • K ⊆ L`, `L ⊆ (1+t) • K`, `0 ∈ K`, `K` is convex,
and `0 < t ≤ 1`, then `K ∆ L ⊆ (1+t) • K \ (1-t) • K`.
This is the set-algebra half of the paper's volume estimate. -/
theorem symmDiff_subset_annulus {K L : Set (V n)} {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (h0 : (0 : V n) ∈ K) (hconv : Convex ℝ K)
    (h1 : (1 - t) • K ⊆ L) (h2 : L ⊆ (1 + t) • K) :
    K ∆ L ⊆ ((1 + t) • K) \ ((1 - t) • K) := by
  have hnest : (1 - t) • K ⊆ (1 + t) • K := by
    have h1t : 0 ≤ 1 - t := by linarith
    have h2t : 1 - t ≤ 1 := by linarith
    have h3t : 1 ≤ 1 + t := by linarith
    exact (smul_subset_self h0 hconv h1t h2t).trans (subset_smul_self h0 hconv h3t)
  have hsub1 : (1 - t) • K ⊆ K := smul_subset_self h0 hconv (by linarith) (by linarith)
  have hsub2 : K ⊆ (1 + t) • K := subset_smul_self h0 hconv (by linarith)
  intro x hx
  have hx' : x ∈ K ∆ L := hx
  rw [Set.mem_symmDiff] at hx'
  constructor
  · rcases hx' with ⟨hxK, hxL⟩ | ⟨hxL, hxK⟩
    · exact hsub2 hxK
    · exact h2 hxL
  · intro hxin
    rcases hx' with ⟨hxK, hxL⟩ | ⟨hxL, hxK⟩
    · exact hxL (h1 hxin)
    · exact hxK (hsub1 hxin)

/-- Volume bound from dilated inclusions: if `(1-t)K ⊆ L ⊆ (1+t)K` with
`0 ∈ K`, `K` convex, `K` compact, and `0 < t ≤ 1`, then
`d_V(K,L) ≤ ((1+t)^n - (1-t)^n) Vol(K)`.
This is the paper's estimate `d_V ≤ ((1+δ/r)^n - (1-δ/r)^n) Vol(K)`. -/
theorem symmDiffVol_le_of_dilated_inclusions {K L : Set (V n)} {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (h0 : (0 : V n) ∈ K) (hconv : Convex ℝ K)
    (hK : IsCompact K) (h1 : (1 - t) • K ⊆ L) (h2 : L ⊆ (1 + t) • K) :
    symmDiffVol K L ≤ ((1 + t) ^ n - (1 - t) ^ n)
      * ENNReal.toReal (MeasureTheory.volume K) := by
  have hvolK : MeasureTheory.volume K ≠ ∞ := hK.measure_ne_top
  have hKsub : K ∆ L ⊆ ((1 + t) • K) \ ((1 - t) • K) :=
    symmDiff_subset_annulus ht ht1 h0 hconv h1 h2
  have hmono : MeasureTheory.volume (K ∆ L)
      ≤ MeasureTheory.volume (((1 + t) • K) \ ((1 - t) • K)) :=
    measure_mono hKsub
  have hnest : (1 - t) • K ⊆ (1 + t) • K := by
    have h1t : 0 ≤ 1 - t := by linarith
    have h2t : 1 - t ≤ 1 := by linarith
    have h3t : 1 ≤ 1 + t := by linarith
    exact (smul_subset_self h0 hconv h1t h2t).trans (subset_smul_self h0 hconv h3t)
  have hdiff : MeasureTheory.volume (((1 + t) • K) \ ((1 - t) • K))
      = MeasureTheory.volume ((1 + t) • K) - MeasureTheory.volume ((1 - t) • K) := by
    have hnm : NullMeasurableSet ((1 - t) • K) MeasureTheory.volume :=
      (IsCompact.nullMeasurableSet (hK.smul _))
    have hfin : MeasureTheory.volume ((1 - t) • K) ≠ ∞ := (hK.smul _).measure_ne_top
    exact measure_diff hnest hnm hfin
  have hsmul1 : MeasureTheory.volume ((1 + t) • K)
      = ENNReal.ofReal ((1 + t) ^ n) * MeasureTheory.volume K :=
    volume_smul_of_nonneg (by linarith) K
  have hsmul2 : MeasureTheory.volume ((1 - t) • K)
      = ENNReal.ofReal ((1 - t) ^ n) * MeasureTheory.volume K :=
    volume_smul_of_nonneg (by linarith) K
  have h1t0 : 0 ≤ 1 - t := by linarith
  have h1tp : 0 ≤ 1 + t := by linarith
  have hsub : (1 - t) ^ n ≤ (1 + t) ^ n := by
    gcongr; linarith
  have hvol_le : MeasureTheory.volume (K ∆ L)
      ≤ ENNReal.ofReal ((1 + t) ^ n - (1 - t) ^ n) * MeasureTheory.volume K := by
    calc MeasureTheory.volume (K ∆ L)
        ≤ MeasureTheory.volume (((1 + t) • K) \ ((1 - t) • K)) := hmono
      _ = MeasureTheory.volume ((1 + t) • K) - MeasureTheory.volume ((1 - t) • K) := hdiff
      _ = ENNReal.ofReal ((1 + t) ^ n) * MeasureTheory.volume K
          - ENNReal.ofReal ((1 - t) ^ n) * MeasureTheory.volume K := by rw [hsmul1, hsmul2]
      _ = (ENNReal.ofReal ((1 + t) ^ n) - ENNReal.ofReal ((1 - t) ^ n))
          * MeasureTheory.volume K := by
          rw [← ENNReal.sub_mul (fun _ _ => hvolK)]
      _ = ENNReal.ofReal ((1 + t) ^ n - (1 - t) ^ n) * MeasureTheory.volume K := by
          congr 1
          exact (ENNReal.ofReal_sub ((1 + t) ^ n) (pow_nonneg h1t0 n)).symm
  have hfin2 : (ENNReal.ofReal ((1 + t) ^ n - (1 - t) ^ n) * MeasureTheory.volume K) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvolK
  have htoReal : symmDiffVol K L
      = ENNReal.toReal (MeasureTheory.volume (K ∆ L)) := rfl
  rw [htoReal]
  have hle : ENNReal.toReal (MeasureTheory.volume (K ∆ L))
      ≤ ENNReal.toReal (ENNReal.ofReal ((1 + t) ^ n - (1 - t) ^ n) * MeasureTheory.volume K) :=
    (ENNReal.toReal_le_toReal (ne_top_of_le_ne_top hfin2 hvol_le) hfin2).mpr hvol_le
  have hcalc : ENNReal.toReal (ENNReal.ofReal ((1 + t) ^ n - (1 - t) ^ n) * MeasureTheory.volume K)
      = ((1 + t) ^ n - (1 - t) ^ n) * ENNReal.toReal (MeasureTheory.volume K) := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by
      have h : (1 - t) ^ n ≤ (1 + t) ^ n := hsub
      linarith)]
  rw [hcalc] at hle
  exact hle

/-! ## Support functions, pairings, and norm bounds -/

/-- If `d_H(K,L) < r` and `r • B ⊆ K`, then `(1 - δ/r) • K ⊆ L ⊆ (1 + δ/r) • K`
where `δ = d_H(K,L)`.  This is the paper's first step:
`h_K - δ ≤ h_L ≤ h_K + δ` and `h_K ≥ r` give the dilated inclusions. -/
theorem dilated_inclusions_of_hausdorffDist_lt
    {K L : Set (V n)} (hK : IsCompact K) (hneK : K.Nonempty)
    (hconvK : Convex ℝ K)
    (hL : IsCompact L) (hneL : L.Nonempty) (hconvL : Convex ℝ L)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδr : δ < r)
    (hrB : Metric.ball (0 : V n) r ⊆ K)
    (hH : Metric.hausdorffDist K L = δ) :
    (1 - δ / r) • K ⊆ L ∧ L ⊆ (1 + δ / r) • K := by
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hδr0 : 0 < δ / r := by positivity
  have hδr1 : δ / r < 1 := by rwa [div_lt_one hr]
  have h1m : 0 ≤ 1 - δ / r := by linarith
  have h1p : 0 ≤ 1 + δ / r := by positivity
  -- support-function sandwich from Hausdorff distance
  have hsubK : ∀ u : V n, supportFunction K u - supportFunction L u
      ≤ δ * (∑ i, |u i|) := by
    intro u
    have h := supportFunction_sub_le_of_hausdorffDist hK hneK hL hneL u
    rwa [hH] at h
  have hsubL : ∀ u : V n, supportFunction L u - supportFunction K u
      ≤ δ * (∑ i, |u i|) := by
    intro u
    have h := supportFunction_sub_le_of_hausdorffDist' hK hneK hL hneL u
    rwa [hH] at h
  -- interior ball forces `h_K(u) ≥ r * ∑|u i|`
  have hball : ∀ u : V n, r * (∑ i, |u i|) ≤ supportFunction K u :=
    fun u => supportFunction_ge_of_ball_subset hK hr hrB u
  -- dilations scale support functions
  have hsmulL : ∀ u : V n,
      supportFunction ((1 - δ / r) • K) u = (1 - δ / r) * supportFunction K u := by
    intro u
    exact supportFunction_smul' hneK h1m u
  have hsmulR : ∀ u : V n,
      supportFunction ((1 + δ / r) • K) u = (1 + δ / r) * supportFunction K u := by
    intro u
    exact supportFunction_smul' hneK h1p u
  -- `(1 - δ/r) • K ⊆ L`
  have hin1 : (1 - δ / r) • K ⊆ L := by
    apply subset_of_forall_dot_le_supportFunction hL hneL hconvL
    intro u x hx
    have hxs : dot u x ≤ supportFunction ((1 - δ / r) • K) u :=
      supportFunction_ub' (hK.smul _) hx
    rw [hsmulL] at hxs
    have hkey : (1 - δ / r) * supportFunction K u ≤ supportFunction L u := by
      have hb := hball u
      have hs := hsubK u
      have hS : 0 ≤ ∑ i, |u i| := Finset.sum_nonneg fun i _ => abs_nonneg _
      -- `(δ/r) * h_K ≥ (δ/r) * r * S = δ * S`, hence
      -- `(1-δ/r) h_K = h_K - (δ/r) h_K ≤ h_K - δ S ≤ h_L`
      have hmul : (δ / r) * supportFunction K u ≥ δ * (∑ i, |u i|) := by
        have hle := mul_le_mul_of_nonneg_left hb (le_of_lt hδr0)
        have hcancel : (δ / r) * (r * (∑ i, |u i|)) = δ * (∑ i, |u i|) := by
          rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hr)]
        rw [hcancel] at hle
        exact hle
      nlinarith
    exact le_trans hxs hkey
  -- `L ⊆ (1 + δ/r) • K`
  have hin2 : L ⊆ (1 + δ / r) • K := by
    apply subset_of_forall_dot_le_supportFunction (hK.smul _) hneK.smul_set (hconvK.smul _)
    intro u x hx
    have hxs : dot u x ≤ supportFunction L u := supportFunction_ub' hL hx
    have hkey : supportFunction L u ≤ (1 + δ / r) * supportFunction K u := by
      have hb := hball u
      have hs := hsubL u
      have hS : 0 ≤ ∑ i, |u i| := Finset.sum_nonneg fun i _ => abs_nonneg _
      -- `h_L ≤ h_K + δ S ≤ h_K + (δ/r) r S ≤ h_K + (δ/r) h_K`
      have hmul : (δ / r) * supportFunction K u ≥ δ * (∑ i, |u i|) := by
        have hle := mul_le_mul_of_nonneg_left hb (le_of_lt hδr0)
        have hcancel : (δ / r) * (r * (∑ i, |u i|)) = δ * (∑ i, |u i|) := by
          rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt hr)]
        rw [hcancel] at hle
        exact hle
      nlinarith
    have hsm := hsmulR u
    rw [hsm]
    exact le_trans hxs hkey
  exact ⟨hin1, hin2⟩

/-- Combined first inequality: if `d_H(K,L) = δ < r` and `rB ⊆ K`, then
`d_V(K,L) ≤ ((1+δ/r)^n - (1-δ/r)^n) Vol(K)`.
This tends to zero as `δ → 0`, so `d_H → 0` implies `d_V → 0`. -/
theorem symmDiffVol_le_of_hausdorffDist_lt
    {K L : Set (V n)} (hK : IsCompact K) (hneK : K.Nonempty) (h0 : (0 : V n) ∈ K)
    (hconv : Convex ℝ K)
    (hL : IsCompact L) (hneL : L.Nonempty) (hconvL : Convex ℝ L)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hδr : δ < r)
    (hrB : Metric.ball (0 : V n) r ⊆ K)
    (hH : Metric.hausdorffDist K L = δ) :
    symmDiffVol K L ≤ ((1 + δ / r) ^ n - (1 - δ / r) ^ n)
      * ENNReal.toReal (MeasureTheory.volume K) := by
  have hinc : (1 - δ / r) • K ⊆ L ∧ L ⊆ (1 + δ / r) • K :=
    dilated_inclusions_of_hausdorffDist_lt hK hneK hconv hL hneL hconvL
      hr hδ hδr hrB hH
  have h1 : (1 - δ / r) • K ⊆ L := hinc.1
  have h2 : L ⊆ (1 + δ / r) • K := hinc.2
  have htt : 0 < δ / r := by positivity
  have htt1 : δ / r ≤ 1 := by
    have : δ / r < 1 := by
      rw [div_lt_one hr]
      exact hδr
    linarith
  exact symmDiffVol_le_of_dilated_inclusions htt htt1 h0 hconv hK h1 h2

/-! ## Converse: small volume forces small Hausdorff distance -/

/-- `d_H(K, L_j) → 0` implies `d_V(K, L_j) → 0`, via the first inequality
`d_V ≤ ((1+δ/r)^n - (1-δ/r)^n) Vol(K)` with `δ = d_H(K, L_j) < r`. -/
theorem symmDiffVol_tendsto_zero_of_hausdorffDist_tendsto_zero
    {K : Set (V n)} (hK : IsCompact K) (hneK : K.Nonempty)
    (h0 : (0 : V n) ∈ K) (hconv : Convex ℝ K)
    {r : ℝ} (hr : 0 < r) (hrB : Metric.ball (0 : V n) r ⊆ K)
    (L : ℕ → Set (V n))
    (hLc : ∀ j, IsCompact (L j)) (hLne : ∀ j, (L j).Nonempty)
    (hconvL : ∀ j, Convex ℝ (L j))
    (hTendsto : Tendsto (fun j => Metric.hausdorffDist K (L j)) atTop (𝓝 0)) :
    Tendsto (fun j => symmDiffVol K (L j)) atTop (𝓝 0) := by
  -- For each j let δ_j = d_H(K, L_j).  For j large, δ_j < r, so
  -- d_V(K, L_j) ≤ ((1+δ_j/r)^n - (1-δ_j/r)^n) Vol(K) → 0 as δ_j → 0.
  -- The bound `((1+δ/r)^n - (1-δ/r)^n) → 0` as `δ → 0` is continuity of
  -- the polynomial function `δ ↦ ((1+δ/r)^n - (1-δ/r)^n)`.
  -- Squeeze: 0 ≤ d_V ≤ bound(δ_j) → 0.
  set volK : ℝ := ENNReal.toReal (MeasureTheory.volume K) with hvolK
  have hvolK0 : 0 ≤ volK := ENNReal.toReal_nonneg
  -- the bounding function of δ
  set f : ℝ → ℝ := fun d => ((1 + d / r) ^ n - (1 - d / r) ^ n) * volK with hf
  have hf0 : f 0 = 0 := by
    simp [hf, zero_div, sub_self, zero_mul]
  -- f is continuous at 0 (polynomial)
  have hfc : ContinuousAt f 0 := by
    refine ContinuousAt.mul (ContinuousAt.sub ?_ ?_) continuousAt_const
    · exact continuousAt_const.add (continuousAt_id.div_const r) |>.pow n
    · exact continuousAt_const.sub (continuousAt_id.div_const r) |>.pow n
  have hft : Tendsto (fun j => f (Metric.hausdorffDist K (L j))) atTop (𝓝 0) := by
    have hcomp := hfc.tendsto.comp (hTendsto : Tendsto
      (fun j => Metric.hausdorffDist K (L j)) atTop (𝓝 0))
    -- f is applied to d_H, and f 0 = 0, so this is Tendsto ... (𝓝 (f 0)) = 𝓝 0
    simpa [hf0] using hcomp
  -- for j large, d_V ≤ f(d_H)
  have hbound : ∀ᶠ j in atTop,
      symmDiffVol K (L j) ≤ f (Metric.hausdorffDist K (L j)) := by
    -- for j large, d_H < r; case split on d_H = 0 vs d_H > 0
    filter_upwards [tendsto_order.1 hTendsto |>.2 r hr] with j hj
    by_cases hz : Metric.hausdorffDist K (L j) = 0
    · -- d_H = 0 implies K = L j (compact), so d_V = 0 ≤ f 0 = 0
      have hfin : EMetric.hausdorffEdist K (L j) ≠ ⊤ :=
        Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded hneK (hLne j)
          hK.isBounded (hLc j).isBounded
      have heq : K = L j :=
        (IsClosed.hausdorffDist_zero_iff_eq hK.isClosed (hLc j).isClosed hfin).1 hz
      rw [heq, symmDiffVol_self]
      have h2 : Metric.hausdorffDist (L j) (L j) = 0 := Metric.hausdorffDist_self_zero
      rw [hf, h2]
      show (0:ℝ) ≤ ((1 + (0:ℝ) / r) ^ n - (1 - (0:ℝ) / r) ^ n) * volK
      simp only [zero_div, add_zero, sub_zero, one_pow, sub_self, zero_mul]
      exact le_refl _
    · -- 0 < d_H < r: apply the first inequality
      have hdpos : 0 < Metric.hausdorffDist K (L j) :=
        lt_of_le_of_ne (Metric.hausdorffDist_nonneg) (Ne.symm hz)
      have hlt : Metric.hausdorffDist K (L j) < r := hj
      have h := symmDiffVol_le_of_hausdorffDist_lt hK hneK h0 hconv
        (hLc j) (hLne j) (hconvL j) hr hdpos hlt hrB rfl
      -- h : d_V ≤ ((1 + δ/r)^n - (1-δ/r)^n) * volK
      simpa [hf, volK] using h
  -- squeeze: 0 ≤ d_V ≤ f(d_H) → 0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ => (0 : ℝ)) atTop (𝓝 0)) hft
    (Eventually.of_forall fun j => symmDiffVol_nonneg _ _) hbound


end Paper17
