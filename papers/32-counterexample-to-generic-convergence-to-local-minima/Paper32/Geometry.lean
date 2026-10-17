import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Data.Real.Sign
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

open Set Filter Topology

noncomputable section

namespace Paper32

abbrev Point := ℝ × ℝ

def l1 (z : Point) : ℝ := |z.1| + |z.2|
def lin (v z : Point) : ℝ := v.1 * z.1 + v.2 * z.2
def g (z : Point) : ℝ := min (|z.1| + 2 * |z.2|) (7 * |z.1| - |z.2|)
def F (z : Point) : ℝ := max (g z + 8) (l1 z)
def tilt (v z : Point) : ℝ := F z - lin v z
def U (v : Point) : Prop := |v.1| < 1 / 100 ∧ |v.2| < 1 / 100
def Dstar (z : Point) : Prop := |z.1| < 1 / 80 ∧ |z.2| < 1 / 20

def gradCore (z : Point) : Point :=
  if |z.2| < 2 * |z.1| then (Real.sign z.1, 2 * Real.sign z.2)
  else (7 * Real.sign z.1, -Real.sign z.2)

@[simp] theorem l1_zero : l1 0 = 0 := by simp [l1]
@[simp] theorem g_zero : g 0 = 0 := by simp [g]
@[simp] theorem F_zero : F 0 = 8 := by norm_num [F]
@[simp] theorem tilt_zero (v : Point) : tilt v 0 = 8 := by simp [tilt, lin]

theorem l1_nonneg (z : Point) : 0 ≤ l1 z := add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem g_lower (z : Point) : - l1 z ≤ g z := by
  simp only [g, le_min_iff, l1]
  constructor <;> linarith [abs_nonneg z.1, abs_nonneg z.2]

theorem F_lower (z : Point) : l1 z ≤ F z := le_max_right _ _

theorem F_nonneg (z : Point) : 0 ≤ F z := (l1_nonneg z).trans (F_lower z)

theorem F_eq_core {z : Point} (hz : l1 z < 4) : F z = g z + 8 := by
  exact max_eq_left (by linarith [g_lower z])

theorem g_horizontal {z : Point} (hz : |z.2| ≤ 2 * |z.1|) :
    g z = |z.1| + 2 * |z.2| := by
  exact min_eq_left (by linarith)

theorem g_vertical {z : Point} (hz : 2 * |z.1| ≤ |z.2|) :
    g z = 7 * |z.1| - |z.2| := by
  exact min_eq_right (by linarith)

theorem abs_lin_le (v z : Point) : |lin v z| ≤ max |v.1| |v.2| * l1 z := by
  calc
    |lin v z| ≤ |v.1 * z.1| + |v.2 * z.2| := abs_add_le _ _
    _ = |v.1| * |z.1| + |v.2| * |z.2| := by rw [abs_mul, abs_mul]
    _ ≤ max |v.1| |v.2| * l1 z := by
      unfold l1
      nlinarith [mul_le_mul_of_nonneg_right (le_max_left |v.1| |v.2|) (abs_nonneg z.1),
        mul_le_mul_of_nonneg_right (le_max_right |v.1| |v.2|) (abs_nonneg z.2)]

theorem tilt_lower (v z : Point) :
    (1 - max |v.1| |v.2|) * l1 z ≤ tilt v z := by
  unfold tilt
  have h := abs_lin_le v z
  have h' := le_abs_self (lin v z)
  nlinarith [F_lower z]

theorem U_max {v : Point} (hv : U v) : max |v.1| |v.2| < 1 / 100 :=
  max_lt hv.1 hv.2

theorem l1_pos {z : Point} (hz : z ≠ 0) : 0 < l1 z := by
  have h := l1_nonneg z
  rcases lt_or_eq_of_le h with h | h
  · exact h
  · exfalso
    have ha : z.1 = 0 := abs_eq_zero.mp (by unfold l1 at h; linarith [abs_nonneg z.1, abs_nonneg z.2])
    have hb : z.2 = 0 := abs_eq_zero.mp (by unfold l1 at h; linarith [abs_nonneg z.1, abs_nonneg z.2])
    exact hz (Prod.ext ha hb)

theorem tilt_strict_lower {v z : Point} (hv : U v) (hz : z ≠ 0) :
    (99 / 100) * l1 z < tilt v z := by
  have := mul_lt_mul_of_pos_right (by linarith [U_max hv] : (99:ℝ)/100 < 1 - max |v.1| |v.2|) (l1_pos hz)
  exact this.trans_le (tilt_lower v z)

theorem tilt_lower_uniform {v : Point} (hv : U v) (z : Point) :
    (99 / 100) * l1 z ≤ tilt v z := by
  rcases eq_or_ne z 0 with rfl | hz
  · norm_num
  · exact (tilt_strict_lower hv hz).le

theorem tilt_nonneg {v : Point} (hv : U v) (z : Point) : 0 ≤ tilt v z := by
  exact (mul_nonneg (by norm_num) (l1_nonneg z)).trans (tilt_lower_uniform hv z)

theorem norm_le_l1 (z : Point) : ‖z‖ ≤ l1 z := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  unfold l1
  exact max_le (by linarith [abs_nonneg z.1, abs_nonneg z.2]) (by linarith [abs_nonneg z.1, abs_nonneg z.2])

theorem F_coercive : Tendsto F (cocompact Point) atTop :=
  tendsto_atTop_mono (fun z => (norm_le_l1 z).trans (F_lower z)) tendsto_norm_cocompact_atTop

theorem tilt_coercive {v : Point} (hv : U v) : Tendsto (tilt v) (cocompact Point) atTop := by
  apply tendsto_atTop_mono (fun z => ?_) (tendsto_norm_cocompact_atTop.const_mul_atTop (by norm_num : (0:ℝ) < 99/100))
  exact (mul_le_mul_of_nonneg_left (norm_le_l1 z) (by norm_num)).trans (tilt_lower_uniform hv z)

theorem continuous_g : Continuous g := by unfold g; fun_prop
theorem continuous_F : Continuous F := by unfold F l1; exact (continuous_g.add continuous_const).max (by fun_prop)
theorem continuous_tilt (v : Point) : Continuous (tilt v) := by unfold tilt lin; exact continuous_F.sub (by fun_prop)

theorem F_vertical {t : ℝ} (ht : |t| < 4) : F (0,t) = 8 - |t| := by
  rw [F_eq_core (by simpa [l1] using ht), g_vertical (by simp)]
  simp
  ring

theorem tilt_vertical_descent {v : Point} (hv : U v) {t : ℝ} (ht : 0 < |t|) (ht4 : |t| < 4) :
    tilt v (0,t) < tilt v 0 := by
  rw [tilt_zero, tilt, F_vertical ht4]
  simp only [lin, zero_mul, add_zero, zero_add]
  have h1 : |v.2 * t| < |t| := by
    rw [abs_mul]
    nlinarith [hv.2]
  have h2 := neg_abs_le (v.2 * t)
  linarith

theorem not_localMin_tilt {v : Point} (hv : U v) : ¬ IsLocalMin (tilt v) 0 := by
  intro h
  rcases Metric.mem_nhds_iff.mp h with ⟨ε, hε, hball⟩
  let t : ℝ := min ε 1 / 2
  have htpos : 0 < t := by dsimp [t]; positivity
  have hteps : t < ε := by dsimp [t]; have := min_le_left ε 1; linarith
  have ht4 : |t| < 4 := by rw [abs_of_pos htpos]; dsimp [t]; have := min_le_right ε 1; linarith
  have hd : dist ((0,t) : Point) 0 < ε := by simpa [Prod.dist_eq, Real.dist_eq, abs_of_pos htpos, hε] using hteps
  exact not_lt_of_ge (hball hd) (tilt_vertical_descent hv (by simpa [abs_of_pos htpos] using htpos) ht4)

private theorem lipschitz_abs_fst : LipschitzWith 1 (fun z : Point => |z.1|) := by
  simpa using (lipschitzWith_one_norm (E := ℝ)).comp (LipschitzWith.prod_fst (α := ℝ) (β := ℝ))

private theorem lipschitz_abs_snd : LipschitzWith 1 (fun z : Point => |z.2|) := by
  simpa using (lipschitzWith_one_norm (E := ℝ)).comp (LipschitzWith.prod_snd (α := ℝ) (β := ℝ))

theorem lipschitz_g : LipschitzWith 8 g := by
  have h2 : LipschitzWith 2 (fun z : Point => 2 * |z.2|) := by
    simpa using (lipschitzWith_smul (2:ℝ) (β := ℝ)).comp lipschitz_abs_snd
  have h7 : LipschitzWith 7 (fun z : Point => 7 * |z.1|) := by
    simpa using (lipschitzWith_smul (7:ℝ) (β := ℝ)).comp lipschitz_abs_fst
  have h := (lipschitz_abs_fst.add h2).min (h7.sub lipschitz_abs_snd)
  norm_num at h
  exact h

theorem lipschitz_l1 : LipschitzWith 2 l1 := by
  have h := lipschitz_abs_fst.add lipschitz_abs_snd
  norm_num at h
  exact h

theorem lipschitz_F : LipschitzWith 8 F := by
  have h : LipschitzWith 8 (fun z => g z + 8) := by
    simpa using lipschitz_g.add (LipschitzWith.const 8)
  have h' := h.max lipschitz_l1
  norm_num at h'
  exact h'


/-- The ordinary differential corresponding to the Euclidean pairing. -/
def linCLM (w : Point) : Point →L[ℝ] ℝ :=
  w.1 • ContinuousLinearMap.fst ℝ ℝ ℝ + w.2 • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem linCLM_apply (w z : Point) : linCLM w z = lin w z := rfl

private theorem abs_fst_deriv {z : Point} (hz : z.1 ≠ 0) :
    HasFDerivAt (fun q : Point => |q.1|)
      (Real.sign z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) z := by
  rcases hz.lt_or_gt with h | h
  · have heq : Real.sign z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ = -ContinuousLinearMap.fst ℝ ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro q
      simp [Real.sign_of_neg h]
    rw [heq]
    exact (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).abs_of_neg h
  · simpa [Real.sign_of_pos h] using (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).abs_of_pos h

private theorem abs_snd_deriv {z : Point} (hz : z.2 ≠ 0) :
    HasFDerivAt (fun q : Point => |q.2|)
      (Real.sign z.2 • ContinuousLinearMap.snd ℝ ℝ ℝ) z := by
  rcases hz.lt_or_gt with h | h
  · have heq : Real.sign z.2 • ContinuousLinearMap.snd ℝ ℝ ℝ = -ContinuousLinearMap.snd ℝ ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro q
      simp [Real.sign_of_neg h]
    rw [heq]
    exact (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).abs_of_neg h
  · simpa [Real.sign_of_pos h] using (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).abs_of_pos h

/-- The actual derivative on each open horizontal sector. -/
theorem hasFDerivAt_g_horizontal {z : Point} (hx : z.1 ≠ 0) (hy : z.2 ≠ 0)
    (hh : |z.2| < 2 * |z.1|) :
    HasFDerivAt g (linCLM (Real.sign z.1, 2 * Real.sign z.2)) z := by
  have heq : g =ᶠ[𝓝 z] (fun q : Point => |q.1| + 2 * |q.2|) := by
    have hc : Continuous (fun q : Point => 2 * |q.1| - |q.2|) := by fun_prop
    filter_upwards [hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by linarith : 0 < 2 * |z.1| - |z.2|))] with q hq
    exact g_horizontal (by change 0 < 2 * |q.1| - |q.2| at hq; linarith)
  have hd := (abs_fst_deriv hx).add ((abs_snd_deriv hy).const_mul 2)
  have hd' : HasFDerivAt (fun q : Point => |q.1| + 2 * |q.2|)
      (linCLM (Real.sign z.1, 2 * Real.sign z.2)) z := by
    simpa [linCLM, smul_smul] using hd
  exact hd'.congr_of_eventuallyEq heq

/-- The actual derivative on each open vertical sector. -/
theorem hasFDerivAt_g_vertical {z : Point} (hx : z.1 ≠ 0) (hy : z.2 ≠ 0)
    (hv : 2 * |z.1| < |z.2|) :
    HasFDerivAt g (linCLM (7 * Real.sign z.1, -Real.sign z.2)) z := by
  have heq : g =ᶠ[𝓝 z] (fun q : Point => 7 * |q.1| - |q.2|) := by
    have hc : Continuous (fun q : Point => |q.2| - 2 * |q.1|) := by fun_prop
    filter_upwards [hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by linarith : 0 < |z.2| - 2 * |z.1|))] with q hq
    exact g_vertical (by change 0 < |q.2| - 2 * |q.1| at hq; linarith)
  have hd := ((abs_fst_deriv hx).const_mul 7).sub (abs_snd_deriv hy)
  have hd' : HasFDerivAt (fun q : Point => 7 * |q.1| - |q.2|)
      (linCLM (7 * Real.sign z.1, -Real.sign z.2)) z := by
    have heq : linCLM (7 * Real.sign z.1, -Real.sign z.2) =
        (7 : ℝ) • (Real.sign z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) -
          Real.sign z.2 • ContinuousLinearMap.snd ℝ ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro q
      simp [linCLM]
      ring
    rw [heq]
    exact hd
  exact hd'.congr_of_eventuallyEq heq

theorem hasFDerivAt_g {z : Point} (hx : z.1 ≠ 0) (hy : z.2 ≠ 0)
    (hb : |z.2| ≠ 2 * |z.1|) : HasFDerivAt g (linCLM (gradCore z)) z := by
  rcases lt_or_gt_of_ne hb with hh | hv
  · simpa [gradCore, hh] using hasFDerivAt_g_horizontal hx hy hh
  · simpa [gradCore, not_lt_of_gt hv] using hasFDerivAt_g_vertical hx hy hv

theorem hasFDerivAt_F {z : Point} (hz : l1 z < 4)
    (hx : z.1 ≠ 0) (hy : z.2 ≠ 0) (hb : |z.2| ≠ 2 * |z.1|) :
    HasFDerivAt F (linCLM (gradCore z)) z := by
  have heq : F =ᶠ[𝓝 z] (fun q => g q + 8) := by
    have hc : Continuous l1 := by unfold l1; fun_prop
    filter_upwards [hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds hz)] with q hq
    exact F_eq_core hq
  exact ((hasFDerivAt_g hx hy hb).add_const 8).congr_of_eventuallyEq heq

theorem hasFDerivAt_tilt {v z : Point} (hz : l1 z < 4)
    (hx : z.1 ≠ 0) (hy : z.2 ≠ 0) (hb : |z.2| ≠ 2 * |z.1|) :
    HasFDerivAt (tilt v) (linCLM (gradCore z - v)) z := by
  have heq : linCLM (gradCore z - v) = linCLM (gradCore z) - linCLM v := by
    apply ContinuousLinearMap.ext
    intro q
    simp [linCLM, lin]
    ring
  rw [heq]
  exact (hasFDerivAt_F hz hx hy hb).sub (linCLM v).hasFDerivAt

theorem gradCore_bounds (z : Point) : |(gradCore z).1| ≤ 7 ∧ |(gradCore z).2| ≤ 2 := by
  rcases Real.sign_apply_eq z.1 with hx | hx | hx <;>
    rcases Real.sign_apply_eq z.2 with hy | hy | hy <;>
    simp [gradCore, hx, hy] <;> split <;> norm_num


private theorem abs_fst_locally_linear {z : Point} (hx : z.1 ≠ 0) :
    (fun q : Point => |q.1|) =ᶠ[𝓝 z] (fun q => Real.sign z.1 * q.1) := by
  rcases hx.lt_or_gt with hx | hx
  · filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds hx)] with q hq
    change q.1 < 0 at hq
    simp [abs_of_neg hq, Real.sign_of_neg hx]
  · filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hx)] with q hq
    change 0 < q.1 at hq
    simp [abs_of_pos hq, Real.sign_of_pos hx]

private theorem abs_snd_locally_linear {z : Point} (hy : z.2 ≠ 0) :
    (fun q : Point => |q.2|) =ᶠ[𝓝 z] (fun q => Real.sign z.2 * q.2) := by
  rcases hy.lt_or_gt with hy | hy
  · filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (Iio_mem_nhds hy)] with q hq
    change q.2 < 0 at hq
    simp [abs_of_neg hq, Real.sign_of_neg hy]
  · filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds (Ioi_mem_nhds hy)] with q hq
    change 0 < q.2 at hq
    simp [abs_of_pos hq, Real.sign_of_pos hy]

theorem g_locally_affine {z : Point} (hx : z.1 ≠ 0) (hy : z.2 ≠ 0)
    (hb : |z.2| ≠ 2 * |z.1|) :
    g =ᶠ[𝓝 z] (fun q => lin (gradCore z) q) := by
  rcases lt_or_gt_of_ne hb with hh | hv
  · have hc : Continuous (fun q : Point => 2 * |q.1| - |q.2|) := by fun_prop
    filter_upwards [abs_fst_locally_linear hx, abs_snd_locally_linear hy,
      hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by linarith : 0 < 2 * |z.1| - |z.2|))] with q hqx hqy hq
    change 0 < 2 * |q.1| - |q.2| at hq
    rw [g_horizontal (by linarith), hqx, hqy]
    simp [gradCore, hh, lin]
    ring
  · have hc : Continuous (fun q : Point => |q.2| - 2 * |q.1|) := by fun_prop
    filter_upwards [abs_fst_locally_linear hx, abs_snd_locally_linear hy,
      hc.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by linarith : 0 < |z.2| - 2 * |z.1|))] with q hqx hqy hq
    change 0 < |q.2| - 2 * |q.1| at hq
    rw [g_vertical (by linarith), hqx, hqy]
    simp [gradCore, not_lt_of_gt hv, lin]
    ring

theorem tilt_locally_affine {v z : Point} (hz : l1 z < 4)
    (hx : z.1 ≠ 0) (hy : z.2 ≠ 0) (hb : |z.2| ≠ 2 * |z.1|) :
    tilt v =ᶠ[𝓝 z] (fun q => lin (gradCore z - v) q + 8) := by
  have hc : Continuous l1 := by unfold l1; fun_prop
  filter_upwards [g_locally_affine hx hy hb,
    hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds hz)] with q hq hnorm
  unfold tilt
  rw [F_eq_core hnorm, hq]
  simp [lin]
  ring


/-- A convex neighborhood is meant literally; the quadratic uses the Euclidean squared norm. -/
def LocallyWeaklyConvex (ρ : ℝ) : Prop :=
  ∃ s : Set Point, s ∈ 𝓝 (0 : Point) ∧
    ConvexOn ℝ s (fun z => F z + ρ / 2 * (z.1 ^ 2 + z.2 ^ 2))

theorem not_locallyWeaklyConvex (ρ : ℝ) (hρ : 0 ≤ ρ) : ¬ LocallyWeaklyConvex ρ := by
  rintro ⟨s, hs, hc⟩
  rcases Metric.mem_nhds_iff.mp hs with ⟨ε, hε, hball⟩
  let t : ℝ := min (min ε 1) (1 / (ρ + 1)) / 2
  have hp : 0 < ρ + 1 := by linarith
  have ht : 0 < t := by dsimp [t]; positivity
  have htε : t < ε := by
    dsimp [t]
    have := min_le_left (min ε 1) (1 / (ρ + 1))
    have := min_le_left ε 1
    linarith
  have ht1 : t < 1 := by
    dsimp [t]
    have := min_le_left (min ε 1) (1 / (ρ + 1))
    have := min_le_right ε 1
    linarith
  have htρ : ρ * t < 1 := by
    have hbound : t ≤ 1 / (ρ + 1) := by
      dsimp [t]
      have := min_le_right (min ε 1) (1 / (ρ + 1))
      have : 0 < 1 / (ρ + 1) := one_div_pos.mpr hp
      linarith
    have := (le_div_iff₀ hp).mp hbound
    nlinarith
  have hplus : ((0,t) : Point) ∈ s := hball (by simpa [Prod.dist_eq, Real.dist_eq, abs_of_pos ht, hε] using htε)
  have hminus : ((0,-t) : Point) ∈ s := hball (by simpa [Prod.dist_eq, Real.dist_eq, abs_of_pos ht, abs_neg, hε] using htε)
  have hi := hc.2 hplus hminus (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 + 1/2 = 1)
  have hFp := F_vertical (by rw [abs_of_pos ht]; linarith : |t| < 4)
  have hFm := F_vertical (by rw [abs_neg, abs_of_pos ht]; linarith : |-t| < 4)
  have hmid : (1/2:ℝ) • ((0,t) : Point) + (1/2:ℝ) • (0,-t) = 0 := by ext <;> simp <;> ring
  rw [hmid] at hi
  dsimp at hi
  rw [hFp, hFm] at hi
  simp [abs_of_pos ht, abs_neg] at hi
  nlinarith

end Paper32
