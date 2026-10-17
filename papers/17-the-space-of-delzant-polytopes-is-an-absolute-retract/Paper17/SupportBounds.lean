import Paper17.Basic
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation

/-! Pairing, separation and support bounds used by the support isometry and metric comparison. -/
noncomputable section
open scoped Pointwise Topology BigOperators
open Set Metric Filter Finset
namespace Paper17
variable {n : ℕ}

/-- The pairing `|dot u x|` is at most `(∑ i, |u i|) * ‖x‖`. -/
theorem abs_dot_le_sum_abs_mul_norm (u x : V n) :
    |dot u x| ≤ (∑ i, |u i|) * ‖x‖ := by
  have hcoord : ∀ i : Fin n, |x i| ≤ ‖x‖ := by
    intro i
    have : (|x i| : ℝ) = ‖x i‖ := by simp [Real.norm_eq_abs]
    rw [this]
    exact norm_le_pi_norm x i
  calc |dot u x| = |∑ i, u i * x i| := by rw [dot_apply]
    _ ≤ ∑ i, |u i * x i| := abs_sum_le_sum_abs _ _
    _ = ∑ i, |u i| * |x i| := by simp only [abs_mul]
    _ ≤ ∑ i, |u i| * ‖x‖ := by
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hcoord i) (abs_nonneg _)
    _ = (∑ i, |u i|) * ‖x‖ := by rw [Finset.sum_mul]

/-- Continuity of `x ↦ dot u x`. -/
theorem continuous_dot_left (u : V n) : Continuous fun x : V n => dot u x := by
  exact continuous_dot u

/-- The support function of a compact set bounds pairings at its points. -/
theorem supportFunction_ub' {K : Set (V n)} (hK : IsCompact K) {u x : V n}
    (hx : x ∈ K) : dot u x ≤ supportFunction K u := by
  unfold supportFunction
  have hmem : dot u x ∈ (fun y => dot u y) '' K := ⟨x, hx, rfl⟩
  refine le_csSup ?_ hmem
  exact IsCompact.bddAbove_image hK (continuous_dot_left u).continuousOn

/-- The support function of a dilation: `h_{t • K} = t * h_K` for `t ≥ 0`. -/
theorem supportFunction_smul' {K : Set (V n)} (hne : K.Nonempty) {t : ℝ} (ht : 0 ≤ t)
    (u : V n) : supportFunction (t • K) u = t * supportFunction K u := by
  have hmap : (fun x => dot u x) '' (t • K) = t • ((fun y => dot u y) '' K) := by
    ext r
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨y, hy, rfl⟩ := Set.mem_smul_set.1 hx
      exact ⟨dot u y, ⟨y, hy, rfl⟩, (dot_smul_right t u y).symm⟩
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨t • y, Set.smul_mem_smul_set hy, dot_smul_right t u y⟩
  unfold supportFunction
  rw [hmap, Real.sSup_smul_of_nonneg ht, smul_eq_mul]

/-- Every linear functional on `V n` is given by `dot u ·`. -/
theorem exists_forall_eq_dot (f : V n →ₗ[ℝ] ℝ) :
    ∃ u : V n, ∀ x : V n, f x = dot u x := by
  refine ⟨fun i => f (fun j => if i = j then (1:ℝ) else 0), fun x => ?_⟩
  rw [LinearMap.pi_apply_eq_sum_univ]
  unfold dot
  exact Finset.sum_congr rfl fun i _ => by
    rw [smul_eq_mul, mul_comm]

/-- If `L` is compact convex and `h_{K'} ≤ h_L` in every direction, then `K' ⊆ L`.
(The bound `h_{K'} ≤ h_L` is only used through the weaker fact
`dot u x ≤ h_L(u)` for `x ∈ K'`.) -/
theorem subset_of_forall_dot_le_supportFunction {K' L : Set (V n)}
    (hL : IsCompact L) (hneL : L.Nonempty) (hconvL : Convex ℝ L)
    (h : ∀ (u x : V n), x ∈ K' → dot u x ≤ supportFunction L u) :
    K' ⊆ L := by
  intro x hx
  by_contra hn
  have hLc : IsClosed L := hL.isClosed
  obtain ⟨f, u, hfL, hfx⟩ := geometric_hahn_banach_closed_point hconvL hLc hn
  obtain ⟨v, hv⟩ := exists_forall_eq_dot (f : V n →L[ℝ] ℝ).toLinearMap
  have hLv : supportFunction L v ≤ u := by
    apply csSup_le (hneL.image _)
    intro b hb
    obtain ⟨y, hy, rfl⟩ := hb
    have hfy := hfL y hy
    change (f : V n →L[ℝ] ℝ).toLinearMap y < u at hfy
    rw [hv y] at hfy
    exact hfy.le
  have h1 : u < dot v x := by
    change u < (f : V n →L[ℝ] ℝ).toLinearMap x at hfx
    rwa [hv x] at hfx
  have h2 : dot v x ≤ supportFunction L v := h v x hx
  exact (not_lt_of_ge (h2.trans hLv)) h1

/-! ## Hausdorff distance forces dilated inclusions -/

/-- From `d_H(K,L) = δ` one has `h_K(u) - h_L(u) ≤ δ * ∑|u i|` for every `u`. -/
theorem supportFunction_sub_le_of_hausdorffDist {K L : Set (V n)}
    (hK : IsCompact K) (hneK : K.Nonempty) (hL : IsCompact L) (hneL : L.Nonempty)
    (u : V n) :
    supportFunction K u - supportFunction L u
      ≤ Metric.hausdorffDist K L * (∑ i, |u i|) := by
  have hfin : EMetric.hausdorffEdist K L ≠ ⊤ :=
    Metric.hausdorffEdist_ne_top_of_nonempty_of_bounded hneK hneL hK.isBounded hL.isBounded
  have hδ0 : 0 ≤ Metric.hausdorffDist K L := Metric.hausdorffDist_nonneg
  -- every x ∈ K is within d_H of L
  have hpt : ∀ x ∈ K, ∃ y ∈ L, dist x y ≤ Metric.hausdorffDist K L := by
    intro x hx
    have hinf : Metric.infDist x L ≤ Metric.hausdorffDist K L :=
      Metric.infDist_le_hausdorffDist_of_mem hx hfin
    obtain ⟨y, hy, hyd⟩ : ∃ y ∈ L, Metric.infDist x L = dist x y :=
      hL.exists_infDist_eq_dist hneL x
    exact ⟨y, hy, by linarith⟩
  obtain ⟨x, hx, hmax⟩ := exists_mem_eq_supportFunction hK hneK u
  obtain ⟨y, hy, hxy⟩ := hpt x hx
  have hyb : dot u y ≤ supportFunction L u := supportFunction_ub' hL hy
  have hsplit : dot u x - dot u y = dot u (x - y) := by
    simp [dot, mul_sub, Finset.sum_sub_distrib]
  calc supportFunction K u - supportFunction L u ≤ dot u x - dot u y := by rw [hmax]; linarith
    _ = dot u (x - y) := hsplit
    _ ≤ |dot u (x - y)| := le_abs_self _
    _ ≤ (∑ i, |u i|) * dist x y := by
      simpa [dist_eq_norm] using abs_dot_le_sum_abs_mul_norm u (x - y)
    _ ≤ (∑ i, |u i|) * Metric.hausdorffDist K L :=
      mul_le_mul_of_nonneg_left hxy (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    _ = Metric.hausdorffDist K L * (∑ i, |u i|) := mul_comm _ _

/-- Symmetric form of the support-function / Hausdorff bound. -/
theorem supportFunction_sub_le_of_hausdorffDist' {K L : Set (V n)}
    (hK : IsCompact K) (hneK : K.Nonempty) (hL : IsCompact L) (hneL : L.Nonempty)
    (u : V n) :
    supportFunction L u - supportFunction K u
      ≤ Metric.hausdorffDist K L * (∑ i, |u i|) := by
  have h := supportFunction_sub_le_of_hausdorffDist hL hneL hK hneK u
  rwa [Metric.hausdorffDist_comm] at h

/-- If `ball 0 r ⊆ K` with `K` compact, then `h_K(u) ≥ r * ∑|u i|`. -/
theorem supportFunction_ge_of_ball_subset {K : Set (V n)} {r : ℝ}
    (hK : IsCompact K) (hr : 0 < r) (hrB : Metric.ball (0 : V n) r ⊆ K) (u : V n) :
    r * (∑ i, |u i|) ≤ supportFunction K u := by
  set S : ℝ := ∑ i, |u i| with hS
  have hS0 : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg fun i _ => abs_nonneg _
  -- `h_K(u) ≥ (r-ε) S` for every `ε ∈ (0,r)`
  have key : ∀ ε : ℝ, 0 < ε → ε < r → (r - ε) * S ≤ supportFunction K u := by
    intro ε hε0 hεr
    let x : V n := fun i => if 0 ≤ u i then r - ε else ε - r
    have hxball : x ∈ Metric.ball (0 : V n) r := by
      rw [mem_ball_zero_iff]
      refine (pi_norm_lt_iff (by linarith)).mpr ?_
      intro i
      by_cases hu : 0 ≤ u i
      · have : x i = r - ε := if_pos hu
        rw [this, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        linarith
      · have : x i = ε - r := if_neg hu
        rw [this, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
        linarith
    have hxK : x ∈ K := hrB hxball
    have hpair : dot u x = (r - ε) * S := by
      unfold dot
      have hterm : ∀ i : Fin n, u i * x i = |u i| * (r - ε) := by
        intro i
        by_cases hu : 0 ≤ u i
        · have : x i = r - ε := if_pos hu
          rw [this, abs_of_nonneg hu]
        · have hui : u i < 0 := lt_of_not_ge hu
          have : x i = ε - r := if_neg hu
          rw [this, abs_of_nonpos hui.le]; ring
      calc ∑ i, u i * x i = ∑ i, |u i| * (r - ε) := Finset.sum_congr rfl fun i _ => hterm i
        _ = S * (r - ε) := by rw [hS, Finset.sum_mul]
        _ = (r - ε) * S := by ring
    rw [← hpair]
    exact supportFunction_ub' hK hxK
  by_cases hS0eq : S = 0
  · rw [hS0eq, mul_zero]
    exact le_csSup (IsCompact.bddAbove_image hK (continuous_dot_left u).continuousOn)
      ⟨0, (hrB (mem_ball_zero_iff.2 (by simp [hr]))), by simp [dot]⟩
  · have hSp : 0 < S := lt_of_le_of_ne hS0 (Ne.symm hS0eq)
    -- `r * S = (r-ε)S + ε S`, so `r * S ≤ h + ε S` for all small `ε`, hence `r * S ≤ h`
    by_contra hc
    push_neg at hc
    -- pick ε small enough that `(r-ε)S > h`
    set ε : ℝ := min (r / 2) ((r * S - supportFunction K u) / (2 * S)) with hε
    have hε0 : 0 < ε := by
      rw [hε]
      refine lt_min (half_pos hr) ?_
      have hpos : 0 < r * S - supportFunction K u := by linarith
      positivity
    have hεr : ε < r := by
      rw [hε]
      exact (min_le_left _ _).trans_lt (by linarith)
    have hεle : ε ≤ (r * S - supportFunction K u) / (2 * S) := min_le_right _ _
    have hkey := key ε hε0 hεr
    -- (r-ε)S = r S - ε S ≥ r S - (r S - h)/2 = (r S + h)/2 > h
    have hεS : ε * S ≤ (r * S - supportFunction K u) / 2 := by
      have hmul := (le_div_iff₀ (show 0 < 2 * S by positivity)).mp hεle
      nlinarith
    nlinarith


end Paper17
