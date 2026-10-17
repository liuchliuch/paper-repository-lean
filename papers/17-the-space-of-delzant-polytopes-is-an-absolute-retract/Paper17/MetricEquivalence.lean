import Paper17.MetricOuter

/-! The converse convergence implication in Proposition 2.5. -/
noncomputable section
open scoped Topology BigOperators Pointwise symmDiff
open Set Metric MeasureTheory Filter
namespace Paper17

theorem kappa_pos (n : ℕ) : 0 < kappa n := by
  unfold kappa
  rw [Real.volume_pi_ball _ (by norm_num), Fintype.card_fin,
    ENNReal.toReal_ofReal (by positivity)]
  positivity

/-- Volume convergence to a compact convex body with an interior ball forces
Hausdorff convergence. No artificial assumption `0 ∈ L j` is imposed. -/
theorem hausdorffDist_tendsto_zero_of_symmDiffVol_tendsto_zero
    {n : ℕ} {K : Set (V n)} (hK : IsCompact K) (hneK : K.Nonempty) (hcK : Convex ℝ K)
    {r : ℝ} (hr : 0 < r) (hrB : Metric.ball (0 : V n) r ⊆ K)
    (L : ℕ → Set (V n)) (hLc : ∀ j, IsCompact (L j)) (hLne : ∀ j, (L j).Nonempty)
    (hconv : ∀ j, Convex ℝ (L j))
    (hTendsto : Tendsto (fun j => symmDiffVol K (L j)) atTop (𝓝 0)) :
    Tendsto (fun j => Metric.hausdorffDist K (L j)) atTop (𝓝 0) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    have hset : ∀ S : Set (V 0), S.Nonempty → S = Set.univ := by
      intro S ⟨x, hx⟩
      apply Set.eq_univ_of_forall
      intro y
      simpa only [Subsingleton.elim y x] using hx
    have hzero : (fun j => Metric.hausdorffDist K (L j)) = fun _ => (0 : ℝ) := by
      funext j
      rw [hset K hneK, hset (L j) (hLne j), Metric.hausdorffDist_self_zero]
    rw [hzero]
    exact tendsto_const_nhds
  · obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hneK continuous_norm.continuousOn
    let R₀ := ‖x‖ + 1
    have hR₀ : 0 < R₀ := by dsimp [R₀]; positivity
    have houtK₀ : K ⊆ Metric.ball (0 : V n) R₀ := by
      intro y hy
      rw [mem_ball_zero_iff]
      have hh : ‖y‖ ≤ ‖x‖ := hmax hy
      dsimp [R₀]
      linarith
    let r₀ := r / 2
    have hr₀ : 0 < r₀ := half_pos hr
    let R := 2 * R₀ + r₀
    have hR : 0 < R := by dsimp [R]; positivity
    have houtK : K ⊆ Metric.ball (0 : V n) R := by
      intro y hy
      have hh : dist y 0 < R₀ := houtK₀ hy
      change dist y 0 < R
      dsimp [R]
      linarith
    have hinK : Metric.ball (0 : V n) r₀ ⊆ K :=
      (Metric.ball_subset_ball (by dsimp [r₀]; linarith)).trans hrB
    have hinner : ∀ᶠ j in atTop, Metric.ball (0 : V n) r₀ ⊆ L j := by
      filter_upwards [(tendsto_order.mp hTendsto).2 ((r / 4) ^ n) (by positivity)] with j hj
      exact inner_ball_of_small_symmDiffVol hK (hLc j) (hLne j) (hconv j) hr hrB hj
    have houter : ∀ᶠ j in atTop, L j ⊆ Metric.ball (0 : V n) R := by
      filter_upwards [hinner, (tendsto_order.mp hTendsto).2 (r₀ ^ n) (by positivity)] with j hj hsmall
      exact outer_ball_of_small_symmDiffVol hK (hLc j) (hconv j) hr₀ hR₀ hj houtK₀ hsmall
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let C := kappa n * (r₀ * ε / (2 * (R + r₀))) ^ n
    have hC : 0 < C := by dsimp [C]; exact mul_pos (kappa_pos n) (by positivity)
    filter_upwards [hinner, houter, (tendsto_order.mp hTendsto).2 C hC] with j hinj houtj hvol
    rw [Real.dist_eq, sub_zero, abs_of_nonneg Metric.hausdorffDist_nonneg]
    by_contra! hdist
    have hlow := symmDiffVol_ball_inside_estimate hn hK hneK hcK
      (hLc j) (hLne j) (hconv j) hr₀ hR hinK hinj houtK houtj
    have hmono : (r₀ * ε / (2 * (R + r₀))) ^ n ≤
        (r₀ * Metric.hausdorffDist K (L j) / (2 * (R + r₀))) ^ n := by
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdist hr₀.le) (by positivity)
    have hbound : C ≤ symmDiffVol K (L j) :=
      (mul_le_mul_of_nonneg_left hmono (kappa_nonneg n)).trans hlow
    exact (not_lt_of_ge hbound) hvol

/-- Convergence equivalence for bodies containing a common prescribed origin ball in the limit. -/
theorem tendsto_symmDiffVol_zero_iff_tendsto_hausdorffDist_zero
    {n : ℕ} {K : Set (V n)} (hK : IsCompact K) (hneK : K.Nonempty) (hcK : Convex ℝ K)
    {r : ℝ} (hr : 0 < r) (hrB : Metric.ball (0 : V n) r ⊆ K)
    (L : ℕ → Set (V n)) (hLc : ∀ j, IsCompact (L j)) (hLne : ∀ j, (L j).Nonempty)
    (hconv : ∀ j, Convex ℝ (L j)) :
    Tendsto (fun j => symmDiffVol K (L j)) atTop (𝓝 0) ↔
      Tendsto (fun j => Metric.hausdorffDist K (L j)) atTop (𝓝 0) := by
  constructor
  · exact hausdorffDist_tendsto_zero_of_symmDiffVol_tendsto_zero hK hneK hcK hr hrB L hLc hLne hconv
  · have h0 : (0 : V n) ∈ K := hrB (Metric.mem_ball_self hr)
    exact symmDiffVol_tendsto_zero_of_hausdorffDist_tendsto_zero hK hneK h0 hcK hr hrB L hLc hLne hconv

/-- **Proposition 2.5** for arbitrary positive convex bodies, after translating
an interior point to the origin. This includes all prescribed limiting bodies. -/
theorem proposition_2_5 {n : ℕ} (K : PosBody n) (L : ℕ → PosBody n) :
    Tendsto (fun j => Metric.hausdorffDist K.carrier (L j).carrier) atTop (𝓝 0) ↔
      Tendsto (fun j => symmDiffVol K.carrier (L j).carrier) atTop (𝓝 0) := by
  obtain ⟨a, ha⟩ := K.interior_nonempty
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ha)
  let φ : V n → V n := fun x => -a + x
  have hφ : Isometry φ := isometry_iff_dist_eq.mpr fun x y => by simp [φ, dist_eq_norm]
  have hφc : Continuous φ := hφ.continuous
  have hμ : ∀ S : Set (V n), volume (φ '' S) = volume S := by
    intro S
    have heq : φ '' S = (fun x => a + x) ⁻¹' S := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [φ] using hy
      · intro hx
        exact ⟨a + x, hx, by simp [φ]⟩
    rw [heq]
    exact measure_preimage_add volume a S
  have hvol : ∀ j, symmDiffVol (φ '' K.carrier) (φ '' (L j).carrier) =
      symmDiffVol K.carrier (L j).carrier := by
    intro j
    unfold symmDiffVol
    rw [← Set.image_symmDiff hφ.injective, hμ]
  have hdist : ∀ j, Metric.hausdorffDist (φ '' K.carrier) (φ '' (L j).carrier) =
      Metric.hausdorffDist K.carrier (L j).carrier := fun j => Metric.hausdorffDist_image hφ
  have hin : Metric.ball (0 : V n) r ⊆ φ '' K.carrier := by
    intro y hy
    refine ⟨a + y, hball ?_, by simp [φ]⟩
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  have heq := tendsto_symmDiffVol_zero_iff_tendsto_hausdorffDist_zero
    (K.isCompact.image hφc) (K.nonempty.image φ) (K.convex.translate (-a)) hr hin
    (fun j => φ '' (L j).carrier) (fun j => (L j).isCompact.image hφc)
    (fun j => (L j).nonempty.image φ) (fun j => (L j).convex.translate (-a))
  change Tendsto (fun j => symmDiffVol (φ '' K.carrier) (φ '' (L j).carrier)) atTop (𝓝 0) ↔
    Tendsto (fun j => Metric.hausdorffDist (φ '' K.carrier) (φ '' (L j).carrier)) atTop (𝓝 0) at heq
  simpa only [hdist, hvol] using heq.symm

end Paper17
