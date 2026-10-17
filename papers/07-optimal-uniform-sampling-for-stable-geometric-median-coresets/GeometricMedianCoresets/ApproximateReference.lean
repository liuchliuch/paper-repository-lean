import GeometricMedianCoresets.StableOnGood

/-! Proposition 4.3, including the sampling probability and infimum consequences. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators RealInnerProductSpace
namespace GeometricMedianCoresets

/-- The cost infimum is nonnegative whenever a candidate point is available. -/
theorem Dist.optimum_nonneg {X : Type*} (D : Dist X) {n : ℕ}
    (P : Dataset X n) (μ : X) : 0 ≤ D.optimum P := by
  apply le_csInf ⟨D.cost P μ, Set.mem_range_self μ⟩
  rintro _ ⟨z, rfl⟩
  exact D.cost_nonneg P z

/-- Modified scalar stability calculation for an approximate reference point. -/
theorem approximate_reference_stable {X : Type*} (D : Dist X) {n m : ℕ}
    (P : Dataset X n) (Q : Dataset X m) (μ : X)
    {ε δ : ℝ} (hε : 0 < ε) (hε' : ε < 1/4) (hδ : 0 ≤ δ)
    (hδ' : δ < (5 - 19 * ε) / (9 + ε))
    (hμ : D.cost P μ ≤ (1 + δ) * D.optimum P)
    (hΔ : ∀ x y, |D.delta P Q x y| ≤ ε * (D.cost P x + D.cost P y))
    (href : D.cost Q μ ≤ 10 * D.cost P μ) :
    IsStableCoreset D P Q ε (17 * ε) := by
  intro x y hcomp
  have hT : D.cost P μ ≤ (1 + δ) * D.cost P y :=
    hμ.trans (mul_le_mul_of_nonneg_left (D.optimum_le_cost P y) (by linarith))
  have hlo := (abs_le.1 (hΔ y μ)).1
  have hhi := (abs_le.1 (hΔ x y)).2
  unfold Dist.delta at hlo hhi
  have hdom0 : D.cost Q y ≤ (1 + ε) * D.cost P y + (9 + ε) * D.cost P μ := by
    nlinarith
  have hdom : D.cost Q y ≤ (10 + 2 * ε + (9 + ε) * δ) * D.cost P y := by
    have hmul := mul_le_mul_of_nonneg_left hT (by linarith : 0 ≤ 9 + ε)
    nlinarith
  have htransfer : (1 - ε) * D.cost P x ≤
      (1 + 11 * ε + 2 * ε ^ 2 + ε * (9 + ε) * δ) * D.cost P y := by
    have hmul := mul_le_mul_of_nonneg_left hdom hε.le
    nlinarith
  have hδmul := (lt_div_iff₀ (by linarith : 0 < 9 + ε)).1 hδ'
  have hgap : 0 ≤ (1 + 17 * ε) * (1 - ε) -
      (1 + 11 * ε + 2 * ε ^ 2 + ε * (9 + ε) * δ) := by
    have hmul := mul_nonneg hε.le (le_of_lt (sub_pos.2 hδmul))
    nlinarith
  have hfy := D.cost_nonneg P y
  have hmul := mul_nonneg hgap hfy
  have h1 : 0 < 1 - ε := by linarith
  exact (mul_le_mul_left h1).1 (by nlinarith [htransfer, hmul])

/-- The single mean-error event gives relative comparison at the increased threshold. -/
theorem comparison_approximate_reference {X : Type*} (S : SquaredMetric X)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (P : Dataset X n)
    (I : Finset (Fin n)) (hI : I.card = m) (μ : X)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 ≤ δ)
    (hμ : S.toDist.cost P μ ≤ (1 + δ) * S.toDist.optimum P)
    (hmsize : 20 * (1 + δ) / (ε * ε) ≤ m)
    (hmean : meanError (fun i => anchoredFeature S μ (P i)) I
      ≤ 10 * ((1:ℝ) / m) * S.toDist.cost P μ) :
    ∀ x y, |S.toDist.delta P (indexedSample P I) x y| ≤
      ε * (S.toDist.cost P x + S.toDist.cost P y) := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hδR : 0 < 1 + δ := by linarith
  have hm' : 0 < (m:ℝ) / (1 + δ) := div_pos hmR hδR
  have hsize' : 20 / (ε * ε) ≤ (m:ℝ) / (1 + δ) := by
    apply (le_div_iff₀ hδR).2
    convert hmsize using 1 <;> ring
  have hmean' : meanError (fun i => anchoredFeature S μ (P i)) I ≤
      10 * S.toDist.optimum P / ((m:ℝ) / (1 + δ)) := by
    have hh := mul_le_mul_of_nonneg_left hμ (by positivity : 0 ≤ 10 * ((1:ℝ) / m))
    apply hmean.trans
    convert hh using 1 <;> field_simp <;> ring
  intro x y
  have hIp : 0 < I.card := by omega
  have hs : 0 ≤ S.toDist.cost P x + S.toDist.cost P y :=
    add_nonneg (S.toDist.cost_nonneg P x) (S.toDist.cost_nonneg P y)
  exact (delta_le_meanError S hn P I hIp μ x y).trans
    ((prop24_deterministic hm' (S.toDist.optimum_nonneg P μ) hmean' (sq_nonneg _)
      (triangle_avg S.toDist hn P x y) (two_opt_le S.toDist P x y) hs (S.d_nonneg x y)).trans
      (mul_le_mul_of_nonneg_right (sqrt_20_div_le_eps hm' hε hsize') hs))

/-- Proposition 4.3 with its actual uniform-without-replacement success probability. -/
theorem prop43_uniform_stable {X : Type*} (S : SquaredMetric X) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (P : Dataset X n) (μ : X)
    {ε δ : ℝ} (hε : 0 < ε) (hε' : ε < 1/4) (hδ : 0 ≤ δ)
    (hδ' : δ < (5 - 19 * ε) / (9 + ε))
    (hμ : S.toDist.cost P μ ≤ (1 + δ) * S.toDist.optimum P)
    (hmsize : ⌈20 * (1 + δ) / (ε * ε)⌉₊ ≤ m) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset S.toDist P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4 / 5 := by
  classical
  apply (two_good_4_5_opt S hn hm hmn P μ).trans
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show
    ((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => meanError (fun i => anchoredFeature S μ (P i)) I
        ≤ 10 * ((1:ℝ) / m) * S.toDist.cost P μ ∧
        sampleCostM S.toDist P μ m I ≤ 10 * S.toDist.cost P μ) ⊆
    ((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset S.toDist P (indexedSample P I) ε (17 * ε)) from by
    intro I hi
    obtain ⟨hmem, hmean, hcost⟩ := Finset.mem_filter.1 hi
    have hI := (Finset.mem_powersetCard.1 hmem).2
    apply Finset.mem_filter.2 ⟨hmem, ?_⟩
    apply approximate_reference_stable S.toDist P (indexedSample P I) μ hε hε' hδ hδ' hμ
      (comparison_approximate_reference S hn hm P I hI μ hε hδ hμ (Nat.ceil_le.1 hmsize) hmean)
    rw [cost_indexedSample S.toDist P I hI]
    exact hcost)

/-- Any `δ < 1/37` satisfies the paper's uniform admissibility bound. -/
theorem delta_uniform_admissible {ε δ : ℝ} (hε : 0 < ε) (hε' : ε < 1/4)
    (hδ : δ < 1/37) : δ < (5 - 19 * ε) / (9 + ε) := by
  apply hδ.trans
  apply (lt_div_iff₀ (by linarith : 0 < 9 + ε)).2
  linarith

/-- If the infimum is positive, approximate anchors exist at every positive factor. -/
theorem exists_approximate_reference {X : Type*} (D : Dist X) {n : ℕ}
    (P : Dataset X n) (μ₀ : X) (hα : 0 < D.optimum P) {δ : ℝ} (hδ : 0 < δ) :
    ∃ μ, D.cost P μ ≤ (1 + δ) * D.optimum P := by
  have hlt : D.optimum P < (1 + δ) * D.optimum P := by nlinarith
  obtain ⟨r, ⟨μ, rfl⟩, hr⟩ := (csInf_lt_iff (D.optimum_bddBelow P)
    ⟨D.cost P μ₀, Set.mem_range_self μ₀⟩).1 hlt
  exact ⟨μ, hr.le⟩

/-- Each summand is controlled by the population average. -/
theorem Dist.point_cost_le {X : Type*} (D : Dist X) {n : ℕ}
    (hn : 0 < n) (P : Dataset X n) (i : Fin n) (z : X) :
    D.d z (P i) ≤ (n:ℝ) * D.cost P z := by
  have hs : D.d z (P i) ≤ ∑ j, D.d z (P j) :=
    Finset.single_le_sum (fun j _ => D.nonneg z (P j)) (Finset.mem_univ i)
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold Dist.cost
  convert hs using 1 <;> field_simp

/-- A zero infimum is attained at a data point, even without ambient compactness. -/
theorem optimum_zero_attained {X : Type*} (D : Dist X) {n : ℕ}
    (hn : 0 < n) (P : Dataset X n) (hα : D.optimum P = 0) :
    ∃ μ, D.IsGeometricMedian P μ := by
  let i₀ : Fin n := ⟨0, hn⟩
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hd : ∀ i j, D.d (P i) (P j) = 0 := by
    intro i j
    have hlow : D.d (P i) (P j) / (2 * n) ≤ D.optimum P := by
      apply le_csInf ⟨D.cost P (P i₀), Set.mem_range_self _⟩
      rintro _ ⟨z, rfl⟩
      apply (div_le_iff₀ (by positivity : (0:ℝ) < 2 * n)).2
      have htri := D.triangle (P i) (P j) z
      rw [D.symm (P i) z] at htri
      linarith [D.point_cost_le hn P i z, D.point_cost_le hn P j z]
    rw [hα] at hlow
    have hle : D.d (P i) (P j) ≤ 0 := by
      simpa using (div_le_iff₀ (by positivity : (0:ℝ) < 2 * n)).1 hlow
    exact le_antisymm hle (D.nonneg _ _)
  refine ⟨P i₀, ?_⟩
  intro z
  have hc : D.cost P (P i₀) = 0 := by simp [Dist.cost, hd]
  rw [hc]
  exact D.cost_nonneg P z

/-- Nonattainment forces a positive infimum, so all positive relative overheads admit anchors. -/
theorem nonattainment_optimum_pos {X : Type*} (D : Dist X) {n : ℕ}
    (hn : 0 < n) (P : Dataset X n) (hnot : ¬ ∃ μ, D.IsGeometricMedian P μ) :
    0 < D.optimum P := by
  have hnonneg := D.optimum_nonneg P (P ⟨0, hn⟩)
  exact lt_of_le_of_ne hnonneg (Ne.symm (fun hz => hnot (optimum_zero_attained D hn P hz)))

/-- No attainment assumption is needed after any admissible positive constant overhead. -/
theorem uniform_stable_without_attainment {X : Type*} (S : SquaredMetric X) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (P : Dataset X n)
    {ε δ : ℝ} (hε : 0 < ε) (hε' : ε < 1/4) (hδ : 0 < δ) (hδ' : δ < 1/37)
    (hmsize : ⌈20 * (1 + δ) / (ε * ε)⌉₊ ≤ m) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset S.toDist P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4 / 5 := by
  by_cases hatt : ∃ μ, S.toDist.IsGeometricMedian P μ
  · obtain ⟨μ, hμ⟩ := hatt
    apply prop43_uniform_stable S hn hm hmn P μ hε hε' hδ.le
      (delta_uniform_admissible hε hε' hδ') _ hmsize
    rw [cost_median_eq_optimum S.toDist P μ hμ]
    have hα := S.toDist.optimum_nonneg P μ
    nlinarith
  · have hα := nonattainment_optimum_pos S.toDist hn P hatt
    obtain ⟨μ, hμ⟩ := exists_approximate_reference S.toDist P (P ⟨0, hn⟩) hα hδ
    exact prop43_uniform_stable S hn hm hmn P μ hε hε' hδ.le
      (delta_uniform_admissible hε hε' hδ') hμ hmsize

end GeometricMedianCoresets
