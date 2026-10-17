import GeometricMedianCoresets.StableOnGood

/-! Proposition 2.4 under the finite uniform law, simultaneously over all centres. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace GeometricMedianCoresets

/-- Monotonicity of the counting probability of sample events. -/
theorem sample_fraction_mono {n m : ℕ} (E F : Finset (Fin n) → Prop)
    [DecidablePred E] [DecidablePred F]
    (h : ∀ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m, E I → F I) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter E).card / (n.choose m : ℝ) ≤
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter F).card / (n.choose m : ℝ) := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (show
    ((Finset.univ : Finset (Fin n)).powersetCard m).filter E ⊆
    ((Finset.univ : Finset (Fin n)).powersetCard m).filter F from by
    intro I hi
    obtain ⟨hi, he⟩ := Finset.mem_filter.1 hi
    exact Finset.mem_filter.2 ⟨hi, h I hi he⟩)

/-- Proposition 2.4, for a squared-Hilbert metric and an attained population median. -/
theorem uniform_comparison_9_10 {X : Type*} (S : SquaredMetric X) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (P : Dataset X n)
    (μ : X) (hμ : S.toDist.IsGeometricMedian P μ) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => ∀ x y, |S.toDist.delta P (indexedSample P I) x y| ≤
        Real.sqrt (20 / m) * (S.toDist.cost P x + S.toDist.cost P y))).card
      / (n.choose m : ℝ) ≥ 9 / 10 := by
  apply (meanError_good_9_10_opt S hn hm hmn P μ).trans
  apply sample_fraction_mono
  intro I hI hmean
  exact comparison_on_good_event S hn hm P I (Finset.mem_powersetCard.1 hI).2 μ hμ hmean

/-- Full-sample stability also holds after enumerating the full index set. -/
theorem indexedSample_full_stable {X : Type*} (D : Dist X) {n : ℕ}
    (P : Dataset X n) {ε η : ℝ} (hεη : ε ≤ η) :
    IsStableCoreset D P (indexedSample P Finset.univ) ε η := by
  have hc : ∀ z, D.cost (indexedSample P Finset.univ) z = D.cost P z := by
    intro z
    unfold Dist.cost
    rw [sum_indexedSample]
    simp
  intro x y hcomp
  rw [hc x, hc y] at hcomp
  exact stable_of_full_of_le D P hεη x y hcomp

/-- All size-`n` samples are stable, with probability exactly one. -/
theorem uniform_stable_full {X : Type*} (D : Dist X) {n : ℕ}
    (P : Dataset X n) {ε η : ℝ} (hεη : ε ≤ η) :
    (((Finset.univ : Finset (Fin n)).powersetCard n).filter
      (fun I => IsStableCoreset D P (indexedSample P I) ε η)).card
      / (n.choose n : ℝ) = 1 := by
  have hp : (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  have hgood : IsStableCoreset D P (indexedSample P Finset.univ) ε η :=
    indexedSample_full_stable D P hεη
  rw [hp, Finset.filter_singleton]
  rw [if_pos hgood]
  simp

/-- The practical sample rule `min(n,ceil(20/ε²))` includes small datasets. -/
theorem uniform_stable_min {X : Type*} (S : SquaredMetric X) {n : ℕ}
    (hn : 0 < n) (P : Dataset X n) (μ : X) (hμ : S.toDist.IsGeometricMedian P μ)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4) :
    let m := min n ⌈20 / (ε * ε)⌉₊
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset S.toDist P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4 / 5 := by
  dsimp only
  by_cases hsmall : n ≤ ⌈20 / (ε * ε)⌉₊
  · rw [min_eq_left hsmall, uniform_stable_full S.toDist P (by linarith : ε ≤ 17 * ε)]
    norm_num
  · rw [min_eq_right (le_of_not_ge hsmall)]
    apply uniform_stable_4_5_ceil S hn _ (le_of_not_ge hsmall) P μ hμ hε hε' le_rfl
    exact Nat.ceil_pos.2 (by positivity)

end GeometricMedianCoresets
