import Paper08.Perturbation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Total-level product expansion and its tail

We first prove the tail bound for finite rectangular partial sums, and then
pass to the product limit.  This avoids presupposing a multivariate summation
or an error certificate.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Paper08.Quadrature

lemma mem_totalLevels_iff_sum_le {t J : ℕ} {ν : Fin t → ℕ} :
    ν ∈ totalLevels t J ↔ ∑ i, ν i ≤ J := by
  constructor
  · exact fun h => (mem_totalLevels.mp h).2
  · intro h
    exact mem_totalLevels.mpr ⟨fun i =>
      (Finset.single_le_sum (fun j _ => Nat.zero_le (ν j)) (Finset.mem_univ i)).trans h, h⟩

lemma totalLevels_subset_larger_box {t J N : ℕ} (hJN : J ≤ N) :
    totalLevels t J ⊆ levelBox t N := by
  intro ν hν
  apply Fintype.mem_piFinset.mpr
  intro i
  exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr ((mem_totalLevels.mp hν).1 i |>.trans hJN))

/-- Multiplying finite one-dimensional partial sums gives the corresponding
finite box of level vectors, including overlapping local scopes. -/
lemma product_partial_sums (t N : ℕ) (δ : Fin t → ℕ → ℝ) :
    (∏ i, ∑ l ∈ Finset.range (N + 1), δ i l) =
      ∑ ν ∈ levelBox t N, ∏ i, δ i (ν i) :=
  Finset.prod_univ_sum _ _

/-- A finite geometric sum bound, including level zero. -/
lemma finite_geometric_budget {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (N : ℕ) :
    (∑ l ∈ Finset.range (N + 1), q ^ l) ≤ (1 - q)⁻¹ := by
  simpa [Nat.Ico_zero_eq_range, one_div] using
    (geom_sum_Ico_le_of_lt_one (m := 0) (n := N + 1) hq0 hq1)

/-- The key total-level decay: an omitted term is small in one half of its
level, while the other half is summable independently in every factor. -/
lemma total_level_decay {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {J L : ℕ}
    (hJL : J ≤ L) :
    (q * q) ^ L ≤ q ^ J * q ^ L := by
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq0 hq1 hJL) (pow_nonneg hq0 _)

/-- Actual finite-box truncation bound.  The bound is uniform in the outer
box size `N`; its retained set is the total-level simplex of (3.4). -/
theorem finite_box_total_level_tail {t J N : ℕ} (hJN : J ≤ N)
    (δ : Fin t → ℕ → ℝ) (B : Fin t → ℝ) (q : ℝ)
    (hB : ∀ i, 0 ≤ B i) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hδ : ∀ i l, |δ i l| ≤ B i * (q * q) ^ l) :
    |(∏ i, ∑ l ∈ Finset.range (N + 1), δ i l) -
      ∑ ν ∈ totalLevels t J, ∏ i, δ i (ν i)| ≤
        (∏ i, B i) * q ^ J * ((1 - q)⁻¹) ^ t := by
  have hsubset := totalLevels_subset_larger_box (t := t) hJN
  have hsum := Finset.sum_sdiff (f := fun ν : Fin t → ℕ => ∏ i, δ i (ν i)) hsubset
  have hdiff : (∑ ν ∈ levelBox t N, ∏ i, δ i (ν i)) -
      (∑ ν ∈ totalLevels t J, ∏ i, δ i (ν i)) =
      ∑ ν ∈ levelBox t N \ totalLevels t J, ∏ i, δ i (ν i) := by linarith
  have hBprod : 0 ≤ ∏ i, B i := Finset.prod_nonneg fun i _ => hB i
  have hconst : 0 ≤ (∏ i, B i) * q ^ J := mul_nonneg hBprod (pow_nonneg hq0 _)
  rw [product_partial_sums, hdiff]
  calc
    _ ≤ ∑ ν ∈ levelBox t N \ totalLevels t J, |∏ i, δ i (ν i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ν ∈ levelBox t N \ totalLevels t J,
        ((∏ i, B i) * q ^ J) * q ^ (∑ i, ν i) := by
      apply Finset.sum_le_sum
      intro ν hν
      have hnot : J < ∑ i, ν i := by
        have := (Finset.mem_sdiff.mp hν).2
        rwa [mem_totalLevels_iff_sum_le, not_le] at this
      calc
        _ = ∏ i, |δ i (ν i)| := Finset.abs_prod _ _
        _ ≤ ∏ i, B i * (q * q) ^ (ν i) :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hδ i (ν i))
        _ = (∏ i, B i) * (q * q) ^ (∑ i, ν i) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
        _ ≤ (∏ i, B i) * (q ^ J * q ^ (∑ i, ν i)) :=
          mul_le_mul_of_nonneg_left (total_level_decay hq0 hq1.le hnot.le) hBprod
        _ = _ := by ring
    _ ≤ ∑ ν ∈ levelBox t N, ((∏ i, B i) * q ^ J) * q ^ (∑ i, ν i) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      intro ν _ _
      exact mul_nonneg hconst (pow_nonneg hq0 _)
    _ = ((∏ i, B i) * q ^ J) * (∑ l ∈ Finset.range (N + 1), q ^ l) ^ t := by
      rw [← Finset.mul_sum]
      congr 1
      simp_rw [← Finset.prod_pow_eq_pow_sum]
      rw [levelBox, Finset.sum_prod_piFinset]
      simp
    _ ≤ ((∏ i, B i) * q ^ J) * ((1 - q)⁻¹) ^ t := by
      apply mul_le_mul_of_nonneg_left _ hconst
      exact pow_le_pow_left₀ (Finset.sum_nonneg fun l _ => pow_nonneg hq0 l)
        (finite_geometric_budget hq0 hq1 N) t

/-- Pass from the finite-box identity to the limit product.  Convergence of
each one-dimensional increment sum is sufficient; no product-series identity
or tail inequality is assumed. -/
theorem total_level_product_error {t J : ℕ}
    (δ : Fin t → ℕ → ℝ) (u B : Fin t → ℝ) (q : ℝ)
    (hB : ∀ i, 0 ≤ B i) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hδ : ∀ i l, |δ i l| ≤ B i * (q * q) ^ l)
    (hlimit : ∀ i, Tendsto (fun N => ∑ l ∈ Finset.range (N + 1), δ i l)
      atTop (𝓝 (u i))) :
    |(∏ i, u i) - ∑ ν ∈ totalLevels t J, ∏ i, δ i (ν i)| ≤
      (∏ i, B i) * q ^ J * ((1 - q)⁻¹) ^ t := by
  have hprod := tendsto_finset_prod Finset.univ (fun i _ => hlimit i)
  have habs : Tendsto
      (fun N => |(∏ i, ∑ l ∈ Finset.range (N + 1), δ i l) -
        ∑ ν ∈ totalLevels t J, ∏ i, δ i (ν i)|) atTop
      (𝓝 |(∏ i, u i) - ∑ ν ∈ totalLevels t J, ∏ i, δ i (ν i)|) :=
    (hprod.sub tendsto_const_nhds).abs
  apply le_of_tendsto habs
  filter_upwards [eventually_ge_atTop J] with N hN
  exact finite_box_total_level_tail hN δ B q hB hq0 hq1 hδ

/-- The half-decay ratio of Section 3. -/
def halfRatio : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / 2)

lemma halfRatio_nonneg : 0 ≤ halfRatio := by unfold halfRatio; positivity
lemma halfRatio_lt_one : halfRatio < 1 := two_rpow_neg_half_lt_one

lemma halfRatio_sq : halfRatio * halfRatio = (1 / 2 : ℝ) := by
  unfold halfRatio
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  norm_num

lemma halfRatio_pow (J : ℕ) : halfRatio ^ J = (2 : ℝ) ^ (-(J : ℝ) / 2) := by
  unfold halfRatio
  rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
  congr 1
  ring

/-- Uniform total-level error (3.5) for any convergent dyadic increment
expansions; it is a bound on the actual product, with its complete retained
sum explicitly present. -/
theorem dyadic_total_level_product_error {t J : ℕ}
    (δ : Fin t → ℕ → ℝ) (u B : Fin t → ℝ)
    (hB : ∀ i, 0 ≤ B i)
    (hδ : ∀ i l, |δ i l| ≤ B i * (1 / 2 : ℝ) ^ l)
    (hlimit : ∀ i, Tendsto (fun N => ∑ l ∈ Finset.range (N + 1), δ i l)
      atTop (𝓝 (u i))) :
    |(∏ i, u i) - ∑ ν ∈ totalLevels t J, ∏ i, δ i (ν i)| ≤
      (∏ i, B i) * C0 ^ t * (2 : ℝ) ^ (-(J : ℝ) / 2) := by
  have hbound := total_level_product_error (J := J) δ u B halfRatio hB halfRatio_nonneg
    halfRatio_lt_one (by simpa only [halfRatio_sq] using hδ) hlimit
  rw [halfRatio_pow] at hbound
  change _ ≤ (∏ i, B i) * (2 : ℝ) ^ (-(J : ℝ) / 2) * C0 ^ t at hbound
  calc
    _ ≤ _ := hbound
    _ = _ := by ring

end Paper08.Quadrature
