import Paper08.LowerBoundGrid
import Paper08.FactorModel
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section
open scoped Real BigOperators
open Set
namespace Paper08.LowerBound

lemma compactBumpDeriv_eq_zero_of_not_mem_Ioo {t : ℝ} (ht : t ∉ Ioo (0 : ℝ) 1) :
    compactBumpDeriv t = 0 := by
  by_cases hc : t ∈ Icc (0 : ℝ) 1
  · have he : t = 0 ∨ t = 1 := by
      simp only [mem_Ioo, not_and_or, not_lt] at ht
      rcases ht with h | h
      · exact Or.inl (le_antisymm h hc.1)
      · exact Or.inr (le_antisymm hc.2 h)
    rcases he with rfl | rfl
    · exact compactBumpDeriv_zero
    · exact compactBumpDeriv_one
  · exact if_neg hc

lemma compactBumpDeriv_abs_le (t : ℝ) : |compactBumpDeriv t| ≤ 8 := by
  rw [← (hasDerivAt_compactBump t).deriv]
  exact compactBump_deriv_abs_le_eight t

/-- The actual directional derivative of one cell bump. -/
def gridBumpD {r L : ℕ} (a : ℝ) (z : GridCell r L) (x h : Fin r → ℝ) : ℝ :=
  a * ∑ j, (∏ k ∈ Finset.univ.erase j,
    compactBump ((L : ℝ) * x k - (z k : ℝ))) *
      compactBumpDeriv ((L : ℝ) * x j - (z j : ℝ)) * h j

lemma hasDerivAt_gridBump_line {r L : ℕ} (hL : 0 < L) (a : ℝ)
    (z : GridCell r L) (x h : Fin r → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gridBump a z (fun j => x j + s * h j))
      (gridBumpD a z (fun j => x j + t * h j) h) t := by
  have hd : ∀ j : Fin r, HasDerivAt
      (fun s : ℝ => compactBump ((L : ℝ) * (x j + s * h j) - (z j : ℝ)))
      (compactBumpDeriv ((L : ℝ) * (x j + t * h j) - (z j : ℝ)) * ((L : ℝ) * h j)) t := by
    intro j
    have hi : HasDerivAt (fun s : ℝ => (L : ℝ) * (x j + s * h j) - (z j : ℝ))
        ((L : ℝ) * h j) t := by
      simpa only [id_eq, one_mul] using
        ((((hasDerivAt_id t).mul_const (h j)).const_add (x j)).const_mul (L : ℝ)).sub_const (z j : ℝ)
    exact (hasDerivAt_compactBump _).comp t hi
  have hp := (HasDerivAt.fun_finset_prod (u := Finset.univ) (fun j _ => hd j)).const_mul (a / L)
  convert hp using 1
  simp only [gridBumpD, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  field_simp

lemma gridBumpD_zero_of_not_inGridCell {r L : ℕ} (a : ℝ) (z : GridCell r L)
    (x h : Fin r → ℝ) (hx : ¬ InGridCell z x) : gridBumpD a z x h = 0 := by
  classical
  simp only [InGridCell, not_forall] at hx
  obtain ⟨j, hj⟩ := hx
  have hout : (L : ℝ) * x j - (z j : ℝ) ∉ Ioo (0 : ℝ) 1 := by
    intro hh
    exact hj ⟨by linarith [hh.1], by linarith [hh.2]⟩
  have hb := compactBump_eq_zero_of_not_mem_Ioo hout
  have hd := compactBumpDeriv_eq_zero_of_not_mem_Ioo hout
  unfold gridBumpD
  rw [Finset.sum_eq_zero, mul_zero]
  intro k _
  by_cases hkj : k = j
  · subst k
    rw [hd, mul_zero, zero_mul]
  · have hz : (∏ l ∈ Finset.univ.erase k,
        compactBump ((L : ℝ) * x l - (z l : ℝ))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hkj, Finset.mem_univ j⟩) hb
    rw [hz, zero_mul, zero_mul]

lemma gridBumpD_abs_le {r L : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (z : GridCell r L) (x h : Fin r → ℝ) :
    |gridBumpD a z x h| ≤ 8 * a * ∑ j, |h j| := by
  unfold gridBumpD
  rw [abs_mul, abs_of_nonneg ha]
  calc
    a * |∑ j, (∏ k ∈ Finset.univ.erase j,
        compactBump ((L : ℝ) * x k - (z k : ℝ))) *
        compactBumpDeriv ((L : ℝ) * x j - (z j : ℝ)) * h j|
      ≤ a * ∑ j, |(∏ k ∈ Finset.univ.erase j,
        compactBump ((L : ℝ) * x k - (z k : ℝ))) *
        compactBumpDeriv ((L : ℝ) * x j - (z j : ℝ)) * h j| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) ha
    _ ≤ a * ∑ j, 8 * |h j| := by
      apply mul_le_mul_of_nonneg_left _ ha
      apply Finset.sum_le_sum
      intro j _
      have hp0 : 0 ≤ ∏ k ∈ Finset.univ.erase j,
          compactBump ((L : ℝ) * x k - (z k : ℝ)) :=
        Finset.prod_nonneg fun k _ => compactBump_nonneg _
      have hp1 : (∏ k ∈ Finset.univ.erase j,
          compactBump ((L : ℝ) * x k - (z k : ℝ))) ≤ 1 :=
        Finset.prod_le_one (fun k _ => compactBump_nonneg _) (fun k _ => compactBump_le_one _)
      rw [abs_mul, abs_mul, abs_of_nonneg hp0]
      have hh : (∏ k ∈ Finset.univ.erase j,
          compactBump ((L : ℝ) * x k - (z k : ℝ))) *
          |compactBumpDeriv ((L : ℝ) * x j - (z j : ℝ))| ≤ 8 := by
        exact (mul_le_mul hp1 (compactBumpDeriv_abs_le _) (abs_nonneg _) zero_le_one).trans_eq
          (one_mul 8)
      exact mul_le_mul_of_nonneg_right hh (abs_nonneg _)
    _ = 8 * a * ∑ j, |h j| := by rw [← Finset.mul_sum]; ring

/-- Disjoint cell interiors bound the derivative of the complete fooling function. -/
lemma foolingBumpD_abs_le {r L : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (queries : Finset (Fin r → ℝ)) (x h : Fin r → ℝ) :
    |∑ z ∈ activeGridCells (L := L) queries, gridBumpD a z x h| ≤
      8 * a * ∑ j, |h j| := by
  classical
  by_cases hin : ∃ z ∈ activeGridCells (L := L) queries, InGridCell z x
  · obtain ⟨z, hz, hx⟩ := hin
    rw [Finset.sum_eq_single z]
    · exact gridBumpD_abs_le ha z x h
    · intro w hw hne
      exact gridBumpD_zero_of_not_inGridCell a w x h
        (fun hwx => hne (inGridCell_unique hwx hx))
    · intro hn
      exact False.elim (hn hz)
  · rw [Finset.sum_eq_zero]
    · simp only [abs_zero]
      positivity
    · intro z hz
      exact gridBumpD_zero_of_not_inGridCell a z x h (fun hx => hin ⟨z, hz, hx⟩)

lemma sum_abs_le_sqrt_mul_euclNorm {r : ℕ} (h : Fin r → ℝ) :
    (∑ j, |h j|) ≤ Real.sqrt r * euclNorm h := by
  have hc := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : Fin r => (1 : ℝ))
    (fun j => |h j|)
  simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, euclNorm, EuclideanSpace.norm_eq,
    Real.norm_eq_abs] using hc

/-- The assembled global `C¹` fooling function has the paper's Euclidean
Lipschitz constant `8 a sqrt r`, independent of the grid size and query count. -/
theorem foolingBump_euclidean_lipschitz {r L : ℕ} {a : ℝ} (ha : 0 ≤ a) (hL : 0 < L)
    (queries : Finset (Fin r → ℝ)) (x y : Fin r → ℝ) :
    |foolingBump (L := L) a queries x - foolingBump (L := L) a queries y| ≤
      (8 * a * Real.sqrt r) * euclDist x y := by
  let h : Fin r → ℝ := fun j => x j - y j
  let f : ℝ → ℝ := fun t => foolingBump (L := L) a queries (fun j => y j + t * h j)
  have hd (t : ℝ) : HasDerivAt f
      (∑ z ∈ activeGridCells (L := L) queries,
        gridBumpD a z (fun j => y j + t * h j) h) t :=
    HasDerivAt.fun_sum fun z _ => hasDerivAt_gridBump_line hL a z y h t
  have hC : 0 ≤ 8 * a * ∑ j, |h j| := by positivity
  have hLip : LipschitzWith ⟨8 * a * ∑ j, |h j|, hC⟩ f :=
    lipschitzWith_of_nnnorm_deriv_le (fun t => (hd t).differentiableAt) (fun t => by
      change |deriv f t| ≤ _
      rw [(hd t).deriv]
      exact foolingBumpD_abs_le ha queries _ h)
  have hxy := hLip.norm_sub_le (1 : ℝ) 0
  have hx : (fun j => y j + 1 * h j) = x := by funext j; dsimp [h]; ring
  have hy : (fun j => y j + 0 * h j) = y := by funext j; ring
  simp only [f, hx, hy, Real.norm_eq_abs, sub_zero, abs_one, mul_one] at hxy
  calc
    _ ≤ 8 * a * ∑ j, |h j| := hxy
    _ ≤ 8 * a * (Real.sqrt r * euclNorm h) :=
      mul_le_mul_of_nonneg_left (sum_abs_le_sqrt_mul_euclNorm h) (by positivity)
    _ = (8 * a * Real.sqrt r) * euclDist x y := by simp only [mul_assoc]; rfl

end Paper08.LowerBound
