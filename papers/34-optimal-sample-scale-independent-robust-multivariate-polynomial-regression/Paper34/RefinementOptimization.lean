import Paper34.Refinement
import Paper34.NativeNorms
import Paper34.LADInitialization
import Mathlib.Topology.Order.Lattice

/-! Actual optimizer existence on every nonempty-cell branch. No assumption
about the unknown truth, noise scale, or corruption is used in this module. -/
namespace Paper34
open BigOperators
noncomputable section

/-- The minimax objective is continuous on the genuine finite-dimensional
polynomial space, for any representatives and any finite residual medians. -/
theorem continuous_representativeResidual {n d m : ℕ} [NeZero m]
    (a : CellIndex n m → Point n) (y : CellIndex n m → ℝ) :
    Continuous (representativeResidual (d := d) a y) := by
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro j _
  exact ((continuous_polyEval_in_polynomial (a j)).sub continuous_const).abs

/-- Cell oscillation makes representative evaluation a norm. This is the
quantitative argument in Proposition 6.2, before adding the median offsets. -/
theorem norm_le_residual_add_oscillation {n d m : ℕ} [NeZero m]
    (a : CellIndex n m → Point n) (y : CellIndex n m → ℝ)
    (ha : ∀ j, a j ∈ closedCell j) (q : PolynomialSpace n d) {gamma : ℝ}
    (hosc : CellOscillation (m := m) gamma q) :
    (1-gamma)*‖q‖-representativeResidual a y (0 : PolynomialSpace n d) ≤
      representativeResidual a y q := by
  obtain ⟨x, hx, hmax⟩ := supNorm_attained q
  obtain ⟨j, hj⟩ := cube_covered_by_closedCells (NeZero.pos m) x hx
  have htri : |polyEval q x| ≤ |polyEval q (a j)|+
      |polyEval q x-polyEval q (a j)| := by
    calc |polyEval q x| = |polyEval q (a j)+(polyEval q x-polyEval q (a j))| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hrep : |polyEval q (a j)| ≤ |polyEval q (a j)-y j|+|y j| := by
    simpa only [sub_add_cancel] using abs_add_le (polyEval q (a j)-y j) (y j)
  have hq := representative_le_residual a y q j
  have h0 := representative_le_residual a y (0 : PolynomialSpace n d) j
  have h0' : |y j| ≤ representativeResidual a y (0 : PolynomialSpace n d) := by
    simpa [polyEval] using h0
  have ho := hosc j x (a j) hj (ha j)
  rw [hmax, ← norm_eq_supNorm] at htri
  rw [← norm_eq_supNorm] at ho
  linarith

theorem representativeResidual_attains_minimum {n d m : ℕ} [NeZero m]
    (a : CellIndex n m → Point n) (y : CellIndex n m → ℝ)
    (ha : ∀ j, a j ∈ closedCell j) {gamma : ℝ} (hg : gamma < 1)
    (hosc : ∀ q : PolynomialSpace n d, CellOscillation (m := m) gamma q) :
    ∃ r : PolynomialSpace n d, ∀ q : PolynomialSpace n d,
      representativeResidual a y r ≤ representativeResidual a y q := by
  apply exists_min_of_lower_norm (continuous_representativeResidual a y) (by linarith : 0 < 1-gamma)
  intro q
  exact norm_le_residual_add_oscillation a y ha q (hosc q)

/-- The full-sample evaluation objective is an actual multiset Phi. -/
theorem weightedEvaluation_eq_Phi {n m d : ℕ} {ι : Type*}
    (D : GoodSampleGrid n m ι) (q : PolynomialSpace n d) :
    weightedAverage D.samples (fun _ i => |polyEval q (D.location i)|) =
      multisetPhi (fun j => locationMultiset (D.samples j) D.location) q := by
  simp only [multisetPhi, locationMultiset_average, weightedAverage]
  simp [CellIndex, div_eq_mul_inv, mul_comm]

/-- Every nonempty family of cell samples gives an attained LAD objective,
including inputs that are not statistically good. -/
theorem weightedLAD_attains_on_nonempty_grid {n m d : ℕ} [NeZero m] {ι : Type*}
    (D : GoodSampleGrid n m ι) (Y : ι → ℝ) {z : ℝ} (hz : z < 1)
    (hnorm : MultisetNorming n d m z) (hnik : L1ToSup n d) :
    ∃ q : PolynomialSpace n d, ∀ r : PolynomialSpace n d,
      weightedLAD D.samples D.location Y q ≤ weightedLAD D.samples D.location Y r := by
  let A := fun j => locationMultiset (D.samples j) D.location
  have hA : ∀ j, A j ≠ 0 := by
    intro j hz
    have hc := congrArg Multiset.card hz
    apply Finset.card_ne_zero.mpr (D.nonempty j)
    simpa [A, locationMultiset] using hc
  have hAC : ∀ j x, x ∈ A j → x ∈ closedCell j := by
    intro j x hx
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
    exact D.inside j i hi
  let K : ℝ := (2*(d : ℝ)+1)^n
  have hK : 0 < K := by dsimp [K]; positivity
  have hc : 0 < (1-z)/K := div_pos (by linarith) hK
  apply exists_min_of_lower_norm (continuous_weightedLAD D.samples D.location Y) hc
    (B := weightedLAD D.samples D.location Y (0 : PolynomialSpace n d))
  intro q
  have hpoint : ∀ j, ∀ i ∈ D.samples j,
      |polyEval q (D.location i)|-|Y i| ≤ |polyEval q (D.location i)-Y i| := by
    intro j i hi
    have ht : |polyEval q (D.location i)| ≤
        |polyEval q (D.location i)-Y i|+|Y i| := by
      simpa only [sub_add_cancel] using abs_add_le (polyEval q (D.location i)-Y i) (Y i)
    linarith
  have hraw := weightedAverage_mono D.samples hpoint
  rw [weightedAverage_sub, weightedEvaluation_eq_Phi] at hraw
  have hzero : weightedAverage D.samples (fun _ i => |Y i|) =
      weightedLAD D.samples D.location Y (0 : PolynomialSpace n d) := by
    simp [weightedLAD, polyEval]
  rw [hzero] at hraw
  have hnormq := (hnorm q A hA hAC).1
  have hnikq := mul_le_mul_of_nonneg_left (hnik q) hc.le
  change (1-z)/K*supNorm q ≤ (1-z)/K*(K*l1Norm q) at hnikq
  have hid : (1-z)/K*(K*l1Norm q) = (1-z)*l1Norm q := by field_simp
  rw [hid, ← norm_eq_supNorm] at hnikq
  change _ ≤ weightedLAD D.samples D.location Y q
  dsimp [A] at hnormq
  change multisetPhi (fun j => locationMultiset (D.samples j) D.location) q -
    weightedLAD D.samples D.location Y 0 ≤ weightedLAD D.samples D.location Y q at hraw
  linarith

end
end Paper34
