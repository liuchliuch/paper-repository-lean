import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Source objects for P34. The polynomial space is mathlib's actual bounded
coordinate-degree submodule, not an arbitrary normed space. The Chebyshev
law is defined by the angular pushforward; equivalence with the displayed
Lebesgue density and its cell masses is not asserted here. -/
open Set MeasureTheory
namespace Paper34

abbrev Point (n : ℕ) := Fin n → ℝ
abbrev PolynomialSpace (n d : ℕ) := MvPolynomial.restrictDegree (Fin n) ℝ d
abbrev CellIndex (n m : ℕ) := Fin n → Fin m

noncomputable def polyEval {n d : ℕ} (q : PolynomialSpace n d) (x : Point n) : ℝ :=
  MvPolynomial.eval x q.1

def cube (n : ℕ) : Set (Point n) := Icc (fun _ => -1) (fun _ => 1)

noncomputable def cellLower {n m : ℕ} (j : CellIndex n m) (k : Fin n) : ℝ :=
  Real.cos (((j k : ℕ) + 1 : ℝ) * Real.pi / m)

noncomputable def cellUpper {n m : ℕ} (j : CellIndex n m) (k : Fin n) : ℝ :=
  Real.cos ((j k : ℕ) * Real.pi / m)

noncomputable def closedCell {n m : ℕ} (j : CellIndex n m) : Set (Point n) :=
  Icc (cellLower j) (cellUpper j)

noncomputable def angularLaw (n : ℕ) : Measure (Point n) :=
  (ENNReal.ofReal (Real.pi ^ n))⁻¹ •
    (volume.restrict (Icc (fun _ => 0) (fun _ => Real.pi)))

noncomputable def chebyshevLaw (n : ℕ) : Measure (Point n) :=
  Measure.map (fun theta k => Real.cos (theta k)) (angularLaw n)

noncomputable def uniformLaw (n : ℕ) : Measure (Point n) :=
  (ENNReal.ofReal ((2 : ℝ) ^ n))⁻¹ • volume.restrict (cube n)

noncomputable def l1Norm {n d : ℕ} (q : PolynomialSpace n d) : ℝ :=
  ∫ x, |polyEval q x| ∂chebyshevLaw n

noncomputable def supNorm {n d : ℕ} (q : PolynomialSpace n d) : ℝ :=
  sSup ((fun x => |polyEval q x|) '' cube n)

theorem continuous_polyEval {n d : ℕ} (q : PolynomialSpace n d) :
    Continuous (polyEval q) := MvPolynomial.continuous_eval q.1

theorem convex_closedCell {n m : ℕ} (j : CellIndex n m) :
    Convex ℝ (closedCell j) := convex_Icc _ _

theorem isCompact_closedCell {n m : ℕ} (j : CellIndex n m) :
    IsCompact (closedCell j) := isCompact_Icc

theorem closedCell_subset_cube {n m : ℕ} (j : CellIndex n m) :
    closedCell j ⊆ cube n := by
  intro x hx
  constructor
  · intro k
    exact (Real.neg_one_le_cos _).trans (hx.1 k)
  · intro k
    exact (hx.2 k).trans (Real.cos_le_one _)

theorem cube_nonempty (n : ℕ) : (cube n).Nonempty := by
  refine ⟨0, ?_⟩
  constructor <;> intro k <;> norm_num

/-- Actual compact-domain supremum attainment for every source polynomial. -/
theorem supNorm_attained {n d : ℕ} (q : PolynomialSpace n d) :
    ∃ x ∈ cube n, |polyEval q x| = supNorm q := by
  have hc : ContinuousOn (fun x => |polyEval q x|) (cube n) :=
    (continuous_polyEval q).abs.continuousOn
  obtain ⟨x, hx, hmax⟩ := (isCompact_Icc : IsCompact (cube n)).exists_isMaxOn
    (cube_nonempty n) hc
  refine ⟨x, hx, ?_⟩
  apply le_antisymm
  · exact le_csSup (by
      refine ⟨|polyEval q x|, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact hmax hy) ⟨x, hx, rfl⟩
  · exact csSup_le (Set.Nonempty.image _ (cube_nonempty n)) (by
      rintro _ ⟨y, hy, rfl⟩
      exact hmax hy)

theorem eval_le_supNorm {n d : ℕ} (q : PolynomialSpace n d) {x : Point n}
    (hx : x ∈ cube n) : |polyEval q x| ≤ supNorm q := by
  obtain ⟨z, hz, heq⟩ := supNorm_attained q
  have hc : ContinuousOn (fun x => |polyEval q x|) (cube n) :=
    (continuous_polyEval q).abs.continuousOn
  have hbounded := ((isCompact_Icc : IsCompact (cube n)).image_of_continuousOn hc).bddAbove
  exact le_csSup hbounded ⟨x, hx, rfl⟩

theorem supNorm_nonneg {n d : ℕ} (q : PolynomialSpace n d) : 0 ≤ supNorm q := by
  obtain ⟨x, _, hx⟩ := supNorm_attained q
  rw [← hx]
  exact abs_nonneg _

@[simp] theorem polyEval_add {n d : ℕ} (q r : PolynomialSpace n d) (x : Point n) :
    polyEval (q+r) x = polyEval q x + polyEval r x := by simp [polyEval]

@[simp] theorem polyEval_sub {n d : ℕ} (q r : PolynomialSpace n d) (x : Point n) :
    polyEval (q-r) x = polyEval q x - polyEval r x := by simp [polyEval]

/-- The total-degree extension in Appendix A uses a genuine subspace inclusion. -/
theorem totalDegree_subspace (n d : ℕ) :
    MvPolynomial.restrictTotalDegree (Fin n) ℝ d ≤
      MvPolynomial.restrictDegree (Fin n) ℝ d :=
  MvPolynomial.restrictTotalDegree_le_restrictDegree _ _ _

end Paper34
