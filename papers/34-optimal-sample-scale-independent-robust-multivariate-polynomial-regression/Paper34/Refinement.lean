import Paper34.Model
import Paper34.GridGeometry
import Paper34.MedianWitness
import Paper34.Parameters
import Mathlib.Data.Finset.Lattice.Fold

/-! The exact polynomial median-witness result, followed by the deterministic
refinement bridge. The bridge explicitly takes the still-unproved analytic
cell-oscillation estimate and grid-cover property as hypotheses. It is not
claimed as the unconditional source Proposition 5.3. -/
namespace Paper34
open Set
noncomputable section

/-- The full source Lemma 5.2, specialized to the actual product-Chebyshev cell. -/
theorem median_witness {n d m : ℕ} {ι : Type*} {I G : Finset ι}
    (j : CellIndex n m) (e : PolynomialSpace n d)
    (X : ι → Point n) (Z : ι → ℝ) {sigma y : ℝ}
    (hG : G ⊆ I) (hmajor : I.card < 2*G.card)
    (hX : ∀ i ∈ I, X i ∈ closedCell j)
    (hnoise : ∀ i ∈ G, |Z i - polyEval e (X i)| ≤ sigma)
    (hmedian : IsSampleMedian I Z y) :
    ∃ z ∈ closedCell j, |polyEval e z-y| ≤ sigma :=
  mvPolynomial_median_witness_of_convex e.1 hG hmajor hX hnoise hmedian
    (convex_closedCell j)

/-- The analytic property supplied by source Lemma 5.1 (not proved here). -/
def CellOscillation {n d m : ℕ} (gamma : ℝ) (q : PolynomialSpace n d) : Prop :=
  ∀ (j : CellIndex n m) (x z : Point n),
    x ∈ closedCell j → z ∈ closedCell j →
    |polyEval q x - polyEval q z| ≤ gamma * supNorm q

/-- The actual finite minimax objective from (2.8). -/
def representativeResidual {n d m : ℕ} [NeZero m]
    (a : CellIndex n m → Point n) (y : CellIndex n m → ℝ)
    (q : PolynomialSpace n d) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun j => |polyEval q (a j) - y j|)

theorem representative_le_residual {n d m : ℕ} [NeZero m]
    (a : CellIndex n m → Point n) (y : CellIndex n m → ℝ)
    (q : PolynomialSpace n d) (j : CellIndex n m) :
    |polyEval q (a j)-y j| ≤ representativeResidual a y q :=
by
  unfold representativeResidual
  exact Finset.le_sup' (fun j => |polyEval q (a j)-y j|) (Finset.mem_univ j)

theorem residual_le_of_forall {n d m : ℕ} [NeZero m]
    (a : CellIndex n m → Point n) (y : CellIndex n m → ℝ)
    (q : PolynomialSpace n d) {v : ℝ}
    (h : ∀ j, |polyEval q (a j)-y j| ≤ v) :
    representativeResidual a y q ≤ v :=
  Finset.sup'_le _ _ (fun j _ => h j)

/-- The true one-step polynomial argument, with its analytic dependency visible.
The optimizer premise is actual minimization over all source polynomials. -/
theorem one_step_of_cell_oscillation {n d m : ℕ} [NeZero m]
    (e r : PolynomialSpace n d) (a : CellIndex n m → Point n)
    (y : CellIndex n m → ℝ) {sigma gamma b : ℝ}
    (ha : ∀ j, a j ∈ closedCell j)
    (hcover : ∀ x ∈ cube n, ∃ j : CellIndex n m, x ∈ closedCell j)
    (hwitness : ∀ j, ∃ z ∈ closedCell j, |polyEval e z-y j| ≤ sigma)
    (heosc : CellOscillation (m := m) gamma e)
    (hrosc : CellOscillation (m := m) gamma (r-e))
    (hopt : ∀ q : PolynomialSpace n d,
      representativeResidual a y r ≤ representativeResidual a y q)
    (hs : 0 ≤ sigma) (hb : 0 ≤ b) (hg0 : 0 ≤ gamma)
    (hg : gamma ≤ b/(2+b)) :
    supNorm (r-e) ≤ (2+b)*sigma + b*supNorm e := by
  have heval : ∀ j, |polyEval e (a j)-y j| ≤ sigma + gamma*supNorm e := by
    intro j
    obtain ⟨z, hz, hw⟩ := hwitness j
    calc |polyEval e (a j)-y j| ≤
        |polyEval e (a j)-polyEval e z| + |polyEval e z-y j| :=
      abs_sub_le _ _ _
      _ ≤ gamma*supNorm e + sigma := add_le_add (heosc j (a j) z (ha j) hz) hw
      _ = sigma + gamma*supNorm e := add_comm _ _
  have hrval : ∀ j, |polyEval r (a j)-y j| ≤ sigma+gamma*supNorm e := by
    intro j
    exact (representative_le_residual a y r j).trans
      ((hopt e).trans (residual_le_of_forall a y e heval))
  have hdiff : ∀ j, |polyEval (r-e) (a j)| ≤ 2*sigma+2*gamma*supNorm e := by
    intro j
    rw [polyEval_sub]
    calc |polyEval r (a j)-polyEval e (a j)| ≤
        |polyEval r (a j)-y j| + |y j-polyEval e (a j)| := abs_sub_le _ _ _
      _ = |polyEval r (a j)-y j| + |polyEval e (a j)-y j| := by rw [abs_sub_comm (y j)]
      _ ≤ (sigma+gamma*supNorm e) + (sigma+gamma*supNorm e) :=
        add_le_add (hrval j) (heval j)
      _ = 2*sigma+2*gamma*supNorm e := by ring
  obtain ⟨x, hx, hmax⟩ := supNorm_attained (r-e)
  obtain ⟨j, hj⟩ := hcover x hx
  have hraw : supNorm (r-e) ≤ 2*sigma+2*gamma*supNorm e+gamma*supNorm (r-e) := by
    calc supNorm (r-e) = |polyEval (r-e) x| := hmax.symm
      _ ≤ |polyEval (r-e) (a j)| + |polyEval (r-e) x-polyEval (r-e) (a j)| := by
        calc |polyEval (r-e) x| =
            |polyEval (r-e) (a j) + (polyEval (r-e) x-polyEval (r-e) (a j))| := by congr 1; ring
          _ ≤ _ := abs_add_le _ _
      _ ≤ (2*sigma+2*gamma*supNorm e) + gamma*supNorm (r-e) :=
        add_le_add (hdiff j) (hrosc j x (a j) hj (ha j))
  exact absorb_oscillation (supNorm_nonneg _) (supNorm_nonneg _) hs hb hg0 hg hraw

/-- Source objects and finite-sample hypotheses of Proposition 5.3, with only
its unresolved analytic cell-oscillation dependency explicitly retained. -/
theorem refinement_of_oscillation {n d m : ℕ} [NeZero m] {ι : Type*}
    (e r : PolynomialSpace n d) (a : CellIndex n m → Point n)
    (S G : CellIndex n m → Finset ι) (X : ι → Point n) (Z : ι → ℝ)
    (y : CellIndex n m → ℝ) {sigma gamma b : ℝ}
    (ha : ∀ j, a j ∈ closedCell j)
    (hG : ∀ j, G j ⊆ S j) (hmajor : ∀ j, (S j).card < 2*(G j).card)
    (hX : ∀ j, ∀ i ∈ S j, X i ∈ closedCell j)
    (hnoise : ∀ j, ∀ i ∈ G j, |Z i-polyEval e (X i)| ≤ sigma)
    (hmedian : ∀ j, IsSampleMedian (S j) Z (y j))
    (hosc : ∀ q : PolynomialSpace n d, CellOscillation (m := m) gamma q)
    (hopt : ∀ q : PolynomialSpace n d,
      representativeResidual a y r ≤ representativeResidual a y q)
    (hs : 0 ≤ sigma) (hb : 0 ≤ b) (hg0 : 0 ≤ gamma)
    (hg : gamma ≤ b/(2+b)) :
    supNorm (r-e) ≤ (2+b)*sigma+b*supNorm e := by
  apply one_step_of_cell_oscillation e r a y ha
    (cube_covered_by_closedCells (NeZero.pos m))
    (fun j => median_witness j e X Z (hG j) (hmajor j) (hX j) (hnoise j) (hmedian j))
    (hosc e) (hosc (r-e)) hopt hs hb hg0 hg

end
end Paper34
