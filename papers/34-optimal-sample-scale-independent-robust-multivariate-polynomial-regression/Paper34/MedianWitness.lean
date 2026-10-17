import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith

/-!
# The median witness (Lemma 5.2)

This file proves the finite counting step and the continuity step of the paper's
median witness lemma.  The central statement holds for every continuous real
function on a preconnected set.  Convex cells and genuine multivariate
polynomials are then instances, with no analytic witness premise.
-/

namespace Paper34

/-- A sample median has at least half the observations on each weak side.
The doubled natural-number inequalities express the exact half-count condition
also when the number of observations is odd. -/
def IsSampleMedian {ι : Type*} (I : Finset ι) (Z : ι → ℝ) (y : ℝ) : Prop := by
  classical
  exact I.card ≤ 2 * (I.filter (fun i => Z i ≤ y)).card ∧
    I.card ≤ 2 * (I.filter (fun i => y ≤ Z i)).card

/-- Any subset containing at least half of a finite sample intersects every
strict-majority subset.  This proves the counting assertion used on both sides
of a median, including the even-sample equality case. -/
theorem strict_majority_intersects_half {ι : Type*} [DecidableEq ι]
    {I G H : Finset ι} (hG : G ⊆ I) (hH : H ⊆ I)
    (hmajor : I.card < 2 * G.card) (hhalf : I.card ≤ 2 * H.card) :
    ∃ i, i ∈ G ∧ i ∈ H := by
  by_contra h
  have hsub : H ⊆ I \ G := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨hH hi, fun hgi => h ⟨i, hgi, hi⟩⟩
  have hc := Finset.card_le_card hsub
  have hs := Finset.card_sdiff_add_card_eq_card hG
  omega

/-- There is a good observation on each weak side of every sample median. -/
theorem sample_median_good_sides {ι : Type*} {I G : Finset ι}
    {Z : ι → ℝ} {y : ℝ} (hG : G ⊆ I)
    (hmajor : I.card < 2 * G.card) (hmedian : IsSampleMedian I Z y) :
    (∃ i ∈ G, Z i ≤ y) ∧ (∃ i ∈ G, y ≤ Z i) := by
  classical
  rcases hmedian with ⟨hleft, hright⟩
  constructor
  · obtain ⟨i, hiG, hi⟩ := strict_majority_intersects_half hG
      (Finset.filter_subset (fun i => Z i ≤ y) I) hmajor hleft
    exact ⟨i, hiG, (Finset.mem_filter.mp hi).2⟩
  · obtain ⟨i, hiG, hi⟩ := strict_majority_intersects_half hG
      (Finset.filter_subset (fun i => y ≤ Z i) I) hmajor hright
    exact ⟨i, hiG, (Finset.mem_filter.mp hi).2⟩

/-- **Lemma 5.2**, generalized from polynomial functions on rectangular cells to
continuous real functions on preconnected sets.  The index set is finite, the
good indices form a strict majority, and the median uses actual finite counts.
The witness is a point of the cell and need not be a sample location. -/
theorem median_witness_of_isPreconnected
    {ι E : Type*} [TopologicalSpace E]
    {I G : Finset ι} {C : Set E} {X : ι → E} {Z : ι → ℝ}
    {e : E → ℝ} {σ y : ℝ}
    (hG : G ⊆ I) (hmajor : I.card < 2 * G.card)
    (hX : ∀ i ∈ I, X i ∈ C)
    (hnoise : ∀ i ∈ G, |Z i - e (X i)| ≤ σ)
    (hmedian : IsSampleMedian I Z y)
    (hC : IsPreconnected C) (he : ContinuousOn e C) :
    ∃ z ∈ C, |e z - y| ≤ σ := by
  obtain ⟨⟨i_minus, hi_minus, hle⟩, ⟨i_plus, hi_plus, hge⟩⟩ :=
    sample_median_good_sides hG hmajor hmedian
  have hn_minus := (abs_le.mp (hnoise i_minus hi_minus))
  have hn_plus := (abs_le.mp (hnoise i_plus hi_plus))
  have hσ : 0 ≤ σ := (abs_nonneg _).trans (hnoise i_minus hi_minus)
  have hx_minus : X i_minus ∈ C := hX i_minus (hG hi_minus)
  have hx_plus : X i_plus ∈ C := hX i_plus (hG hi_plus)
  have hupper : e (X i_minus) ≤ y + σ := by linarith
  have hlower : y - σ ≤ e (X i_plus) := by linarith
  by_cases hm : y - σ ≤ e (X i_minus)
  · exact ⟨X i_minus, hx_minus, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  by_cases hp : e (X i_plus) ≤ y + σ
  · exact ⟨X i_plus, hx_plus, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  obtain ⟨z, hz, hez⟩ := hC.intermediate_value₂ hx_minus hx_plus he
    (continuousOn_const (c := y)) (by linarith) (by linarith)
  exact ⟨z, hz, by simpa only [hez, sub_self, abs_zero] using hσ⟩

/-- The median witness for a continuous function on a convex real cell. -/
theorem median_witness_of_convex
    {ι E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [Module ℝ E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {I G : Finset ι} {C : Set E} {X : ι → E} {Z : ι → ℝ}
    {e : E → ℝ} {σ y : ℝ}
    (hG : G ⊆ I) (hmajor : I.card < 2 * G.card)
    (hX : ∀ i ∈ I, X i ∈ C)
    (hnoise : ∀ i ∈ G, |Z i - e (X i)| ≤ σ)
    (hmedian : IsSampleMedian I Z y)
    (hC : Convex ℝ C) (he : ContinuousOn e C) :
    ∃ z ∈ C, |e z - y| ≤ σ :=
  median_witness_of_isPreconnected hG hmajor hX hnoise hmedian hC.isPreconnected he

/-- A coordinate rectangle, including degenerate rectangles. -/
def RectangularCell {ν : Type*} (lower upper : ν → ℝ) : Set (ν → ℝ) :=
  {x | ∀ k, lower k ≤ x k ∧ x k ≤ upper k}

/-- Rectangular cells are convex, without needing a positive-width premise. -/
theorem rectangularCell_convex {ν : Type*} (lower upper : ν → ℝ) :
    Convex ℝ (RectangularCell lower upper) := by
  intro x hx y hy a b ha hb hab k
  exact (convex_Icc (lower k) (upper k)) (hx k) (hy k) ha hb hab

/-- The witness for a genuine multivariate polynomial on a convex cell.  Its
continuity is discharged by the polynomial evaluation theorem from Mathlib. -/
theorem mvPolynomial_median_witness_of_convex
    {ι ν : Type*} {I G : Finset ι} {C : Set (ν → ℝ)}
    {X : ι → (ν → ℝ)} {Z : ι → ℝ} (e : MvPolynomial ν ℝ) {σ y : ℝ}
    (hG : G ⊆ I) (hmajor : I.card < 2 * G.card)
    (hX : ∀ i ∈ I, X i ∈ C)
    (hnoise : ∀ i ∈ G, |Z i - MvPolynomial.eval (X i) e| ≤ σ)
    (hmedian : IsSampleMedian I Z y) (hC : Convex ℝ C) :
    ∃ z ∈ C, |MvPolynomial.eval z e - y| ≤ σ :=
  median_witness_of_convex hG hmajor hX hnoise hmedian hC e.continuous_eval.continuousOn

/-- **Lemma 5.2** for a multivariate polynomial and a rectangular cell.
Coordinate-degree restrictions are unnecessary for this lemma, so this theorem
applies in particular to every polynomial in the paper's tensor-degree space. -/
theorem mvPolynomial_rectangular_median_witness
    {ι ν : Type*} {I G : Finset ι} (lower upper : ν → ℝ)
    {X : ι → (ν → ℝ)} {Z : ι → ℝ} (e : MvPolynomial ν ℝ) {σ y : ℝ}
    (hG : G ⊆ I) (hmajor : I.card < 2 * G.card)
    (hX : ∀ i ∈ I, X i ∈ RectangularCell lower upper)
    (hnoise : ∀ i ∈ G, |Z i - MvPolynomial.eval (X i) e| ≤ σ)
    (hmedian : IsSampleMedian I Z y) :
    ∃ z ∈ RectangularCell lower upper, |MvPolynomial.eval z e - y| ≤ σ :=
  mvPolynomial_median_witness_of_convex e hG hmajor hX hnoise hmedian
    (rectangularCell_convex lower upper)

end Paper34
