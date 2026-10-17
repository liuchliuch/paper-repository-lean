import Paper34.GoodGrid
import Paper34.ArbitraryRepresentatives
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Sampling on the fixed source half-open partition

`GoodGrid` proves concentration for the closed product cells.  The source
algorithm uses the fixed `halfOpenCell` partition from `ArbitraryRepresentatives`.
This file proves that both actual location laws give the same sample membership
and good-grid event almost surely.  The normalized uniform case is proved from
zero volume of coordinate hyperplanes; the Chebyshev case reuses the proved
angular-pushforward boundary result.  No label measurability is required to
transfer a lower probability bound to a containing estimation-error event.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Paper34

noncomputable section

/-- Coordinate boundary hyperplanes have zero product volume. Consequently
the fixed half-open source cell and its closure agree almost everywhere. -/
theorem halfOpenCell_ae_eq_closedCell_volume {n m : ℕ} (j : CellIndex n m) :
    halfOpenCell j =ᵐ[(volume : Measure (Point n))] closedCell j := by
  have hcoord (k : Fin n) : ∀ᵐ x : Point n ∂volume, x k ≠ cellLower j k :=
    Measure.ae_eval_ne (fun _ : Fin n => (volume : Measure ℝ)) k (cellLower j k)
  filter_upwards [ae_all_iff.mpr hcoord] with x hx
  apply propext
  constructor
  · exact fun hx => halfOpenCell_subset_closedCell j hx
  · intro hclosed
    refine ⟨hclosed, ?_⟩
    intro k
    exact Or.inl (lt_of_le_of_ne (hclosed.1 k) (Ne.symm (hx k)))

/-- The actual normalized-uniform law has the same half-open and closed cell
membership almost surely, including the exterior endpoint convention. -/
theorem uniformLaw_halfOpenCell_ae_eq_closedCell {n m : ℕ} (j : CellIndex n m) :
    halfOpenCell j =ᵐ[uniformLaw n] closedCell j :=
  Measure.ae_smul_measure (ae_restrict_of_ae (halfOpenCell_ae_eq_closedCell_volume j)) _

/-- Actual source sample indices assigned to one fixed half-open cell. -/
def halfOpenSamples {Ω : Type*} [MeasurableSpace Ω] {n m M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (ω : Ω) (j : CellIndex n m) :
    Finset (Fin M) := by
  classical
  exact Finset.univ.filter (fun i => S.X i ω ∈ halfOpenCell j)

/-- Actual outlier indices among the samples assigned to one half-open cell. -/
def halfOpenOutliers {Ω : Type*} [MeasurableSpace Ω] {n m M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (ω : Ω) (j : CellIndex n m) :
    Finset (Fin M) :=
  (halfOpenSamples S ω j).filter (fun i => S.O i ω = true)

/-- The source good-sample event on the fixed disjoint half-open partition.
It uses actual finite sample and outlier cardinalities. -/
def halfOpenGoodEvent {Ω : Type*} [MeasurableSpace Ω] {n m M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) : Set Ω :=
  {ω | ∀ j : CellIndex n m, (halfOpenSamples S ω j).Nonempty ∧
    ((halfOpenOutliers S ω j).card : ℝ) ≤
      alpha rho * ((halfOpenSamples S ω j).card : ℝ)}

/-- Each sample's actual location law transports a cell-membership equality
back to the sample space. The final universal event is obtained by finite
intersection over every sample and every source cell. -/
theorem sampled_cell_membership_ae
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n m M : ℕ} {rho : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law)
    (hcell : ∀ j : CellIndex n m, halfOpenCell j =ᵐ[law] closedCell j) :
    ∀ᵐ ω ∂P, ∀ (i : Fin M) (j : CellIndex n m),
      S.X i ω ∈ halfOpenCell j ↔ S.X i ω ∈ closedCell j := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  have hmap : halfOpenCell j =ᵐ[P.map (S.X i)] closedCell j := by
    rw [S.location_law i]
    exact hcell j
  exact (ae_of_ae_map (S.measurable_X i).aemeasurable hmap).mono
    (fun _ h => Iff.of_eq h)

/-- On an outcome with matching memberships, the fixed half-open sample
assignment is exactly the closed-cell selection used by `GoodGrid`. -/
lemma halfOpenSamples_eq_closedSelection
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n m M : ℕ} {rho : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (ω : Ω) (j : CellIndex n m)
    (hmem : ∀ i : Fin M, S.X i ω ∈ halfOpenCell j ↔ S.X i ω ∈ closedCell j) :
    halfOpenSamples S ω j = selectedIndices (gridPattern S j ω) := by
  classical
  ext i
  simpa [halfOpenSamples, selectedIndices, gridPattern, locationPattern] using hmem i

/-- The two actual cardinality pairs agree whenever the cell memberships do. -/
lemma halfOpenCounts_eq_closedCounts
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n m M : ℕ} {rho : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (ω : Ω) (j : CellIndex n m)
    (hmem : ∀ i : Fin M, S.X i ω ∈ halfOpenCell j ↔ S.X i ω ∈ closedCell j) :
    ((halfOpenSamples S ω j).card : ℝ) = gridCellCount S j ω ∧
      ((halfOpenOutliers S ω j).card : ℝ) = gridOutlierCount S j ω := by
  have hs := halfOpenSamples_eq_closedSelection S ω j hmem
  constructor
  · change ((halfOpenSamples S ω j).card : ℝ) =
      ((selectedIndices (gridPattern S j ω)).card : ℝ)
    rw [hs]
  · change (((halfOpenSamples S ω j).filter (fun i => S.O i ω = true)).card : ℝ) =
      (((selectedIndices (gridPattern S j ω)).filter (fun i => S.O i ω = true)).card : ℝ)
    rw [hs]

/-- Outcome-wise equivalence of the source and closed good-grid events, on
the probability-one event of matching all sample memberships. -/
lemma halfOpenGoodEvent_iff_closed_of_membership
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n m M : ℕ} {rho : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (ω : Ω)
    (hmem : ∀ (i : Fin M) (j : CellIndex n m),
      S.X i ω ∈ halfOpenCell j ↔ S.X i ω ∈ closedCell j) :
    ω ∈ halfOpenGoodEvent (m := m) S ↔ ω ∈ goodGridEvent (m := m) S := by
  constructor
  · intro h j
    have hc := halfOpenCounts_eq_closedCounts S ω j (fun i => hmem i j)
    constructor
    · rw [← hc.1]
      exact Nat.cast_pos.mpr (Finset.card_pos.mpr (h j).1)
    · rw [← hc.1, ← hc.2]
      exact (h j).2
  · intro h j
    have hc := halfOpenCounts_eq_closedCounts S ω j (fun i => hmem i j)
    constructor
    · have hn : (0 : ℝ) < ((halfOpenSamples S ω j).card : ℝ) := by
        rw [hc.1]
        exact (h j).1
      exact Finset.card_pos.mp (Nat.cast_pos.mp hn)
    · rw [hc.1, hc.2]
      exact (h j).2

/-- Almost-sure equality of the actual source event and the concentration event. -/
theorem halfOpenGoodEvent_ae_eq_closed
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n m M : ℕ} {rho : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law)
    (hcell : ∀ j : CellIndex n m, halfOpenCell j =ᵐ[law] closedCell j) :
    halfOpenGoodEvent (m := m) S =ᵐ[P] goodGridEvent (m := m) S := by
  filter_upwards [sampled_cell_membership_ae S hcell] with ω hω
  exact propext (halfOpenGoodEvent_iff_closed_of_membership S ω hω)

/-- Equality of the real probabilities used by the statistical theorem. -/
theorem halfOpenGoodEvent_probability_eq_closed
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n m M : ℕ} {rho : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law)
    (hcell : ∀ j : CellIndex n m, halfOpenCell j =ᵐ[law] closedCell j) :
    P.real (halfOpenGoodEvent (m := m) S) = P.real (goodGridEvent (m := m) S) :=
  measureReal_congr (halfOpenGoodEvent_ae_eq_closed S hcell)

/-- Chebyshev sampling on the source half-open partition, with the exact sample
threshold from Lemma 6.1 and the actual angular-pushforward location law. -/
theorem chebyshev_halfOpen_good_grid_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m M : ℕ} {rho δ : ℝ}
    (S : GridSamplingModel n M rho P (chebyshevLaw n))
    (hChernoff : BernoulliLowerHalfInput P M)
    (hHoeffding : BernoulliSubsetHoeffdingInput P M)
    (hm : 0 < m) (hMpos : 0 < M) (hrho0 : 0 ≤ rho) (hrho : rho < 1/2)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : gridConcentrationConstant rho * (m : ℝ)^n *
      Real.log (2 * ((m ^ n : ℕ) : ℝ) / δ) ≤ M) :
    1 - δ ≤ P.real (halfOpenGoodEvent (m := m) S) := by
  rw [halfOpenGoodEvent_probability_eq_closed S (fun j => halfOpenCell_ae_eq_closedCell hm j)]
  exact chebyshev_good_grid_probability S hChernoff hHoeffding hm hMpos hrho0 hrho hδ0 hδ1 hM

/-- Uniform sampling on the source half-open partition, using the proven
coordinate-hyperplane boundary argument and the exact exponent 2n threshold. -/
theorem uniform_halfOpen_good_grid_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m M : ℕ} {rho δ : ℝ}
    (S : GridSamplingModel n M rho P (uniformLaw n))
    (hChernoff : BernoulliLowerHalfInput P M)
    (hHoeffding : BernoulliSubsetHoeffdingInput P M)
    (hm : 0 < m) (hMpos : 0 < M) (hrho0 : 0 ≤ rho) (hrho : rho < 1/2)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : gridConcentrationConstant rho * (m : ℝ)^(2*n) *
      Real.log (2 * ((m ^ n : ℕ) : ℝ) / δ) ≤ M) :
    1 - δ ≤ P.real (halfOpenGoodEvent (m := m) S) := by
  rw [halfOpenGoodEvent_probability_eq_closed S (fun j => uniformLaw_halfOpenCell_ae_eq_closedCell j)]
  exact uniform_good_grid_probability S hChernoff hHoeffding hm hMpos hrho0 hrho hδ0 hδ1 hM

/-- Source per-cell facts needed by the deterministic initializer and refinement. -/
theorem halfOpenGoodEvent_cell_spec
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n m M : ℕ} {rho : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) {ω : Ω}
    (hω : ω ∈ halfOpenGoodEvent (m := m) S) (j : CellIndex n m) :
    (halfOpenSamples S ω j).Nonempty ∧
      ((halfOpenOutliers S ω j).card : ℝ) ≤
        alpha rho * ((halfOpenSamples S ω j).card : ℝ) := hω j

/-- A containing success/error event inherits the source good-grid probability
by measure monotonicity. E can include arbitrary adversarial label functions;
this theorem does not assume measurability of E or of those labels. -/
theorem probability_of_event_containing_halfOpenGoodEvent
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m M : ℕ} {rho δ : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) {E : Set Ω}
    (hgood : 1 - δ ≤ P.real (halfOpenGoodEvent (m := m) S))
    (hcontains : halfOpenGoodEvent (m := m) S ⊆ E) :
    1 - δ ≤ P.real E := hgood.trans (measureReal_mono hcontains)

end
end Paper34
