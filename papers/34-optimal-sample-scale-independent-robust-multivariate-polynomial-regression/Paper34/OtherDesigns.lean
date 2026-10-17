import Paper34.SourceSamplingBridge
import Paper34.MainStochastic

/-!
# Appendix A.3: arbitrary iid designs

For a design with boundary atoms, "each cell has probability at least pmin"
means the source algorithm's fixed, disjoint `halfOpenCell` convention. Closed
cell probabilities would count a shared atom more than once and do not imply
the hypothesis below. No absence-of-atoms hypothesis is imposed or inferred.

The two standard Bernoulli concentration contracts are the published inputs
already documented in `GoodGrid`. The random selected-subset transfer,
single-cell tails, sample exponent arithmetic, and finite-grid union bound
are all proved from those inputs and the actual sampling model. In particular,
a good-grid probability estimate is not an external premise.
-/

noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Paper34
namespace OtherDesigns

def cellPattern {Ω : Type*} [MeasurableSpace Ω] {n M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (C : Set (Point n)) (ω : Ω) : Fin M → Bool :=
  locationPattern C (fun i => S.X i ω)

def cellCount {Ω : Type*} [MeasurableSpace Ω] {n M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (C : Set (Point n)) (ω : Ω) : ℝ :=
  boolCount (cellPattern S C ω) Finset.univ

def outlierCount {Ω : Type*} [MeasurableSpace Ω] {n M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (C : Set (Point n)) (ω : Ω) : ℝ :=
  boolCount (fun i => S.O i ω) (selectedIndices (cellPattern S C ω))

lemma measurable_cellPattern {Ω : Type*} [MeasurableSpace Ω] {n M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) {C : Set (Point n)} (hC : MeasurableSet C) :
    Measurable (cellPattern S C) :=
  (measurable_locationPattern hC).comp (measurable_pi_lambda _ S.measurable_X)

lemma measurable_cellCount {Ω : Type*} [MeasurableSpace Ω] {n M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) {C : Set (Point n)} (hC : MeasurableSet C) :
    Measurable (cellCount S C) :=
  (measurable_of_finite (fun b : Fin M → Bool => boolCount b Finset.univ)).comp
    (measurable_cellPattern S hC)

lemma measurable_outlierCount {Ω : Type*} [MeasurableSpace Ω] {n M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) {C : Set (Point n)} (hC : MeasurableSet C) :
    Measurable (outlierCount S C) := by
  have ho : Measurable (fun ω i => S.O i ω) := measurable_pi_lambda _ S.measurable_O
  have hf : Measurable (fun bo : (Fin M → Bool) × (Fin M → Bool) =>
      boolCount bo.2 (selectedIndices bo.1)) := measurable_of_finite _
  change Measurable ((fun bo : (Fin M → Bool) × (Fin M → Bool) =>
      boolCount bo.2 (selectedIndices bo.1)) ∘
        (fun ω => (cellPattern S C ω, fun i => S.O i ω)))
  exact hf.comp ((measurable_cellPattern S hC).prodMk ho)

/-- iid occupancy Chernoff for an arbitrary measurable cell, including cells
whose boundaries carry atoms of the location distribution. -/
theorem occupancy_lower_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n M : ℕ} {rho : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (hChernoff : BernoulliLowerHalfInput P M)
    {C : Set (Point n)} (hC : MeasurableSet C) :
    P.real {ω | cellCount S C ω < (M : ℝ) * law.real C / 2} ≤
      Real.exp (-(M : ℝ) * law.real C / 8) := by
  classical
  let f : Point n → Bool := fun x => if x ∈ C then true else false
  have hf : Measurable f := Measurable.ite hC measurable_const measurable_const
  let Y : Fin M → Ω → Bool := fun i => f ∘ S.X i
  have hY : ∀ i, Measurable (Y i) := fun i => hf.comp (S.measurable_X i)
  have hI : iIndepFun Y P := S.independent_X.comp (fun _ => f) (fun _ => hf)
  have hmean (i : Fin M) : P.real {ω | Y i ω = true} = law.real C := by
    have hset : {ω | Y i ω = true} = S.X i ⁻¹' C := by ext ω; simp [Y, f]
    rw [hset]
    have hmap := Measure.map_apply (μ := P) (S.measurable_X i) hC
    rw [S.location_law i] at hmap
    exact (congrArg ENNReal.toReal hmap).symm
  exact hChernoff Y hY hI (law.real C) hmean

/-- Fixed-subset Hoeffding is transferred to the actual random indices
selected by the measurable cell. All full-vector independence is retained. -/
theorem outlier_tail_above_half_occupancy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n M : ℕ} {rho : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law)
    (hHoeffding : BernoulliSubsetHoeffdingInput P M)
    (hrho0 : 0 ≤ rho) (hrho : rho < 1/2)
    {C : Set (Point n)} (hC : MeasurableSet C) :
    P.real {ω | alpha rho * cellCount S C ω < outlierCount S C ω ∧
      (M : ℝ) * law.real C / 2 ≤ cellCount S C ω} ≤
      Real.exp (-(alpha rho - rho)^2 * (M : ℝ) * law.real C) := by
  have hfixed := hHoeffding S.O S.measurable_O S.independent_O rho (alpha rho)
    hrho0 (by dsimp [alpha]; linarith) S.outlier_rate
  have hindep : IndepFun (cellPattern S C) (fun ω i => S.O i ω) P :=
    S.independent_blocks.comp (measurable_locationPattern hC) measurable_id
  have h := random_subset_hoeffding_transfer (cellPattern S C) S.O
    (measurable_cellPattern S hC) hindep (r := (M : ℝ) * law.real C / 2) hfixed
  convert h using 1
  congr 1
  ring

lemma selectedIndices_halfOpenPattern
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n m M : ℕ} {rho : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (j : CellIndex n m) (ω : Ω) :
    selectedIndices (cellPattern S (halfOpenCell j) ω) = halfOpenSamples S ω j := by
  classical
  ext i
  simp [selectedIndices, cellPattern, locationPattern, halfOpenSamples]

lemma halfOpenCounts
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n m M : ℕ} {rho : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (j : CellIndex n m) (ω : Ω) :
    cellCount S (halfOpenCell j) ω = ((halfOpenSamples S ω j).card : ℝ) ∧
      outlierCount S (halfOpenCell j) ω = ((halfOpenOutliers S ω j).card : ℝ) := by
  constructor
  · rw [cellCount, boolCount_univ, selectedIndices_halfOpenPattern]
  · change (((selectedIndices (cellPattern S (halfOpenCell j) ω)).filter
      (fun i => S.O i ω = true)).card : ℝ) = _
    rw [selectedIndices_halfOpenPattern]
    rfl

lemma halfOpenGoodEvent_iff_counts
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n m M : ℕ} {rho : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (ω : Ω) :
    ω ∈ halfOpenGoodEvent (m := m) S ↔
      ∀ j : CellIndex n m, 0 < cellCount S (halfOpenCell j) ω ∧
        outlierCount S (halfOpenCell j) ω ≤ alpha rho * cellCount S (halfOpenCell j) ω := by
  constructor
  · intro h j
    rw [(halfOpenCounts S j ω).1, (halfOpenCounts S j ω).2]
    exact ⟨Nat.cast_pos.mpr (Finset.card_pos.mpr (h j).1), (h j).2⟩
  · intro h j
    have hj := h j
    rw [(halfOpenCounts S j ω).1, (halfOpenCounts S j ω).2] at hj
    exact ⟨Finset.card_pos.mp (Nat.cast_pos.mp hj.1), hj.2⟩

end OtherDesigns

theorem measurableSet_halfOpenGoodEvent
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {n m M : ℕ} {rho : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) : MeasurableSet (halfOpenGoodEvent (m := m) S) := by
  have heq : halfOpenGoodEvent (m := m) S = {ω |
      ∀ j : CellIndex n m, 0 < OtherDesigns.cellCount S (halfOpenCell j) ω ∧
        OtherDesigns.outlierCount S (halfOpenCell j) ω ≤
          alpha rho * OtherDesigns.cellCount S (halfOpenCell j) ω} := by
    ext ω
    exact OtherDesigns.halfOpenGoodEvent_iff_counts S ω
  rw [heq]
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro j
  exact (measurableSet_lt measurable_const
      (OtherDesigns.measurable_cellCount S (measurableSet_halfOpenCell j))).inter
    (measurableSet_le (OtherDesigns.measurable_outlierCount S (measurableSet_halfOpenCell j))
      (measurable_const.mul (OtherDesigns.measurable_cellCount S (measurableSet_halfOpenCell j))))

/-- Appendix A.3's arbitrary-design good-grid probability on the actual fixed
half-open partition. The threshold is `C_rho/pmin * log(2*m^n/delta)` with
`C_rho = 16/(1-2*rho)^2`. No boundary-atom restriction is present. -/
theorem other_design_halfOpen_good_grid_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m M : ℕ} {rho δ pmin : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law)
    (hChernoff : BernoulliLowerHalfInput P M)
    (hHoeffding : BernoulliSubsetHoeffdingInput P M)
    (hm : 0 < m) (hMpos : 0 < M) (hrho0 : 0 ≤ rho) (hrho : rho < 1/2)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hpmin : 0 < pmin)
    (hcell : ∀ j : CellIndex n m, pmin ≤ law.real (halfOpenCell j))
    (hM : gridConcentrationConstant rho * pmin⁻¹ *
      Real.log (2 * ((m ^ n : ℕ) : ℝ) / δ) ≤ M) :
    1 - δ ≤ P.real (halfOpenGoodEvent (m := m) S) := by
  classical
  let A (j : CellIndex n m) : Set Ω :=
    {ω | OtherDesigns.cellCount S (halfOpenCell j) ω < (M : ℝ) * law.real (halfOpenCell j) / 2}
  let B (j : CellIndex n m) : Set Ω :=
    {ω | alpha rho * OtherDesigns.cellCount S (halfOpenCell j) ω <
        OtherDesigns.outlierCount S (halfOpenCell j) ω ∧
      (M : ℝ) * law.real (halfOpenCell j) / 2 ≤ OtherDesigns.cellCount S (halfOpenCell j) ω}
  have hsub : (halfOpenGoodEvent (m := m) S)ᶜ ⊆ ⋃ j, A j ∪ B j := by
    intro ω hω
    by_contra hn
    apply hω
    apply (OtherDesigns.halfOpenGoodEvent_iff_counts S ω).mpr
    intro j
    have hj : ω ∉ A j ∪ B j := fun hj => hn (Set.mem_iUnion.mpr ⟨j, hj⟩)
    have hN : (M : ℝ) * law.real (halfOpenCell j) / 2 ≤
        OtherDesigns.cellCount S (halfOpenCell j) ω := by
      by_contra h
      exact hj (Or.inl (lt_of_not_ge h))
    constructor
    · have hp : 0 < law.real (halfOpenCell j) := hpmin.trans_le (hcell j)
      have hMp : (0 : ℝ) < M := by exact_mod_cast hMpos
      nlinarith
    · by_contra h
      exact hj (Or.inr ⟨lt_of_not_ge h, hN⟩)
  have hK : 0 < m ^ n := pow_pos hm n
  have hcard : Fintype.card (CellIndex n m) = m ^ n := by simp [CellIndex]
  apply finite_grid_union_probability (measurableSet_halfOpenGoodEvent S) A B hsub
    (by simpa [hcard] using hK) hδ0 hδ1
  · intro j
    have he := (grid_sample_bound_exponents hK hrho0 hrho hδ0 hδ1 hpmin (hcell j) hM).1
    exact (OtherDesigns.occupancy_lower_tail S hChernoff (measurableSet_halfOpenCell j)).trans
      (by simpa [hcard] using he)
  · intro j
    have he := (grid_sample_bound_exponents hK hrho0 hrho hδ0 hδ1 hpmin (hcell j) hM).2
    exact (OtherDesigns.outlier_tail_above_half_occupancy S hHoeffding hrho0 hrho
      (measurableSet_halfOpenCell j)).trans (by simpa [hcard] using he)

/-- The exact finite sample threshold is strictly positive, so no independent
nonempty-batch assumption is necessary in the arbitrary-design formulation. -/
theorem other_design_sample_threshold_implies_positive_batch
    {n m M : ℕ} {rho δ pmin : ℝ} (hm : 0 < m) (hrho : rho < 1/2)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hpmin : 0 < pmin)
    (hM : gridConcentrationConstant rho * pmin⁻¹ *
      Real.log (2 * ((m ^ n : ℕ) : ℝ) / δ) ≤ M) : 0 < M := by
  have hK1 : (1 : ℝ) ≤ (m ^ n : ℕ) := by exact_mod_cast (pow_pos hm n)
  have hratio : 1 < 2 * ((m ^ n : ℕ) : ℝ) / δ :=
    (lt_div_iff₀ hδ0).mpr (by nlinarith)
  have hC : 0 < gridConcentrationConstant rho := by
    unfold gridConcentrationConstant
    apply div_pos (by norm_num)
    exact sq_pos_of_pos (by linarith)
  have hbound : (0 : ℝ) < (M : ℝ) :=
    (mul_pos (mul_pos hC (inv_pos.mpr hpmin)) (Real.log_pos hratio)).trans_le hM
  exact_mod_cast hbound

/-- Threshold-only version of the arbitrary-design source good-grid theorem. -/
theorem other_design_halfOpen_good_grid_probability_of_threshold
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m M : ℕ} {rho δ pmin : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law)
    (hChernoff : BernoulliLowerHalfInput P M) (hHoeffding : BernoulliSubsetHoeffdingInput P M)
    (hm : 0 < m) (hrho0 : 0 ≤ rho) (hrho : rho < 1/2)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hpmin : 0 < pmin)
    (hcell : ∀ j : CellIndex n m, pmin ≤ law.real (halfOpenCell j))
    (hM : gridConcentrationConstant rho * pmin⁻¹ *
      Real.log (2 * ((m ^ n : ℕ) : ℝ) / δ) ≤ M) :
    1 - δ ≤ P.real (halfOpenGoodEvent (m := m) S) :=
  other_design_halfOpen_good_grid_probability S hChernoff hHoeffding hm
    (other_design_sample_threshold_implies_positive_batch hm hrho hδ0 hδ1 hpmin hM)
    hrho0 hrho hδ0 hδ1 hpmin hcell hM

/-- The same actual estimator and error under an arbitrary iid design. The
only change from the two named designs is the true half-open cell mass bound;
neither the estimator nor the deterministic proof receives the location law. -/
theorem other_design_regression_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d m M : ℕ} [NeZero m] {rho eps sigma δ pmin : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (Y : Fin M → Ω → ℝ)
    (hChernoff : BernoulliLowerHalfInput P M) (hHoeffding : BernoulliSubsetHoeffdingInput P M)
    (hrho0 : 0 ≤ rho) (hrho : rho < 1/2) (heps0 : 0 < eps) (heps : eps ≤ 1/2)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hpmin : 0 < pmin)
    (hcell : ∀ j : CellIndex n m, pmin ≤ law.real (halfOpenCell j))
    (hM : gridConcentrationConstant rho * pmin⁻¹ *
      Real.log (2 * ((m ^ n : ℕ) : ℝ) / δ) ≤ M)
    (O : ExactRegressionLPOracle n d m) (C : RegressionAnalysis n d m rho)
    (p : PolynomialSpace n d) (hsigma : 0 ≤ sigma)
    (hgamma0 : 0 ≤ C.gamma) (hgamma : C.gamma ≤ beta eps/(2+beta eps))
    (hnoise : ∀ ω i, S.O i ω = false → |Y i ω-polyEval p (S.X i ω)| ≤ sigma) :
    1-δ ≤ P.real {ω | supNorm
      (batchEstimate O C (refinementBudget n d rho eps heps0 heps)
        (fun i => S.X i ω) (fun i => Y i ω)-p) ≤ (2+eps)*sigma} := by
  exact regression_probability_of_good_grid S Y O C p hrho0 hrho heps0 heps hsigma
    hgamma0 hgamma hnoise
    (other_design_halfOpen_good_grid_probability_of_threshold S hChernoff hHoeffding
      (NeZero.pos m) hrho0 hrho hδ0 hδ1 hpmin hcell hM)

end Paper34
