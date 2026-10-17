import Paper34.CellMass
import Paper34.Parameters
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Lemma 6.1: the good product grid

Two standard concentration inequalities enter as explicit theorem parameters,
never as axioms.  Their source is Dubhashi--Panconesi, *Concentration of Measure
for the Analysis of Randomized Algorithms*, Cambridge UP (2009), Theorem 1.1,
(1.6) and the lower-tail part of (1.7), pp. 6--7:
https://beckassets.blob.core.windows.net/product/readingsample/143671/9780521884273_excerpt_001.pdf

`BernoulliLowerHalfInput` is (1.7) with epsilon = 1/2 and common success
probability p. `BernoulliSubsetHoeffdingInput` is (1.6), restricted to any fixed
subset, with total mean at most rho times its cardinality and
`t = (a-rho)*card`.  Thus non-identical outlier probabilities are retained.

The random-subset transfer below is proved here, using the finite partition
by location membership patterns and the independence of the whole location
vector from the whole outlier vector.  No good-grid probability assertion is
an input.  Only lightweight incremental compilation is authorized for this file.
-/

open Set MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Paper34

noncomputable section

/-- Count successes in a specified finite set; repeated sample indices are
separate observations even when their locations coincide. -/
def boolCount {M : ℕ} (b : Fin M → Bool) (S : Finset (Fin M)) : ℝ :=
  ((S.filter (fun i => b i = true)).card : ℝ)

/-- The selected indices encoded by a location membership pattern. -/
def selectedIndices {M : ℕ} (b : Fin M → Bool) : Finset (Fin M) :=
  Finset.univ.filter (fun i => b i = true)

/-- Membership in a measurable cell, encoded without quotienting sample indices. -/
def locationPattern {E : Type*} {M : ℕ} (C : Set E) (x : Fin M → E) : Fin M → Bool :=
  by
    classical
    exact fun i => if x i ∈ C then true else false

lemma boolCount_univ {M : ℕ} (b : Fin M → Bool) :
    boolCount b Finset.univ = ((selectedIndices b).card : ℝ) := rfl

lemma measurable_locationPattern {E : Type*} [MeasurableSpace E] {M : ℕ}
    {C : Set E} (hC : MeasurableSet C) :
    Measurable (locationPattern (M := M) C) := by
  classical
  apply measurable_pi_lambda
  intro i
  change Measurable (fun x : Fin M → E => if x i ∈ C then true else false)
  exact Measurable.ite (hC.preimage (measurable_pi_apply i)) measurable_const measurable_const

/-- The source's full independence assumptions: iid locations, mutually
independent Bernoulli outliers with possibly different probabilities, and
independence of the two entire random vectors. Labels need no distributional
assumption for Lemma 6.1. -/
structure GridSamplingModel {Ω : Type*} [MeasurableSpace Ω]
    (n M : ℕ) (rho : ℝ) (P : Measure Ω) (locationLaw : Measure (Point n)) where
  X : Fin M → Ω → Point n
  O : Fin M → Ω → Bool
  measurable_X : ∀ i, Measurable (X i)
  measurable_O : ∀ i, Measurable (O i)
  location_law : ∀ i, Measure.map (X i) P = locationLaw
  independent_X : iIndepFun X P
  independent_O : iIndepFun O P
  independent_blocks : IndepFun (fun ω i => X i ω) (fun ω i => O i ω) P
  outlier_rate : ∀ i, P.real {ω | O i ω = true} ≤ rho

/-- Explicit standard external input: independent Bernoulli lower-tail
Chernoff, specialized to half the mean. Original source: Theorem 1.1 (1.7),
lower tail, epsilon = 1/2. Every probabilistic hypothesis is present. -/
def BernoulliLowerHalfInput {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : ℕ) : Prop :=
  ∀ (Y : Fin M → Ω → Bool), (∀ i, Measurable (Y i)) → iIndepFun Y P →
    ∀ p : ℝ, (∀ i, P.real {ω | Y i ω = true} = p) →
      P.real {ω | boolCount (fun i => Y i ω) Finset.univ < (M : ℝ) * p / 2} ≤
        Real.exp (-(M : ℝ) * p / 8)

/-- Explicit standard external input: Hoeffding for a deterministic subset of
independent Bernoulli variables. Original source: Theorem 1.1 (1.6), with
`t = (a-rho)*card`; individual expectations may differ and are only bounded
above by rho. The empty-subset instance is also valid (its event is empty). -/
def BernoulliSubsetHoeffdingInput {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : ℕ) : Prop :=
  ∀ (Y : Fin M → Ω → Bool), (∀ i, Measurable (Y i)) → iIndepFun Y P →
    ∀ rho a : ℝ, 0 ≤ rho → rho < a →
      (∀ i, P.real {ω | Y i ω = true} ≤ rho) →
      ∀ S : Finset (Fin M),
        P.real {ω | a * (S.card : ℝ) < boolCount (fun i => Y i ω) S} ≤
          Real.exp (-2 * (a - rho) ^ 2 * (S.card : ℝ))

/-- The probabilities of all atoms of any finite-valued measurable random
variable sum to one. This is the exact partition identity used in the transfer. -/
lemma sum_pattern_atom_prob {Ω A : Type*} [MeasurableSpace Ω]
    [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    {P : Measure Ω} [IsProbabilityMeasure P] (b : Ω → A) (hb : Measurable b) :
    ∑ a : A, P.real {ω | b ω = a} = 1 := by
  have hd : Pairwise (fun a a' => Disjoint {ω | b ω = a} {ω | b ω = a'}) := by
    intro a a' haa'
    apply Set.disjoint_left.mpr
    intro ω h h'
    exact haa' (h.symm.trans h')
  have hm (a : A) : MeasurableSet {ω | b ω = a} := hb (measurableSet_singleton a)
  have hu : (⋃ a : A, {ω | b ω = a}) = Set.univ := by
    ext ω
    simp
  have h := measureReal_iUnion_fintype (μ := P) hd hm
  rw [hu] at h
  simpa using h.symm

/-- **Random selected-subset transfer.** If the entire membership pattern is
independent of the entire outlier vector, deterministic-subset Hoeffding bounds
remain valid after restricting to outcomes with selected size at least r.
This is proved by a finite partition and multiplication of independent event
probabilities, not by assuming a conditional concentration estimate. -/
theorem random_subset_hoeffding_transfer
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {M : ℕ} (b : Ω → (Fin M → Bool)) (O : Fin M → Ω → Bool)
    (hb : Measurable b) (hindep : IndepFun b (fun ω i => O i ω) P)
    {rho a r : ℝ}
    (hfixed : ∀ S : Finset (Fin M),
      P.real {ω | a * (S.card : ℝ) < boolCount (fun i => O i ω) S} ≤
        Real.exp (-2 * (a - rho) ^ 2 * (S.card : ℝ))) :
    P.real {ω | a * boolCount (b ω) Finset.univ <
        boolCount (fun i => O i ω) (selectedIndices (b ω)) ∧
        r ≤ boolCount (b ω) Finset.univ} ≤
      Real.exp (-2 * (a - rho) ^ 2 * r) := by
  classical
  let atom (s : Fin M → Bool) : Set Ω := {ω | b ω = s}
  let bad (s : Fin M → Bool) : Set Ω :=
    {ω | a * ((selectedIndices s).card : ℝ) <
      boolCount (fun i => O i ω) (selectedIndices s)}
  let piece (s : Fin M → Bool) : Set Ω :=
    if r ≤ ((selectedIndices s).card : ℝ) then atom s ∩ bad s else ∅
  have hsub : {ω | a * boolCount (b ω) Finset.univ <
      boolCount (fun i => O i ω) (selectedIndices (b ω)) ∧
      r ≤ boolCount (b ω) Finset.univ} ⊆ ⋃ s, piece s := by
    intro ω hω
    apply Set.mem_iUnion.mpr
    refine ⟨b ω, ?_⟩
    have hs : r ≤ ((selectedIndices (b ω)).card : ℝ) := hω.2
    simp only [piece, if_pos hs, mem_inter_iff, atom, mem_setOf_eq, true_and]
    exact hω.1
  have hpiece (s : Fin M → Bool) :
      P.real (piece s) ≤ P.real (atom s) * Real.exp (-2 * (a - rho) ^ 2 * r) := by
    by_cases hs : r ≤ ((selectedIndices s).card : ℝ)
    · have hB : MeasurableSet {v : Fin M → Bool |
          a * ((selectedIndices s).card : ℝ) < boolCount v (selectedIndices s)} :=
        (Set.toFinite _).measurableSet
      have hmul := hindep.measure_inter_preimage_eq_mul {s} _
        (measurableSet_singleton s) hB
      have hmulR : P.real (atom s ∩ bad s) = P.real (atom s) * P.real (bad s) := by
        simpa only [Measure.real, ENNReal.toReal_mul] using congrArg ENNReal.toReal hmul
      change P.real (if r ≤ ((selectedIndices s).card : ℝ) then atom s ∩ bad s else ∅) ≤ _
      rw [if_pos hs, hmulR]
      apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
      apply (hfixed (selectedIndices s)).trans
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (a - rho)]
    · change P.real (if r ≤ ((selectedIndices s).card : ℝ) then atom s ∩ bad s else ∅) ≤ _
      rw [if_neg hs]
      simp only [measureReal_empty]
      exact mul_nonneg measureReal_nonneg (Real.exp_pos _).le
  calc
    P.real _ ≤ P.real (⋃ s, piece s) := measureReal_mono hsub
    _ ≤ ∑ s, P.real (piece s) := measureReal_iUnion_fintype_le piece
    _ ≤ ∑ s, P.real (atom s) * Real.exp (-2 * (a - rho) ^ 2 * r) :=
      Finset.sum_le_sum (fun s _ => hpiece s)
    _ = (∑ s, P.real (atom s)) * Real.exp (-2 * (a - rho) ^ 2 * r) :=
      (Finset.sum_mul _ _ _).symm
    _ = Real.exp (-2 * (a - rho) ^ 2 * r) := by
      rw [show (∑ s, P.real (atom s)) = 1 from sum_pattern_atom_prob b hb, one_mul]


/-- The actual source cell-membership pattern of all M sampled locations. -/
def gridPattern {Ω : Type*} [MeasurableSpace Ω] {n m M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (j : CellIndex n m) (ω : Ω) : Fin M → Bool :=
  locationPattern (closedCell j) (fun i => S.X i ω)

/-- Actual sample count in a source cell. -/
def gridCellCount {Ω : Type*} [MeasurableSpace Ω] {n m M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (j : CellIndex n m) (ω : Ω) : ℝ :=
  boolCount (gridPattern S j ω) Finset.univ

/-- Actual outlier count among the selected sample indices in a source cell. -/
def gridOutlierCount {Ω : Type*} [MeasurableSpace Ω] {n m M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (j : CellIndex n m) (ω : Ω) : ℝ :=
  boolCount (fun i => S.O i ω) (selectedIndices (gridPattern S j ω))

/-- The paper's good sample event: every cell is occupied, and its outlier
fraction is at most alpha. Counts refer to indices, so repeated locations count. -/
def goodGridEvent {Ω : Type*} [MeasurableSpace Ω] {n m M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) : Set Ω :=
  {ω | ∀ j : CellIndex n m, 0 < gridCellCount S j ω ∧
    gridOutlierCount S j ω ≤ alpha rho * gridCellCount S j ω}

lemma measurable_gridPattern {Ω : Type*} [MeasurableSpace Ω] {n m M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (j : CellIndex n m) :
    Measurable (gridPattern S j) :=
  (measurable_locationPattern measurableSet_Icc).comp
    (measurable_pi_lambda _ S.measurable_X)

lemma measurable_gridCellCount {Ω : Type*} [MeasurableSpace Ω] {n m M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (j : CellIndex n m) :
    Measurable (gridCellCount S j) :=
  (measurable_of_finite (fun b : Fin M → Bool => boolCount b Finset.univ)).comp
    (measurable_gridPattern S j)

lemma measurable_gridOutlierCount {Ω : Type*} [MeasurableSpace Ω] {n m M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (j : CellIndex n m) :
    Measurable (gridOutlierCount S j) := by
  have ho : Measurable (fun ω i => S.O i ω) := measurable_pi_lambda _ S.measurable_O
  have hf : Measurable (fun bo : (Fin M → Bool) × (Fin M → Bool) =>
      boolCount bo.2 (selectedIndices bo.1)) := measurable_of_finite _
  change Measurable ((fun bo : (Fin M → Bool) × (Fin M → Bool) =>
      boolCount bo.2 (selectedIndices bo.1)) ∘
        (fun ω => (gridPattern S j ω, fun i => S.O i ω)))
  exact hf.comp ((measurable_gridPattern S j).prodMk ho)

lemma measurableSet_goodGridEvent {Ω : Type*} [MeasurableSpace Ω] {n m M : ℕ} {rho : ℝ}
    {P : Measure Ω} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) : MeasurableSet (goodGridEvent (m := m) S) := by
  simp only [goodGridEvent, setOf_forall]
  apply MeasurableSet.iInter
  intro j
  exact (measurableSet_lt measurable_const (measurable_gridCellCount S j)).inter
    (measurableSet_le (measurable_gridOutlierCount S j)
      (measurable_const.mul (measurable_gridCellCount S j)))

/-- The first tail in the proof of Lemma 6.1, from the explicitly identified
standard Chernoff input and the source's iid location law. -/
theorem grid_occupancy_lower_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m M : ℕ} {rho : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law) (hChernoff : BernoulliLowerHalfInput P M)
    (j : CellIndex n m) :
    P.real {ω | gridCellCount S j ω < (M : ℝ) * law.real (closedCell j) / 2} ≤
      Real.exp (-(M : ℝ) * law.real (closedCell j) / 8) := by
  classical
  let f : Point n → Bool := fun x => if x ∈ closedCell j then true else false
  have hf : Measurable f :=
    Measurable.ite measurableSet_Icc measurable_const measurable_const
  let Y : Fin M → Ω → Bool := fun i => f ∘ S.X i
  have hY : ∀ i, Measurable (Y i) := fun i => hf.comp (S.measurable_X i)
  have hI : iIndepFun Y P := S.independent_X.comp (fun _ => f) (fun _ => hf)
  have hmean (i : Fin M) : P.real {ω | Y i ω = true} = law.real (closedCell j) := by
    have hset : {ω | Y i ω = true} = S.X i ⁻¹' closedCell j := by
      ext ω
      simp [Y, f]
    rw [hset]
    have hmap := Measure.map_apply (μ := P) (S.measurable_X i) (measurableSet_Icc :
      MeasurableSet (closedCell j))
    rw [S.location_law i] at hmap
    exact (congrArg ENNReal.toReal hmap).symm
  exact hChernoff Y hY hI (law.real (closedCell j)) hmean

/-- The second tail in Lemma 6.1, including the transfer from deterministic
subsets to the random set of sample indices selected by the locations. -/
theorem grid_outlier_tail_above_half_occupancy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m M : ℕ} {rho : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law)
    (hHoeffding : BernoulliSubsetHoeffdingInput P M)
    (hrho0 : 0 ≤ rho) (hrho : rho < 1/2) (j : CellIndex n m) :
    P.real {ω | alpha rho * gridCellCount S j ω < gridOutlierCount S j ω ∧
      (M : ℝ) * law.real (closedCell j) / 2 ≤ gridCellCount S j ω} ≤
      Real.exp (-(alpha rho - rho)^2 * (M : ℝ) * law.real (closedCell j)) := by
  have hfixed := hHoeffding S.O S.measurable_O S.independent_O rho (alpha rho)
    hrho0 (by dsimp [alpha]; linarith) S.outlier_rate
  have hindep : IndepFun (gridPattern S j) (fun ω i => S.O i ω) P :=
    S.independent_blocks.comp (measurable_locationPattern measurableSet_Icc) measurable_id
  have h := random_subset_hoeffding_transfer (gridPattern S j) S.O
    (measurable_gridPattern S j) hindep (r := (M : ℝ) * law.real (closedCell j) / 2) hfixed
  convert h using 1
  congr 1
  ring

/-- The exact source constant in Lemma 6.1. -/
def gridConcentrationConstant (rho : ℝ) : ℝ := 16 / (1 - 2 * rho)^2

/-- Pure exponential arithmetic behind the final finite union bound. -/
lemma grid_exponential_budget {K : ℕ} (hK : 0 < K) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (K : ℝ) * (Real.exp (-Real.log (2 * (K : ℝ) / δ)) +
      Real.exp (-2 * Real.log (2 * (K : ℝ) / δ))) ≤ δ := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hratio : 0 < 2 * (K : ℝ) / δ := div_pos (by linarith) hδ0
  have hratio1 : 1 ≤ 2 * (K : ℝ) / δ :=
    (le_div_iff₀ hδ0).mpr (by nlinarith)
  have hL : 0 ≤ Real.log (2 * (K : ℝ) / δ) := Real.log_nonneg hratio1
  have hsmall : Real.exp (-2 * Real.log (2 * (K : ℝ) / δ)) ≤
      Real.exp (-Real.log (2 * (K : ℝ) / δ)) := Real.exp_le_exp.mpr (by linarith)
  have he : Real.exp (-Real.log (2 * (K : ℝ) / δ)) = δ / (2 * (K : ℝ)) := by
    rw [Real.exp_neg, Real.exp_log hratio, inv_div]
  calc
    (K : ℝ) * (Real.exp (-Real.log (2 * (K : ℝ) / δ)) +
        Real.exp (-2 * Real.log (2 * (K : ℝ) / δ))) ≤
        (K : ℝ) * (2 * Real.exp (-Real.log (2 * (K : ℝ) / δ))) := by
      nlinarith
    _ = δ := by rw [he]; field_simp

/-- The sample-size hypothesis gives exactly the two exponent comparisons
used by the paper, including `16/(1-2*rho)^2`. -/
lemma grid_sample_bound_exponents {K M : ℕ} (hK : 0 < K)
    {rho δ pmin p : ℝ} (hrho0 : 0 ≤ rho) (hrho : rho < 1/2)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hpmin : 0 < pmin) (hp : pmin ≤ p)
    (hM : gridConcentrationConstant rho * pmin⁻¹ * Real.log (2 * (K : ℝ) / δ) ≤ M) :
    Real.exp (-(M : ℝ) * p / 8) ≤ Real.exp (-2 * Real.log (2 * (K : ℝ) / δ)) ∧
    Real.exp (-(alpha rho - rho)^2 * (M : ℝ) * p) ≤
      Real.exp (-Real.log (2 * (K : ℝ) / δ)) := by
  let L := Real.log (2 * (K : ℝ) / δ)
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hL : 0 ≤ L := Real.log_nonneg ((le_div_iff₀ hδ0).mpr (by nlinarith))
  have ht : 0 < 1 - 2 * rho := by linarith
  have ht1 : 1 - 2 * rho ≤ 1 := by linarith
  have hsq : 0 < (1 - 2 * rho)^2 := sq_pos_of_pos ht
  have hC : 16 ≤ gridConcentrationConstant rho := by
    apply (le_div_iff₀ hsq).mpr
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hM hpmin.le
  have hbase : gridConcentrationConstant rho * L ≤ (M : ℝ) * pmin := by
    convert hmul using 1
    dsimp [L]
    field_simp
  have hbase' : gridConcentrationConstant rho * L ≤ (M : ℝ) * p :=
    hbase.trans (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg M))
  have hfirst : 16 * L ≤ (M : ℝ) * p :=
    (mul_le_mul_of_nonneg_right hC hL).trans hbase'
  have hid : (alpha rho - rho)^2 * gridConcentrationConstant rho = 1 := by
    dsimp [alpha, gridConcentrationConstant]
    field_simp
    ring
  have hsecond := mul_le_mul_of_nonneg_left hbase' (sq_nonneg (alpha rho - rho))
  rw [← mul_assoc, hid, one_mul] at hsecond
  constructor <;> apply Real.exp_le_exp.mpr <;> dsimp [L] at * <;> nlinarith

/-- A finite two-tail union bound with all probability operations proved. -/
lemma finite_grid_union_probability
    {Ω κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {G : Set Ω} (hG : MeasurableSet G) (A B : κ → Set Ω)
    (hsub : Gᶜ ⊆ ⋃ j, A j ∪ B j)
    (hK : 0 < Fintype.card κ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hA : ∀ j, P.real (A j) ≤
      Real.exp (-2 * Real.log (2 * (Fintype.card κ : ℝ) / δ)))
    (hB : ∀ j, P.real (B j) ≤
      Real.exp (-Real.log (2 * (Fintype.card κ : ℝ) / δ))) :
    1 - δ ≤ P.real G := by
  have hfail : P.real Gᶜ ≤ δ := by
    calc
      P.real Gᶜ ≤ P.real (⋃ j, A j ∪ B j) := measureReal_mono hsub
      _ ≤ ∑ j, P.real (A j ∪ B j) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _j : κ, (Real.exp (-Real.log (2 * (Fintype.card κ : ℝ) / δ)) +
          Real.exp (-2 * Real.log (2 * (Fintype.card κ : ℝ) / δ))) := by
        apply Finset.sum_le_sum
        intro j _
        have h := measureReal_union_le (μ := P) (A j) (B j)
        linarith [hA j, hB j]
      _ = (Fintype.card κ : ℝ) *
          (Real.exp (-Real.log (2 * (Fintype.card κ : ℝ) / δ)) +
          Real.exp (-2 * Real.log (2 * (Fintype.card κ : ℝ) / δ))) := by simp [mul_add]
      _ ≤ δ := grid_exponential_budget hK hδ0 hδ1
  have ht := measureReal_add_measureReal_compl (μ := P) hG
  have hu : P.real Set.univ = 1 := by simp
  linarith

/-- **Lemma 6.1**, with only the two named standard concentration inequalities
as explicit external inputs. The location law, all location independence,
non-identical Bernoulli outlier rates, entire-vector independence, random
selection transfer, source constant, and union over the actual m^n cells are
retained. This theorem does not take a good-grid or random-subset tail bound as
an assumption. -/
theorem lemma_6_1_good_product_grid
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m M : ℕ} {rho δ pmin : ℝ} {law : Measure (Point n)}
    (S : GridSamplingModel n M rho P law)
    (hChernoff : BernoulliLowerHalfInput P M)
    (hHoeffding : BernoulliSubsetHoeffdingInput P M)
    (hm : 0 < m) (hMpos : 0 < M) (hrho0 : 0 ≤ rho) (hrho : rho < 1/2)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hpmin : 0 < pmin)
    (hcell : ∀ j : CellIndex n m, pmin ≤ law.real (closedCell j))
    (hM : gridConcentrationConstant rho * pmin⁻¹ *
      Real.log (2 * ((m ^ n : ℕ) : ℝ) / δ) ≤ M) :
    1 - δ ≤ P.real (goodGridEvent (m := m) S) := by
  classical
  let A (j : CellIndex n m) : Set Ω :=
    {ω | gridCellCount S j ω < (M : ℝ) * law.real (closedCell j) / 2}
  let B (j : CellIndex n m) : Set Ω :=
    {ω | alpha rho * gridCellCount S j ω < gridOutlierCount S j ω ∧
      (M : ℝ) * law.real (closedCell j) / 2 ≤ gridCellCount S j ω}
  have hsub : (goodGridEvent (m := m) S)ᶜ ⊆ ⋃ j, A j ∪ B j := by
    intro ω hω
    by_contra hn
    apply hω
    intro j
    have hj : ω ∉ A j ∪ B j := fun hj => hn (Set.mem_iUnion.mpr ⟨j, hj⟩)
    have hN : (M : ℝ) * law.real (closedCell j) / 2 ≤ gridCellCount S j ω := by
      by_contra h
      exact hj (Or.inl (lt_of_not_ge h))
    constructor
    · have hp : 0 < law.real (closedCell j) := hpmin.trans_le (hcell j)
      have hMp : (0 : ℝ) < M := by exact_mod_cast hMpos
      nlinarith
    · by_contra h
      exact hj (Or.inr ⟨lt_of_not_ge h, hN⟩)
  have hK : 0 < m ^ n := pow_pos hm n
  have hcard : Fintype.card (CellIndex n m) = m ^ n := by simp [CellIndex]
  apply finite_grid_union_probability (measurableSet_goodGridEvent S) A B hsub
    (by simpa [hcard] using hK) hδ0 hδ1
  · intro j
    have he := (grid_sample_bound_exponents hK hrho0 hrho hδ0 hδ1 hpmin (hcell j) hM).1
    exact (grid_occupancy_lower_tail S hChernoff j).trans (by simpa [hcard] using he)
  · intro j
    have he := (grid_sample_bound_exponents hK hrho0 hrho hδ0 hδ1 hpmin (hcell j) hM).2
    exact (grid_outlier_tail_above_half_occupancy S hHoeffding hrho0 hrho j).trans
      (by simpa [hcard] using he)


/-- Lemma 6.1 with the actual angular-pushforward Chebyshev cell masses from
`CellMass`: the source's exact finite sample threshold, before asymptotics. -/
theorem chebyshev_good_grid_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m M : ℕ} {rho δ : ℝ}
    (S : GridSamplingModel n M rho P (chebyshevLaw n))
    (hChernoff : BernoulliLowerHalfInput P M)
    (hHoeffding : BernoulliSubsetHoeffdingInput P M)
    (hm : 0 < m) (hMpos : 0 < M) (hrho0 : 0 ≤ rho) (hrho : rho < 1/2)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : gridConcentrationConstant rho * (m : ℝ)^n *
      Real.log (2 * ((m ^ n : ℕ) : ℝ) / δ) ≤ M) :
    1 - δ ≤ P.real (goodGridEvent (m := m) S) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  apply lemma_6_1_good_product_grid S hChernoff hHoeffding hm hMpos hrho0 hrho
    hδ0 hδ1 (pmin := ((m : ℝ)^n)⁻¹) (by positivity)
  · intro j
    change ((m : ℝ)^n)⁻¹ ≤ (chebyshevLaw n (closedCell j)).toReal
    rw [chebyshevLaw_closedCell hm j, ENNReal.toReal_ofReal (by positivity)]
    simp only [inv_pow]
    exact le_rfl
  · simpa only [inv_inv] using hM

/-- Lemma 6.1 with the actual normalized-uniform law and its proven lower
cell-mass bound, yielding the source's exponent 2n in the sample threshold. -/
theorem uniform_good_grid_probability
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n m M : ℕ} {rho δ : ℝ}
    (S : GridSamplingModel n M rho P (uniformLaw n))
    (hChernoff : BernoulliLowerHalfInput P M)
    (hHoeffding : BernoulliSubsetHoeffdingInput P M)
    (hm : 0 < m) (hMpos : 0 < M) (hrho0 : 0 ≤ rho) (hrho : rho < 1/2)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hM : gridConcentrationConstant rho * (m : ℝ)^(2*n) *
      Real.log (2 * ((m ^ n : ℕ) : ℝ) / δ) ≤ M) :
    1 - δ ≤ P.real (goodGridEvent (m := m) S) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  apply lemma_6_1_good_product_grid S hChernoff hHoeffding hm hMpos hrho0 hrho
    hδ0 hδ1 (pmin := ((m : ℝ)^(2*n))⁻¹) (by positivity)
  · intro j
    have h := ENNReal.toReal_mono (measure_ne_top (uniformLaw n) (closedCell j))
      (uniformLaw_closedCell_lower_bound hm j)
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    simpa only [Measure.real, inv_pow] using h
  · simpa only [inv_inv] using hM

end
end Paper34
