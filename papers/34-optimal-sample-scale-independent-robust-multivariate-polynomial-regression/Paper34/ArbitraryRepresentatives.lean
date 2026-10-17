import Paper34.CellMass
import Paper34.CellOscillation
import Paper34.AngularMeasure
import Paper34.NativeNorms
import Paper34.NormingInterface
import Paper34.TensorNorming
import Paper34.TensorDerivative
import Paper34.CosineFourierLift
import Paper34.HaarChebyshev
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# The arbitrary representative construction in Lemma 3.3

The representatives below are an arbitrary function of the *whole* cell index.
No tensor product or coordinatewise selection hypothesis is imposed.  We use
`(lower,upper]` in every coordinate, with the exterior endpoint `-1` included
in the final cell.  This is a fixed half-open convention on the source cube.

The proof uses the actual step function, the arccosine lift, the exact
normalized angular integral identity, and a coordinatewise path reduction.
The final theorem `lemma_3_3` calls the internally proved bounded-degree
Fourier representation, local supremum, endpoint Bernstein, and Haar cosine
pushforward theorems. It has no additional analytic or norming premise.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace Paper34

/-- The fixed half-open convention, including the external lower endpoint in
the last coordinate interval. -/
def halfOpenCell {n m : ℕ} (j : CellIndex n m) : Set (Point n) :=
  {x | x ∈ closedCell j ∧ ∀ k, cellLower j k < x k ∨ (j k : ℕ) + 1 = m}

lemma halfOpenCell_subset_closedCell {n m : ℕ} (j : CellIndex n m) :
    halfOpenCell j ⊆ closedCell j := fun _ h => h.1

lemma measurableSet_halfOpenCell {n m : ℕ} (j : CellIndex n m) :
    MeasurableSet (halfOpenCell j) := by
  unfold halfOpenCell
  apply measurableSet_Icc.inter
  have hcoord (k : Fin n) : MeasurableSet {x : Point n |
      cellLower j k < x k ∨ (j k : ℕ) + 1 = m} := by
    by_cases h : (j k : ℕ) + 1 = m
    · simp only [h, or_true, setOf_true, MeasurableSet.univ]
    · simp only [h, or_false]
      exact measurableSet_lt measurable_const (measurable_pi_apply k)
  convert MeasurableSet.iInter hcoord using 1
  ext x
  change (∀ k, cellLower j k < x k ∨ (j k : ℕ) + 1 = m) ↔ _
  simp

lemma exists_unit_halfopen_subinterval : ∀ (m : ℕ), 0 < m → ∀ (u : ℝ),
    0 ≤ u → u ≤ m → ∃ j : Fin m,
      (j : ℝ) ≤ u ∧ (u < (j : ℝ) + 1 ∨ (j : ℕ) + 1 = m) := by
  intro m
  induction m with
  | zero => intro hm; omega
  | succ m ih =>
      intro hm u hu0 hum
      by_cases hm0 : m = 0
      · subst m
        exact ⟨⟨0, by omega⟩, by simpa using hu0, Or.inr rfl⟩
      · by_cases hu : u < (m : ℝ)
        · obtain ⟨j, hj0, hj1⟩ := ih (by omega) u hu0 hu.le
          refine ⟨⟨j.val, Nat.lt_succ_of_lt j.isLt⟩, hj0, Or.inl ?_⟩
          rcases hj1 with hj1 | hj1
          · exact hj1
          · have hcast : (j : ℝ) + 1 = m := by exact_mod_cast hj1
            linarith
        · exact ⟨⟨m, Nat.lt_succ_self m⟩, (not_lt.mp hu), Or.inr rfl⟩

/-- Every point is assigned a cell, including every shared boundary and the
two external endpoints. -/
theorem cube_covered_by_halfOpenCells {n m : ℕ} (hm : 0 < m) (x : Point n)
    (hx : x ∈ cube n) : ∃ j : CellIndex n m, x ∈ halfOpenCell j := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hcoord (k : Fin n) : ∃ j : Fin m,
      Real.cos (((j : ℕ) + (1 : ℝ)) * Real.pi / m) ≤ x k ∧
      x k ≤ Real.cos ((j : ℕ) * Real.pi / m) ∧
      (Real.cos (((j : ℕ) + (1 : ℝ)) * Real.pi / m) < x k ∨
        (j : ℕ) + 1 = m) := by
    let theta := Real.arccos (x k)
    have htheta0 : 0 ≤ theta := Real.arccos_nonneg _
    have hthetaPi : theta ≤ Real.pi := Real.arccos_le_pi _
    have hu0 : (0 : ℝ) ≤ theta * m / Real.pi := by positivity
    have hum : theta * m / Real.pi ≤ m := by
      apply (div_le_iff₀ Real.pi_pos).2
      nlinarith [mul_le_mul_of_nonneg_right hthetaPi (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    obtain ⟨j, hjlo, hjhi⟩ := exists_unit_halfopen_subinterval m hm
      (theta * m / Real.pi) hu0 hum
    have hj : (j : ℝ) + 1 ≤ m := by exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
    have hlo : (j : ℕ) * Real.pi / m ≤ theta := by
      apply (div_le_iff₀ hm').2
      exact (le_div_iff₀ Real.pi_pos).mp hjlo
    have hlo0 : (0 : ℝ) ≤ (j : ℕ) * Real.pi / m := by positivity
    have hhiPi : ((j : ℕ) + (1 : ℝ)) * Real.pi / m ≤ Real.pi := by
      apply (div_le_iff₀ hm').2
      nlinarith [mul_le_mul_of_nonneg_right hj Real.pi_pos.le]
    have hhi : theta ≤ ((j : ℕ) + (1 : ℝ)) * Real.pi / m := by
      rcases hjhi with hh | hh
      · apply (le_div_iff₀ hm').2
        exact (div_le_iff₀ Real.pi_pos).mp hh.le
      · have hh' : (j : ℝ) + 1 = m := by exact_mod_cast hh
        rw [hh', mul_div_cancel_left₀ Real.pi hm'.ne']
        exact hthetaPi
    have hcos : Real.cos theta = x k := Real.cos_arccos (hx.1 k) (hx.2 k)
    refine ⟨j, ?_, ?_, ?_⟩
    · simpa only [hcos] using Real.cos_le_cos_of_nonneg_of_le_pi htheta0 hhiPi hhi
    · simpa only [hcos] using Real.cos_le_cos_of_nonneg_of_le_pi hlo0 hthetaPi hlo
    · rcases hjhi with hh | hh
      · left
        have hstrict : theta < ((j : ℕ) + (1 : ℝ)) * Real.pi / m := by
          apply (lt_div_iff₀ hm').2
          exact (div_lt_iff₀ Real.pi_pos).mp hh
        simpa only [hcos] using Real.cos_lt_cos_of_nonneg_of_le_pi htheta0 hhiPi hstrict
      · exact Or.inr hh
  choose j hj using hcoord
  exact ⟨j, ⟨fun k => (hj k).1, fun k => (hj k).2.1⟩, fun k => (hj k).2.2⟩

/-- Earlier Chebyshev intervals lie above every later interval. -/
lemma cellUpper_le_cellLower_of_lt {n m : ℕ} (hm : 0 < m)
    (i j : CellIndex n m) (k : Fin n) (hij : i k < j k) :
    cellUpper j k ≤ cellLower i k := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hij' : (i k : ℝ) + 1 ≤ j k := by exact_mod_cast hij
  have hj : (j k : ℝ) ≤ m := by exact_mod_cast (j k).isLt.le
  apply Real.cos_le_cos_of_nonneg_of_le_pi
  · positivity
  · change (j k : ℕ) * Real.pi / m ≤ Real.pi
    apply (div_le_iff₀ hm').2
    nlinarith [mul_le_mul_of_nonneg_right hj Real.pi_pos.le]
  · change ((i k : ℕ) + (1 : ℝ)) * Real.pi / m ≤ (j k : ℕ) * Real.pi / m
    apply div_le_div_of_nonneg_right _ hm'.le
    nlinarith [mul_le_mul_of_nonneg_right hij' Real.pi_pos.le]

/-- Distinct cells are disjoint under the fixed convention. -/
theorem halfOpenCell_pairwiseDisjoint {n m : ℕ} (hm : 0 < m) :
    Pairwise (fun i j : CellIndex n m => Disjoint (halfOpenCell i) (halfOpenCell j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hcoord (k : Fin n) : i k = j k := by
    apply le_antisymm
    · by_contra h
      have hji : j k < i k := lt_of_not_ge h
      have hlast : ¬(j k : ℕ) + 1 = m := by
        have hlt := (i k).isLt
        have hji' : (j k : ℕ) < (i k : ℕ) := hji
        omega
      have hstrict := (hxj.2 k).resolve_right hlast
      exact (not_lt_of_ge ((hxi.1.2 k).trans
        (cellUpper_le_cellLower_of_lt hm j i k hji))) hstrict
    · by_contra h
      have hij' : i k < j k := lt_of_not_ge h
      have hlast : ¬(i k : ℕ) + 1 = m := by
        have hlt := (j k).isLt
        have hij'' : (i k : ℕ) < (j k : ℕ) := hij'
        omega
      have hstrict := (hxi.2 k).resolve_right hlast
      exact (not_lt_of_ge ((hxj.1.2 k).trans
        (cellUpper_le_cellLower_of_lt hm i j k hij'))) hstrict
  exact hij (funext hcoord)

/-- An arbitrary jointly chosen family of cell representatives. -/
def IsCellRepresentative {n m : ℕ} (xi : CellIndex n m → Point n) : Prop :=
  ∀ j, xi j ∈ closedCell j

/-- The source step function, defined everywhere by the fixed partition and
extended by zero outside the cube. -/
def representativeStep {n d m : ℕ} (q : PolynomialSpace n d)
    (xi : CellIndex n m → Point n) (x : Point n) : ℝ :=
  ∑ j : CellIndex n m, (halfOpenCell j).indicator (fun _ => polyEval q (xi j)) x

lemma measurable_representativeStep {n d m : ℕ} (q : PolynomialSpace n d)
    (xi : CellIndex n m → Point n) : Measurable (representativeStep q xi) := by
  apply Finset.measurable_sum
  intro j _
  exact measurable_const.indicator (measurableSet_halfOpenCell j)

theorem representativeStep_eq {n d m : ℕ} (q : PolynomialSpace n d)
    (hm : 0 < m) (xi : CellIndex n m → Point n) (j : CellIndex n m)
    {x : Point n} (hx : x ∈ halfOpenCell j) :
    representativeStep q xi x = polyEval q (xi j) := by
  unfold representativeStep
  rw [Finset.sum_eq_single j]
  · exact Set.indicator_of_mem hx _
  · intro i _ hij
    exact Set.indicator_of_notMem (fun hi =>
      Set.disjoint_left.mp (halfOpenCell_pairwiseDisjoint hm hij) hi hx) _
  · simp

/-- The angular representative is the arccosine of the actual polynomial
representative; every coordinate may depend on the entire cell index. -/
def angularRepresentative {n m : ℕ} (xi : CellIndex n m → Point n)
    (j : CellIndex n m) : Point n := fun k => Real.arccos (xi j k)

theorem angularRepresentative_mem {n m : ℕ} (hm : 0 < m)
    (xi : CellIndex n m → Point n) (hxi : IsCellRepresentative xi)
    (j : CellIndex n m) : angularRepresentative xi j ∈ angularCell j := by
  constructor <;> intro k
  · exact (arccos_mem_angularCell hm j (xi j) (hxi j) k).1
  · exact (arccos_mem_angularCell hm j (xi j) (hxi j) k).2

theorem angularEval_angularRepresentative {n d m : ℕ} (q : PolynomialSpace n d)
    (xi : CellIndex n m → Point n) (hxi : IsCellRepresentative xi)
    (j : CellIndex n m) :
    angularEval q (angularRepresentative xi j) = polyEval q (xi j) :=
  angularEval_arccos q (xi j) (closedCell_subset_cube j (hxi j))

/-- Exact normalization for `q-q♯`, with the actual arbitrary-representative
step function. No representative factorization is used. -/
theorem representative_error_eq_normalized_angular {n d m : ℕ}
    (q : PolynomialSpace n d) (xi : CellIndex n m → Point n) :
    (∫ x, |polyEval q x - representativeStep q xi x| ∂chebyshevLaw n) =
      (Real.pi ^ n)⁻¹ * ∫ theta in Icc (fun _ : Fin n => (0 : ℝ))
        (fun _ => Real.pi), |angularEval q theta -
          representativeStep q xi (fun k => Real.cos (theta k))| := by
  exact chebyshev_integral_eq_normalized_angular _
    (continuous_abs.measurable.comp
      ((continuous_polyEval q).measurable.sub (measurable_representativeStep q xi)))

/-- The open upper angular faces have zero volume.  The half-open convention
therefore has exactly the same actual Chebyshev mass as a closed cell. -/
theorem chebyshevLaw_halfOpenCell {n m : ℕ} (hm : 0 < m) (j : CellIndex n m) :
    chebyshevLaw n (halfOpenCell j) = ENNReal.ofReal ((m : ℝ)⁻¹ ^ n) := by
  let box := Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => Real.pi)
  let core := Set.pi Set.univ (fun k => Ico (angularCellLower j k) (angularCellUpper j k))
  let pre := ((fun theta : Point n => fun k => Real.cos (theta k)) ⁻¹'
    halfOpenCell j) ∩ box
  have hsub : pre ⊆ angularCell j := by
    intro theta ht
    exact (cos_mem_closedCell_iff hm j theta ht.2).mp ht.1.1
  have hcore : core ⊆ pre := by
    intro theta ht
    have ht' (k : Fin n) : theta k ∈ Ico (angularCellLower j k) (angularCellUpper j k) :=
      ht k (Set.mem_univ k)
    have ha : theta ∈ angularCell j :=
      ⟨fun k => (ht' k).1, fun k => (ht' k).2.le⟩
    have hb := angularCell_subset_box hm j ha
    refine ⟨⟨(cos_mem_closedCell_iff hm j theta hb).mpr ha, fun k => Or.inl ?_⟩, hb⟩
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (hb.1 k)
      (angularCellUpper_le_pi hm j k) (ht' k).2
  have hvol : volume pre = volume (angularCell j) := by
    apply le_antisymm (measure_mono hsub)
    have hvolcore : volume core = volume (angularCell j) := by
      change volume (Set.pi Set.univ (fun k => Ico (angularCellLower j k)
        (angularCellUpper j k))) = volume (Icc (angularCellLower j) (angularCellUpper j))
      rw [Real.volume_pi_Ico, Real.volume_Icc_pi]
    rw [← hvolcore]
    exact measure_mono hcore
  rw [← chebyshevLaw_closedCell hm j]
  have hc : MeasurableSet (closedCell j) := measurableSet_Icc
  rw [chebyshevLaw, Measure.map_apply (continuous_cosPoint n).measurable
      (measurableSet_halfOpenCell j),
    Measure.map_apply (continuous_cosPoint n).measurable hc,
    angularLaw, Measure.smul_apply, Measure.smul_apply,
    Measure.restrict_apply ((measurableSet_halfOpenCell j).preimage (continuous_cosPoint n).measurable),
    Measure.restrict_apply (hc.preimage (continuous_cosPoint n).measurable),
    cos_preimage_closedCell_inter_box hm j]
  change _ * volume pre = _ * volume (angularCell j)
  rw [hvol]

/-- Shared closed-cell boundaries do not affect any Chebyshev integral. -/
theorem halfOpenCell_ae_eq_closedCell {n m : ℕ} (hm : 0 < m) (j : CellIndex n m) :
    halfOpenCell j =ᵐ[chebyshevLaw n] closedCell j := by
  apply ae_eq_of_subset_of_measure_ge (halfOpenCell_subset_closedCell j)
  · rw [chebyshevLaw_halfOpenCell hm j, chebyshevLaw_closedCell hm j]
  · exact (measurableSet_halfOpenCell j).nullMeasurableSet
  · exact measure_ne_top _ _

lemma integrable_representativeStep {n d m : ℕ} (q : PolynomialSpace n d)
    (xi : CellIndex n m → Point n) :
    Integrable (representativeStep q xi) (chebyshevLaw n) := by
  apply integrable_finset_sum
  intro j _
  exact (integrable_const _).indicator (measurableSet_halfOpenCell j)

/-- The integral of the actual step function has the source weights `m⁻ⁿ`. -/
theorem integral_representativeStep {n d m : ℕ} (q : PolynomialSpace n d)
    (hm : 0 < m) (xi : CellIndex n m → Point n) :
    (∫ x, representativeStep q xi x ∂chebyshevLaw n) =
      (m : ℝ)⁻¹ ^ n * ∑ j : CellIndex n m, polyEval q (xi j) := by
  unfold representativeStep
  rw [integral_finset_sum _ (fun j _ =>
    (integrable_const _).indicator (measurableSet_halfOpenCell j))]
  simp_rw [integral_indicator_const _ (measurableSet_halfOpenCell _),
    measureReal_def, chebyshevLaw_halfOpenCell hm,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (m : ℝ)⁻¹ ^ n), smul_eq_mul]
  exact (Finset.mul_sum ..).symm

/-- The actual derivative of the angular polynomial along coordinate `k`. -/
def angularPartial {n d : ℕ} (q : PolynomialSpace n d) (k : Fin n)
    (theta : Point n) : ℝ :=
  deriv (fun t => angularEval q (Function.update theta k t)) (theta k)

lemma update_mem_angularCell {n m : ℕ} (j : CellIndex n m)
    {theta : Point n} (htheta : theta ∈ angularCell j) (k : Fin n) {t : ℝ}
    (ht : t ∈ Icc (angularCellLower j k) (angularCellUpper j k)) :
    Function.update theta k t ∈ angularCell j := by
  constructor <;> intro i <;> by_cases hi : i = k
  · subst i
    simpa using ht.1
  · simpa only [Function.update_of_ne hi] using htheta.1 i
  · subst i
    simpa using ht.2
  · simpa only [Function.update_of_ne hi] using htheta.2 i

lemma replaceCoordinates_mem_angularCell {n m : ℕ} (j : CellIndex n m)
    {theta eta : Point n} (htheta : theta ∈ angularCell j) (heta : eta ∈ angularCell j)
    (S : Finset (Fin n)) : replaceCoordinates S theta eta ∈ angularCell j := by
  constructor <;> intro k <;> by_cases hk : k ∈ S
  · simpa only [replaceCoordinates, if_pos hk] using heta.1 k
  · simpa only [replaceCoordinates, if_neg hk] using htheta.1 k
  · simpa only [replaceCoordinates, if_pos hk] using heta.2 k
  · simpa only [replaceCoordinates, if_neg hk] using htheta.2 k

/-- The one-coordinate mean-value estimate uses the genuine derivative on
the full closed cell, so other representative coordinates can be arbitrary. -/
theorem angular_coordinate_local_bound {n d m : ℕ} (q : PolynomialSpace n d)
    (j : CellIndex n m) {theta : Point n} (htheta : theta ∈ angularCell j)
    (k : Fin n) (C : ℝ)
    (hC : ∀ phi ∈ angularCell j, |angularPartial q k phi| ≤ C)
    {s t : ℝ} (hs : s ∈ Icc (angularCellLower j k) (angularCellUpper j k))
    (ht : t ∈ Icc (angularCellLower j k) (angularCellUpper j k)) :
    |angularEval q (Function.update theta k t) -
      angularEval q (Function.update theta k s)| ≤ C * |t - s| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun u (_ : u ∈ Icc (angularCellLower j k) (angularCellUpper j k)) =>
      differentiable_angularSlice q theta k u)
    (fun u hu => show ‖deriv (fun v => angularEval q (Function.update theta k v)) u‖ ≤ C from by
      simpa only [angularPartial, Function.update_self, Function.update_idem,
        Real.norm_eq_abs] using hC (Function.update theta k u)
          (update_mem_angularCell j htheta k hu))
    (convex_Icc _ _) hs ht
  simpa only [Real.norm_eq_abs] using h

/-- Finite telescoping of a coordinate path, entirely inside the same cell.
No selection operator is tensorized in this proof. -/
theorem angular_finite_local_path {n d m : ℕ} (q : PolynomialSpace n d)
    (j : CellIndex n m) (C : Fin n → ℝ)
    (hC : ∀ phi ∈ angularCell j, ∀ k, |angularPartial q k phi| ≤ C k)
    {theta eta : Point n} (htheta : theta ∈ angularCell j) (heta : eta ∈ angularCell j)
    (S : Finset (Fin n)) :
    |angularEval q (replaceCoordinates S theta eta) - angularEval q theta| ≤
      ∑ k ∈ S, C k * |eta k - theta k| := by
  induction S using Finset.induction_on with
  | empty =>
      have heq : replaceCoordinates ∅ theta eta = theta := by
        funext k
        simp [replaceCoordinates]
      simp [heq]
  | @insert k S hk ih =>
      have hstep := angular_coordinate_local_bound q j
        (replaceCoordinates_mem_angularCell j htheta heta S) k (C k)
        (fun phi hphi => hC phi hphi k)
        (show theta k ∈ Icc (angularCellLower j k) (angularCellUpper j k) from
          ⟨htheta.1 k, htheta.2 k⟩)
        (show eta k ∈ Icc (angularCellLower j k) (angularCellUpper j k) from
          ⟨heta.1 k, heta.2 k⟩)
      rw [replaceCoordinates_update_original S theta eta k hk,
        ← replaceCoordinates_insert S theta eta k] at hstep
      calc
        _ ≤ |angularEval q (replaceCoordinates (insert k S) theta eta) -
              angularEval q (replaceCoordinates S theta eta)| +
            |angularEval q (replaceCoordinates S theta eta) - angularEval q theta| :=
          abs_sub_le _ _ _
        _ ≤ C k * |eta k - theta k| + ∑ i ∈ S, C i * |eta i - theta i| :=
          add_le_add hstep ih
        _ = _ := by rw [Finset.sum_insert hk]

/-- The precise coordinate-path inequality displayed in the proof of 3.3,
with any valid local derivative bounds `C k`. -/
theorem angular_local_path_bound {n d m : ℕ} (q : PolynomialSpace n d)
    (j : CellIndex n m) (C : Fin n → ℝ)
    (hC : ∀ phi ∈ angularCell j, ∀ k, |angularPartial q k phi| ≤ C k)
    {theta eta : Point n} (htheta : theta ∈ angularCell j) (heta : eta ∈ angularCell j) :
    |angularEval q theta - angularEval q eta| ≤ (Real.pi / m) * ∑ k, C k := by
  have hpath := angular_finite_local_path q j C hC heta htheta Finset.univ
  have heq : replaceCoordinates Finset.univ eta theta = theta := by
    funext k
    simp [replaceCoordinates]
  rw [heq] at hpath
  calc
    _ ≤ ∑ k : Fin n, C k * |theta k - eta k| := hpath
    _ ≤ ∑ k : Fin n, C k * (Real.pi / m) := by
      apply Finset.sum_le_sum
      intro k _
      have hC0 : 0 ≤ C k := (abs_nonneg _).trans (hC theta htheta k)
      apply mul_le_mul_of_nonneg_left _ hC0
      have hw := angularCell_width j k
      exact abs_le.mpr ⟨by linarith [htheta.1 k, heta.2 k],
        by linarith [htheta.2 k, heta.1 k]⟩
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

/-- The path estimate on actual polynomial cells and actual arbitrary
representatives, after the exact arccosine lift. -/
theorem representative_cell_error_le {n d m : ℕ} (q : PolynomialSpace n d)
    (hm : 0 < m) (xi : CellIndex n m → Point n) (hxi : IsCellRepresentative xi)
    (C : CellIndex n m → Fin n → ℝ)
    (hC : ∀ j phi, phi ∈ angularCell j → ∀ k, |angularPartial q k phi| ≤ C j k)
    (j : CellIndex n m) {x : Point n} (hx : x ∈ closedCell j) :
    |polyEval q x - polyEval q (xi j)| ≤ (Real.pi / m) * ∑ k, C j k := by
  have hxangle : (fun k => Real.arccos (x k)) ∈ angularCell j :=
    ⟨fun k => (arccos_mem_angularCell hm j x hx k).1,
      fun k => (arccos_mem_angularCell hm j x hx k).2⟩
  have h := angular_local_path_bound q j (C j) (hC j) hxangle
    (angularRepresentative_mem hm xi hxi j)
  rw [angularEval_arccos q x (closedCell_subset_cube j hx),
    angularEval_angularRepresentative q xi hxi j] at h
  exact h

/-- A measurable cellwise constant majorant on the fixed source partition. -/
def cellStep {n m : ℕ} (v : CellIndex n m → ℝ) (x : Point n) : ℝ :=
  ∑ j : CellIndex n m, (halfOpenCell j).indicator (fun _ => v j) x

lemma cellStep_eq {n m : ℕ} (hm : 0 < m) (v : CellIndex n m → ℝ)
    (j : CellIndex n m) {x : Point n} (hx : x ∈ halfOpenCell j) :
    cellStep v x = v j := by
  unfold cellStep
  rw [Finset.sum_eq_single j]
  · exact Set.indicator_of_mem hx _
  · intro i _ hij
    exact Set.indicator_of_notMem (fun hi =>
      Set.disjoint_left.mp (halfOpenCell_pairwiseDisjoint hm hij) hi hx) _
  · simp

lemma integrable_cellStep {n m : ℕ} (v : CellIndex n m → ℝ) :
    Integrable (cellStep v) (chebyshevLaw n) := by
  apply integrable_finset_sum
  intro j _
  exact (integrable_const _).indicator (measurableSet_halfOpenCell j)

theorem integral_cellStep {n m : ℕ} (hm : 0 < m) (v : CellIndex n m → ℝ) :
    (∫ x, cellStep v x ∂chebyshevLaw n) = (m : ℝ)⁻¹ ^ n * ∑ j, v j := by
  unfold cellStep
  rw [integral_finset_sum _ (fun j _ =>
    (integrable_const _).indicator (measurableSet_halfOpenCell j))]
  simp_rw [integral_indicator_const _ (measurableSet_halfOpenCell _),
    measureReal_def, chebyshevLaw_halfOpenCell hm,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (m : ℝ)⁻¹ ^ n), smul_eq_mul]
  exact (Finset.mul_sum ..).symm

/-- Integrating cellwise bounds gives the actual weighted error, rather than
an assumed norm-comparison conclusion. -/
theorem representative_error_le_cell_sum {n d m : ℕ} (q : PolynomialSpace n d)
    (hm : 0 < m) (xi : CellIndex n m → Point n) (b : CellIndex n m → ℝ)
    (hb : ∀ j x, x ∈ closedCell j → |polyEval q x - polyEval q (xi j)| ≤ b j) :
    (∫ x, |polyEval q x - representativeStep q xi x| ∂chebyshevLaw n) ≤
      (m : ℝ)⁻¹ ^ n * ∑ j, b j := by
  rw [← integral_cellStep hm b]
  apply integral_mono_ae
  · exact ((integrable_polyEval q).sub (integrable_representativeStep q xi)).abs
  · exact integrable_cellStep b
  · filter_upwards [chebyshevLaw_ae_cube n] with x hx
    obtain ⟨j, hj⟩ := cube_covered_by_halfOpenCells hm x hx
    rw [representativeStep_eq q hm xi j hj, cellStep_eq hm b j hj]
    exact hb j x hj.1

/-- The first integrated inequality in the proof of (3.7), on `[0,π]^n`,
with its exact cell masses and exact mesh width. -/
theorem representative_error_le_partial_sum {n d m : ℕ} (q : PolynomialSpace n d)
    (hm : 0 < m) (xi : CellIndex n m → Point n) (hxi : IsCellRepresentative xi)
    (C : CellIndex n m → Fin n → ℝ)
    (hC : ∀ j phi, phi ∈ angularCell j → ∀ k, |angularPartial q k phi| ≤ C j k) :
    (∫ x, |polyEval q x - representativeStep q xi x| ∂chebyshevLaw n) ≤
      (Real.pi / m) * ((m : ℝ)⁻¹ ^ n * ∑ j, ∑ k, C j k) := by
  have h := representative_error_le_cell_sum q hm xi
    (fun j => (Real.pi / m) * ∑ k, C j k)
    (fun j x hx => representative_cell_error_le q hm xi hxi C hC j hx)
  simpa only [← Finset.mul_sum, mul_left_comm] using h

/-- The absolute values of a source step function integrate to the discrete
`L¹` functional used in Corollary 3.4. -/
theorem integral_abs_representativeStep {n d m : ℕ} (q : PolynomialSpace n d)
    (hm : 0 < m) (xi : CellIndex n m → Point n) :
    (∫ x, |representativeStep q xi x| ∂chebyshevLaw n) =
      ((m : ℝ)^n)⁻¹ * ∑ j : CellIndex n m, |polyEval q (xi j)| := by
  have heq : (fun x => |representativeStep q xi x|) =ᵐ[chebyshevLaw n]
      cellStep (fun j => |polyEval q (xi j)|) := by
    filter_upwards [chebyshevLaw_ae_cube n] with x hx
    obtain ⟨j, hj⟩ := cube_covered_by_halfOpenCells hm x hx
    rw [representativeStep_eq q hm xi j hj, cellStep_eq hm _ j hj]
  rw [integral_congr_ae heq, integral_cellStep hm, inv_pow]

/-- The discrete norming error is controlled by the proved integral error.
This is the reverse-triangle step of Corollary 3.4. -/
theorem representative_discrete_error_le_integral {n d m : ℕ}
    (q : PolynomialSpace n d) (hm : 0 < m) (xi : CellIndex n m → Point n) :
    |((m : ℝ)^n)⁻¹ * ∑ j : CellIndex n m, |polyEval q (xi j)| - l1Norm q| ≤
      ∫ x, |polyEval q x - representativeStep q xi x| ∂chebyshevLaw n := by
  rw [← integral_abs_representativeStep q hm xi, l1Norm,
    ← integral_sub (integrable_representativeStep q xi).abs (integrable_polyEval q).abs]
  refine abs_integral_le_integral_abs.trans ?_
  apply integral_mono
  · exact ((integrable_representativeStep q xi).abs.sub (integrable_polyEval q).abs).abs
  · exact ((integrable_polyEval q).sub (integrable_representativeStep q xi)).abs
  · intro x
    change abs (abs (representativeStep q xi x) - abs (polyEval q x)) ≤
      abs (polyEval q x - representativeStep q xi x)
    exact (abs_abs_sub_abs_le _ _).trans_eq (abs_sub_comm _ _)

/-- A producer for the shared norming interface from a proved step-error
estimate. The input is the remaining analytic estimate, not an axiom or an
assertion that the paper's new theorem is already true. -/
theorem representativeNorming_of_integral_error {n d m : ℕ} (hm : 0 < m) {z : ℝ}
    (herror : ∀ (q : PolynomialSpace n d) (xi : CellIndex n m → Point n),
      IsCellRepresentative xi →
      (∫ x, |polyEval q x - representativeStep q xi x| ∂chebyshevLaw n) ≤ z*l1Norm q) :
    RepresentativeNorming n d m z := by
  intro q xi hxi
  exact (representative_discrete_error_le_integral q hm xi).trans (herror q xi hxi)

/-- Embed the positive half-period grid into the full torus grid.  This
avoids placing any restriction on the chosen representative coordinates. -/
def positiveGridIndex {n m : ℕ} (j : CellIndex n m) : TensorNorming.GridIndex n m :=
  fun k => ⟨(j k : ℕ), by have := (j k).isLt; omega⟩

lemma positiveGridIndex_injective {n m : ℕ} :
    Function.Injective (@positiveGridIndex n m) := by
  intro i j hij
  funext k
  apply Fin.ext
  exact congrArg (fun f : TensorNorming.GridIndex n m => (f k : ℕ)) hij

lemma angularCell_eq_positive_gridCell {n m : ℕ} (j : CellIndex n m) :
    angularCell j = TensorNorming.gridCell (positiveGridIndex j) := by
  apply congrArg₂ Icc
  · funext k
    simp only [angularCellLower, positiveGridIndex]
    ring
  · funext k
    simp only [angularCellUpper, positiveGridIndex]
    ring

lemma norm_le_torus_cellSup {n m : ℕ} (f : C(TensorNorming.TorusN n, ℂ))
    (j : TensorNorming.GridIndex n m) {theta : Point n}
    (htheta : theta ∈ TensorNorming.gridCell j) :
    ‖f (TensorNorming.angularPoint theta)‖ ≤ TensorNorming.cellSup f j := by
  have hc : Continuous (fun t : Point n => ‖f (TensorNorming.angularPoint t)‖) :=
    (f.continuous.comp (TensorNorming.continuous_angularPoint n)).norm
  exact le_csSup (((isCompact_Icc : IsCompact (TensorNorming.gridCell j)).image
    hc).bddAbove) ⟨theta, htheta, rfl⟩

lemma torus_cellSup_nonneg {n m : ℕ} (f : C(TensorNorming.TorusN n, ℂ))
    (j : TensorNorming.GridIndex n m) : 0 ≤ TensorNorming.cellSup f j := by
  obtain ⟨theta, ht⟩ := TensorNorming.gridCell_nonempty j
  exact (norm_nonneg _).trans (norm_le_torus_cellSup f j ht)

lemma positive_grid_sum_le {n m : ℕ} (f : TensorNorming.GridIndex n m → ℝ)
    (hf : ∀ j, 0 ≤ f j) :
    (∑ j : CellIndex n m, f (positiveGridIndex j)) ≤
      ∑ j : TensorNorming.GridIndex n m, f j := by
  classical
  calc
    _ = ∑ j ∈ Finset.univ.image positiveGridIndex, f j := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => positiveGridIndex_injective h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun j _ _ => hf j)

/-- The positive angular cells satisfy the required local-supremum sum bound.
Using their inclusion in the full grid costs only the dimension constant `2ⁿ`.
All norms and suprema in this statement are actual values and Haar integrals. -/
theorem positive_local_supremum_bound {n d m : ℕ}
    (H : TensorNorming.TrigPolynomial n d) (hd : 1 ≤ d) (hm : d ≤ m) :
    (m : ℝ)⁻¹ ^ n * ∑ j : CellIndex n m,
      TensorNorming.cellSup H.toContinuousMap (positiveGridIndex j) ≤
        ((2 : ℝ) * (3 + 10 * Real.pi)) ^ n *
          ∫ u : TensorNorming.TorusN n, ‖H.eval u‖ ∂TensorNorming.haarN n := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hw : (m : ℝ)⁻¹ = 2 * TensorNorming.gridWeight m := by
    unfold TensorNorming.gridWeight
    field_simp
  have hsum := positive_grid_sum_le
    (fun j : TensorNorming.GridIndex n m => TensorNorming.cellSup H.toContinuousMap j)
    (fun j => torus_cellSup_nonneg H.toContinuousMap j)
  have hlocal := TensorNorming.local_supremum_bound H hd hm
  calc
    _ ≤ (m : ℝ)⁻¹ ^ n * ∑ j : TensorNorming.GridIndex n m,
        TensorNorming.cellSup H.toContinuousMap j :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = 2 ^ n * (TensorNorming.gridWeight m ^ n *
        ∑ j : TensorNorming.GridIndex n m, TensorNorming.cellSup H.toContinuousMap j) := by
      rw [hw, mul_pow]
      ring
    _ ≤ 2 ^ n * ((3 + 10 * Real.pi) ^ n *
        ∫ u : TensorNorming.TorusN n, ‖H.eval u‖ ∂TensorNorming.haarN n) :=
      mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- Derivative uniqueness connects the real polynomial derivative to the
finite Fourier derivative. The only input here is equality of actual functions. -/
theorem angularPartial_eq_fourier_partial {n d : ℕ} (q : PolynomialSpace n d)
    (H : TensorNorming.TrigPolynomial n d)
    (hH : ∀ theta, H.eval (TensorNorming.angularPoint theta) = (angularEval q theta : ℂ))
    (k : Fin n) (theta : Point n) :
    (angularPartial q k theta : ℂ) = (H.partial k).eval (TensorNorming.angularPoint theta) := by
  have hreal := ((differentiable_angularSlice q theta k (theta k)).hasDerivAt).ofReal_comp
  have hcomplex := TensorNorming.hasDerivAt_partial H k theta
  have heq : (fun t : ℝ => H.eval (TensorNorming.angularPoint (Function.update theta k t))) =
      (fun t : ℝ => (angularEval q (Function.update theta k t) : ℂ)) :=
    funext (fun t => hH (Function.update theta k t))
  rw [heq] at hcomplex
  exact hreal.unique hcomplex

theorem angularPartial_le_fourier_cellSup {n d m : ℕ} (q : PolynomialSpace n d)
    (H : TensorNorming.TrigPolynomial n d)
    (hH : ∀ theta, H.eval (TensorNorming.angularPoint theta) = (angularEval q theta : ℂ))
    (j : CellIndex n m) (theta : Point n) (htheta : theta ∈ angularCell j) (k : Fin n) :
    |angularPartial q k theta| ≤
      TensorNorming.cellSup (H.partial k).toContinuousMap (positiveGridIndex j) := by
  have hnorm : |angularPartial q k theta| =
      ‖(H.partial k).eval (TensorNorming.angularPoint theta)‖ := by
    rw [← angularPartial_eq_fourier_partial q H hH, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  exact norm_le_torus_cellSup (H.partial k).toContinuousMap _
    ((angularCell_eq_positive_gridCell j) ▸ htheta)

/-- The integrated path estimate followed by local supremum bounds, for the
actual Fourier lift of the source polynomial. This proves the first two
inequalities in the displayed calculation following (3.7). -/
theorem representative_error_le_fourier_partial_sum {n d m : ℕ}
    (q : PolynomialSpace n d) (hd : 1 ≤ d) (hm : d ≤ m)
    (xi : CellIndex n m → Point n) (hxi : IsCellRepresentative xi)
    (H : TensorNorming.TrigPolynomial n d)
    (hH : ∀ theta, H.eval (TensorNorming.angularPoint theta) = (angularEval q theta : ℂ)) :
    (∫ x, |polyEval q x - representativeStep q xi x| ∂chebyshevLaw n) ≤
      (Real.pi / m) * (((2 : ℝ) * (3 + 10 * Real.pi)) ^ n *
        ∑ k : Fin n, ∫ u : TensorNorming.TorusN n,
          ‖(H.partial k).eval u‖ ∂TensorNorming.haarN n) := by
  have hm0 : 0 < m := by omega
  let C : CellIndex n m → Fin n → ℝ := fun j k =>
    TensorNorming.cellSup (H.partial k).toContinuousMap (positiveGridIndex j)
  have hpath := representative_error_le_partial_sum q hm0 xi hxi C
    (fun j theta htheta k => angularPartial_le_fourier_cellSup q H hH j theta htheta k)
  have hsum : (m : ℝ)⁻¹ ^ n * ∑ j : CellIndex n m, ∑ k : Fin n, C j k ≤
      ((2 : ℝ) * (3 + 10 * Real.pi)) ^ n *
        ∑ k : Fin n, ∫ u : TensorNorming.TorusN n,
          ‖(H.partial k).eval u‖ ∂TensorNorming.haarN n := by
    rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum (fun k _ => positive_local_supremum_bound (H.partial k) hd hm)
  exact hpath.trans (mul_le_mul_of_nonneg_left hsum (by positivity))

/-- Apply the internally proved endpoint `L¹` Bernstein theorem to the actual
Fourier derivatives. Only the final normalization remains in this bound. -/
theorem representative_error_le_fourier_norm {n d m : ℕ}
    (q : PolynomialSpace n d) (hd : 1 ≤ d) (hm : d ≤ m)
    (xi : CellIndex n m → Point n) (hxi : IsCellRepresentative xi)
    (H : TensorNorming.TrigPolynomial n d)
    (hH : ∀ theta, H.eval (TensorNorming.angularPoint theta) = (angularEval q theta : ℂ)) :
    (∫ x, |polyEval q x - representativeStep q xi x| ∂chebyshevLaw n) ≤
      (Real.pi * n * (((2 : ℝ) * (3 + 10 * Real.pi)) ^ n) *
        (10 * 3 ^ (n - 1))) * (d : ℝ) / m *
          ∫ u : TensorNorming.TorusN n, ‖H.eval u‖ ∂TensorNorming.haarN n := by
  have hpath := representative_error_le_fourier_partial_sum q hd hm xi hxi H hH
  have hsum : (∑ k : Fin n, ∫ u : TensorNorming.TorusN n,
      ‖(H.partial k).eval u‖ ∂TensorNorming.haarN n) ≤
      n * ((10 * 3 ^ (n - 1) : ℝ) * d *
        ∫ u : TensorNorming.TorusN n, ‖H.eval u‖ ∂TensorNorming.haarN n) := by
    calc
      _ ≤ ∑ _k : Fin n, (10 * 3 ^ (n - 1) : ℝ) * d *
          ∫ u : TensorNorming.TorusN n, ‖H.eval u‖ ∂TensorNorming.haarN n :=
        Finset.sum_le_sum (fun k _ => TensorNorming.partial_L1 H hd k)
      _ = _ := by simp
  calc
    _ ≤ (Real.pi / m) * (((2 : ℝ) * (3 + 10 * Real.pi)) ^ n *
        ∑ k : Fin n, ∫ u : TensorNorming.TorusN n,
          ‖(H.partial k).eval u‖ ∂TensorNorming.haarN n) := hpath
    _ ≤ (Real.pi / m) * (((2 : ℝ) * (3 + 10 * Real.pi)) ^ n *
        (n * ((10 * 3 ^ (n - 1) : ℝ) * d *
          ∫ u : TensorNorming.TorusN n, ‖H.eval u‖ ∂TensorNorming.haarN n))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

/-- An explicit finite constant depending only on dimension.  The extra `2ⁿ`
comes from embedding the positive half-period cells in the full torus grid. -/
def arbitraryRepresentativeConstant (n : ℕ) : ℝ :=
  max 1 (Real.pi * n * (((2 : ℝ) * (3 + 10 * Real.pi)) ^ n) *
    (10 * 3 ^ (n - 1)))

theorem arbitraryRepresentativeConstant_ge_one (n : ℕ) :
    1 ≤ arbitraryRepresentativeConstant n := le_max_left _ _

/-- The final algebraic and normalization step. The source theorem below
supplies the Fourier lift and its exact normalized norm equality. -/
theorem representative_error_of_fourier_normalization {n d m : ℕ}
    (q : PolynomialSpace n d) (hd : 1 ≤ d) (hm : d ≤ m)
    (xi : CellIndex n m → Point n) (hxi : IsCellRepresentative xi)
    (H : TensorNorming.TrigPolynomial n d)
    (hH : ∀ theta, H.eval (TensorNorming.angularPoint theta) = (angularEval q theta : ℂ))
    (hnorm : (∫ u : TensorNorming.TorusN n, ‖H.eval u‖ ∂TensorNorming.haarN n) = l1Norm q) :
    (∫ x, |polyEval q x - representativeStep q xi x| ∂chebyshevLaw n) ≤
      arbitraryRepresentativeConstant n * (d : ℝ) / m * l1Norm q := by
  have h := representative_error_le_fourier_norm q hd hm xi hxi H hH
  rw [hnorm] at h
  have hnorm0 : 0 ≤ l1Norm q := integral_nonneg (fun _ => abs_nonneg _)
  have hnonneg : 0 ≤ (d : ℝ) / m * l1Norm q :=
    mul_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hnorm0
  let K := Real.pi * n * (((2 : ℝ) * (3 + 10 * Real.pi)) ^ n) * (10 * 3 ^ (n - 1))
  calc
    _ ≤ K * ((d : ℝ) / m * l1Norm q) := by simpa only [K, mul_div_assoc, mul_assoc] using h
    _ ≤ arbitraryRepresentativeConstant n * ((d : ℝ) / m * l1Norm q) :=
      mul_le_mul_of_nonneg_right (le_max_right 1 K) hnonneg
    _ = _ := by ring

/-- Source Lemma 3.3, equation (3.7), for an arbitrary jointly chosen family
of representatives of the actual Chebyshev cells and the fixed half-open step
function. The constant is finite, at least one, and depends only on dimension.
Every analytical dependency is proved on the actual source objects. -/
theorem lemma_3_3 {n d m : ℕ} (hd : 1 ≤ d) (hm : d ≤ m)
    (q : PolynomialSpace n d) (xi : CellIndex n m → Point n)
    (hxi : IsCellRepresentative xi) :
    (∫ x, |polyEval q x - representativeStep q xi x| ∂chebyshevLaw n) ≤
      arbitraryRepresentativeConstant n * (d : ℝ) / m * l1Norm q := by
  exact representative_error_of_fourier_normalization q hd hm xi hxi
    (CosineFourierLift.toTrigPolynomial q)
    (CosineFourierLift.toTrigPolynomial_angular q)
    (HaarChebyshev.toTrigPolynomial_haar_l1 q)

/-- The existential quantifiers in source Lemma 3.3, with the same constant
working for every degree, grid size, polynomial, and representative family. -/
theorem lemma_3_3_dimension_constant (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (d m : ℕ), 1 ≤ d → d ≤ m →
      ∀ (q : PolynomialSpace n d) (xi : CellIndex n m → Point n),
        IsCellRepresentative xi →
          (∫ x, |polyEval q x - representativeStep q xi x| ∂chebyshevLaw n) ≤
            A * (d : ℝ) / m * l1Norm q := by
  exact ⟨arbitraryRepresentativeConstant n, arbitraryRepresentativeConstant_ge_one n,
    fun _ _ hd hm q xi hxi => lemma_3_3 hd hm q xi hxi⟩

/-- The shared discrete interface is produced by the actual new theorem,
with no additional premise encoding representative norming. -/
theorem representativeNorming_of_degree_grid {n d m : ℕ} (hd : 1 ≤ d) (hm : d ≤ m) :
    RepresentativeNorming n d m (arbitraryRepresentativeConstant n * (d : ℝ) / m) := by
  apply representativeNorming_of_integral_error (by omega)
  intro q xi hxi
  exact lemma_3_3 hd hm q xi hxi

/-- The source oversampling threshold turns the relative error into any
prescribed `0 < ζ < 1`. -/
theorem representativeNorming_of_oversampling {n d m : ℕ} (hd : 1 ≤ d)
    {zeta : ℝ} (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hmesh : arbitraryRepresentativeConstant n * (d : ℝ) / zeta ≤ m) :
    RepresentativeNorming n d m zeta := by
  have hA := arbitraryRepresentativeConstant_ge_one n
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hAd : (d : ℝ) ≤ arbitraryRepresentativeConstant n * d := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA) (Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hmesh' : arbitraryRepresentativeConstant n * (d : ℝ) ≤ m * zeta :=
    (div_le_iff₀ hzeta0).mp hmesh
  have hmpos : (0 : ℝ) < m := by
    by_contra h
    have hm0 : (m : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg m)
    rw [hm0, zero_mul] at hmesh'
    linarith
  have hdm : (d : ℝ) ≤ m := by
    have hmz : (m : ℝ) * zeta ≤ m := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hzeta1.le (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    exact hAd.trans (hmesh'.trans hmz)
  have hm : d ≤ m := by exact_mod_cast hdm
  have hcoef : arbitraryRepresentativeConstant n * (d : ℝ) / m ≤ zeta := by
    apply (div_le_iff₀ hmpos).2
    nlinarith
  intro q xi hxi
  have h := representativeNorming_of_degree_grid hd hm q xi hxi
  exact h.trans (mul_le_mul_of_nonneg_right hcoef (integral_nonneg fun _ => abs_nonneg _))

/-- Source Corollary 3.4, equation (3.8), with actual finite multisets and
the exact product-Chebyshev weights. The multiset witness was proved separately. -/
theorem corollary_3_4 {n d m : ℕ} (hd : 1 ≤ d)
    {zeta : ℝ} (hzeta0 : 0 < zeta) (hzeta1 : zeta < 1)
    (hmesh : arbitraryRepresentativeConstant n * (d : ℝ) / zeta ≤ m) :
    MultisetNorming n d m zeta :=
  multisetNorming_of_representativeNorming
    (representativeNorming_of_oversampling hd hzeta0 hzeta1 hmesh)

end Paper34
