import Paper34.ArbitraryRepresentatives
import Paper34.Anisotropic

/-! The variable-mesh representative geometry and integral reduction in A.3.
Each coordinate has its own positive mesh size. All cell masses and paths
are proved for the actual source Chebyshev pushforward. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace Paper34.AnisotropicRepresentatives

abbrev CellIndex {n : ℕ} (m : Fin n → ℕ) := ∀ i, Fin (m i)

def coordinateIndex {n : ℕ} {m : Fin n → ℕ} (j : CellIndex m) (i : Fin n) :
    Paper34.CellIndex 1 (m i) := fun _ => j i

def coordinatePoint {n : ℕ} (x : Point n) (i : Fin n) : Point 1 := fun _ => x i

def lower {n : ℕ} {m : Fin n → ℕ} (j : CellIndex m) (i : Fin n) : ℝ :=
  (j i : ℕ) * Real.pi / m i

def upper {n : ℕ} {m : Fin n → ℕ} (j : CellIndex m) (i : Fin n) : ℝ :=
  ((j i : ℕ) + (1 : ℝ)) * Real.pi / m i

def angularCell {n : ℕ} {m : Fin n → ℕ} (j : CellIndex m) : Set (Point n) :=
  Icc (lower j) (upper j)

def closedCell {n : ℕ} {m : Fin n → ℕ} (j : CellIndex m) : Set (Point n) :=
  Icc (fun i => Real.cos (upper j i)) (fun i => Real.cos (lower j i))

/-- The same fixed half-open convention as the uniform mesh, in each
coordinate separately. -/
def halfOpenCell {n : ℕ} {m : Fin n → ℕ} (j : CellIndex m) : Set (Point n) :=
  ⋂ i, (fun x => coordinatePoint x i) ⁻¹' Paper34.halfOpenCell (coordinateIndex j i)

lemma measurableSet_halfOpenCell {n : ℕ} {m : Fin n → ℕ} (j : CellIndex m) :
    MeasurableSet (halfOpenCell j) := by
  apply MeasurableSet.iInter
  intro i
  exact (Paper34.measurableSet_halfOpenCell _).preimage
    (measurable_pi_lambda _ (fun _ => measurable_pi_apply i))

lemma halfOpenCell_subset_closedCell {n : ℕ} {m : Fin n → ℕ} (j : CellIndex m) :
    halfOpenCell j ⊆ closedCell j := by
  intro x hx
  have hc (i : Fin n) := (Set.mem_iInter.mp hx i).1
  exact ⟨fun i => (hc i).1 0, fun i => (hc i).2 0⟩

lemma closedCell_subset_cube {n : ℕ} {m : Fin n → ℕ} (j : CellIndex m) :
    closedCell j ⊆ cube n := by
  intro x hx
  exact ⟨fun i => (Real.neg_one_le_cos _).trans (hx.1 i),
    fun i => (hx.2 i).trans (Real.cos_le_one _)⟩

theorem cube_covered {n : ℕ} {m : Fin n → ℕ} (hm : ∀ i, 0 < m i)
    (x : Point n) (hx : x ∈ cube n) : ∃ j : CellIndex m, x ∈ halfOpenCell j := by
  have hcoord (i : Fin n) : ∃ j : Fin (m i),
      coordinatePoint x i ∈ Paper34.halfOpenCell (fun _ : Fin 1 => j) := by
    obtain ⟨j, hj⟩ := Paper34.cube_covered_by_halfOpenCells (hm i) (coordinatePoint x i)
      ⟨fun _ => hx.1 i, fun _ => hx.2 i⟩
    refine ⟨j 0, ?_⟩
    have heq : j = fun _ : Fin 1 => j 0 := by
      funext k
      exact congrArg j (Subsingleton.elim k 0)
    rwa [← heq]
  choose j hj using hcoord
  exact ⟨j, Set.mem_iInter.mpr hj⟩

theorem pairwiseDisjoint {n : ℕ} {m : Fin n → ℕ} (hm : ∀ i, 0 < m i) :
    Pairwise (fun j k : CellIndex m => Disjoint (halfOpenCell j) (halfOpenCell k)) := by
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro x hxj hxk
  apply hjk
  funext i
  by_contra h
  have h' : coordinateIndex j i ≠ coordinateIndex k i := fun heq => h (congrFun heq 0)
  exact Set.disjoint_left.mp (Paper34.halfOpenCell_pairwiseDisjoint (hm i) h')
    (Set.mem_iInter.mp hxj i) (Set.mem_iInter.mp hxk i)

lemma lower_nonneg {n : ℕ} {m : Fin n → ℕ} (j : CellIndex m) (i : Fin n) :
    0 ≤ lower j i := by unfold lower; positivity

lemma lower_le_upper {n : ℕ} {m : Fin n → ℕ} (j : CellIndex m) (i : Fin n) :
    lower j i ≤ upper j i := by
  unfold lower upper
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  nlinarith [Real.pi_pos]

lemma upper_le_pi {n : ℕ} {m : Fin n → ℕ} (hm : ∀ i, 0 < m i)
    (j : CellIndex m) (i : Fin n) : upper j i ≤ Real.pi := by
  have hm' : (0 : ℝ) < m i := by exact_mod_cast hm i
  have hj : (j i : ℝ) + 1 ≤ m i := by exact_mod_cast (Nat.succ_le_iff.mpr (j i).isLt)
  unfold upper
  apply (div_le_iff₀ hm').2
  nlinarith [mul_le_mul_of_nonneg_right hj Real.pi_pos.le]

lemma angularCell_subset_box {n : ℕ} {m : Fin n → ℕ} (hm : ∀ i, 0 < m i)
    (j : CellIndex m) :
    angularCell j ⊆ Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => Real.pi) := by
  intro theta ht
  exact ⟨fun i => (lower_nonneg j i).trans (ht.1 i),
    fun i => (ht.2 i).trans (upper_le_pi hm j i)⟩

lemma cos_mem_closedCell_iff {n : ℕ} {m : Fin n → ℕ} (hm : ∀ i, 0 < m i)
    (j : CellIndex m) (theta : Point n)
    (ht : theta ∈ Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => Real.pi)) :
    (fun i => Real.cos (theta i)) ∈ closedCell j ↔ theta ∈ angularCell j := by
  have hlo (i : Fin n) : lower j i ∈ Icc (0 : ℝ) Real.pi :=
    ⟨lower_nonneg j i, (lower_le_upper j i).trans (upper_le_pi hm j i)⟩
  have hhi (i : Fin n) : upper j i ∈ Icc (0 : ℝ) Real.pi :=
    ⟨(lower_nonneg j i).trans (lower_le_upper j i), upper_le_pi hm j i⟩
  constructor
  · intro h
    exact ⟨fun i => (Real.strictAntiOn_cos.le_iff_ge ⟨ht.1 i, ht.2 i⟩ (hlo i)).mp (h.2 i),
      fun i => (Real.strictAntiOn_cos.le_iff_ge (hhi i) ⟨ht.1 i, ht.2 i⟩).mp (h.1 i)⟩
  · intro h
    exact ⟨fun i => (Real.strictAntiOn_cos.le_iff_ge (hhi i) ⟨ht.1 i, ht.2 i⟩).mpr (h.2 i),
      fun i => (Real.strictAntiOn_cos.le_iff_ge ⟨ht.1 i, ht.2 i⟩ (hlo i)).mpr (h.1 i)⟩

lemma arccos_mem_angularCell {n : ℕ} {m : Fin n → ℕ} (hm : ∀ i, 0 < m i)
    (j : CellIndex m) {x : Point n} (hx : x ∈ closedCell j) :
    (fun i => Real.arccos (x i)) ∈ angularCell j := by
  have hxbox := closedCell_subset_cube j hx
  have hbox : (fun i => Real.arccos (x i)) ∈
      Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => Real.pi) :=
    ⟨fun _ => Real.arccos_nonneg _, fun _ => Real.arccos_le_pi _⟩
  apply (cos_mem_closedCell_iff hm j _ hbox).mp
  convert hx using 1
  funext i
  exact Real.cos_arccos (hxbox.1 i) (hxbox.2 i)

lemma width {n : ℕ} {m : Fin n → ℕ} (j : CellIndex m) (i : Fin n) :
    upper j i - lower j i = Real.pi / m i := by unfold upper lower; ring

/-- The exact mass of a cell for a vector of mesh sizes. -/
def cellWeight {n : ℕ} (m : Fin n → ℕ) : ℝ := ∏ i, (m i : ℝ)⁻¹

lemma chebyshevLaw_closedCell {n : ℕ} {m : Fin n → ℕ} (hm : ∀ i, 0 < m i)
    (j : CellIndex m) : chebyshevLaw n (closedCell j) = ENNReal.ofReal (cellWeight m) := by
  have hpre : ((fun theta : Point n => fun i => Real.cos (theta i)) ⁻¹' closedCell j) ∩
      Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => Real.pi) = angularCell j := by
    ext theta
    constructor
    · rintro ⟨h, hb⟩
      exact (cos_mem_closedCell_iff hm j theta hb).mp h
    · intro h
      have hb := angularCell_subset_box hm j h
      exact ⟨(cos_mem_closedCell_iff hm j theta hb).mpr h, hb⟩
  have hc : MeasurableSet (closedCell j) := measurableSet_Icc
  rw [chebyshevLaw, Measure.map_apply (continuous_cosPoint n).measurable hc,
    angularLaw, Measure.smul_apply,
    Measure.restrict_apply (hc.preimage (continuous_cosPoint n).measurable), hpre]
  change (ENNReal.ofReal (Real.pi ^ n))⁻¹ * volume (angularCell j) = _
  rw [angularCell, Real.volume_Icc_pi]
  simp_rw [width]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity :
      ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ Real.pi / m i),
    ← ENNReal.ofReal_inv_of_pos (pow_pos Real.pi_pos n),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (Real.pi ^ n)⁻¹)]
  congr 1
  simp only [div_eq_mul_inv, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, cellWeight]
  rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n Real.pi_pos.ne'), one_mul]

theorem chebyshevLaw_halfOpenCell {n : ℕ} {m : Fin n → ℕ} (hm : ∀ i, 0 < m i)
    (j : CellIndex m) : chebyshevLaw n (halfOpenCell j) = ENNReal.ofReal (cellWeight m) := by
  let box := Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => Real.pi)
  let core := Set.pi Set.univ (fun i => Ico (lower j i) (upper j i))
  let pre := ((fun theta : Point n => fun i => Real.cos (theta i)) ⁻¹' halfOpenCell j) ∩ box
  have hsub : pre ⊆ angularCell j := by
    intro theta ht
    exact (cos_mem_closedCell_iff hm j theta ht.2).mp (halfOpenCell_subset_closedCell j ht.1)
  have hcore : core ⊆ pre := by
    intro theta ht
    have ht' (i : Fin n) : theta i ∈ Ico (lower j i) (upper j i) := ht i (mem_univ i)
    have ha : theta ∈ angularCell j := ⟨fun i => (ht' i).1, fun i => (ht' i).2.le⟩
    have hb := angularCell_subset_box hm j ha
    have hc := (cos_mem_closedCell_iff hm j theta hb).mpr ha
    refine ⟨Set.mem_iInter.mpr (fun i => ?_), hb⟩
    refine ⟨⟨fun _ => hc.1 i, fun _ => hc.2 i⟩, fun _ => Or.inl ?_⟩
    exact Real.cos_lt_cos_of_nonneg_of_le_pi (hb.1 i) (upper_le_pi hm j i) (ht' i).2
  have hvol : volume pre = volume (angularCell j) := by
    apply le_antisymm (measure_mono hsub)
    have hv : volume core = volume (angularCell j) := by
      change volume (Set.pi Set.univ (fun i => Ico (lower j i) (upper j i))) =
        volume (Icc (lower j) (upper j))
      rw [Real.volume_pi_Ico, Real.volume_Icc_pi]
    rw [← hv]
    exact measure_mono hcore
  rw [← chebyshevLaw_closedCell hm j]
  have hc : MeasurableSet (closedCell j) := measurableSet_Icc
  rw [chebyshevLaw, Measure.map_apply (continuous_cosPoint n).measurable
      (measurableSet_halfOpenCell j), Measure.map_apply (continuous_cosPoint n).measurable hc,
    angularLaw, Measure.smul_apply, Measure.smul_apply,
    Measure.restrict_apply ((measurableSet_halfOpenCell j).preimage (continuous_cosPoint n).measurable),
    Measure.restrict_apply (hc.preimage (continuous_cosPoint n).measurable)]
  have hpre : ((fun theta : Point n => fun i => Real.cos (theta i)) ⁻¹' closedCell j) ∩ box =
      angularCell j := by
    ext theta
    constructor
    · rintro ⟨h, hb⟩
      exact (cos_mem_closedCell_iff hm j theta hb).mp h
    · intro h
      have hb := angularCell_subset_box hm j h
      exact ⟨(cos_mem_closedCell_iff hm j theta hb).mpr h, hb⟩
  change _ * volume pre = _ * volume (_ ∩ box)
  rw [hpre, hvol]

lemma update_mem_angularCell {n : ℕ} {m : Fin n → ℕ} (j : CellIndex m)
    {theta : Point n} (htheta : theta ∈ angularCell j) (k : Fin n) {t : ℝ}
    (ht : t ∈ Icc (lower j k) (upper j k)) : Function.update theta k t ∈ angularCell j := by
  constructor <;> intro i <;> by_cases hi : i = k
  · subst i; simpa using ht.1
  · simpa only [Function.update_of_ne hi] using htheta.1 i
  · subst i; simpa using ht.2
  · simpa only [Function.update_of_ne hi] using htheta.2 i

lemma replaceCoordinates_mem_angularCell {n : ℕ} {m : Fin n → ℕ} (j : CellIndex m)
    {theta eta : Point n} (htheta : theta ∈ angularCell j) (heta : eta ∈ angularCell j)
    (S : Finset (Fin n)) : Paper34.replaceCoordinates S theta eta ∈ angularCell j := by
  constructor <;> intro k <;> by_cases hk : k ∈ S
  · simpa only [Paper34.replaceCoordinates, if_pos hk] using heta.1 k
  · simpa only [Paper34.replaceCoordinates, if_neg hk] using htheta.1 k
  · simpa only [Paper34.replaceCoordinates, if_pos hk] using heta.2 k
  · simpa only [Paper34.replaceCoordinates, if_neg hk] using htheta.2 k

theorem coordinate_local_bound {n D : ℕ} {m : Fin n → ℕ} (q : PolynomialSpace n D)
    (j : CellIndex m) {theta : Point n} (htheta : theta ∈ angularCell j)
    (k : Fin n) (C : ℝ)
    (hC : ∀ phi ∈ angularCell j, |Paper34.angularPartial q k phi| ≤ C)
    {s t : ℝ} (hs : s ∈ Icc (lower j k) (upper j k))
    (ht : t ∈ Icc (lower j k) (upper j k)) :
    |angularEval q (Function.update theta k t) - angularEval q (Function.update theta k s)| ≤
      C * |t - s| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun u (_ : u ∈ Icc (lower j k) (upper j k)) => differentiable_angularSlice q theta k u)
    (fun u hu => show ‖deriv (fun v => angularEval q (Function.update theta k v)) u‖ ≤ C from by
      simpa only [Paper34.angularPartial, Function.update_self, Function.update_idem,
        Real.norm_eq_abs] using hC (Function.update theta k u)
          (update_mem_angularCell j htheta k hu))
    (convex_Icc _ _) hs ht
  simpa only [Real.norm_eq_abs] using h

theorem finite_local_path {n D : ℕ} {m : Fin n → ℕ} (q : PolynomialSpace n D)
    (j : CellIndex m) (C : Fin n → ℝ)
    (hC : ∀ phi ∈ angularCell j, ∀ k, |Paper34.angularPartial q k phi| ≤ C k)
    {theta eta : Point n} (htheta : theta ∈ angularCell j) (heta : eta ∈ angularCell j)
    (S : Finset (Fin n)) :
    |angularEval q (Paper34.replaceCoordinates S theta eta) - angularEval q theta| ≤
      ∑ k ∈ S, C k * |eta k - theta k| := by
  induction S using Finset.induction_on with
  | empty =>
      have heq : Paper34.replaceCoordinates ∅ theta eta = theta := by
        funext k; simp [Paper34.replaceCoordinates]
      simp [heq]
  | @insert k S hk ih =>
      have hstep := coordinate_local_bound q j
        (replaceCoordinates_mem_angularCell j htheta heta S) k (C k)
        (fun phi hphi => hC phi hphi k)
        (show theta k ∈ Icc (lower j k) (upper j k) from ⟨htheta.1 k, htheta.2 k⟩)
        (show eta k ∈ Icc (lower j k) (upper j k) from ⟨heta.1 k, heta.2 k⟩)
      rw [Paper34.replaceCoordinates_update_original S theta eta k hk,
        ← Paper34.replaceCoordinates_insert S theta eta k] at hstep
      calc
        _ ≤ |angularEval q (Paper34.replaceCoordinates (insert k S) theta eta) -
              angularEval q (Paper34.replaceCoordinates S theta eta)| +
            |angularEval q (Paper34.replaceCoordinates S theta eta) - angularEval q theta| :=
          abs_sub_le _ _ _
        _ ≤ C k * |eta k - theta k| + ∑ i ∈ S, C i * |eta i - theta i| := add_le_add hstep ih
        _ = _ := by rw [Finset.sum_insert hk]

/-- The variable-width path uses `π/mₖ` separately in coordinate `k`. -/
theorem local_path_bound {n D : ℕ} {m : Fin n → ℕ} (q : PolynomialSpace n D)
    (j : CellIndex m) (C : Fin n → ℝ)
    (hC : ∀ phi ∈ angularCell j, ∀ k, |Paper34.angularPartial q k phi| ≤ C k)
    {theta eta : Point n} (htheta : theta ∈ angularCell j) (heta : eta ∈ angularCell j) :
    |angularEval q theta - angularEval q eta| ≤ ∑ k, (Real.pi / m k) * C k := by
  have hpath := finite_local_path q j C hC heta htheta Finset.univ
  have heq : Paper34.replaceCoordinates Finset.univ eta theta = theta := by
    funext k; simp [Paper34.replaceCoordinates]
  rw [heq] at hpath
  refine hpath.trans (Finset.sum_le_sum (fun k _ => ?_))
  have hC0 : 0 ≤ C k := (abs_nonneg _).trans (hC theta htheta k)
  have hdist : |theta k - eta k| ≤ Real.pi / m k := by
    have hw := width j k
    exact abs_le.mpr ⟨by linarith [htheta.1 k, heta.2 k],
      by linarith [htheta.2 k, heta.1 k]⟩
  exact (mul_le_mul_of_nonneg_left hdist hC0).trans_eq (mul_comm _ _)

def cellStep {n : ℕ} {m : Fin n → ℕ} (v : CellIndex m → ℝ) (x : Point n) : ℝ :=
  ∑ j, (halfOpenCell j).indicator (fun _ => v j) x

def representativeStep {n D : ℕ} {m : Fin n → ℕ} (q : PolynomialSpace n D)
    (xi : CellIndex m → Point n) : Point n → ℝ := cellStep (fun j => polyEval q (xi j))

lemma cellStep_eq {n : ℕ} {m : Fin n → ℕ} (hm : ∀ i, 0 < m i)
    (v : CellIndex m → ℝ) (j : CellIndex m) {x : Point n} (hx : x ∈ halfOpenCell j) :
    cellStep v x = v j := by
  unfold cellStep
  rw [Finset.sum_eq_single j]
  · exact Set.indicator_of_mem hx _
  · intro i _ hij
    exact Set.indicator_of_notMem (fun hi => Set.disjoint_left.mp (pairwiseDisjoint hm hij) hi hx) _
  · simp

lemma integrable_cellStep {n : ℕ} {m : Fin n → ℕ} (v : CellIndex m → ℝ) :
    Integrable (cellStep v) (chebyshevLaw n) := by
  apply integrable_finset_sum
  intro j _
  exact (integrable_const _).indicator (measurableSet_halfOpenCell j)

theorem integral_cellStep {n : ℕ} {m : Fin n → ℕ} (hm : ∀ i, 0 < m i)
    (v : CellIndex m → ℝ) :
    (∫ x, cellStep v x ∂chebyshevLaw n) = cellWeight m * ∑ j, v j := by
  unfold cellStep
  rw [integral_finset_sum _ (fun j _ =>
    (integrable_const _).indicator (measurableSet_halfOpenCell j))]
  simp_rw [integral_indicator_const _ (measurableSet_halfOpenCell _), measureReal_def,
    chebyshevLaw_halfOpenCell hm, ENNReal.toReal_ofReal (by unfold cellWeight; positivity :
      (0 : ℝ) ≤ cellWeight m), smul_eq_mul]
  exact (Finset.mul_sum ..).symm

theorem representative_cell_error_le {n D : ℕ} {m : Fin n → ℕ} (q : PolynomialSpace n D)
    (hm : ∀ i, 0 < m i) (xi : CellIndex m → Point n) (hxi : ∀ j, xi j ∈ closedCell j)
    (C : CellIndex m → Fin n → ℝ)
    (hC : ∀ j phi, phi ∈ angularCell j → ∀ k, |Paper34.angularPartial q k phi| ≤ C j k)
    (j : CellIndex m) {x : Point n} (hx : x ∈ closedCell j) :
    |polyEval q x - polyEval q (xi j)| ≤ ∑ k, (Real.pi / m k) * C j k := by
  have h := local_path_bound q j (C j) (hC j)
    (arccos_mem_angularCell hm j hx) (arccos_mem_angularCell hm j (hxi j))
  rw [angularEval_arccos q x (closedCell_subset_cube j hx),
    angularEval_arccos q (xi j) (closedCell_subset_cube j (hxi j))] at h
  exact h

/-- The actual anisotropic error integral, before local-supremum and Bernstein
bounds. Representatives may depend jointly on every cell coordinate. -/
theorem representative_error_le_partial_sum {n D : ℕ} {m : Fin n → ℕ}
    (q : PolynomialSpace n D) (hm : ∀ i, 0 < m i)
    (xi : CellIndex m → Point n) (hxi : ∀ j, xi j ∈ closedCell j)
    (C : CellIndex m → Fin n → ℝ)
    (hC : ∀ j phi, phi ∈ angularCell j → ∀ k, |Paper34.angularPartial q k phi| ≤ C j k) :
    (∫ x, |polyEval q x - representativeStep q xi x| ∂chebyshevLaw n) ≤
      ∑ k, (Real.pi / m k) * (cellWeight m * ∑ j, C j k) := by
  have hbound : (∫ x, |polyEval q x - representativeStep q xi x| ∂chebyshevLaw n) ≤
      cellWeight m * ∑ j, ∑ k, (Real.pi / m k) * C j k := by
    rw [← integral_cellStep hm]
    apply integral_mono_ae
    · exact ((integrable_polyEval q).sub (integrable_cellStep _)).abs
    · exact integrable_cellStep _
    · filter_upwards [chebyshevLaw_ae_cube n] with x hx
      obtain ⟨j, hj⟩ := cube_covered hm x hx
      rw [representativeStep, cellStep_eq hm _ j hj, cellStep_eq hm _ j hj]
      exact representative_cell_error_le q hm xi hxi C hC j (halfOpenCell_subset_closedCell j hj)
  convert hbound using 1
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.mul_sum]
  ring

def positiveGridIndex {n : ℕ} {m : Fin n → ℕ} (j : CellIndex m) :
    Anisotropic.GridIndex n m := fun k => ⟨j k, by have := (j k).isLt; omega⟩

lemma positiveGridIndex_injective {n : ℕ} {m : Fin n → ℕ} :
    Function.Injective (@positiveGridIndex n m) := by
  intro j k hjk
  funext i
  apply Fin.ext
  exact congrArg (fun f : Anisotropic.GridIndex n m => (f i : ℕ)) hjk

lemma angularCell_eq_gridCell {n : ℕ} {m : Fin n → ℕ} (j : CellIndex m) :
    angularCell j = Anisotropic.gridCell (positiveGridIndex j) := by
  apply congrArg₂ Icc <;> funext k <;> simp only [lower, upper, positiveGridIndex] <;> ring

lemma norm_le_cellSup {n : ℕ} {m : Fin n → ℕ} (f : C(TensorNorming.TorusN n, ℂ))
    (j : Anisotropic.GridIndex n m) {theta : Point n} (htheta : theta ∈ Anisotropic.gridCell j) :
    ‖f (TensorNorming.angularPoint theta)‖ ≤ Anisotropic.cellSup f j := by
  have hc : Continuous (fun t : Point n => ‖f (TensorNorming.angularPoint t)‖) :=
    (f.continuous.comp (TensorNorming.continuous_angularPoint n)).norm
  exact le_csSup (((isCompact_Icc : IsCompact (Anisotropic.gridCell j)).image hc).bddAbove)
    ⟨theta, htheta, rfl⟩

lemma cellSup_nonneg {n : ℕ} {m : Fin n → ℕ} (f : C(TensorNorming.TorusN n, ℂ))
    (j : Anisotropic.GridIndex n m) : 0 ≤ Anisotropic.cellSup f j := by
  obtain ⟨theta, ht⟩ := Anisotropic.gridCell_nonempty j
  exact (norm_nonneg _).trans (norm_le_cellSup f j ht)

lemma positive_grid_sum_le {n : ℕ} {m : Fin n → ℕ}
    (f : Anisotropic.GridIndex n m → ℝ) (hf : ∀ j, 0 ≤ f j) :
    (∑ j : CellIndex m, f (positiveGridIndex j)) ≤ ∑ j : Anisotropic.GridIndex n m, f j := by
  classical
  calc
    _ = ∑ j ∈ Finset.univ.image positiveGridIndex, f j := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => positiveGridIndex_injective h
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hf j)

theorem positive_local_supremum_bound {n : ℕ} {d m : Fin n → ℕ}
    (H : Anisotropic.BoxTrigPolynomial d) (hm : ∀ i, max 1 (d i) ≤ m i) :
    cellWeight m * ∑ j : CellIndex m, Anisotropic.cellSup H.toContinuousMap (positiveGridIndex j) ≤
      ((2 : ℝ) * (3 + 10 * Real.pi)) ^ n *
        ∫ u : TensorNorming.TorusN n, ‖H.eval u‖ ∂TensorNorming.haarN n := by
  have hwi (i : Fin n) : (m i : ℝ)⁻¹ = 2 * TensorNorming.gridWeight (m i) := by
    have hmpos : (0 : ℝ) < m i := by exact_mod_cast (show 0 < m i by have := hm i; omega)
    unfold TensorNorming.gridWeight
    field_simp
  have hw : cellWeight m = 2 ^ n * Anisotropic.gridWeight m := by
    unfold cellWeight Anisotropic.gridWeight
    simp_rw [hwi, Finset.prod_mul_distrib]
    simp
  have hsum := positive_grid_sum_le
    (fun j : Anisotropic.GridIndex n m => Anisotropic.cellSup H.toContinuousMap j)
    (fun j => cellSup_nonneg H.toContinuousMap j)
  have hlocal := Anisotropic.local_supremum_bound H hm
  calc
    _ ≤ cellWeight m * ∑ j : Anisotropic.GridIndex n m, Anisotropic.cellSup H.toContinuousMap j :=
      mul_le_mul_of_nonneg_left hsum (by unfold cellWeight; positivity)
    _ = 2 ^ n * (Anisotropic.gridWeight m *
        ∑ j : Anisotropic.GridIndex n m, Anisotropic.cellSup H.toContinuousMap j) := by rw [hw]; ring
    _ ≤ 2 ^ n * ((3 + 10 * Real.pi) ^ n *
        ∫ u : TensorNorming.TorusN n, ‖H.eval u‖ ∂TensorNorming.haarN n) :=
      mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = _ := by rw [mul_pow]; ring

lemma angularPartial_le_fourier_cellSup {n : ℕ} {d m : Fin n → ℕ}
    (q : Anisotropic.BoxPolynomial d) (j : CellIndex m) (theta : Point n)
    (htheta : theta ∈ angularCell j) (k : Fin n) :
    |Paper34.angularPartial q.toUniform k theta| ≤
      Anisotropic.cellSup (q.fourierLift.partial k).toContinuousMap (positiveGridIndex j) := by
  have heq := Paper34.angularPartial_eq_fourier_partial q.toUniform q.fourierLift.toUniform
    (Anisotropic.fourierLift_angular q) k theta
  have hnorm : |Paper34.angularPartial q.toUniform k theta| =
      ‖(q.fourierLift.partial k).eval (TensorNorming.angularPoint theta)‖ := by
    change _ = ‖(q.fourierLift.toUniform.partial k).eval (TensorNorming.angularPoint theta)‖
    rw [← heq, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm]
  exact norm_le_cellSup _ _ ((angularCell_eq_gridCell j) ▸ htheta)

/-- A dimension-only constant valid for the variable-coordinate-degree result.
It also dominates the uniform-grid constant already proved in Lemma 3.3. -/
def normingConstant (n : ℕ) : ℝ :=
  max (Paper34.arbitraryRepresentativeConstant n)
    (Real.pi * (((2 : ℝ) * (3 + 10 * Real.pi)) ^ n) * (10 * 3 ^ (n - 1)))

theorem normingConstant_ge_one (n : ℕ) : 1 ≤ normingConstant n :=
  (Paper34.arbitraryRepresentativeConstant_ge_one n).trans (le_max_left _ _)

/-- Appendix A.3's anisotropic `L¹` error, including every zero coordinate
degree. The polynomial, cells, jointly chosen representatives, half-open step,
and normalized Chebyshev law are all actual source objects. -/
theorem anisotropic_representative_error {n : ℕ} {d m : Fin n → ℕ}
    (q : Anisotropic.BoxPolynomial d) (hm : ∀ i, max 1 (d i) ≤ m i)
    (xi : CellIndex m → Point n) (hxi : ∀ j, xi j ∈ closedCell j) :
    (∫ x, |polyEval q.toUniform x - representativeStep q.toUniform xi x| ∂chebyshevLaw n) ≤
      normingConstant n * (∑ k, (d k : ℝ) / m k) * l1Norm q.toUniform := by
  have hm0 (i : Fin n) : 0 < m i := by have := hm i; omega
  let H := q.fourierLift
  let C : CellIndex m → Fin n → ℝ := fun j k =>
    Anisotropic.cellSup (H.partial k).toContinuousMap (positiveGridIndex j)
  have hpath := representative_error_le_partial_sum q.toUniform hm0 xi hxi C
    (fun j theta htheta k => angularPartial_le_fourier_cellSup q j theta htheta k)
  have hnorm : (∫ u : TensorNorming.TorusN n, ‖H.eval u‖ ∂TensorNorming.haarN n) =
      l1Norm q.toUniform := HaarChebyshev.haar_l1_eq_l1Norm q.toUniform H.toUniform
        (Anisotropic.fourierLift_angular q)
  let Cn : ℝ := ((2 : ℝ) * (3 + 10 * Real.pi)) ^ n
  let Dn : ℝ := 10 * 3 ^ (n - 1)
  have hs (k : Fin n) : cellWeight m * ∑ j, C j k ≤
      Cn * (Dn * d k * l1Norm q.toUniform) := by
    have hl := positive_local_supremum_bound (H.partial k) hm
    have hb := Anisotropic.partial_L1 H k
    rw [hnorm] at hb
    exact hl.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  have hl10 : 0 ≤ l1Norm q.toUniform := integral_nonneg (fun _ => abs_nonneg _)
  have hsum0 : 0 ≤ (∑ k, (d k : ℝ) / m k) * l1Norm q.toUniform :=
    mul_nonneg (Finset.sum_nonneg fun k _ => by positivity) hl10
  calc
    _ ≤ ∑ k, (Real.pi / m k) * (cellWeight m * ∑ j, C j k) := hpath
    _ ≤ ∑ k, (Real.pi / m k) * (Cn * (Dn * d k * l1Norm q.toUniform)) :=
      Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hs k) (by positivity))
    _ = (Real.pi * Cn * Dn) * ((∑ k, (d k : ℝ) / m k) * l1Norm q.toUniform) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ ≤ normingConstant n * ((∑ k, (d k : ℝ) / m k) * l1Norm q.toUniform) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hsum0
    _ = _ := by ring

/-- The sharp cell-oscillation factor in Appendix A.3. Its sole external input
is the explicitly documented classical one-dimensional trigonometric Bernstein
theorem, after the actual bounded-degree cosine membership is proved. -/
theorem anisotropic_cell_difference
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {n : ℕ} {d m : Fin n → ℕ} (q : Anisotropic.BoxPolynomial d)
    (hm : ∀ i, 0 < m i) (j : CellIndex m) (x z : Point n)
    (hx : x ∈ closedCell j) (hz : z ∈ closedCell j) :
    |polyEval q.toUniform x - polyEval q.toUniform z| ≤
      (Real.pi * ∑ k, (d k : ℝ) / m k) * supNorm q.toUniform := by
  have hpath := local_path_bound q.toUniform j (fun k => (d k : ℝ) * supNorm q.toUniform)
    (fun theta _ k => Anisotropic.angularDerivative_bound hBernstein q theta k (theta k))
    (arccos_mem_angularCell hm j hx) (arccos_mem_angularCell hm j hz)
  rw [angularEval_arccos q.toUniform x (closedCell_subset_cube j hx),
    angularEval_arccos q.toUniform z (closedCell_subset_cube j hz)] at hpath
  convert hpath using 1
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma closedCell_nonempty {n : ℕ} {m : Fin n → ℕ} (hm : ∀ i, 0 < m i)
    (j : CellIndex m) : (closedCell j).Nonempty := by
  have ha : lower j ∈ angularCell j := ⟨le_rfl, fun i => lower_le_upper j i⟩
  exact ⟨fun i => Real.cos (lower j i),
    (cos_mem_closedCell_iff hm j _ (angularCell_subset_box hm j ha)).mpr ha⟩

def cellOscillation {n : ℕ} {d m : Fin n → ℕ} (q : Anisotropic.BoxPolynomial d)
    (j : CellIndex m) : ℝ :=
  sSup ((fun xz : Point n × Point n =>
    |polyEval q.toUniform xz.1 - polyEval q.toUniform xz.2|) ''
      (closedCell j ×ˢ closedCell j))

/-- The supremum form of the Appendix's actual cell-oscillation estimate. -/
theorem anisotropic_cellOscillation
    (hBernstein : TrigBernstein.ClassicalTrigBernstein)
    {n : ℕ} {d m : Fin n → ℕ} (q : Anisotropic.BoxPolynomial d)
    (hm : ∀ i, 0 < m i) (j : CellIndex m) :
    cellOscillation q j ≤ (Real.pi * ∑ k, (d k : ℝ) / m k) * supNorm q.toUniform := by
  unfold cellOscillation
  apply csSup_le
  · exact ((closedCell_nonempty hm j).prod (closedCell_nonempty hm j)).image _
  · rintro _ ⟨⟨x, z⟩, ⟨hx, hz⟩, rfl⟩
    exact anisotropic_cell_difference hBernstein q hm j x z hx hz

/-- All anisotropic degrees and meshes use one dimension-dependent constant. -/
theorem anisotropic_dimension_constant (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (d m : Fin n → ℕ) (q : Anisotropic.BoxPolynomial d),
      (∀ i, max 1 (d i) ≤ m i) → ∀ (xi : CellIndex m → Point n),
        (∀ j, xi j ∈ closedCell j) →
          (∫ x, |polyEval q.toUniform x - representativeStep q.toUniform xi x| ∂chebyshevLaw n) ≤
            A * (∑ k, (d k : ℝ) / m k) * l1Norm q.toUniform := by
  exact ⟨normingConstant n, normingConstant_ge_one n,
    fun _ _ q hm xi hxi => anisotropic_representative_error q hm xi hxi⟩

end Paper34.AnisotropicRepresentatives
