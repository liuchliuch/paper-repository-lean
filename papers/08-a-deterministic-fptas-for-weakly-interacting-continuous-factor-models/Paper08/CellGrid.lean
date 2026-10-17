import Paper08.QuadratureIntegral
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.MeasureTheory.Integral.Pi

/-! # Actual anisotropic dyadic cells and exact finite Lebesgue quadrature -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory Set
namespace Paper08.CellGrid

/-- A one-dimensional dyadic cell, including the endpoint one in the last cell. -/
def atom (level : ℕ) (j : Fin (2 ^ level)) : Set ℝ :=
  {x | x ∈ Icc (0 : ℝ) 1 ∧ Dyadic.cellIndex level x = j.val}

/-- The cells for independent coordinate levels `m`. -/
abbrev Grid {n : ℕ} (m : Fin n → ℕ) := (v : Fin n) → Fin (2 ^ m v)

def cell {n : ℕ} (m : Fin n → ℕ) (z : Grid m) : Set (Fin n → ℝ) :=
  Set.pi Set.univ fun v => atom (m v) (z v)

/-- The rational lower corner of an anisotropic cell. -/
def cornerQ {n : ℕ} {m : Fin n → ℕ} (z : Grid m) : Fin n → ℚ :=
  fun v => (z v : ℚ) / (2 : ℚ) ^ m v

def corner {n : ℕ} {m : Fin n → ℕ} (z : Grid m) : Fin n → ℝ :=
  fun v => (cornerQ z v : ℝ)

/-- Every cell has the same rational dyadic weight. -/
def weightQ {n : ℕ} (m : Fin n → ℕ) : ℚ := ((2 : ℚ) ^ (∑ v, m v))⁻¹

lemma corner_apply {n : ℕ} {m : Fin n → ℕ} (z : Grid m) (v : Fin n) :
    corner z v = (z v : ℝ) / (2 : ℝ) ^ m v := by simp [corner, cornerQ]

lemma measurableSet_atom (level : ℕ) (j : Fin (2 ^ level)) : MeasurableSet (atom level j) :=
  measurableSet_Icc.inter ((Dyadic.measurable_cellIndex level) (measurableSet_singleton j.val))

lemma mem_cell {n : ℕ} {m : Fin n → ℕ} {z : Grid m} {x : Fin n → ℝ} :
    x ∈ cell m z ↔ ∀ v, x v ∈ atom (m v) (z v) := by
  change (∀ v, v ∈ (Set.univ : Set (Fin n)) → x v ∈ atom (m v) (z v)) ↔ _
  simp

lemma cell_subset_cube {n : ℕ} (m : Fin n → ℕ) (z : Grid m) :
    cell m z ⊆ Integral.cube n := by
  intro x hx
  exact Integral.mem_cube.mpr fun v => ((mem_cell.mp hx) v).1

lemma measurableSet_cell {n : ℕ} (m : Fin n → ℕ) (z : Grid m) : MeasurableSet (cell m z) :=
  MeasurableSet.pi Set.countable_univ fun v _ => measurableSet_atom (m v) (z v)

lemma atom_Ico_subset (level : ℕ) (j : Fin (2 ^ level)) :
    Ico ((j : ℝ) / (2 : ℝ) ^ level) (((j : ℝ) + 1) / (2 : ℝ) ^ level) ⊆ atom level j := by
  intro x hx
  have hp : 0 < (2 : ℝ) ^ level := by positivity
  have hj : (j : ℝ) + 1 ≤ (2 : ℝ) ^ level := by exact_mod_cast j.isLt
  have hx0 : 0 ≤ x := (div_nonneg (by positivity) hp.le).trans hx.1
  have hx1 : x ≤ 1 := by
    have hupper : ((j : ℝ) + 1) / (2 : ℝ) ^ level ≤ 1 := by
      exact (div_le_one hp).mpr hj
    exact hx.2.le.trans hupper
  refine ⟨⟨hx0, hx1⟩, ?_⟩
  have hfloor : ⌊(2 : ℝ) ^ level * x⌋₊ = j.val := by
    apply (Nat.floor_eq_iff (mul_nonneg hp.le hx0)).mpr
    constructor
    · simpa only [mul_comm] using (div_le_iff₀ hp).mp hx.1
    · simpa only [mul_comm] using (lt_div_iff₀ hp).mp hx.2
  rw [Dyadic.cellIndex, hfloor, min_eq_left]
  omega

lemma atom_subset_Icc (level : ℕ) (j : Fin (2 ^ level)) :
    atom level j ⊆ Icc ((j : ℝ) / (2 : ℝ) ^ level)
      (((j : ℝ) + 1) / (2 : ℝ) ^ level) := by
  intro x hx
  have hp : 0 < (2 : ℝ) ^ level := by positivity
  have hlo := Dyadic.lower_le (level := level) hx.1.1
  rw [Dyadic.lower, hx.2] at hlo
  refine ⟨hlo, ?_⟩
  by_cases hf : ⌊(2 : ℝ) ^ level * x⌋₊ ≤ 2 ^ level - 1
  · have he : ⌊(2 : ℝ) ^ level * x⌋₊ = j.val := by
      simpa only [Dyadic.cellIndex, min_eq_left hf] using hx.2
    have ht := Nat.lt_floor_add_one ((2 : ℝ) ^ level * x)
    rw [he] at ht
    exact (le_div_iff₀ hp).mpr (by nlinarith)
  · have he : 2 ^ level - 1 = j.val := by
      simpa only [Dyadic.cellIndex, min_eq_right (le_of_not_ge hf)] using hx.2
    have hj : (j : ℝ) + 1 = (2 : ℝ) ^ level := by
      have hn : j.val + 1 = 2 ^ level := by omega
      exact_mod_cast hn
    rw [hj, div_self hp.ne']
    exact hx.1.2

lemma volume_atom (level : ℕ) (j : Fin (2 ^ level)) :
    volume (atom level j) = ENNReal.ofReal (((2 : ℝ) ^ level)⁻¹) := by
  have hlen : ((j : ℝ) + 1) / (2 : ℝ) ^ level - (j : ℝ) / (2 : ℝ) ^ level =
      ((2 : ℝ) ^ level)⁻¹ := by ring
  apply le_antisymm
  · exact (measure_mono (atom_subset_Icc level j)).trans_eq (by rw [Real.volume_Icc, hlen])
  · exact (show volume (Ico ((j : ℝ) / (2 : ℝ) ^ level)
        (((j : ℝ) + 1) / (2 : ℝ) ^ level)) ≤ volume (atom level j) from
      measure_mono (atom_Ico_subset level j)) |>.trans_eq' (by rw [Real.volume_Ico, hlen])

lemma volume_cell_lt_top {n : ℕ} (m : Fin n → ℕ) (z : Grid m) :
    volume (cell m z) < ⊤ :=
  (measure_mono (cell_subset_cube m z)).trans_lt (Integral.volume_cube_lt_top n)

lemma volume_real_cell {n : ℕ} (m : Fin n → ℕ) (z : Grid m) :
    volume.real (cell m z) = (weightQ m : ℝ) := by
  unfold cell Measure.real
  rw [volume_pi_pi, ENNReal.toReal_prod]
  simp_rw [volume_atom, ENNReal.toReal_ofReal (by positivity : 0 ≤ ((2 : ℝ) ^ _)⁻¹)]
  rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]
  simp [weightQ]

lemma cells_pairwise_disjoint {n : ℕ} (m : Fin n → ℕ) : Pairwise (fun z w : Grid m => Disjoint (cell m z) (cell m w)) := by
  intro z w hzw
  rw [Set.disjoint_left]
  intro x hxz hxw
  apply hzw
  funext v
  apply Fin.ext
  exact ((mem_cell.mp hxz v).2).symm.trans (mem_cell.mp hxw v).2

lemma cells_union {n : ℕ} (m : Fin n → ℕ) : (⋃ z : Grid m, cell m z) = Integral.cube n := by
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun z => cell_subset_cube m z
  · intro x hx
    let z : Grid m := fun v => ⟨Dyadic.cellIndex (m v) (x v), Dyadic.cellIndex_lt _ _⟩
    apply Set.mem_iUnion.mpr
    refine ⟨z, mem_cell.mpr fun v => ?_⟩
    exact ⟨Integral.mem_cube.mp hx v, rfl⟩

lemma corner_mem_cell {n : ℕ} {m : Fin n → ℕ} (z : Grid m) : corner z ∈ cell m z := by
  apply mem_cell.mpr
  intro v
  apply atom_Ico_subset (m v) (z v)
  rw [corner_apply]
  exact ⟨le_rfl, (div_lt_div_iff_of_pos_right (by positivity)).mpr (by linarith)⟩

/-- Exact finite quadrature for a function constant on these actual cells. -/
theorem cubeIntegral_eq_cell_sum {n : ℕ} (m : Fin n → ℕ) (f : (Fin n → ℝ) → ℝ)
    (hf : ∀ z : Grid m, ∀ x ∈ cell m z, f x = f (corner z)) :
    Integral.cubeIntegral f = ∑ z : Grid m, (weightQ m : ℝ) * f (corner z) := by
  have hi : ∀ z : Grid m, IntegrableOn f (cell m z) := by
    intro z
    have hc : IntegrableOn (fun _ : Fin n → ℝ => f (corner z)) (cell m z) :=
      integrableOn_const (volume_cell_lt_top m z).ne
    exact hc.congr_fun (fun x hx => (hf z x hx).symm) (measurableSet_cell m z)
  unfold Integral.cubeIntegral
  rw [← cells_union m, integral_iUnion_fintype (measurableSet_cell m) (cells_pairwise_disjoint m) hi]
  apply Finset.sum_congr rfl
  intro z _
  rw [setIntegral_congr_fun (measurableSet_cell m z) (hf z), setIntegral_const,
    volume_real_cell, smul_eq_mul]

/-- The number of anisotropic cells is exactly `2^(sum coordinate levels)`. -/
lemma card_grid {n : ℕ} (m : Fin n → ℕ) : Fintype.card (Grid m) = 2 ^ (∑ v, m v) := by
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin]
  exact Finset.prod_pow_eq_pow_sum Finset.univ m 2

/-- Exact dyadic coarsening of capped interval indices. It includes both endpoints. -/
lemma cellIndex_coarsen {l m : ℕ} (hlm : l ≤ m) (x : ℝ) :
    Dyadic.cellIndex m x / 2 ^ (m - l) = Dyadic.cellIndex l x := by
  have hp : 2 ^ m = 2 ^ (m - l) * 2 ^ l := by rw [← pow_add, Nat.sub_add_cancel hlm]
  have hdivmin : ∀ a b : ℕ,
      min a b / 2 ^ (m - l) = min (a / 2 ^ (m - l)) (b / 2 ^ (m - l)) := by
    intro a b
    exact (show Monotone (fun k : ℕ => k / 2 ^ (m - l)) from
      fun a b hab => Nat.div_le_div_right hab).map_min
  have hcap : (2 ^ m - 1) / 2 ^ (m - l) = 2 ^ l - 1 := by
    rw [hp]
    simpa using Nat.mul_sub_div 0 (2 ^ (m - l)) (2 ^ l) (by positivity)
  have hfloor : ⌊(2 : ℝ) ^ m * x⌋₊ / 2 ^ (m - l) = ⌊(2 : ℝ) ^ l * x⌋₊ := by
    rw [← Nat.floor_div_natCast]
    congr 1
    have hpr : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - l) * (2 : ℝ) ^ l := by exact_mod_cast hp
    push_cast
    rw [hpr]
    field_simp
  simp only [Dyadic.cellIndex, hdivmin, hcap, hfloor]

lemma lower_coarsen {l m : ℕ} (hlm : l ≤ m) (x : ℝ) :
    Dyadic.lower l (Dyadic.lower m x) = Dyadic.lower l x := by
  have hp : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - l) * (2 : ℝ) ^ l := by
    rw [← pow_add, Nat.sub_add_cancel hlm]
  have harg : (2 : ℝ) ^ l * ((Dyadic.cellIndex m x : ℝ) / (2 : ℝ) ^ m) =
      (Dyadic.cellIndex m x : ℝ) / (2 ^ (m - l) : ℕ) := by
    push_cast
    rw [hp]
    field_simp
  have hi : Dyadic.cellIndex l (Dyadic.lower m x) = Dyadic.cellIndex l x := by
    unfold Dyadic.lower
    rw [Dyadic.cellIndex, harg, Nat.floor_div_eq_div, cellIndex_coarsen hlm]
    exact min_eq_left (Nat.le_pred_of_lt (Dyadic.cellIndex_lt l x))
  exact congrArg (fun j : ℕ => (j : ℝ) / (2 : ℝ) ^ l) hi

/-- On a fine cell, every coarser lower-corner projection is constant. -/
lemma lower_eq_on_cell {n : ℕ} {m : Fin n → ℕ} {z : Grid m} {x : Fin n → ℝ}
    (hx : x ∈ cell m z) (v : Fin n) {l : ℕ} (hl : l ≤ m v) :
    Dyadic.lower l (x v) = Dyadic.lower l (corner z v) := by
  have hlow : Dyadic.lower (m v) (x v) = corner z v := by
    rw [Dyadic.lower, (mem_cell.mp hx v).2, corner_apply]
  rw [← hlow, lower_coarsen hl]

/-- The shared coordinate level is the maximum over factors using that coordinate. -/
def commonLevels {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (ν : Fin t → ℕ)
    (v : Fin n) : ℕ := Finset.univ.sup fun i => if v ∈ scopes i then ν i else 0

lemma level_le_common {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (ν : Fin t → ℕ)
    (i : Fin t) {v : Fin n} (hv : v ∈ scopes i) : ν i ≤ commonLevels scopes ν v := by
  simpa only [if_pos hv] using
    (Finset.le_sup (s := Finset.univ) (f := fun j => if v ∈ scopes j then ν j else 0) (Finset.mem_univ i))

/-- The overlap bound (1.2)/(3.6), for the actual maximum coordinate levels. -/
lemma sum_commonLevels_le {n t r : ℕ} (scopes : Fin t → Finset (Fin n))
    (hscopes : ∀ i, (scopes i).card ≤ r) (ν : Fin t → ℕ) :
    (∑ v, commonLevels scopes ν v) ≤ r * ∑ i, ν i := by
  calc
    _ ≤ ∑ v : Fin n, ∑ i : Fin t, if v ∈ scopes i then ν i else 0 := by
      apply Finset.sum_le_sum
      intro v _
      apply Finset.sup_le
      intro i _
      exact Finset.single_le_sum (f := fun i : Fin t => if v ∈ scopes i then ν i else 0)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = ∑ i : Fin t, (scopes i).card * ν i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter]
      simp
    _ ≤ ∑ i : Fin t, r * ν i := Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (hscopes i)
    _ = _ := by rw [Finset.mul_sum]

lemma common_grid_card_le {n t r J : ℕ} (scopes : Fin t → Finset (Fin n))
    (hscopes : ∀ i, (scopes i).card ≤ r) (ν : Fin t → ℕ) (hν : ∑ i, ν i ≤ J) :
    Fintype.card (Grid (commonLevels scopes ν)) ≤ 2 ^ (r * J) := by
  rw [card_grid]
  exact Nat.pow_le_pow_right (by omega) ((sum_commonLevels_le scopes hscopes ν).trans
    (Nat.mul_le_mul_left r hν))

lemma scopedStep_eq_on_cell {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (ν : Fin t → ℕ) (i : Fin t) (f : LocalFunc (scopes i).card) {l : ℕ} (hl : l ≤ ν i)
    {z : Grid (commonLevels scopes ν)} {x : Fin n → ℝ}
    (hx : x ∈ cell (commonLevels scopes ν) z) :
    (Dyadic.step f l).toFun (Integral.restrictTo (scopes i) x) =
      (Dyadic.step f l).toFun (Integral.restrictTo (scopes i) (corner z)) := by
  apply congrArg f.toFun
  funext j
  apply lower_eq_on_cell hx
  exact hl.trans (level_le_common scopes ν i (Finset.orderEmbOfFin_mem (scopes i) rfl j))

lemma scopedIncrement_eq_on_cell {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (f : (i : Fin t) → LocalFunc (scopes i).card) (ν : Fin t → ℕ) (i : Fin t)
    {l : ℕ} (hl : l ≤ ν i) {z : Grid (commonLevels scopes ν)} {x : Fin n → ℝ}
    (hx : x ∈ cell (commonLevels scopes ν) z) :
    Quadrature.scopedIncrement scopes f i l x = Quadrature.scopedIncrement scopes f i l (corner z) := by
  cases l with
  | zero => exact scopedStep_eq_on_cell scopes ν i (f i) hl hx
  | succ l =>
      change (Dyadic.step (f i) (l + 1)).toFun _ - (Dyadic.step (f i) l).toFun _ = _
      rw [scopedStep_eq_on_cell scopes ν i (f i) hl hx,
        scopedStep_eq_on_cell scopes ν i (f i) (Nat.le_trans (Nat.le_succ l) hl) hx]
      rfl

/-- Exact evaluation of each retained product, for arbitrary overlapping scopes. -/
theorem integral_increment_product_eq_cell_sum {n t : ℕ}
    (scopes : Fin t → Finset (Fin n)) (f : (i : Fin t) → LocalFunc (scopes i).card)
    (ν : Fin t → ℕ) :
    Integral.cubeIntegral (fun x => ∏ i, Quadrature.scopedIncrement scopes f i (ν i) x) =
      ∑ z : Grid (commonLevels scopes ν), (weightQ (commonLevels scopes ν) : ℝ) *
        ∏ i, Quadrature.scopedIncrement scopes f i (ν i) (corner z) := by
  apply cubeIntegral_eq_cell_sum
  intro z x hx
  exact Finset.prod_congr rfl fun i _ => scopedIncrement_eq_on_cell scopes f ν i le_rfl hx

lemma storedScopedIncrement_eq_on_cell {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (samples : (i : Fin t) → ℕ → LocalFunc (scopes i).card) (ν : Fin t → ℕ) (i : Fin t)
    {l : ℕ} (hl : l ≤ ν i) {z : Grid (commonLevels scopes ν)} {x : Fin n → ℝ}
    (hx : x ∈ cell (commonLevels scopes ν) z) :
    Quadrature.storedScopedIncrement scopes samples i l x =
      Quadrature.storedScopedIncrement scopes samples i l (corner z) := by
  cases l with
  | zero => exact scopedStep_eq_on_cell scopes ν i (samples i 0) hl hx
  | succ l =>
      change (Dyadic.step (samples i (l + 1)) (l + 1)).toFun _ -
        (Dyadic.step (samples i l) l).toFun _ = _
      rw [scopedStep_eq_on_cell scopes ν i (samples i (l + 1)) hl hx,
        scopedStep_eq_on_cell scopes ν i (samples i l) (Nat.le_trans (Nat.le_succ l) hl) hx]
      rfl

/-- Exact cell formula for the actual stored, perturbed samples. -/
theorem integral_stored_product_eq_cell_sum {n t : ℕ}
    (scopes : Fin t → Finset (Fin n))
    (samples : (i : Fin t) → ℕ → LocalFunc (scopes i).card) (ν : Fin t → ℕ) :
    Integral.cubeIntegral (fun x => ∏ i, Quadrature.storedScopedIncrement scopes samples i (ν i) x) =
      ∑ z : Grid (commonLevels scopes ν), (weightQ (commonLevels scopes ν) : ℝ) *
        ∏ i, Quadrature.storedScopedIncrement scopes samples i (ν i) (corner z) := by
  apply cubeIntegral_eq_cell_sum
  intro z x hx
  exact Finset.prod_congr rfl fun i _ => storedScopedIncrement_eq_on_cell scopes samples ν i le_rfl hx

lemma cellIndex_lower_self (l : ℕ) (x : ℝ) :
    Dyadic.cellIndex l (Dyadic.lower l x) = Dyadic.cellIndex l x := by
  have h := lower_coarsen (le_refl l) x
  change (Dyadic.cellIndex l (Dyadic.lower l x) : ℝ) / (2 : ℝ) ^ l =
    (Dyadic.cellIndex l x : ℝ) / (2 : ℝ) ^ l at h
  have hm := congrArg (fun y : ℝ => y * (2 : ℝ) ^ l) h
  simp only [div_mul_cancel₀ _ (by positivity : (2 : ℝ) ^ l ≠ 0)] at hm
  exact_mod_cast hm

lemma cellIndex_corner {n : ℕ} {m : Fin n → ℕ} (z : Grid m) (v : Fin n) :
    Dyadic.cellIndex (m v) (corner z v) = (z v).val :=
  (mem_cell.mp (corner_mem_cell z) v).2

lemma cellIndex_corner_coarsen {n : ℕ} {m : Fin n → ℕ} (z : Grid m) (v : Fin n)
    {l : ℕ} (hl : l ≤ m v) :
    Dyadic.cellIndex l (corner z v) = (z v).val / 2 ^ (m v - l) := by
  rw [← cellIndex_coarsen hl, cellIndex_corner]

end Paper08.CellGrid
