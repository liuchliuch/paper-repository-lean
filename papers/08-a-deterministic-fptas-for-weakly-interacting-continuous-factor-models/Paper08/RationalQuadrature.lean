import Paper08.CellGrid
import Paper08.Oracle
import Paper08.TupleCount

/-! # Executable rational total-level quadrature
Only the correctness proofs use real numbers. The rule itself uses finite tuple
and cell enumerations, integer division, dyadic rational coordinates, and rational
arithmetic, with oracle calls passed as ordinary deterministic functions. -/
open scoped BigOperators
namespace Paper08.RationalQuadrature
open CellGrid

abbrev SampleTable {n t : ℕ} (scopes : Fin t → Finset (Fin n)) :=
  (i : Fin t) → ℕ → (Fin (scopes i).card → ℕ) → ℚ

/-- Select a coarse local corner from an anisotropic fine-grid cell by integer division. -/
def localIndex {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (ν : Fin t → ℕ)
    (z : Grid (commonLevels scopes ν)) (i : Fin t) (l : ℕ) : Fin (scopes i).card → ℕ :=
  fun j => (z ((scopes i).orderEmbOfFin rfl j)).val /
    2 ^ (commonLevels scopes ν ((scopes i).orderEmbOfFin rfl j) - l)

def stepQ {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (table : SampleTable scopes)
    (ν : Fin t → ℕ) (z : Grid (commonLevels scopes ν)) (i : Fin t) (l : ℕ) : ℚ :=
  table i l (localIndex scopes ν z i l)

/-- The two samples used for an increment are evaluated at their own coarse corners. -/
def incrementQ {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (table : SampleTable scopes)
    (ν : Fin t → ℕ) (z : Grid (commonLevels scopes ν)) (i : Fin t) : ℚ :=
  match ν i with
  | 0 => stepQ scopes table ν z i 0
  | l + 1 => stepQ scopes table ν z i (l + 1) - stepQ scopes table ν z i l

/-- The actual finite rational rule: no real integral occurs in its definition. -/
def ruleQ {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (table : SampleTable scopes)
    (J : ℕ) : ℚ :=
  ∑ ν ∈ TupleCount.boundedTuples t J,
    ∑ z : Grid (commonLevels scopes ν), weightQ (commonLevels scopes ν) *
      ∏ i, incrementQ scopes table ν z i

/-- A natural-index tuple is queried at its actual dyadic rational corner. -/
def queryPoint {k : ℕ} (l : ℕ) (p : Fin k → ℕ) : Fin k → ℚ :=
  fun j => (p j : ℚ) / (2 : ℚ) ^ l

/-- Primitive local samples are computed by the rational log/power/rounding algorithm. -/
def primitiveTable {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (query : (i : Fin t) → (Fin (scopes i).card → ℚ) → ℕ → ℚ)
    (α : Fin t → ℕ) (P : ℕ) : SampleTable scopes :=
  fun i l p => Oracle.primitiveSampleQ P (α i) (query i (queryPoint l p) P)

/-- The complete local integration program with the rationally chosen global parameters. -/
def primitiveRuleQ {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (query : (i : Fin t) → (Fin (scopes i).card → ℚ) → ℕ → ℚ)
    (α : Fin t → ℕ) (s C : ℕ) (τ : ℚ) : ℚ :=
  let J := Oracle.totalLevelChoice s C τ
  let ζ := Oracle.primitiveSampleTol s J C τ
  let P := Oracle.samplePrecision s ζ
  ruleQ scopes (primitiveTable scopes query α P) J

/-- The number of value queries in the explicit uncached nested loops. -/
def queryCalls {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (J : ℕ) : ℕ :=
  ∑ ν ∈ TupleCount.boundedTuples t J,
    ∑ _z : Grid (commonLevels scopes ν), ∑ i : Fin t, if ν i = 0 then 1 else 2


noncomputable section
open MeasureTheory

/-- The real step-table interpretation used only to prove correctness of the program. -/
def tableLocal {n t : ℕ} {scopes : Fin t → Finset (Fin n)} (table : SampleTable scopes)
    (i : Fin t) (l : ℕ) : LocalFunc (scopes i).card :=
  ⟨fun x => (table i l (fun j => Dyadic.cellIndex l (x j)) : ℝ)⟩

lemma stepQ_cast {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (table : SampleTable scopes)
    (ν : Fin t → ℕ) (z : Grid (commonLevels scopes ν)) (i : Fin t) {l : ℕ} (hl : l ≤ ν i) :
    (stepQ scopes table ν z i l : ℝ) =
      Quadrature.storedScopedStep scopes (tableLocal table) i l (corner z) := by
  change (table i l (localIndex scopes ν z i l) : ℝ) =
    (table i l (fun j => Dyadic.cellIndex l
      (Dyadic.lower l (corner z ((scopes i).orderEmbOfFin rfl j)))) : ℝ)
  apply congrArg (fun p => (table i l p : ℝ))
  funext j
  change _ = Dyadic.cellIndex l (Dyadic.lower l (corner z ((scopes i).orderEmbOfFin rfl j)))
  rw [cellIndex_lower_self, cellIndex_corner_coarsen z _
    (hl.trans (level_le_common scopes ν i (Finset.orderEmbOfFin_mem (scopes i) rfl j)))]
  rfl

lemma incrementQ_cast {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (table : SampleTable scopes)
    (ν : Fin t → ℕ) (z : Grid (commonLevels scopes ν)) (i : Fin t) :
    (incrementQ scopes table ν z i : ℝ) =
      Quadrature.storedScopedIncrement scopes (tableLocal table) i (ν i) (corner z) := by
  unfold incrementQ Quadrature.storedScopedIncrement
  generalize h : ν i = l
  cases l with
  | zero => exact stepQ_cast scopes table ν z i (by omega)
  | succ l =>
      rw [Rat.cast_sub]
      change _ = Quadrature.storedScopedStep scopes (tableLocal table) i (l + 1) (corner z) -
        Quadrature.storedScopedStep scopes (tableLocal table) i l (corner z)
      rw [stepQ_cast scopes table ν z i (by omega), stepQ_cast scopes table ν z i (by omega)]

/-- The executable rational result equals the actual stored-sample integral rule. -/
theorem ruleQ_cast {n t : ℕ} (scopes : Fin t → Finset (Fin n)) (table : SampleTable scopes)
    (J : ℕ) :
    (ruleQ scopes table J : ℝ) =
      Quadrature.totalLevelRule (Quadrature.storedScopedIncrement scopes (tableLocal table)) J := by
  unfold ruleQ Quadrature.totalLevelRule
  rw [TupleCount.boundedTuples_eq_totalLevels]
  push_cast
  apply Finset.sum_congr rfl
  intro ν _
  rw [integral_stored_product_eq_cell_sum]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact incrementQ_cast scopes table ν z i

lemma queryPoint_mem {k l : ℕ} {p : Fin k → ℕ} (hp : ∀ j, p j < 2 ^ l) :
    ∀ j, 0 ≤ queryPoint l p j ∧ queryPoint l p j ≤ 1 := by
  intro j
  refine ⟨by unfold queryPoint; positivity, ?_⟩
  rw [queryPoint, div_le_one (by positivity)]
  exact_mod_cast (hp j).le

lemma queryPoint_cellIndex_cast {k l : ℕ} (y : Fin k → ℝ) :
    (fun j => (queryPoint l (fun j => Dyadic.cellIndex l (y j)) j : ℝ)) = Dyadic.corner l y := by
  funext j
  simp [queryPoint, Dyadic.corner, Dyadic.lower]

lemma tableLocal_at_corner {n t : ℕ} {scopes : Fin t → Finset (Fin n)}
    (table : SampleTable scopes) (i : Fin t) (l : ℕ) (y : Fin (scopes i).card → ℝ) :
    (tableLocal table i l).toFun (Dyadic.corner l y) =
      (table i l (fun j => Dyadic.cellIndex l (y j)) : ℝ) := by
  unfold tableLocal
  simp only [Dyadic.corner, cellIndex_lower_self]

/-- Actual logarithmic power factors in a primitive moment. -/
def logPower {k : ℕ} (Ψ : LocalFunc k) (a : ℕ) : LocalFunc k :=
  ⟨fun x => Real.log (Ψ.toFun x) ^ a⟩

lemma primitiveTable_error {n t s : ℕ} (scopes : Fin t → Finset (Fin n))
    (Ψ : (i : Fin t) → LocalFunc (scopes i).card)
    (O : (i : Fin t) → Oracle.Oracle (scopes i).card (Ψ i).toFun)
    (α : Fin t → ℕ) (hα : ∀ i, 1 ≤ α i) (hαs : ∀ i, α i ≤ s)
    (hΨ : ∀ i x, x ∈ Integral.cube (scopes i).card → 1 ≤ (Ψ i).toFun x ∧ (Ψ i).toFun x ≤ 2)
    (ζ : ℚ) (hζ : 0 < ζ) (i : Fin t) (l : ℕ) (y : Fin (scopes i).card → ℝ)
    (hy : y ∈ Integral.cube (scopes i).card) :
    let P := Oracle.samplePrecision s ζ
    |(tableLocal (primitiveTable scopes (fun i => (O i).query) α P) i l).toFun (Dyadic.corner l y) -
      (logPower (Ψ i) (α i)).toFun (Dyadic.corner l y)| ≤ (ζ : ℝ) := by
  dsimp only
  rw [tableLocal_at_corner]
  let p := fun j => Dyadic.cellIndex l (y j)
  have hpoint := queryPoint_cellIndex_cast (l := l) y
  have hr := hΨ i (Dyadic.corner l y) (Dyadic.corner_mem (level := l) hy)
  have he := Oracle.primitiveSampleQ_chosen_precision_error (O i) (queryPoint l p)
    (queryPoint_mem fun j => Dyadic.cellIndex_lt l (y j)) (α i) (hα i) (hαs i) ζ hζ
    (by simpa only [p, hpoint] using hr.1) (by simpa only [p, hpoint] using hr.2)
  simpa only [primitiveTable, logPower, p, hpoint] using he

lemma logPower_bound {k : ℕ} (Ψ : LocalFunc k) (a : ℕ) {q : ℝ} (hq : 0 ≤ q)
    (hΨ : ∀ x, x ∈ Integral.cube k → 1 ≤ Ψ.toFun x ∧ Ψ.toFun x ≤ Real.exp q) :
    (logPower Ψ a).BoundBy (q ^ a) := by
  intro x hx
  have hr := Oracle.log_factor_range (hΨ x (Integral.mem_cube.mpr hx)).1
    (hΨ x (Integral.mem_cube.mpr hx)).2
  change |Real.log (Ψ.toFun x) ^ a| ≤ _
  rw [abs_of_nonneg (pow_nonneg hr.1 a)]
  exact pow_le_pow_left₀ hr.1 hr.2 a

lemma logPower_lip {k : ℕ} (Ψ : LocalFunc k) (a : ℕ) {q K : ℝ} (hq : 0 ≤ q) (hK : 0 ≤ K)
    (hΨ : ∀ x, x ∈ Integral.cube k → 1 ≤ Ψ.toFun x ∧ Ψ.toFun x ≤ Real.exp q)
    (hLip : Ψ.LipLe K) :
    (logPower Ψ a).LipLe ((a : ℝ) * K * q ^ (a - 1)) := by
  intro x y hx hy
  have hrx := hΨ x (Integral.mem_cube.mpr hx)
  have hry := hΨ y (Integral.mem_cube.mpr hy)
  exact (Oracle.log_power_bounds a hq hrx.1 hrx.2 hry.1 hry.2
    (norm_nonneg _) hK (hLip x y hx hy)).2

lemma logPowerBudget_eq (r a : ℕ) (q K : ℝ) :
    Dyadic.budget r (q ^ a) ((a : ℝ) * K * q ^ (a - 1)) =
      Oracle.primitiveFactorBudget q (3 * Real.sqrt r * K) a := by
  unfold Dyadic.budget Oracle.primitiveFactorBudget
  congr 2
  ring

/-- Lemma 3.3's actual rational integration algorithm, with the effective choices
(3.11)--(3.13), approximates the original primitive Lebesgue moment. -/
theorem primitiveRuleQ_error {n t r s C : ℕ}
    (scopes : Fin t → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (Ψ : (i : Fin t) → LocalFunc (scopes i).card)
    (O : (i : Fin t) → Oracle.Oracle (scopes i).card (Ψ i).toFun)
    (α : Fin t → ℕ) (hα : ∀ i, 1 ≤ α i) (hαsum : ∑ i, α i ≤ s) (hs : 1 ≤ s)
    {q K : ℝ} (hq : 0 ≤ q) (hqthird : q < 1 / 3) (hK : 0 ≤ K)
    (hΨ : ∀ i x, x ∈ Integral.cube (scopes i).card →
      1 ≤ (Ψ i).toFun x ∧ (Ψ i).toFun x ≤ Real.exp q)
    (hLip : ∀ i, (Ψ i).LipLe K)
    (hC : 2 ≤ C) (hqC : 2 * q ≤ (C : ℝ)) (hKC : 6 * Real.sqrt r * K ≤ (C : ℝ))
    (τ : ℚ) (hτ : 0 < τ) :
    |(primitiveRuleQ scopes (fun i => (O i).query) α s C τ : ℝ) -
      Integral.cubeIntegral (fun x => ∏ i,
        Real.log ((Ψ i).toFun (Integral.restrictTo (scopes i) x)) ^ α i)| ≤ (τ : ℝ) := by
  let J := Oracle.totalLevelChoice s C τ
  let ζ := Oracle.primitiveSampleTol s J C τ
  let P := Oracle.samplePrecision s ζ
  let f := fun i => logPower (Ψ i) (α i)
  let A := fun i => q ^ α i
  let Ki := fun i => (α i : ℝ) * K * q ^ (α i - 1)
  let B := fun i => Dyadic.budget r (A i) (Ki i)
  let samples := tableLocal (primitiveTable scopes (fun i => (O i).query) α P)
  have hC1 : 1 ≤ C := by omega
  have ht : t ≤ s := by
    calc
      t = ∑ _i : Fin t, 1 := by simp
      _ ≤ ∑ i, α i := Finset.sum_le_sum fun i _ => hα i
      _ ≤ s := hαsum
  have hαs : ∀ i, α i ≤ s := fun i =>
    (Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) (Finset.mem_univ i)).trans hαsum
  have hζ : 0 < ζ := Oracle.primitiveSampleTol_pos hs hC1 hτ
  have hA : ∀ i, (f i).BoundBy (A i) := fun i => logPower_bound (Ψ i) (α i) hq (hΨ i)
  have hKi : ∀ i, 0 ≤ Ki i := fun i => by dsimp [Ki]; positivity
  have hf : ∀ i, (f i).LipLe (Ki i) := fun i => logPower_lip (Ψ i) (α i) hq hK (hΨ i) (hLip i)
  have hBprod : (∏ i, B i) ≤ (C : ℝ) ^ s := by
    simp only [B, A, Ki, logPowerBudget_eq]
    exact Oracle.primitiveFactorBudget_prod_le α hq (by positivity) (by exact_mod_cast hC)
      hqC (by nlinarith) hαsum
  have hprecision : ∀ i, 2 * (J + 1 : ℝ) * (ζ : ℝ) ≤ B i := by
    intro i
    have hh : 2 * (J + 1 : ℝ) * (ζ : ℝ) ≤ 1 := by
      exact_mod_cast Oracle.primitiveSampleTol_hyp s J C τ
    exact hh.trans (Dyadic.one_le_budget r _ _)
  have hsample : ∀ i l, l ≤ J → ∀ y, y ∈ Integral.cube (scopes i).card →
      |(samples i l).toFun (Dyadic.corner l y) - (f i).toFun (Dyadic.corner l y)| ≤ (ζ : ℝ) := by
    intro i l _ y hy
    apply primitiveTable_error scopes Ψ O α hα hαs _ ζ hζ i l y hy
    intro i x hx
    exact ⟨(hΨ i x hx).1, (hΨ i x hx).2.trans (Oracle.exp_lt_two_of_q_lt_third hqthird).le⟩
  have hpert := (Quadrature.dyadic_stored_sample_perturbation (J := J) scopes hscopes f A Ki
    hKi hA hf samples (fun _ => (ζ : ℝ)) (ζ : ℝ) (fun _ => (by change (0 : ℝ) ≤ (ζ : ℝ); exact_mod_cast hζ.le))
    (fun _ => le_rfl) hprecision hsample).2
  have htail := Quadrature.dyadic_quadrature_error (J := J) scopes hscopes f A Ki hKi hA hf
  have hpert_budget : 2 * (t : ℝ) * (J + 1 : ℝ) * 3 ^ (t - 1) * (∏ i, B i) * (ζ : ℝ) ≤ (τ : ℝ) / 2 := by
    calc
      _ ≤ 2 * (t : ℝ) * (J + 1 : ℝ) * 3 ^ (t - 1) * (C : ℝ) ^ s * (ζ : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (by exact_mod_cast hζ.le)
        exact mul_le_mul_of_nonneg_left hBprod (by positivity)
      _ ≤ _ := by exact_mod_cast Oracle.primitiveSampleTol_error hs hC1 hτ ht
  have htail_budget : (∏ i, B i) * C0 ^ t * (2 : ℝ) ^ (-(J : ℝ) / 2) ≤ (τ : ℝ) / 2 := by
    calc
      _ ≤ (C : ℝ) ^ s * C0 ^ t * (2 : ℝ) ^ (-(J : ℝ) / 2) := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBprod (pow_nonneg C0_pos.le t)) (by positivity)
      _ ≤ _ := Oracle.totalLevelChoice_error s C t τ hτ hC1 ht
  change |(ruleQ scopes (primitiveTable scopes (fun i => (O i).query) α P) J : ℝ) - _| ≤ _
  rw [ruleQ_cast]
  calc
    _ ≤ |Quadrature.totalLevelRule (Quadrature.storedScopedIncrement scopes samples) J -
          Quadrature.totalLevelRule (Quadrature.scopedIncrement scopes f) J| +
        |Quadrature.totalLevelRule (Quadrature.scopedIncrement scopes f) J -
          Integral.cubeIntegral (fun x => ∏ i, Integral.pullback (scopes i) (f i) x)| :=
      abs_sub_le _ _ _
    _ ≤ (τ : ℝ) / 2 + (τ : ℝ) / 2 := by
      apply add_le_add (hpert.trans hpert_budget)
      rw [abs_sub_comm]
      exact htail.trans htail_budget
    _ = _ := by ring

/-- Each query made on a retained cell is in the cube and has at most J dyadic bits. -/
theorem local_query_valid {n t J : ℕ} (scopes : Fin t → Finset (Fin n))
    {ν : Fin t → ℕ} (hν : ν ∈ TupleCount.boundedTuples t J)
    (z : Grid (commonLevels scopes ν)) (i : Fin t) {l : ℕ} (hl : l ≤ ν i) :
    ∀ j, 0 ≤ queryPoint l (localIndex scopes ν z i l) j ∧
      queryPoint l (localIndex scopes ν z i l) j ≤ 1 ∧
      Oracle.IsDyadicAt J (queryPoint l (localIndex scopes ν z i l) j) := by
  have hp : ∀ j, localIndex scopes ν z i l j < 2 ^ l := by
    intro j
    change (z ((scopes i).orderEmbOfFin rfl j)).val / 2 ^ (_ - l) < _
    rw [← cellIndex_corner_coarsen z _
      (hl.trans (level_le_common scopes ν i (Finset.orderEmbOfFin_mem (scopes i) rfl j)))]
    exact Dyadic.cellIndex_lt _ _
  have hlJ : l ≤ J := hl.trans
    ((Finset.single_le_sum (fun j _ => Nat.zero_le (ν j)) (Finset.mem_univ i)).trans
      (TupleCount.mem_boundedTuples.mp hν))
  intro j
  refine ⟨(queryPoint_mem hp j).1, (queryPoint_mem hp j).2, ?_⟩
  apply Oracle.IsDyadicAt.mono (P := l) _ hlJ
  exact ⟨(localIndex scopes ν z i l j : ℤ), by simp [queryPoint]⟩

/-- The explicit program's value-query count obeys the first bound of (3.2). -/
theorem queryCalls_bound {n t r J : ℕ} (scopes : Fin t → Finset (Fin n))
    (hscopes : ∀ i, (scopes i).card ≤ r) :
    queryCalls scopes J ≤ 2 * t * (J + t).choose t * 2 ^ (r * J) := by
  unfold queryCalls
  calc
    _ ≤ ∑ _ν ∈ TupleCount.boundedTuples t J, 2 * t * 2 ^ (r * J) := by
      apply Finset.sum_le_sum
      intro ν hν
      have hcost : (∑ i : Fin t, if ν i = 0 then 1 else 2) ≤ 2 * t := by
        calc
          _ ≤ ∑ _i : Fin t, 2 := Finset.sum_le_sum fun i _ => by split_ifs <;> omega
          _ = _ := by simp; omega
      have hc := common_grid_card_le scopes hscopes ν (TupleCount.mem_boundedTuples.mp hν)
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc
        _ ≤ 2 ^ (r * J) * (2 * t) := Nat.mul_le_mul hc hcost
        _ = _ := by ring
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, TupleCount.card_boundedTuples]; norm_cast; ring

/-- The elementary exponential version of the query bound in (3.2). -/
theorem queryCalls_bound_pow {n t r J : ℕ} (scopes : Fin t → Finset (Fin n))
    (hscopes : ∀ i, (scopes i).card ≤ r) :
    queryCalls scopes J ≤ 2 * t * 2 ^ ((r + 1) * J + t) := by
  calc
    _ ≤ 2 * t * (J + t).choose t * 2 ^ (r * J) := queryCalls_bound scopes hscopes
    _ ≤ 2 * t * 2 ^ (J + t) * 2 ^ (r * J) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.choose_le_two_pow _ _))
    _ = 2 * t * (2 ^ (J + t) * 2 ^ (r * J)) := by ring
    _ = _ := by rw [← pow_add]; congr 2; ring

lemma incrementQ_isDyadicAt {n t P : ℕ} (scopes : Fin t → Finset (Fin n)) (table : SampleTable scopes)
    (htable : ∀ i l p, Oracle.IsDyadicAt P (table i l p))
    (ν : Fin t → ℕ) (z : Grid (commonLevels scopes ν)) (i : Fin t) :
    Oracle.IsDyadicAt P (incrementQ scopes table ν z i) := by
  unfold incrementQ
  split
  · exact htable _ _ _
  · exact (htable _ _ _).sub (htable _ _ _)

/-- The actual rational cell sum has a common dyadic denominator. -/
theorem ruleQ_isDyadicAt {n t r J P : ℕ} (scopes : Fin t → Finset (Fin n))
    (hscopes : ∀ i, (scopes i).card ≤ r) (table : SampleTable scopes)
    (htable : ∀ i l p, Oracle.IsDyadicAt P (table i l p)) :
    Oracle.IsDyadicAt (P * t + r * J) (ruleQ scopes table J) := by
  unfold ruleQ
  apply Oracle.IsDyadicAt.sum
  intro ν hν
  apply Oracle.IsDyadicAt.sum
  intro z _
  have hp := Oracle.IsDyadicAt.prod Finset.univ (fun i => incrementQ scopes table ν z i) P
    (fun i _ => incrementQ_isDyadicAt scopes table htable ν z i)
  simp only [Finset.card_univ, Fintype.card_fin] at hp
  have hlevel : ∑ v, commonLevels scopes ν v ≤ r * J :=
    (sum_commonLevels_le scopes hscopes ν).trans
      (Nat.mul_le_mul_left r (TupleCount.mem_boundedTuples.mp hν))
  have hd := (hp.div_two_pow (Q := ∑ v, commonLevels scopes ν v)).mono
    (Nat.add_le_add_left hlevel (P * t))
  simpa only [weightQ, div_eq_mul_inv, mul_comm] using hd

/-- The primitive program's reduced denominator divides `2^(P s+r J)` of Section 3.2. -/
theorem primitiveRuleQ_den_dvd {n t r s C : ℕ} (scopes : Fin t → Finset (Fin n))
    (hscopes : ∀ i, (scopes i).card ≤ r)
    (query : (i : Fin t) → (Fin (scopes i).card → ℚ) → ℕ → ℚ)
    (α : Fin t → ℕ) (ht : t ≤ s) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    (primitiveRuleQ scopes query α s C τ).den ∣ 2 ^ (P * s + r * J) := by
  dsimp only
  unfold primitiveRuleQ
  apply Oracle.IsDyadicAt.den_dvd
  apply Oracle.IsDyadicAt.mono (P := _ * t + r * _)
  · apply ruleQ_isDyadicAt scopes hscopes
    intro i l p
    exact Oracle.primitiveSampleQ_isDyadicAt _ _ _
  · exact Nat.add_le_add_right (Nat.mul_le_mul_left _ ht) _

end
end Paper08.RationalQuadrature
