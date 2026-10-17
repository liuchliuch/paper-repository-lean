import Paper08.RationalQuadrature
import Paper08.Surrogate
import Paper08.ZeroFree
import Paper08.MultiMoments

/-! # Actual finite-query uniform dyadic surrogates (Proposition B.1 converse)
A certified rational bound T≥K√r determines the mesh using integer binary logs.
The queried values are rounded over ℚ and projected onto [1,∞). Uniform error
and partition accuracy are proved from the original range/Lipschitz/oracle promises.
-/
open scoped BigOperators
namespace Paper08.GridSurrogate
open CellGrid RationalQuadrature

/-- Uniform grid level selected by rational arithmetic. -/
def meshLevel (M : ℕ) (T ε : ℚ) : ℕ := Oracle.samplePrecision 0 (ε / (2 * T * M))

/-- Oracle and rounding precision selected by rational arithmetic. -/
def valueBits (M : ℕ) (ε : ℚ) : ℕ := Oracle.samplePrecision 0 (ε / (4 * M))

/-- The actual rounded rational sample, with the mandatory lower range bound. -/
def sampleQ (b : ℕ) (answer : ℚ) : ℚ := max 1 (Oracle.dyadQ b answer)

/-- A finite table of actual queries, one per local dyadic corner. -/
def gridTable {k : ℕ} (query : (Fin k → ℚ) → ℕ → ℚ) (l b : ℕ)
    (z : Grid (fun _ : Fin k => l)) : ℚ := sampleQ b (query (cornerQ z) b)

/-- A computable, recursive enumeration of all uniform-grid corners. -/
def uniformCorners (k l : ℕ) : List (Fin k → Fin (2 ^ l)) :=
  match k with
  | 0 => [Fin.elim0]
  | k + 1 => (List.finRange (2 ^ l)).flatMap fun z =>
      (uniformCorners k l).map fun x => Fin.cons z x

/-- The finite query list is materialized without real arithmetic or choice. -/
def queryList {k : ℕ} (query : (Fin k → ℚ) → ℕ → ℚ) (l b : ℕ) :
    List (Grid (fun _ : Fin k => l) × ℚ) :=
  (uniformCorners k l).map fun z => (z, gridTable query l b z)

/-- The number of value queries for all local tables. -/
def queryCount {n M : ℕ} (scopes : Fin M → Finset (Fin n)) (l : ℕ) : ℕ :=
  ∑ i, Fintype.card (Grid (fun _ : Fin (scopes i).card => l))

/-- A local surrogate integral is computed by its finite rational grid average. -/
def localAverageQ {k : ℕ} (query : (Fin k → ℚ) → ℕ → ℚ) (l b : ℕ) : ℚ :=
  ∑ z : Grid (fun _ : Fin k => l), weightQ (fun _ : Fin k => l) * gridTable query l b z

/-- For disjoint scopes, multiply the local rational grid averages. -/
def disjointRuleQ {n M : ℕ} (scopes : Fin M → Finset (Fin n))
    (query : (i : Fin M) → (Fin (scopes i).card → ℚ) → ℕ → ℚ)
    (T ε : ℚ) : ℚ :=
  ∏ i, localAverageQ (query i) (meshLevel M T ε) (valueBits M ε)

noncomputable section
open MeasureTheory

/-- The actual finite table defines a rational-valued step function over the whole cube. -/
def surrogate {k : ℕ} (query : (Fin k → ℚ) → ℕ → ℚ) (l b : ℕ) : LocalFunc k :=
  ⟨fun x => (gridTable query l b (fun j =>
    ⟨Dyadic.cellIndex l (x j), Dyadic.cellIndex_lt l (x j)⟩) : ℝ)⟩

lemma sampleQ_ge_one (b : ℕ) (answer : ℚ) : 1 ≤ sampleQ b answer := le_max_left _ _

lemma sampleQ_isDyadicAt (b : ℕ) (answer : ℚ) : Oracle.IsDyadicAt b (sampleQ b answer) := by
  unfold sampleQ
  by_cases h : Oracle.dyadQ b answer ≤ 1
  · rw [max_eq_left h]
    exact Oracle.isDyadicAt_one b
  · rw [max_eq_right (le_of_not_ge h)]
    exact Oracle.dyadQ_isDyadicAt b answer

lemma abs_project_ge_one {x z : ℝ} (hz : 1 ≤ z) : |max 1 x - z| ≤ |x - z| := by
  by_cases hx : x ≤ 1
  · rw [max_eq_left hx, abs_of_nonpos (by linarith : (1 : ℝ) - z ≤ 0),
      abs_of_nonpos (by linarith : x - z ≤ 0)]
    linarith
  · rw [max_eq_right (le_of_not_ge hx)]

lemma sampleQ_error {b : ℕ} {answer : ℚ} {z : ℝ} (hz : 1 ≤ z)
    (herr : |(answer : ℝ) - z| ≤ ((2 : ℝ) ^ b)⁻¹) :
    |(sampleQ b answer : ℝ) - z| ≤ 2 * ((2 : ℝ) ^ b)⁻¹ := by
  have hr := Oracle.abs_dyadQ_sub_le b answer
  have hpow : (2 : ℝ) ^ (-(b : ℝ)) = ((2 : ℝ) ^ b)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  rw [hpow] at hr
  change |((max 1 (Oracle.dyadQ b answer) : ℚ) : ℝ) - z| ≤ _
  push_cast
  exact (abs_project_ge_one hz).trans
    ((abs_sub_le (Oracle.dyadQ b answer : ℝ) answer z).trans (by linarith))

lemma surrogate_ge_one {k : ℕ} (query : (Fin k → ℚ) → ℕ → ℚ) (l b : ℕ) (x : Fin k → ℝ) :
    1 ≤ (surrogate query l b).toFun x := by
  change (1 : ℝ) ≤ (sampleQ b (query _ b) : ℝ)
  exact_mod_cast sampleQ_ge_one b (query _ b)

lemma measurable_surrogate {k : ℕ} (query : (Fin k → ℚ) → ℕ → ℚ) (l b : ℕ) :
    Measurable (surrogate query l b).toFun := by
  let ind : (Fin k → ℝ) → (Fin k → ℕ) := fun x j => Dyadic.cellIndex l (x j)
  have hm : Measurable ind :=
    measurable_pi_lambda _ fun j => (Dyadic.measurable_cellIndex l).comp (measurable_pi_apply j)
  have hn : Measurable (fun p : Fin k → ℕ => (sampleQ b (query (queryPoint l p) b) : ℝ)) :=
    measurable_of_countable _
  exact hn.comp hm

lemma surrogate_corner_cast {k : ℕ} (l : ℕ) (x : Fin k → ℝ) :
    (fun j => (cornerQ (fun i => ⟨Dyadic.cellIndex l (x i), Dyadic.cellIndex_lt l (x i)⟩) j : ℝ)) =
      Dyadic.corner l x := by
  funext j
  simp [cornerQ, Dyadic.corner, Dyadic.lower]

lemma cornerQ_mem {k : ℕ} {l : ℕ} (z : Grid (fun _ : Fin k => l)) :
    ∀ j, 0 ≤ cornerQ z j ∧ cornerQ z j ≤ 1 := by
  intro j
  refine ⟨by unfold cornerQ; positivity, ?_⟩
  rw [cornerQ, div_le_one (by positivity)]
  exact_mod_cast (z j).isLt.le

/-- Uniform error derived from actual lower-corner queries and oracle accuracy. -/
lemma surrogate_error {k r l b : ℕ} (hkr : k ≤ r) (Ψ : LocalFunc k)
    (O : Oracle.Oracle k Ψ.toFun) {K : ℝ} (hK : 0 ≤ K) (hLip : Ψ.LipLe K)
    (hΨ : ∀ x, x ∈ Integral.cube k → 1 ≤ Ψ.toFun x) (hb : 1 ≤ b)
    {x : Fin k → ℝ} (hx : x ∈ Integral.cube k) :
    |(surrogate O.query l b).toFun x - Ψ.toFun x| ≤
      2 * ((2 : ℝ) ^ b)⁻¹ + Real.sqrt r * K * ((2 : ℝ) ^ l)⁻¹ := by
  let z : Grid (fun _ : Fin k => l) := fun j =>
    ⟨Dyadic.cellIndex l (x j), Dyadic.cellIndex_lt l (x j)⟩
  have hz : (fun j => (cornerQ z j : ℝ)) = Dyadic.corner l x := surrogate_corner_cast l x
  have horacle := O.query_approx (cornerQ z) b (cornerQ_mem z) hb
  rw [hz, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast] at horacle
  have hsample := sampleQ_error (hΨ _ (Dyadic.corner_mem (level := l) hx)) horacle
  have hstep := Dyadic.step_error hK hLip (level := l) hx
  have hkr' : Real.sqrt k * K * ((2 : ℝ) ^ l)⁻¹ ≤ Real.sqrt r * K * ((2 : ℝ) ^ l)⁻¹ := by gcongr
  change |(gridTable O.query l b z : ℝ) - Ψ.toFun x| ≤ _
  exact (abs_sub_le _ (Ψ.toFun (Dyadic.corner l x)) _).trans
    (add_le_add hsample (hstep.trans hkr'))

lemma meshLevel_sufficient {M : ℕ} {T ε : ℚ} (hM : 1 ≤ M) (hT : 0 < T) (hε : 0 < ε) :
    ((2 : ℚ) ^ meshLevel M T ε)⁻¹ ≤ ε / (2 * T * M) := by
  simpa [Oracle.sampleBudgetQ, meshLevel, one_div] using
    Oracle.samplePrecision_sufficient 0 (ε / (2 * T * M)) (by positivity)

lemma valueBits_sufficient {M : ℕ} {ε : ℚ} (hM : 1 ≤ M) (hε : 0 < ε) :
    2 * ((2 : ℚ) ^ valueBits M ε)⁻¹ ≤ ε / (2 * M) := by
  have hh := Oracle.samplePrecision_sufficient 0 (ε / (4 * M)) (by positivity)
  simp only [Oracle.sampleBudgetQ, Nat.mul_zero, Nat.zero_add, Nat.cast_one, one_div] at hh
  change 2 * _ ≤ _
  dsimp only [valueBits]
  calc
    _ ≤ 2 * (ε / (4 * M)) := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by ring

/-- The actual uniform surrogate meets the original ε/M local error budget. -/
theorem chosen_surrogate_error {k r M : ℕ} (hkr : k ≤ r) (Ψ : LocalFunc k)
    (O : Oracle.Oracle k Ψ.toFun) {K : ℝ} (hK : 0 ≤ K) (hLip : Ψ.LipLe K)
    (hΨ : ∀ x, x ∈ Integral.cube k → 1 ≤ Ψ.toFun x)
    {T ε : ℚ} (hM : 1 ≤ M) (hT : 0 < T) (hε : 0 < ε)
    (hTK : Real.sqrt r * K ≤ (T : ℝ)) {x : Fin k → ℝ} (hx : x ∈ Integral.cube k) :
    |(surrogate O.query (meshLevel M T ε) (valueBits M ε)).toFun x - Ψ.toFun x| ≤ (ε : ℝ) / M := by
  have he := surrogate_error (l := meshLevel M T ε) (b := valueBits M ε) hkr Ψ O hK hLip hΨ
    (Oracle.samplePrecision_pos 0 (ε / (4 * M))) hx
  have hb : 2 * ((2 : ℝ) ^ valueBits M ε)⁻¹ ≤ (ε : ℝ) / (2 * M) := by
    have hh := valueBits_sufficient hM hε
    have hc : ((2 * ((2 : ℚ) ^ valueBits M ε)⁻¹ : ℚ) : ℝ) ≤ ((ε / (2 * M) : ℚ) : ℝ) := by exact_mod_cast hh
    push_cast at hc
    exact hc
  have hl : ((2 : ℝ) ^ meshLevel M T ε)⁻¹ ≤ (ε : ℝ) / (2 * (T : ℝ) * M) := by
    have hh := meshLevel_sufficient hM hT hε
    have hc : ((((2 : ℚ) ^ meshLevel M T ε)⁻¹ : ℚ) : ℝ) ≤ ((ε / (2 * T * M) : ℚ) : ℝ) := by exact_mod_cast hh
    push_cast at hc
    exact hc
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hmesh : Real.sqrt r * K * ((2 : ℝ) ^ meshLevel M T ε)⁻¹ ≤ (ε : ℝ) / (2 * M) := by
    calc
      _ ≤ (T : ℝ) * ((2 : ℝ) ^ meshLevel M T ε)⁻¹ := mul_le_mul_of_nonneg_right hTK (by positivity)
      _ ≤ (T : ℝ) * ((ε : ℝ) / (2 * (T : ℝ) * M)) := mul_le_mul_of_nonneg_left hl hT0.le
      _ = _ := by field_simp
  exact (he.trans (add_le_add hb hmesh)).trans_eq (by ring)

/-- Uniform local surrogates give the actual partition-function guarantee,
including overlapping scopes; the uniform error is derived, not assumed. -/
theorem partition_surrogate_accurate {n M r : ℕ} (scopes : Fin M → Finset (Fin n))
    (hscopes : ∀ i, (scopes i).card ≤ r)
    (Ψ : (i : Fin M) → LocalFunc (scopes i).card)
    (O : (i : Fin M) → Oracle.Oracle (scopes i).card (Ψ i).toFun)
    {K U : ℝ} (hK : 0 ≤ K) (hLip : ∀ i, (Ψ i).LipLe K)
    (hΨ : ∀ i x, x ∈ Integral.cube (scopes i).card → 1 ≤ (Ψ i).toFun x ∧ (Ψ i).toFun x ≤ U)
    {T ε : ℚ} (hM : 1 ≤ M) (hT : 0 < T) (hε : 0 < ε)
    (hTK : Real.sqrt r * K ≤ (T : ℝ)) :
    FPTAS.Accurate
      (Integral.partitionFunction n (fun i => Integral.pullback (scopes i)
        (surrogate (O i).query (meshLevel M T ε) (valueBits M ε))))
      (Integral.partitionFunction n (fun i => Integral.pullback (scopes i) (Ψ i))) (ε : ℝ) := by
  let l := meshLevel M T ε
  let b := valueBits M ε
  let f := fun i => Integral.pullback (scopes i) (Ψ i)
  let g := fun i => Integral.pullback (scopes i) (surrogate (O i).query l b)
  have hf : IntegrableOn (fun x => ∏ i, f i x) (Integral.cube n) := by
    apply ContinuousOn.integrableOn_compact (ZeroFree.isCompact_cube n)
    apply continuousOn_finset_prod
    intro i _
    exact (ZeroFree.continuousOn_of_lip (Ψ i) (hLip i)).comp
      (ZeroFree.continuous_restrictTo (scopes i)).continuousOn
      (fun x hx => Integral.restrictTo_mem_cube (scopes i) hx)
  have he : ∀ x, x ∈ Integral.cube n → ∀ i, |g i x - f i x| ≤ (ε : ℝ) / M := by
    intro x hx i
    exact chosen_surrogate_error (hscopes i) (Ψ i) (O i) hK (hLip i) (fun x hx => (hΨ i x hx).1)
      hM hT hε hTK (Integral.restrictTo_mem_cube (scopes i) hx)
  have hg : IntegrableOn (fun x => ∏ i, g i x) (Integral.cube n) := by
    apply Quadrature.integrableOn_product_of_bounds g (fun _ => U + (ε : ℝ) / M)
    · intro i
      exact (measurable_surrogate (O i).query l b).comp (Integral.measurable_restrictTo (scopes i))
    · intro i x hx
      have hlo : 1 ≤ g i x := surrogate_ge_one _ _ _ _
      rw [abs_of_nonneg (by linarith : 0 ≤ g i x)]
      have hdiff := (le_abs_self (g i x - f i x)).trans (he x hx i)
      have hhi : f i x ≤ U := (hΨ i _ (Integral.restrictTo_mem_cube (scopes i) hx)).2
      linarith
  have hacc := Surrogate.partitionFunction_accurate f g hf hg
    (fun x hx i => (hΨ i _ (Integral.restrictTo_mem_cube (scopes i) hx)).1)
    (fun x hx i => surrogate_ge_one _ _ _ _) he
  have hm0 : (M : ℝ) ≠ 0 := by positivity
  simpa only [Fintype.card_fin, mul_div_cancel₀ _ hm0] using hacc

lemma mem_uniformCorners (k l : ℕ) (z : Fin k → Fin (2 ^ l)) : z ∈ uniformCorners k l := by
  induction k with
  | zero =>
      have hz : z = Fin.elim0 := by funext i; exact Fin.elim0 i
      simp [uniformCorners, hz]
  | succ k ih =>
      rw [uniformCorners, List.mem_flatMap]
      exact ⟨z 0, List.mem_finRange _, List.mem_map.mpr ⟨Fin.tail z, ih _, Fin.cons_self_tail z⟩⟩

lemma length_uniformCorners (k l : ℕ) : (uniformCorners k l).length = (2 ^ l) ^ k := by
  induction k with
  | zero => simp [uniformCorners]
  | succ k ih =>
      simp [uniformCorners, List.length_flatMap, ih, pow_succ, Nat.mul_comm]

lemma queryList_length {k : ℕ} (query : (Fin k → ℚ) → ℕ → ℚ) (l b : ℕ) :
    (queryList query l b).length = (2 ^ l) ^ k := by simp [queryList, length_uniformCorners]

lemma gridTable_mem_queryList {k : ℕ} (query : (Fin k → ℚ) → ℕ → ℚ) (l b : ℕ)
    (z : Grid (fun _ : Fin k => l)) : (z, gridTable query l b z) ∈ queryList query l b := by
  exact List.mem_map.mpr ⟨z, mem_uniformCorners k l z, rfl⟩

/-- Quantitative binary-log bound, including coarse meshes whose target exceeds one. -/
lemma pow_samplePrecision_le {ζ : ℚ} (hζ : 0 < ζ) :
    (2 : ℚ) ^ Oracle.samplePrecision 0 ζ ≤ 4 * max 1 (1 / ζ) := by
  let N := ⌈(1 : ℚ) / ζ⌉₊
  let c := Nat.clog 2 N
  change (2 : ℚ) ^ max 1 c ≤ _
  have hx : (0 : ℚ) ≤ 1 / ζ := by positivity
  have hceil : (N : ℚ) ≤ 1 / ζ + 1 := (Nat.ceil_lt_add_one hx).le
  have hmax1 : (1 : ℚ) ≤ max 1 (1 / ζ) := le_max_left _ _
  have hmaxx : 1 / ζ ≤ max 1 (1 / ζ) := le_max_right _ _
  by_cases hc : c ≤ 1
  · rw [max_eq_left hc]
    norm_num only [pow_one]
    linarith
  · have hN : 1 < N := by
      by_contra hn
      have hle : c ≤ 0 := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr (by simpa using le_of_not_gt hn)
      omega
    have hp : (2 : ℚ) ^ (c - 1) < N := by
      exact_mod_cast Nat.pow_pred_clog_lt_self (by decide : 1 < 2) hN
    rw [max_eq_right (le_of_not_ge hc), show c = (c - 1) + 1 by omega, pow_succ]
    nlinarith

/-- At most a constant times the optimal uniform-grid scale per coordinate. -/
lemma mesh_cells_per_coordinate {M : ℕ} {T ε : ℚ} (hM : 1 ≤ M) (hT : 0 < T) (hε : 0 < ε) :
    (2 : ℚ) ^ meshLevel M T ε ≤ 4 * max 1 (2 * T * M / ε) := by
  have he : (1 : ℚ) / (ε / (2 * T * M)) = 2 * T * M / ε := by field_simp
  simpa only [meshLevel, he] using pow_samplePrecision_le (ζ := ε / (2 * T * M)) (by positivity)

lemma queryCount_le {n M r : ℕ} (scopes : Fin M → Finset (Fin n))
    (hscopes : ∀ i, (scopes i).card ≤ r) (l : ℕ) :
    queryCount scopes l ≤ M * (2 ^ l) ^ r := by
  unfold queryCount
  calc
    _ ≤ ∑ _i : Fin M, (2 ^ l) ^ r := by
      apply Finset.sum_le_sum
      intro i _
      rw [card_grid]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, nsmul_eq_mul]
      rw [Nat.mul_comm (scopes i).card l, pow_mul]
      exact Nat.pow_le_pow_right (one_le_pow₀ (by omega : 1 ≤ (2 : ℕ))) (hscopes i)
    _ = _ := by simp

/-- The concrete converse query bound is M[4 max{1,2TM/ε}]^r.
For a fixed certified T comparable to K√r this is O_{r,K}(M^(r+1) ε^-r). -/
theorem chosen_queryCount_bound {n M r : ℕ} (scopes : Fin M → Finset (Fin n))
    (hscopes : ∀ i, (scopes i).card ≤ r) {T ε : ℚ} (hM : 1 ≤ M) (hT : 0 < T) (hε : 0 < ε) :
    (queryCount scopes (meshLevel M T ε) : ℚ) ≤
      M * (4 * max 1 (2 * T * M / ε)) ^ r := by
  have hcount : (queryCount scopes (meshLevel M T ε) : ℚ) ≤ M * ((2 : ℚ) ^ meshLevel M T ε) ^ r := by
    exact_mod_cast queryCount_le scopes hscopes (meshLevel M T ε)
  exact hcount.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (mesh_cells_per_coordinate hM hT hε) r) (Nat.cast_nonneg M))

/-- The chosen oracle precision has an explicit logarithmic upper bound. -/
theorem valueBits_log_bound {M : ℕ} {ε : ℚ} (hε : 0 < ε) :
    valueBits M ε ≤ 1 + Nat.clog 2 ⌈4 * (M : ℚ) / ε⌉₊ := by
  have he : (1 : ℚ) / (ε / (4 * M)) = 4 * M / ε := by field_simp
  simp only [valueBits, Oracle.samplePrecision, Nat.mul_zero, Nat.zero_add, Nat.cast_one, he]
  omega

/-- A quantitative form of b=O(log(M/ε)) for 0<ε≤1, M≥1. -/
theorem valueBits_pow_bound {M : ℕ} {ε : ℚ} (hM : 1 ≤ M) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (2 : ℚ) ^ valueBits M ε ≤ 16 * M / ε := by
  have he : (1 : ℚ) / (ε / (4 * M)) = 4 * M / ε := by field_simp
  have hlarge : (1 : ℚ) ≤ 4 * M / ε := by
    apply (le_div_iff₀ hε).mpr
    have hm : (1 : ℚ) ≤ M := by exact_mod_cast hM
    nlinarith
  have hp := pow_samplePrecision_le (ζ := ε / (4 * M)) (by positivity)
  rw [he, max_eq_right hlarge] at hp
  change (2 : ℚ) ^ Oracle.samplePrecision 0 (ε / (4 * M)) ≤ _
  exact hp.trans_eq (by ring)

/-- Query coordinates have the chosen logarithmic number of dyadic fractional bits. -/
lemma cornerQ_isDyadicAt {k l : ℕ} (z : Grid (fun _ : Fin k => l)) (j : Fin k) :
    Oracle.IsDyadicAt l (cornerQ z j) :=
  ⟨((z j).val : ℤ), by simp [cornerQ]⟩

lemma meshLevel_log_bound {M : ℕ} {T ε : ℚ} (hε : 0 < ε) :
    meshLevel M T ε ≤ 1 + Nat.clog 2 ⌈2 * T * M / ε⌉₊ := by
  have he : (1 : ℚ) / (ε / (2 * T * M)) = 2 * T * M / ε := by field_simp
  simp only [meshLevel, Oracle.samplePrecision, Nat.mul_zero, Nat.zero_add, Nat.cast_one, he]
  omega

/-- The converse's explicit polynomial query bound after pulling out fixed constants. -/
theorem chosen_queryCount_polynomial {n M r : ℕ} (scopes : Fin M → Finset (Fin n))
    (hscopes : ∀ i, (scopes i).card ≤ r) {T ε : ℚ}
    (hM : 1 ≤ M) (hT : 0 < T) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (queryCount scopes (meshLevel M T ε) : ℚ) ≤
      (4 * max 1 (2 * T)) ^ r * (M : ℚ) ^ (r + 1) / ε ^ r := by
  have hM0 : (0 : ℚ) < M := by exact_mod_cast hM
  have hscale : (1 : ℚ) ≤ M / ε := (le_div_iff₀ hε).mpr (by
    have hm : (1 : ℚ) ≤ M := by exact_mod_cast hM
    linarith)
  have hA1 : (1 : ℚ) ≤ max 1 (2 * T) := le_max_left _ _
  have hAT : 2 * T ≤ max 1 (2 * T) := le_max_right _ _
  have hm : max 1 (2 * T * M / ε) ≤ max 1 (2 * T) * (M / ε) := by
    apply max_le
    · nlinarith
    · have hh := mul_le_mul_of_nonneg_right hAT (show (0 : ℚ) ≤ M / ε by positivity)
      convert hh using 1 <;> ring
  calc
    _ ≤ M * (4 * max 1 (2 * T * M / ε)) ^ r := chosen_queryCount_bound scopes hscopes hM hT hε
    _ ≤ M * (4 * (max 1 (2 * T) * (M / ε))) ^ r := by gcongr
    _ = _ := by rw [show (4 : ℚ) * (max 1 (2 * T) * (M / ε)) = (4 * max 1 (2 * T)) * (M / ε) by ring,
        mul_pow, div_pow, pow_succ]; ring

/-- The query-count expression is exactly the length of the materialized local query lists. -/
lemma queryCount_eq_list_lengths {n M : ℕ} (scopes : Fin M → Finset (Fin n))
    (query : (i : Fin M) → (Fin (scopes i).card → ℚ) → ℕ → ℚ) (l b : ℕ) :
    queryCount scopes l = ∑ i, (queryList (query i) l b).length := by
  unfold queryCount
  apply Finset.sum_congr rfl
  intro i _
  rw [queryList_length, card_grid]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← pow_mul, Nat.mul_comm]

/-- A fixed certified rational mesh constant exists under exactly K>0 and r≥1. -/
lemma exists_mesh_constant {r : ℕ} {K : ℝ} (hr : 1 ≤ r) (hK : 0 < K) :
    ∃ T : ℚ, 0 < T ∧ Real.sqrt r * K ≤ (T : ℝ) ∧ (T : ℝ) ≤ 2 * Real.sqrt r * K := by
  have hp : 0 < Real.sqrt r * K := mul_pos (Real.sqrt_pos.2 (by exact_mod_cast hr)) hK
  obtain ⟨T, hlo, hhi⟩ := exists_rat_btwn (show Real.sqrt r * K < 2 * Real.sqrt r * K by nlinarith)
  exact ⟨T, by exact_mod_cast (hp.trans hlo), hlo.le, hhi.le⟩

/-- The fixed-parameter constant can be expressed using the original K and r. -/
theorem chosen_queryCount_bound_K {n M r : ℕ} (scopes : Fin M → Finset (Fin n))
    (hscopes : ∀ i, (scopes i).card ≤ r) {T ε : ℚ} {K : ℝ}
    (hM : 1 ≤ M) (hT : 0 < T) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hTK : (T : ℝ) ≤ 2 * Real.sqrt r * K) :
    (queryCount scopes (meshLevel M T ε) : ℝ) ≤
      (4 * max 1 (4 * Real.sqrt r * K)) ^ r * (M : ℝ) ^ (r + 1) / (ε : ℝ) ^ r := by
  have hq := chosen_queryCount_polynomial scopes hscopes hM hT hε hε1
  have hc : (queryCount scopes (meshLevel M T ε) : ℝ) ≤
      ((4 * max 1 (2 * T)) ^ r * (M : ℚ) ^ (r + 1) / ε ^ r : ℚ) := by exact_mod_cast hq
  push_cast at hc
  apply hc.trans
  have hm : max (1 : ℝ) (2 * (T : ℝ)) ≤ max 1 (4 * Real.sqrt r * K) :=
    max_le_max le_rfl (by nlinarith)
  have hb : 4 * max (1 : ℝ) (2 * (T : ℝ)) ≤ 4 * max 1 (4 * Real.sqrt r * K) :=
    mul_le_mul_of_nonneg_left hm (by norm_num)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hb r) (by positivity))
    (pow_nonneg (by exact_mod_cast hε.le) r)

lemma surrogate_at_cell {k l b : ℕ} (query : (Fin k → ℚ) → ℕ → ℚ)
    (z : Grid (fun _ : Fin k => l)) {x : Fin k → ℝ}
    (hx : x ∈ cell (fun _ : Fin k => l) z) :
    (surrogate query l b).toFun x = (gridTable query l b z : ℝ) := by
  apply congrArg (fun z => (gridTable query l b z : ℝ))
  funext j
  apply Fin.ext
  exact (mem_cell.mp hx j).2

/-- The program's local grid average equals the actual local Lebesgue integral. -/
theorem localAverageQ_cast {k : ℕ} (query : (Fin k → ℚ) → ℕ → ℚ) (l b : ℕ) :
    (localAverageQ query l b : ℝ) = Integral.cubeIntegral (surrogate query l b).toFun := by
  rw [cubeIntegral_eq_cell_sum (fun _ : Fin k => l) _ (fun z x hx => by
    rw [surrogate_at_cell query z hx, surrogate_at_cell query z (corner_mem_cell z)])]
  simp_rw [surrogate_at_cell query _ (corner_mem_cell _)]
  simp [localAverageQ]

/-- Marginalizing unused coordinates preserves the actual local cube integral. -/
theorem cubeIntegral_pullback {n : ℕ} (s : Finset (Fin n)) (f : LocalFunc s.card) :
    Integral.cubeIntegral (Integral.pullback s f) = Integral.cubeIntegral f.toFun := by
  letI : Fintype {i : Fin n // i ∈ s} := Subtype.fintype (fun i => i ∈ s)
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun i => i ∈ s)
  let p : Fin s.card ≃ s := (s.orderIsoOfFin rfl).toEquiv
  let F : (s → ℝ) → ℝ := fun y => f.toFun (fun j => y (p j))
  have hmp := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin n => MultiMoments.intervalMeasure) (fun i => i ∈ s)
  have hi := hmp.integral_comp e.measurableEmbedding (fun z => F z.1)
  have heF : ∀ x : Fin n → ℝ, F (e x).1 = Integral.pullback s f x := by
    intro x
    rfl
  change (∫ x, F (e x).1 ∂MultiMoments.unitMeasure (Fin n)) = _ at hi
  simp only [heF] at hi
  have hfst : (∫ z, F z.1 ∂(MultiMoments.unitMeasure s).prod
      (MultiMoments.unitMeasure {i : Fin n // i ∉ s})) = ∫ y, F y ∂MultiMoments.unitMeasure s := by
    simpa using integral_prod_mul (μ := MultiMoments.unitMeasure s)
      (ν := MultiMoments.unitMeasure {i : Fin n // i ∉ s}) F (fun _ => (1 : ℝ))
  have hp := measurePreserving_piCongrLeft (fun _ : s => MultiMoments.intervalMeasure) p
  have hj := hp.symm.integral_comp (MeasurableEquiv.piCongrLeft (fun _ : s => ℝ) p).symm.measurableEmbedding f.toFun
  have heq : Integral.cubeIntegral (Integral.pullback s f) = ∫ y, F y ∂MultiMoments.unitMeasure s := by
    simpa only [Integral.cubeIntegral, MultiMoments.unitMeasure_fin] using hi.trans hfst
  rw [heq]
  change (∫ y, F y ∂MultiMoments.unitMeasure s) =
    ∫ y, f.toFun y ∂MultiMoments.unitMeasure (Fin s.card) at hj
  rw [MultiMoments.unitMeasure_fin] at hj
  exact hj

/-- Pairwise disjoint scopes factor the actual ambient partition integral. -/
theorem cubeIntegral_prod_disjoint {n M : ℕ} (scopes : Fin M → Finset (Fin n))
    (f : (i : Fin M) → LocalFunc (scopes i).card) (A : Finset (Fin M))
    (hdis : Set.Pairwise (A : Set (Fin M)) fun i j => Disjoint (scopes i) (scopes j)) :
    Integral.cubeIntegral (fun x => ∏ i ∈ A, Integral.pullback (scopes i) (f i) x) =
      ∏ i ∈ A, Integral.cubeIntegral (f i).toFun := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [Integral.cubeIntegral_const]
  | @insert i A hi ih =>
      have hpair : Set.Pairwise (A : Set (Fin M)) fun i j => Disjoint (scopes i) (scopes j) := by
        intro j hj k hk hjk
        exact hdis (Finset.mem_insert_of_mem hj) (Finset.mem_insert_of_mem hk) hjk
      have hs : Disjoint (scopes i) (A.biUnion scopes) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact hdis (Finset.mem_insert_self i A) (Finset.mem_insert_of_mem hj)
          (by intro h; subst j; exact hi hj)
      simp only [Finset.prod_insert hi]
      rw [MultiMoments.cubeIntegral_mul_of_depends (scopes i) (A.biUnion scopes) hs]
      · rw [cubeIntegral_pullback, ih hpair]
      · intro x y hxy
        apply congrArg (f i).toFun
        funext j
        exact hxy _ (Finset.orderEmbOfFin_mem (scopes i) rfl j)
      · intro x y hxy
        apply Finset.prod_congr rfl
        intro j hj
        apply congrArg (f j).toFun
        funext k
        exact hxy _ (Finset.mem_biUnion.mpr ⟨j, hj, Finset.orderEmbOfFin_mem (scopes j) rfl k⟩)

/-- The actual rational disjoint-scope output equals the surrogate partition function. -/
theorem disjointRuleQ_eq_partition {n M : ℕ} (scopes : Fin M → Finset (Fin n))
    (query : (i : Fin M) → (Fin (scopes i).card → ℚ) → ℕ → ℚ)
    (hdis : Pairwise fun i j => Disjoint (scopes i) (scopes j)) (T ε : ℚ) :
    (disjointRuleQ scopes query T ε : ℝ) =
      Integral.partitionFunction n (fun i => Integral.pullback (scopes i)
        (surrogate (query i) (meshLevel M T ε) (valueBits M ε))) := by
  unfold disjointRuleQ Integral.partitionFunction
  rw [cubeIntegral_prod_disjoint scopes _ Finset.univ (by intro i hi j hj hij; exact hdis hij)]
  push_cast
  exact Finset.prod_congr rfl fun i _ => localAverageQ_cast _ _ _

/-- The converse's disjoint-scope partition algorithm, with actual rational output. -/
theorem disjointRuleQ_accurate {n M r : ℕ} (scopes : Fin M → Finset (Fin n))
    (hscopes : ∀ i, (scopes i).card ≤ r)
    (hdis : Pairwise fun i j => Disjoint (scopes i) (scopes j))
    (Ψ : (i : Fin M) → LocalFunc (scopes i).card)
    (O : (i : Fin M) → Oracle.Oracle (scopes i).card (Ψ i).toFun)
    {K U : ℝ} (hK : 0 ≤ K) (hLip : ∀ i, (Ψ i).LipLe K)
    (hΨ : ∀ i x, x ∈ Integral.cube (scopes i).card → 1 ≤ (Ψ i).toFun x ∧ (Ψ i).toFun x ≤ U)
    {T ε : ℚ} (hM : 1 ≤ M) (hT : 0 < T) (hε : 0 < ε)
    (hTK : Real.sqrt r * K ≤ (T : ℝ)) :
    FPTAS.Accurate (disjointRuleQ scopes (fun i => (O i).query) T ε : ℝ)
      (Integral.partitionFunction n (fun i => Integral.pullback (scopes i) (Ψ i))) (ε : ℝ) := by
  rw [disjointRuleQ_eq_partition scopes _ hdis T ε]
  exact partition_surrogate_accurate scopes hscopes Ψ O hK hLip hΨ hM hT hε hTK

/-- Proposition B.1 converse, under the original range and Lipschitz promises.
The mesh constant is existentially supplied, so the statement adds no analytic
certificate to the paper's hypotheses. The surrogate family and disjoint-scope
output are the concrete programs above. -/
theorem prop_B1_converse {n M r : ℕ} (hr : 1 ≤ r) (hM : 1 ≤ M)
    (scopes : Fin M → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (Ψ : (i : Fin M) → LocalFunc (scopes i).card)
    (O : (i : Fin M) → Oracle.Oracle (scopes i).card (Ψ i).toFun)
    {K U : ℝ} (hK : 0 < K) (_hU : 1 < U) (hLip : ∀ i, (Ψ i).LipLe K)
    (hΨ : ∀ i x, x ∈ Integral.cube (scopes i).card → 1 ≤ (Ψ i).toFun x ∧ (Ψ i).toFun x ≤ U)
    (ε : ℚ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ T : ℚ, 0 < T ∧
      FPTAS.Accurate
        (Integral.partitionFunction n (fun i => Integral.pullback (scopes i)
          (surrogate (O i).query (meshLevel M T ε) (valueBits M ε))))
        (Integral.partitionFunction n (fun i => Integral.pullback (scopes i) (Ψ i))) (ε : ℝ) ∧
      (queryCount scopes (meshLevel M T ε) : ℝ) ≤
        (4 * max 1 (4 * Real.sqrt r * K)) ^ r * (M : ℝ) ^ (r + 1) / (ε : ℝ) ^ r ∧
      valueBits M ε ≤ 1 + Nat.clog 2 ⌈4 * (M : ℚ) / ε⌉₊ ∧
      meshLevel M T ε ≤ 1 + Nat.clog 2 ⌈2 * T * M / ε⌉₊ ∧
      (Pairwise (fun i j => Disjoint (scopes i) (scopes j)) →
        FPTAS.Accurate (disjointRuleQ scopes (fun i => (O i).query) T ε : ℝ)
          (Integral.partitionFunction n (fun i => Integral.pullback (scopes i) (Ψ i))) (ε : ℝ)) := by
  obtain ⟨T, hT, hlo, hhi⟩ := exists_mesh_constant hr hK
  exact ⟨T, hT, partition_surrogate_accurate scopes hscopes Ψ O hK.le hLip hΨ hM hT hε hlo,
    chosen_queryCount_bound_K scopes hscopes hM hT hε hε1 hhi,
    valueBits_log_bound hε, meshLevel_log_bound hε,
    fun hdis => disjointRuleQ_accurate scopes hscopes hdis Ψ O hK.le hLip hΨ hM hT hε hlo⟩

end
end Paper08.GridSurrogate
