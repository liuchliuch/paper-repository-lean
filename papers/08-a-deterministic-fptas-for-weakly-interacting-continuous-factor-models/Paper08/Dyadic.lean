import Paper08.Integral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Normed.Lp.PiLp

/-! # The actual lower-corner dyadic step functions of Lemma 3.1
The final dyadic interval is closed at one. Its lower-corner index is therefore
capped at `2^level - 1`, including at the endpoint `x = 1`. -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace Paper08.Dyadic

/-- Index of the dyadic interval containing `x`, with the last cell closed at one. -/
def cellIndex (level : ℕ) (x : ℝ) : ℕ :=
  min ⌊(2 : ℝ) ^ level * x⌋₊ (2 ^ level - 1)

/-- The lower endpoint of the cell containing `x`. -/
def lower (level : ℕ) (x : ℝ) : ℝ := (cellIndex level x : ℝ) / (2 : ℝ) ^ level

lemma cellIndex_lt (level : ℕ) (x : ℝ) : cellIndex level x < 2 ^ level := by
  exact lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt (by positivity) (by omega))

@[simp] lemma cellIndex_zero (x : ℝ) : cellIndex 0 x = 0 := by simp [cellIndex]
@[simp] lemma lower_zero (x : ℝ) : lower 0 x = 0 := by simp [lower]

lemma lower_nonneg (level : ℕ) (x : ℝ) : 0 ≤ lower level x := by
  unfold lower
  positivity

lemma lower_le {level : ℕ} {x : ℝ} (hx : 0 ≤ x) : lower level x ≤ x := by
  rw [lower, div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ level)]
  calc (cellIndex level x : ℝ) ≤ (⌊(2 : ℝ) ^ level * x⌋₊ : ℝ) := by
        unfold cellIndex
        exact_mod_cast (min_le_left ⌊(2 : ℝ) ^ level * x⌋₊ (2 ^ level - 1))
    _ ≤ (2 : ℝ) ^ level * x := Nat.floor_le (mul_nonneg (by positivity) hx)
    _ = x * (2 : ℝ) ^ level := by ring

lemma sub_lower_le {level : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x - lower level x ≤ ((2 : ℝ) ^ level)⁻¹ := by
  have hp : 0 < (2 : ℝ) ^ level := by positivity
  have hpow : (1 : ℝ) ≤ 2 ^ level := one_le_pow₀ (by norm_num)
  have hcast : ((2 ^ level - 1 : ℕ) : ℝ) = (2 : ℝ) ^ level - 1 := by
    rw [Nat.cast_sub (one_le_pow₀ (by omega : 1 ≤ (2 : ℕ)))]
    simp
  have hmin : (2 : ℝ) ^ level * x - 1 ≤ (cellIndex level x : ℝ) := by
    rw [cellIndex, Nat.cast_min]
    apply le_min
    · have h := (Nat.lt_floor_add_one ((2 : ℝ) ^ level * x)).le
      linarith
    · rw [hcast]
      nlinarith
  have hlower : lower level x * (2 : ℝ) ^ level = (cellIndex level x : ℝ) := by
    exact div_mul_cancel₀ _ hp.ne'
  apply (mul_le_mul_right hp).mp
  rw [inv_mul_cancel₀ hp.ne']
  nlinarith

lemma lower_mem {level : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ lower level x ∧ lower level x ≤ 1 :=
  ⟨lower_nonneg _ _, (lower_le hx0).trans hx1⟩

lemma abs_sub_lower_le {level : ℕ} {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |x - lower level x| ≤ ((2 : ℝ) ^ level)⁻¹ := by
  rw [abs_of_nonneg (sub_nonneg.mpr (lower_le hx0))]
  exact sub_lower_le hx0 hx1

/-- Simultaneous lower-corner projection in all local coordinates. -/
def corner {k : ℕ} (level : ℕ) (x : Fin k → ℝ) : Fin k → ℝ :=
  fun i => lower level (x i)

lemma corner_mem {k level : ℕ} {x : Fin k → ℝ} (hx : x ∈ Integral.cube k) :
    corner level x ∈ Integral.cube k := by
  rw [Integral.mem_cube] at hx ⊢
  exact fun i => lower_mem (hx i).1 (hx i).2

/-- The actual sampled step function `Π_level f`. -/
def step {k : ℕ} (f : LocalFunc k) (level : ℕ) : LocalFunc k :=
  ⟨fun x => f.toFun (corner level x)⟩

/-- The telescoping increment `Δ_level f`. -/
def increment {k : ℕ} (f : LocalFunc k) : ℕ → LocalFunc k
  | 0 => step f 0
  | level + 1 => ⟨fun x => (step f (level + 1)).toFun x - (step f level).toFun x⟩

lemma step_bound {k level : ℕ} {f : LocalFunc k} {A : ℝ} (hf : f.BoundBy A) :
    (step f level).BoundBy A := by
  intro x hx
  exact hf _ (Integral.mem_cube.mp (corner_mem (Integral.mem_cube.mpr hx)))

lemma measurable_cellIndex (level : ℕ) : Measurable (cellIndex level) := by
  exact ((measurable_const.mul measurable_id).nat_floor).min measurable_const

/-- Sampling any function at finitely many dyadic corners gives a measurable function. -/
lemma measurable_step {k : ℕ} (f : LocalFunc k) (level : ℕ) :
    Measurable (step f level).toFun := by
  let ind : (Fin k → ℝ) → (Fin k → ℕ) := fun x i => cellIndex level (x i)
  have hm : Measurable ind := by
    exact measurable_pi_lambda _ fun i => (measurable_cellIndex level).comp (measurable_pi_apply i)
  have hn : Measurable (fun p : Fin k → ℕ =>
      f.toFun (fun i => (p i : ℝ) / (2 : ℝ) ^ level)) := measurable_of_countable _
  exact hn.comp hm

lemma integrable_step {k : ℕ} {f : LocalFunc k} {A : ℝ}
    (hf : f.BoundBy A) (level : ℕ) :
    IntegrableOn (step f level).toFun (Integral.cube k) := by
  apply Integral.integrableOn_cube_of_bound (measurable_step f level)
  intro x hx
  exact step_bound hf x (Integral.mem_cube.mp hx)

lemma measurable_increment {k : ℕ} (f : LocalFunc k) (level : ℕ) :
    Measurable (increment f level).toFun := by
  cases level with
  | zero => exact measurable_step f 0
  | succ level => exact (measurable_step f (level + 1)).sub (measurable_step f level)

lemma integrable_increment {k : ℕ} {f : LocalFunc k} {A : ℝ}
    (hf : f.BoundBy A) (level : ℕ) :
    IntegrableOn (increment f level).toFun (Integral.cube k) := by
  cases level with
  | zero => exact integrable_step hf 0
  | succ level => exact (integrable_step hf (level + 1)).sub (integrable_step hf level)

/-- Euclidean error of the lower-corner projection on the unit cube. -/
lemma corner_dist_le {k level : ℕ} {x : Fin k → ℝ} (hx : x ∈ Integral.cube k) :
    euclDist x (corner level x) ≤ Real.sqrt k * ((2 : ℝ) ^ level)⁻¹ := by
  have hi := Integral.mem_cube.mp hx
  have hsum : (∑ i : Fin k, ‖x i - lower level (x i)‖ ^ 2) ≤
      (k : ℝ) * (((2 : ℝ) ^ level)⁻¹) ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin k, (((2 : ℝ) ^ level)⁻¹) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply pow_le_pow_left₀ (norm_nonneg _)
        simpa [Real.norm_eq_abs] using abs_sub_lower_le (hi i).1 (hi i).2
      _ = _ := by simp
  change ‖WithLp.toLp 2 (fun i => x i - lower level (x i))‖ ≤ _
  rw [PiLp.norm_eq_of_L2]
  calc
    _ ≤ Real.sqrt ((k : ℝ) * (((2 : ℝ) ^ level)⁻¹) ^ 2) := Real.sqrt_le_sqrt hsum
    _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]

/-- The uniform approximation estimate preceding (3.3). -/
lemma step_error {k level : ℕ} {f : LocalFunc k} {K : ℝ}
    (hK : 0 ≤ K) (hf : f.LipLe K) {x : Fin k → ℝ} (hx : x ∈ Integral.cube k) :
    |(step f level).toFun x - f.toFun x| ≤
      Real.sqrt k * K * ((2 : ℝ) ^ level)⁻¹ := by
  have h := hf x (corner level x) (Integral.mem_cube.mp hx)
    (Integral.mem_cube.mp (corner_mem hx))
  change |f.toFun (corner level x) - f.toFun x| ≤ _
  rw [abs_sub_comm]
  calc
    _ ≤ K * euclDist x (corner level x) := h
    _ ≤ K * (Real.sqrt k * ((2 : ℝ) ^ level)⁻¹) := mul_le_mul_of_nonneg_left (corner_dist_le hx) hK
    _ = _ := by ring

/-- The paper's envelope `B_i = max {1,A_i,3 sqrt(r) K_i}`. -/
def budget (r : ℕ) (A K : ℝ) : ℝ := max 1 (max A (3 * Real.sqrt r * K))

lemma one_le_budget (r : ℕ) (A K : ℝ) : 1 ≤ budget r A K := le_max_left _ _
lemma bound_le_budget (r : ℕ) (A K : ℝ) : A ≤ budget r A K :=
  (le_max_left _ _).trans (le_max_right _ _)
lemma lip_le_budget (r : ℕ) (A K : ℝ) : 3 * Real.sqrt r * K ≤ budget r A K :=
  (le_max_right _ _).trans (le_max_right _ _)
lemma budget_pos (r : ℕ) (A K : ℝ) : 0 < budget r A K :=
  lt_of_lt_of_le zero_lt_one (one_le_budget r A K)

/-- The actual increments satisfy the norm bound (3.3), at every cube point. -/
lemma increment_bound {k r : ℕ} {f : LocalFunc k} {A K : ℝ}
    (hkr : k ≤ r) (hK : 0 ≤ K) (hA : f.BoundBy A) (hf : f.LipLe K)
    (level : ℕ) {x : Fin k → ℝ} (hx : x ∈ Integral.cube k) :
    |(increment f level).toFun x| ≤ budget r A K * ((2 : ℝ) ^ level)⁻¹ := by
  cases level with
  | zero =>
      simpa only [increment, pow_zero, inv_one, mul_one] using
        (step_bound (level := 0) hA x (Integral.mem_cube.mp hx)).trans (bound_le_budget r A K)
  | succ level =>
      have h1 := step_error hK hf (level := level + 1) hx
      have h0 := step_error hK hf (level := level) hx
      have hg : ((2 : ℝ) ^ level)⁻¹ = 2 * ((2 : ℝ) ^ (level + 1))⁻¹ := by
        rw [pow_succ]
        field_simp
      have henv : 3 * Real.sqrt k * K ≤ budget r A K := by
        calc
          _ ≤ 3 * Real.sqrt r * K := by gcongr
          _ ≤ _ := lip_le_budget r A K
      change |(step f (level + 1)).toFun x - (step f level).toFun x| ≤ _
      calc
        _ ≤ |(step f (level + 1)).toFun x - f.toFun x| +
            |(step f level).toFun x - f.toFun x| := by
          simpa only [abs_sub_comm (f.toFun x)] using
            abs_sub_le ((step f (level + 1)).toFun x) (f.toFun x) ((step f level).toFun x)
        _ ≤ Real.sqrt k * K * ((2 : ℝ) ^ (level + 1))⁻¹ +
            Real.sqrt k * K * ((2 : ℝ) ^ level)⁻¹ := add_le_add h1 h0
        _ = (3 * Real.sqrt k * K) * ((2 : ℝ) ^ (level + 1))⁻¹ := by rw [hg]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right henv (by positivity)

/-- The finite telescoping identity for the actual increments. -/
lemma sum_increment {k : ℕ} (f : LocalFunc k) (level : ℕ) (x : Fin k → ℝ) :
    (∑ l ∈ Finset.range (level + 1), (increment f l).toFun x) = (step f level).toFun x := by
  induction level with
  | zero => simp [increment]
  | succ level ih =>
      rw [Finset.sum_range_succ, ih]
      simp [increment]

/-- The sampled step functions converge uniformly to the original Lipschitz function. -/
lemma step_tendstoUniformlyOn {k : ℕ} {f : LocalFunc k} {K : ℝ}
    (hK : 0 ≤ K) (hf : f.LipLe K) :
    TendstoUniformlyOn (fun level => (step f level).toFun) f.toFun
      Filter.atTop (Integral.cube k) := by
  have hgeo : Filter.Tendsto (fun level : ℕ =>
      Real.sqrt k * K * ((2 : ℝ) ^ level)⁻¹) Filter.atTop (nhds 0) := by
    have hg := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (Real.sqrt k * K)
    simpa only [one_div, inv_pow, mul_zero] using hg
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  apply (hgeo.eventually (gt_mem_nhds hε)).mono
  intro level hlevel x hx
  rw [Real.dist_eq, abs_sub_comm]
  exact (step_error hK hf hx).trans_lt hlevel

/-- Equality (3.3): the actual increment series sums to the original local function. -/
lemma hasSum_increment {k r : ℕ} {f : LocalFunc k} {A K : ℝ}
    (hkr : k ≤ r) (hK : 0 ≤ K) (hA : f.BoundBy A) (hf : f.LipLe K)
    {x : Fin k → ℝ} (hx : x ∈ Integral.cube k) :
    HasSum (fun level => (increment f level).toFun x) (f.toFun x) := by
  have hgeo : Summable (fun level : ℕ => budget r A K * ((2 : ℝ) ^ level)⁻¹) := by
    have hg := (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left (budget r A K)
    simpa only [one_div, inv_pow] using hg
  have hsum : Summable (fun level => (increment f level).toFun x) := by
    apply hgeo.of_norm_bounded
    intro level
    simpa only [Real.norm_eq_abs] using increment_bound hkr hK hA hf level hx
  apply hsum.hasSum_iff_tendsto_nat.mpr
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  simpa only [sum_increment] using (step_tendstoUniformlyOn hK hf).tendsto_at hx

/-- Lipschitz local functions with a uniform bound are integrable on the cube.
This follows from their actual measurable step approximations, so no global
measurability assumption outside the cube is needed. -/
lemma integrable_localFunc {k : ℕ} {f : LocalFunc k} {A K : ℝ}
    (hK : 0 ≤ K) (hA : f.BoundBy A) (hf : f.LipLe K) :
    IntegrableOn f.toFun (Integral.cube k) := by
  have hm : AEStronglyMeasurable f.toFun (volume.restrict (Integral.cube k)) := by
    apply aestronglyMeasurable_of_tendsto_ae Filter.atTop
      (fun level => (measurable_step f level).aestronglyMeasurable)
    exact (ae_restrict_mem (Integral.measurableSet_cube k)).mono fun x hx =>
      (step_tendstoUniformlyOn hK hf).tendsto_at hx
  have hc : IntegrableOn (fun _ : Fin k → ℝ => A) (Integral.cube k) :=
    integrableOn_const (Integral.volume_cube_lt_top k).ne
  apply hc.mono' hm
  exact (ae_restrict_mem (Integral.measurableSet_cube k)).mono fun x hx => by
    simpa only [Real.norm_eq_abs] using hA x (Integral.mem_cube.mp hx)

/-- The actual dyadic approximation has the same error after Lebesgue integration. -/
lemma cubeIntegral_step_error {k level : ℕ} {f : LocalFunc k} {A K : ℝ}
    (hK : 0 ≤ K) (hA : f.BoundBy A) (hf : f.LipLe K) :
    |Integral.cubeIntegral (step f level).toFun - Integral.cubeIntegral f.toFun| ≤
      Real.sqrt k * K * ((2 : ℝ) ^ level)⁻¹ := by
  apply Integral.abs_cubeIntegral_sub_le (integrable_step hA level) (integrable_localFunc hK hA hf)
  exact fun _ hx => step_error hK hf hx

end Paper08.Dyadic
