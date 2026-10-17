import Paper32.Steps
import Paper32.Dynamics
import Paper32.Geometry

/-! # Scaling and separable extra coordinates

The algebraic rescaling is valid for the actual update in any real module.
The scalar estimates prove the extra-coordinate invariant from Appendix A.3.
The product model below represents dimension `2 + card ι`.
-/

open Filter Topology BigOperators

namespace Paper32

/-- The two updates in Appendix A.2 are equal, coordinate by coordinate. -/
theorem scaled_update (z a W ν C : ℝ) :
    z - (a / C) * (W + ν) = z - a * (C⁻¹ * W + ν / C) := by
  ring

/-- The same scaling identity for an arbitrary finite-dimensional update. -/
theorem scaled_vector_update {E : Type*} [AddCommGroup E] [Module ℝ E]
    (z W ν : E) (a C : ℝ) :
    z - (a / C) • (W + ν) = z - a • (C⁻¹ • W + C⁻¹ • ν) := by
  simp only [smul_add, smul_smul, div_eq_mul_inv]

/-- The finite-radius choice in Corollary 7.1 gives the required noise radius. -/
theorem scaled_noise_radius {R C : ℝ} (hR : 0 < R) (hC : 100 * R ≤ C) :
    0 < C ∧ R / C ≤ (1 / 100 : ℝ) := by
  have hCp : 0 < C := by linarith
  exact ⟨hCp, (div_le_iff₀ hCp).2 (by linarith)⟩

theorem scaled_coordinate_noise {R C ν : ℝ} (hR : 0 < R) (hC : 100 * R ≤ C)
    (hν : |ν| ≤ R) : |ν / C| ≤ (1 / 100 : ℝ) := by
  have hc := scaled_noise_radius hR hC
  rw [abs_div, abs_of_pos hc.1]
  exact (div_le_div_of_nonneg_right hν hc.1.le).trans hc.2

/-- The concrete scaled objective used in Corollary 7.1. -/
def scaledObjective (C : ℝ) (z : Point) : ℝ := C * F z

/-- Tilting by `C v` gives exactly `C Fᵥ`. -/
theorem scaledObjective_tilt (C : ℝ) (v z : Point) :
    scaledObjective C z - lin (C • v) z = C * tilt v z := by
  simp only [scaledObjective, lin, tilt, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

theorem scaledTilt_nonneg {C : ℝ} (hC : 0 < C) {v : Point} (hv : U v) (z : Point) :
    0 ≤ scaledObjective C z - lin (C • v) z := by
  rw [scaledObjective_tilt]
  exact mul_nonneg hC.le (tilt_nonneg hv z)

theorem scaledTilt_coercive {C : ℝ} (hC : 0 < C) {v : Point} (hv : U v) :
    Tendsto (fun z => scaledObjective C z - lin (C • v) z) (cocompact Point) atTop := by
  simp_rw [scaledObjective_tilt]
  exact (tilt_coercive hv).const_mul_atTop hC

theorem not_localMin_scaledTilt {C : ℝ} (hC : 0 < C) {v : Point} (hv : U v) :
    ¬ IsLocalMin (fun z => scaledObjective C z - lin (C • v) z) 0 := by
  intro h
  apply not_localMin_tilt hv
  filter_upwards [h] with z hz
  simp only [scaledObjective_tilt] at hz
  nlinarith

/-- Constant rescaling preserves both positive power-law comparison constants. -/
theorem scaled_powerStep_sandwich {γ C : ℝ} (hγ : 0 ≤ γ) (hC : 0 < C) (k : ℕ) :
    (0 < (8 : ℝ) ^ (-γ) / C) ∧ 0 < (1 : ℝ) / C ∧
    ((8 : ℝ) ^ (-γ) / C) * ((k : ℝ) + 1) ^ (-γ) ≤ powerStep γ k / C ∧
    powerStep γ k / C ≤ ((1 : ℝ) / C) * ((k : ℝ) + 1) ^ (-γ) := by
  refine ⟨div_pos (Real.rpow_pos_of_pos (by norm_num) _) hC, div_pos (by norm_num) hC, ?_, ?_⟩
  · convert div_le_div_of_nonneg_right (powerStep_lower hγ k) hC.le using 1 <;> ring
  · convert div_le_div_of_nonneg_right (powerStep_upper hγ k) hC.le using 1 <;> ring

/-- One extra-coordinate step closes the strict `2.1 α` envelope. -/
theorem extraCoordinate_step {r α x e : ℝ} (hα : 0 < α)
    (hr : r ≤ (113 / 100 : ℝ) * α) (hx : |x| ≤ (21 / 10 : ℝ) * r)
    (he : |e| ≤ (1 / 50 : ℝ)) :
    |x - α * (2 * quadrantSign x + e)| < (21 / 10 : ℝ) * α := by
  have hse : |quadrantSign x * e| ≤ (1 / 50 : ℝ) := by
    simpa only [abs_mul, abs_quadrantSign, one_mul] using he
  rw [abs_signed_update]
  apply lt_of_le_of_lt (attracting_sign_step (abs_nonneg x)
    (by norm_num : (1 / 50 : ℝ) < 2) (by norm_num) hα hse)
  apply max_lt
  · nlinarith
  · nlinarith

/-- The same estimate in the standard sign notation of Appendix A.3. -/
theorem extraCoordinate_step_sign {r α x e : ℝ} (hx0 : x ≠ 0) (hα : 0 < α)
    (hr : r ≤ (113 / 100 : ℝ) * α) (hx : |x| ≤ (21 / 10 : ℝ) * r)
    (he : |e| ≤ (1 / 50 : ℝ)) :
    |x - α * (2 * Real.sign x + e)| < (21 / 10 : ℝ) * α := by
  rw [← quadrantSign_eq_sign hx0]
  exact extraCoordinate_step hα hr hx he

/-- Tilt plus bounded coordinate noise gives the required effective error. -/
theorem extraCoordinate_error {ν v : ℝ} (hν : |ν| ≤ (1 / 100 : ℝ))
    (hv : |v| < (1 / 100 : ℝ)) : |ν - v| < (1 / 50 : ℝ) := by
  exact (abs_sub ν v).trans_lt (by linarith)

/-- Appendix A.3: the invariant holds at every positive time. -/
theorem extraCoordinate_bound {α z e : ℕ → ℝ}
    (hα : ∀ k, 0 < α k)
    (hratio : ∀ k, α k ≤ (113 / 100 : ℝ) * α (k + 1))
    (hfirst : |z 1| ≤ (101 / 50 : ℝ) * α 0)
    (he : ∀ k, |e (k + 1)| ≤ (1 / 50 : ℝ))
    (hupdate : ∀ k, z (k + 2) = z (k + 1) - α (k + 1) *
      (2 * quadrantSign (z (k + 1)) + e (k + 1))) :
    ∀ k, |z (k + 1)| ≤ (21 / 10 : ℝ) * α k := by
  intro k
  induction k with
  | zero => simpa using (show |z 1| ≤ (21 / 10 : ℝ) * α 0 by nlinarith [hα 0])
  | succ k ih =>
    rw [show k + 1 + 1 = k + 2 by omega, hupdate k]
    exact (extraCoordinate_step (hα (k + 1)) (hratio k) ih (he k)).le

/-- The shrinking envelope forces the actual scalar trajectory to zero. -/
theorem extraCoordinate_tendsto_zero {α z e : ℕ → ℝ}
    (hα : ∀ k, 0 < α k)
    (hzero : Tendsto α atTop (𝓝 0))
    (hratio : ∀ k, α k ≤ (113 / 100 : ℝ) * α (k + 1))
    (hfirst : |z 1| ≤ (101 / 50 : ℝ) * α 0)
    (he : ∀ k, |e (k + 1)| ≤ (1 / 50 : ℝ))
    (hupdate : ∀ k, z (k + 2) = z (k + 1) - α (k + 1) *
      (2 * quadrantSign (z (k + 1)) + e (k + 1))) :
    Tendsto z atTop (𝓝 0) := by
  have hbound := extraCoordinate_bound hα hratio hfirst he hupdate
  have hz : Tendsto (fun k => |z (k + 1)|) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => abs_nonneg _) hbound
    simpa using hzero.const_mul (21 / 10 : ℝ)
  apply (tendsto_add_atTop_iff_nat 1).1
  exact (tendsto_zero_iff_abs_tendsto_zero (fun k => z (k + 1))).2 hz

/-- The estimate specializes without additional schedule assumptions to (2.7). -/
theorem extraCoordinate_powerStep {γ : ℝ} (hγlo : (1 / 2 : ℝ) < γ) (hγhi : γ < 1)
    {z e : ℕ → ℝ}
    (hfirst : |z 1| ≤ (101 / 50 : ℝ) * powerStep γ 0)
    (he : ∀ k, |e (k + 1)| ≤ (1 / 50 : ℝ))
    (hupdate : ∀ k, z (k + 2) = z (k + 1) - powerStep γ (k + 1) *
      (2 * quadrantSign (z (k + 1)) + e (k + 1))) :
    (∀ k, |z (k + 1)| ≤ (21 / 10 : ℝ) * powerStep γ k) ∧
    Tendsto z atTop (𝓝 0) := by
  have hp : 0 < γ := by linarith
  exact ⟨extraCoordinate_bound (powerStep_pos γ) (powerStep_ratio_bound hγhi) hfirst he hupdate,
    extraCoordinate_tendsto_zero (powerStep_pos γ) (powerStep_tendsto_zero hp)
      (powerStep_ratio_bound hγhi) hfirst he hupdate⟩

/-- The positive-time recurrence with the ordinary real sign, exactly as in (A.3). -/
theorem extraCoordinate_powerStep_sign {γ : ℝ} (hγlo : (1 / 2 : ℝ) < γ) (hγhi : γ < 1)
    {z e : ℕ → ℝ} (hnz : ∀ k, z (k + 1) ≠ 0)
    (hfirst : |z 1| ≤ (101 / 50 : ℝ) * powerStep γ 0)
    (he : ∀ k, |e (k + 1)| ≤ (1 / 50 : ℝ))
    (hupdate : ∀ k, z (k + 2) = z (k + 1) - powerStep γ (k + 1) *
      (2 * Real.sign (z (k + 1)) + e (k + 1))) :
    (∀ k, |z (k + 1)| ≤ (21 / 10 : ℝ) * powerStep γ k) ∧
    Tendsto z atTop (𝓝 0) := by
  apply extraCoordinate_powerStep hγlo hγhi hfirst he
  intro k
  simpa only [quadrantSign_eq_sign (hnz k)] using hupdate k

/-- Extra-coordinate first capture from a Clarke value at the origin. -/
theorem extraCoordinate_first_bound {α w v ν : ℝ} (hα : 0 < α)
    (hw : |w| ≤ 2) (hv : |v| < (1 / 100 : ℝ)) (hν : |ν| ≤ (1 / 100 : ℝ)) :
    |0 - α * (w - v + ν)| < (101 / 50 : ℝ) * α := by
  have hab : |w - v + ν| < (101 / 50 : ℝ) := by
    calc
      _ ≤ |w| + |v| + |ν| := by
        calc
          _ ≤ |w - v| + |ν| := abs_add_le _ _
          _ ≤ _ := add_le_add_right (abs_sub w v) _
      _ < _ := by linarith
  simpa only [zero_sub, abs_neg, abs_mul, abs_of_pos hα, mul_comm] using
    mul_lt_mul_of_pos_right hab hα

section Embedding

variable {ι : Type*} [Fintype ι]

/-- A concrete separable objective on `2 + card ι` coordinates. -/
def embeddedObjective (z : Point × (ι → ℝ)) : ℝ :=
  F z.1 + 2 * ∑ i, |z.2 i|

/-- The linear tilts in the extra coordinates retain their full quantifiers. -/
def embeddedTilt (v z : Point × (ι → ℝ)) : ℝ :=
  embeddedObjective z - (lin v.1 z.1 + ∑ i, v.2 i * z.2 i)

def embeddedU (v : Point × (ι → ℝ)) : Prop :=
  U v.1 ∧ ∀ i, |v.2 i| < (1 / 100 : ℝ)

lemma embeddedTilt_eq (v z : Point × (ι → ℝ)) :
    embeddedTilt v z = tilt v.1 z.1 + ∑ i, (2 * |z.2 i| - v.2 i * z.2 i) := by
  simp only [embeddedTilt, embeddedObjective, tilt, Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  ring

/-- The exact coercivity inequality (A.3, final display). -/
theorem embeddedTilt_lower {v : Point × (ι → ℝ)} (hv : embeddedU v)
    (z : Point × (ι → ℝ)) :
    (99 / 100 : ℝ) * l1 z.1 + (199 / 100 : ℝ) * ∑ i, |z.2 i| ≤ embeddedTilt v z := by
  rw [embeddedTilt_eq, Finset.mul_sum]
  apply add_le_add (tilt_lower_uniform hv.1 z.1)
  apply Finset.sum_le_sum
  intro i _
  have hmul : v.2 i * z.2 i ≤ |v.2 i| * |z.2 i| := by
    simpa only [abs_mul] using le_abs_self (v.2 i * z.2 i)
  have hb := mul_le_mul_of_nonneg_right (hv.2 i).le (abs_nonneg (z.2 i))
  nlinarith

theorem embeddedTilt_nonneg {v : Point × (ι → ℝ)} (hv : embeddedU v)
    (z : Point × (ι → ℝ)) : 0 ≤ embeddedTilt v z := by
  apply le_trans _ (embeddedTilt_lower hv z)
  exact add_nonneg (mul_nonneg (by norm_num) (l1_nonneg z.1))
    (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => abs_nonneg (z.2 i))))

lemma extra_norm_le_sum (q : ι → ℝ) : ‖q‖ ≤ ∑ i, |q i| := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun j _ => abs_nonneg (q j)) (Finset.mem_univ i)

lemma embedded_norm_le_l1 (z : Point × (ι → ℝ)) :
    ‖z‖ ≤ l1 z.1 + ∑ i, |z.2 i| := by
  rw [Prod.norm_def]
  apply max_le
  · exact (norm_le_l1 z.1).trans (le_add_of_nonneg_right (by positivity))
  · exact (extra_norm_le_sum z.2).trans (le_add_of_nonneg_left (l1_nonneg z.1))

/-- The explicit product objective is coercive for every allowed tilt. -/
theorem embeddedTilt_coercive {v : Point × (ι → ℝ)} (hv : embeddedU v) :
    Tendsto (embeddedTilt v) (cocompact (Point × (ι → ℝ))) atTop := by
  apply tendsto_atTop_mono (fun z => ?_)
    (tendsto_norm_cocompact_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 99 / 100))
  have hn := mul_le_mul_of_nonneg_left (embedded_norm_le_l1 z) (by norm_num : (0 : ℝ) ≤ 99 / 100)
  have hl := embeddedTilt_lower hv z
  have hs : (0 : ℝ) ≤ ∑ i, |z.2 i| := by positivity
  nlinarith

@[simp] theorem embeddedTilt_restriction (v : Point × (ι → ℝ)) (p : Point) :
    embeddedTilt v (p, 0) = tilt v.1 p := by
  simp [embeddedTilt_eq]

/-- The same strict vertical decrease survives in every added dimension. -/
theorem embeddedTilt_vertical_descent {v : Point × (ι → ℝ)} (hv : embeddedU v)
    {t : ℝ} (ht : 0 < |t|) (ht4 : |t| < 4) :
    embeddedTilt v ((0,t), 0) < embeddedTilt v 0 := by
  change embeddedTilt v (((0,t) : Point), (0 : ι → ℝ)) <
    embeddedTilt v ((0 : Point), (0 : ι → ℝ))
  rw [embeddedTilt_restriction, embeddedTilt_restriction]
  exact tilt_vertical_descent hv.1 ht ht4

/-- Therefore the embedded origin is not a local minimizer. -/
theorem not_localMin_embeddedTilt {v : Point × (ι → ℝ)} (hv : embeddedU v) :
    ¬ IsLocalMin (embeddedTilt v) 0 := by
  intro h
  rcases Metric.mem_nhds_iff.mp h with ⟨ε, hε, hball⟩
  let t : ℝ := min ε 1 / 2
  have htpos : 0 < t := by dsimp [t]; positivity
  have hteps : t < ε := by dsimp [t]; have := min_le_left ε 1; linarith
  have ht4 : |t| < 4 := by rw [abs_of_pos htpos]; dsimp [t]; have := min_le_right ε 1; linarith
  have hd : dist ((((0,t) : Point), (0 : ι → ℝ))) 0 < ε := by
    simpa [Prod.dist_eq, Real.dist_eq, abs_of_pos htpos, hε] using hteps
  exact not_lt_of_ge (hball hd) (embeddedTilt_vertical_descent hv (by simpa [abs_of_pos htpos] using htpos) ht4)

/-- Coordinatewise scalar convergence gives convergence of every finite product. -/
theorem extraCoordinates_tendsto_zero {z : ℕ → ι → ℝ}
    (hz : ∀ i, Tendsto (fun k => z k i) atTop (𝓝 0)) :
    Tendsto z atTop (𝓝 0) := by
  exact tendsto_pi_nhds.2 hz

/-- All extra coordinates in the separable embedding converge simultaneously. -/
theorem embeddedExtra_powerStep {γ : ℝ} (hγlo : (1 / 2 : ℝ) < γ) (hγhi : γ < 1)
    {q e : ℕ → ι → ℝ} (hnz : ∀ k i, q (k + 1) i ≠ 0)
    (hfirst : ∀ i, |q 1 i| ≤ (101 / 50 : ℝ) * powerStep γ 0)
    (he : ∀ k i, |e (k + 1) i| ≤ (1 / 50 : ℝ))
    (hupdate : ∀ k i, q (k + 2) i = q (k + 1) i - powerStep γ (k + 1) *
      (2 * Real.sign (q (k + 1) i) + e (k + 1) i)) :
    (∀ k i, |q (k + 1) i| ≤ (21 / 10 : ℝ) * powerStep γ k) ∧
    Tendsto q atTop (𝓝 0) := by
  have h i := extraCoordinate_powerStep_sign hγlo hγhi
    (z := fun k => q k i) (e := fun k => e k i)
    (fun k => hnz k i) (hfirst i) (fun k => he k i) (fun k => hupdate k i)
  exact ⟨fun k i => (h i).1 k, extraCoordinates_tendsto_zero (fun i => (h i).2)⟩

end Embedding

end Paper32
