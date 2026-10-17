import Paper08.QuadratureSeries
import Paper08.Dyadic

/-!
# The total-level integral and stability bounds

This file connects the finite sums to actual Bochner integrals on the cube,
and then specializes the tail estimate to the lower-corner dyadic increments
of the paper, with arbitrary overlapping scopes.
-/

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace Paper08.Quadrature

/-- The step-function integrand in (3.4). -/
def totalLevelIntegrand {n t : ℕ} (δ : Fin t → ℕ → (Fin n → ℝ) → ℝ) (J : ℕ)
    (x : Fin n → ℝ) : ℝ :=
  ∑ ν ∈ totalLevels t J, ∏ i, δ i (ν i) x

/-- The finite sum of actual integrals defining equation (3.4). -/
def totalLevelRule {n t : ℕ} (δ : Fin t → ℕ → (Fin n → ℝ) → ℝ) (J : ℕ) : ℝ :=
  ∑ ν ∈ totalLevels t J, Integral.cubeIntegral (fun x => ∏ i, δ i (ν i) x)

lemma integrableOn_product_of_bounds {n t : ℕ}
    (f : Fin t → (Fin n → ℝ) → ℝ) (B : Fin t → ℝ)
    (hm : ∀ i, Measurable (f i))
    (hb : ∀ i x, x ∈ Integral.cube n → |f i x| ≤ B i) :
    IntegrableOn (fun x => ∏ i, f i x) (Integral.cube n) := by
  apply Integral.integrableOn_cube_of_bound (Finset.measurable_prod _ fun i _ => hm i)
  intro x hx
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hb i x hx)

lemma totalLevelRule_eq_integral {n t : ℕ}
    (δ : Fin t → ℕ → (Fin n → ℝ) → ℝ) (J : ℕ) (B : Fin t → ℕ → ℝ)
    (hm : ∀ i l, l ≤ J → Measurable (δ i l))
    (hb : ∀ i l, l ≤ J → ∀ x, x ∈ Integral.cube n → |δ i l x| ≤ B i l) :
    totalLevelRule δ J = Integral.cubeIntegral (totalLevelIntegrand δ J) := by
  unfold totalLevelRule totalLevelIntegrand
  symm
  apply Integral.cubeIntegral_sum
  intro ν hν
  have hνJ := (mem_totalLevels.mp hν).1
  exact integrableOn_product_of_bounds (fun i => δ i (ν i)) (fun i => B i (ν i))
    (fun i => hm i (ν i) (hνJ i)) (fun i => hb i (ν i) (hνJ i))

lemma abs_limit_le_dyadic_budget (δ : ℕ → ℝ) (u B : ℝ)
    (hB : 0 ≤ B) (hδ : ∀ l, |δ l| ≤ B * (1 / 2 : ℝ) ^ l)
    (hlimit : Tendsto (fun N => ∑ l ∈ Finset.range (N + 1), δ l) atTop (𝓝 u)) :
    |u| ≤ 2 * B := by
  apply le_of_tendsto' hlimit.abs
  intro N
  calc
    _ ≤ ∑ l ∈ Finset.range (N + 1), |δ l| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ Finset.range (N + 1), B * (1 / 2 : ℝ) ^ l :=
      Finset.sum_le_sum fun l _ => hδ l
    _ = B * ∑ l ∈ Finset.range (N + 1), (1 / 2 : ℝ) ^ l := by rw [Finset.mul_sum]
    _ ≤ 2 * B := by nlinarith [sum_geometric_two_le (N + 1)]

/-- Measurable increment approximations and their actual pointwise limit
produce an integrable product on the cube.  Thus the integral tail theorem
does not need an additional regularity assumption on the limit functions. -/
lemma integrableOn_limit_product {n t : ℕ}
    (δ : Fin t → ℕ → (Fin n → ℝ) → ℝ) (u : Fin t → (Fin n → ℝ) → ℝ)
    (B : Fin t → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hm : ∀ i l, Measurable (δ i l))
    (hδ : ∀ i l x, x ∈ Integral.cube n → |δ i l x| ≤ B i * (1 / 2 : ℝ) ^ l)
    (hlimit : ∀ i x, x ∈ Integral.cube n →
      Tendsto (fun N => ∑ l ∈ Finset.range (N + 1), δ i l x) atTop (𝓝 (u i x))) :
    IntegrableOn (fun x => ∏ i, u i x) (Integral.cube n) := by
  let μ := (volume : Measure (Fin n → ℝ)).restrict (Integral.cube n)
  haveI : IsFiniteMeasure μ := ⟨by simp [μ, Integral.volume_cube]⟩
  have hmprod : AEStronglyMeasurable (fun x => ∏ i, u i x) μ := by
    apply aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun N x => ∏ i, ∑ l ∈ Finset.range (N + 1), δ i l x)
    · intro N
      apply Measurable.aestronglyMeasurable
      apply Finset.measurable_prod
      intro i _
      exact Finset.measurable_sum _ fun l _ => hm i l
    · apply (ae_restrict_mem (Integral.measurableSet_cube n)).mono
      intro x hx
      exact tendsto_finset_prod Finset.univ fun i _ => hlimit i x hx
  apply (integrable_const (∏ i, 2 * B i) : Integrable _ μ).mono' hmprod
  apply (ae_restrict_mem (Integral.measurableSet_cube n)).mono
  intro x hx
  rw [Real.norm_eq_abs, Finset.abs_prod]
  apply Finset.prod_le_prod (fun i _ => abs_nonneg _)
  intro i _
  exact abs_limit_le_dyadic_budget (fun l => δ i l x) (u i x) (B i) (hB i)
    (fun l => hδ i l x hx) (hlimit i x hx)

/-- Equation (3.5) for the actual cube integral and actual total-level rule.
The proof derives integrability from measurable approximants and convergence,
then integrates the pointwise total-level tail. -/
theorem total_level_integral_error {n t J : ℕ}
    (δ : Fin t → ℕ → (Fin n → ℝ) → ℝ) (u : Fin t → (Fin n → ℝ) → ℝ)
    (B : Fin t → ℝ) (hB : ∀ i, 0 ≤ B i)
    (hm : ∀ i l, Measurable (δ i l))
    (hδ : ∀ i l x, x ∈ Integral.cube n → |δ i l x| ≤ B i * (1 / 2 : ℝ) ^ l)
    (hlimit : ∀ i x, x ∈ Integral.cube n →
      Tendsto (fun N => ∑ l ∈ Finset.range (N + 1), δ i l x) atTop (𝓝 (u i x))) :
    |Integral.cubeIntegral (fun x => ∏ i, u i x) - totalLevelRule δ J| ≤
      (∏ i, B i) * C0 ^ t * (2 : ℝ) ^ (-(J : ℝ) / 2) := by
  have huf := integrableOn_limit_product δ u B hB hm hδ hlimit
  have hfinite : IntegrableOn (totalLevelIntegrand δ J) (Integral.cube n) := by
    apply integrable_finset_sum
    intro ν _
    exact integrableOn_product_of_bounds (fun i => δ i (ν i))
      (fun i => B i * (1 / 2 : ℝ) ^ (ν i)) (fun i => hm i (ν i))
      (fun i => hδ i (ν i))
  rw [totalLevelRule_eq_integral δ J (fun i l => B i * (1 / 2 : ℝ) ^ l)
    (fun i l _ => hm i l) (fun i l _ => hδ i l)]
  have hsub : Integral.cubeIntegral (fun x => ∏ i, u i x) -
      Integral.cubeIntegral (totalLevelIntegrand δ J) =
      Integral.cubeIntegral (fun x => (∏ i, u i x) - totalLevelIntegrand δ J x) :=
    (integral_sub huf hfinite).symm
  rw [hsub]
  apply Integral.abs_cubeIntegral_le
  intro x hx
  exact dyadic_total_level_product_error (fun i l => δ i l x) (fun i => u i x) B hB
    (fun i l => hδ i l x hx) (fun i => hlimit i x hx)

/-- Actual dyadic increments pulled back from their possibly overlapping scopes. -/
def scopedIncrement {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (f : (i : Fin t) → LocalFunc (scopes i).card) (i : Fin t) (l : ℕ)
    (x : Fin n → ℝ) : ℝ :=
  (Dyadic.increment (f i) l).toFun (Integral.restrictTo (scopes i) x)

/-- Lemma 3.1's analytic error, with exactly the original envelope and actual
lower-corner functions.  Scopes may overlap arbitrarily. -/
theorem dyadic_quadrature_error {n t r J : ℕ}
    (scopes : Fin t → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (f : (i : Fin t) → LocalFunc (scopes i).card) (A K : Fin t → ℝ)
    (hK : ∀ i, 0 ≤ K i) (hA : ∀ i, (f i).BoundBy (A i))
    (hf : ∀ i, (f i).LipLe (K i)) :
    |Integral.cubeIntegral (fun x => ∏ i, Integral.pullback (scopes i) (f i) x) -
        totalLevelRule (scopedIncrement scopes f) J| ≤
      (∏ i, Dyadic.budget r (A i) (K i)) * C0 ^ t * (2 : ℝ) ^ (-(J : ℝ) / 2) := by
  apply total_level_integral_error (B := fun i => Dyadic.budget r (A i) (K i))
  · intro i
    exact (Dyadic.budget_pos r (A i) (K i)).le
  · intro i l
    exact (Dyadic.measurable_increment (f i) l).comp (Integral.measurable_restrictTo (scopes i))
  · intro i l x hx
    simpa only [scopedIncrement, one_div, inv_pow] using
      Dyadic.increment_bound (hscopes i) (hK i) (hA i) (hf i) l
        (Integral.restrictTo_mem_cube (scopes i) hx)
  · intro i x hx
    have hlocal := Integral.restrictTo_mem_cube (scopes i) hx
    have hconv := (Dyadic.step_tendstoUniformlyOn (hK i) (hf i)).tendsto_at hlocal
    simpa only [scopedIncrement, Dyadic.sum_increment, Integral.pullback] using hconv

/-- Sample perturbations (3.7) for actual finite sums of cube integrals.
Both arrays are required to be measurable, as the stored step arrays are. -/
theorem total_level_integral_perturbation {n t J : ℕ}
    (a b : Fin t → ℕ → (Fin n → ℝ) → ℝ) (B ζ : Fin t → ℝ) (ζmax : ℝ)
    (hB : ∀ i, 1 ≤ B i) (hζ : ∀ i, 0 ≤ ζ i) (hζmax : ∀ i, ζ i ≤ ζmax)
    (hprecision : ∀ i, 2 * (J + 1 : ℝ) * ζ i ≤ B i)
    (hma : ∀ i l, l ≤ J → Measurable (a i l)) (hmb : ∀ i l, l ≤ J → Measurable (b i l))
    (hb : ∀ i l, l ≤ J → ∀ x, x ∈ Integral.cube n → |b i l x| ≤ B i * (1 / 2 : ℝ) ^ l)
    (hab : ∀ i l, l ≤ J → ∀ x, x ∈ Integral.cube n →
      |a i l x - b i l x| ≤ incrementError (ζ i) l) :
    |totalLevelRule a J - totalLevelRule b J| ≤
      2 * (J + 1 : ℝ) * 3 ^ (t - 1) * (∏ i, B i) * (∑ i, ζ i / B i) ∧
    |totalLevelRule a J - totalLevelRule b J| ≤
      2 * (t : ℝ) * (J + 1 : ℝ) * 3 ^ (t - 1) * (∏ i, B i) * ζmax := by
  have ha : ∀ i l, l ≤ J → ∀ x, x ∈ Integral.cube n →
      |a i l x| ≤ incrementMajorant (B i) (ζ i) l := by
    intro i l hl x hx
    have htri : |a i l x| ≤ |a i l x - b i l x| + |b i l x| := by
      simpa using abs_add_le (a i l x - b i l x) (b i l x)
    exact (htri.trans (add_le_add (hab i l hl x hx) (hb i l hl x hx))).trans_eq
      (by unfold incrementMajorant; ring)
  have hia : IntegrableOn (totalLevelIntegrand a J) (Integral.cube n) := by
    apply integrable_finset_sum
    intro ν hν
    have hνJ := (mem_totalLevels.mp hν).1
    exact integrableOn_product_of_bounds (fun i => a i (ν i))
      (fun i => incrementMajorant (B i) (ζ i) (ν i)) (fun i => hma i (ν i) (hνJ i))
      (fun i => ha i (ν i) (hνJ i))
  have hib : IntegrableOn (totalLevelIntegrand b J) (Integral.cube n) := by
    apply integrable_finset_sum
    intro ν hν
    have hνJ := (mem_totalLevels.mp hν).1
    exact integrableOn_product_of_bounds (fun i => b i (ν i))
      (fun i => B i * (1 / 2 : ℝ) ^ (ν i)) (fun i => hmb i (ν i) (hνJ i))
      (fun i => hb i (ν i) (hνJ i))
  rw [totalLevelRule_eq_integral a J (fun i l => incrementMajorant (B i) (ζ i) l) hma ha,
    totalLevelRule_eq_integral b J (fun i l => B i * (1 / 2 : ℝ) ^ l) hmb hb]
  have hrewrite : Integral.cubeIntegral (totalLevelIntegrand a J) -
      Integral.cubeIntegral (totalLevelIntegrand b J) =
      Integral.cubeIntegral (fun x => totalLevelIntegrand a J x - totalLevelIntegrand b J x) :=
    (integral_sub hia hib).symm
  rw [hrewrite]
  constructor
  · apply Integral.abs_cubeIntegral_le
    intro x hx
    exact (total_level_sample_perturbation (fun i l => a i l x) (fun i l => b i l x)
      B ζ ζmax hB hζ hζmax hprecision (fun i l hl => hb i l hl x hx)
      (fun i l hl => hab i l hl x hx)).1
  · apply Integral.abs_cubeIntegral_le
    intro x hx
    exact (total_level_sample_perturbation (fun i l => a i l x) (fun i l => b i l x)
      B ζ ζmax hB hζ hζmax hprecision (fun i l hl => hb i l hl x hx)
      (fun i l hl => hab i l hl x hx)).2

/-- A stored sample table is evaluated at each level's lower dyadic corner.
The same table value is therefore reused whenever a sample is reused. -/
def storedScopedStep {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (samples : (i : Fin t) → ℕ → LocalFunc (scopes i).card)
    (i : Fin t) (l : ℕ) (x : Fin n → ℝ) : ℝ :=
  (Dyadic.step (samples i l) l).toFun (Integral.restrictTo (scopes i) x)

/-- Perturbed increments computed from those actual stored step samples. -/
def storedScopedIncrement {n t : ℕ} (scopes : Fin t → Finset (Fin n))
    (samples : (i : Fin t) → ℕ → LocalFunc (scopes i).card)
    (i : Fin t) (l : ℕ) (x : Fin n → ℝ) : ℝ :=
  sampleIncrement (fun k => storedScopedStep scopes samples i k x) l

lemma scopedIncrement_eq_sampleIncrement {n t : ℕ}
    (scopes : Fin t → Finset (Fin n)) (f : (i : Fin t) → LocalFunc (scopes i).card)
    (i : Fin t) (l : ℕ) (x : Fin n → ℝ) :
    scopedIncrement scopes f i l x = sampleIncrement
      (fun k => (Dyadic.step (f i) k).toFun (Integral.restrictTo (scopes i) x)) l := by
  cases l <;> rfl

/-- Lemma 3.2 for the original scoped local functions and the actual stored
sample tables.  The only accuracy assumptions concern levels at most `J`
and the lower-corner samples that are actually used. -/
theorem dyadic_stored_sample_perturbation {n t r J : ℕ}
    (scopes : Fin t → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (f : (i : Fin t) → LocalFunc (scopes i).card) (A K : Fin t → ℝ)
    (hK : ∀ i, 0 ≤ K i) (hA : ∀ i, (f i).BoundBy (A i))
    (hf : ∀ i, (f i).LipLe (K i))
    (samples : (i : Fin t) → ℕ → LocalFunc (scopes i).card)
    (ζ : Fin t → ℝ) (ζmax : ℝ) (hζ : ∀ i, 0 ≤ ζ i) (hζmax : ∀ i, ζ i ≤ ζmax)
    (hprecision : ∀ i, 2 * (J + 1 : ℝ) * ζ i ≤ Dyadic.budget r (A i) (K i))
    (hsamples : ∀ i l, l ≤ J → ∀ y, y ∈ Integral.cube (scopes i).card →
      |(samples i l).toFun (Dyadic.corner l y) - (f i).toFun (Dyadic.corner l y)| ≤ ζ i) :
    |totalLevelRule (storedScopedIncrement scopes samples) J -
        totalLevelRule (scopedIncrement scopes f) J| ≤
      2 * (J + 1 : ℝ) * 3 ^ (t - 1) * (∏ i, Dyadic.budget r (A i) (K i)) *
        (∑ i, ζ i / Dyadic.budget r (A i) (K i)) ∧
    |totalLevelRule (storedScopedIncrement scopes samples) J -
        totalLevelRule (scopedIncrement scopes f) J| ≤
      2 * (t : ℝ) * (J + 1 : ℝ) * 3 ^ (t - 1) *
        (∏ i, Dyadic.budget r (A i) (K i)) * ζmax := by
  apply total_level_integral_perturbation
    (B := fun i => Dyadic.budget r (A i) (K i)) (ζ := ζ)
    (hB := fun i => Dyadic.one_le_budget r (A i) (K i))
    (hζ := hζ) (hζmax := hζmax) (hprecision := hprecision)
  · intro i l _
    have hm : ∀ k, Measurable (storedScopedStep scopes samples i k) := fun k =>
      (Dyadic.measurable_step (samples i k) k).comp (Integral.measurable_restrictTo (scopes i))
    cases l with
    | zero => exact hm 0
    | succ l => exact (hm (l + 1)).sub (hm l)
  · intro i l _
    exact (Dyadic.measurable_increment (f i) l).comp (Integral.measurable_restrictTo (scopes i))
  · intro i l _ x hx
    simpa only [scopedIncrement, one_div, inv_pow] using
      Dyadic.increment_bound (hscopes i) (hK i) (hA i) (hf i) l
        (Integral.restrictTo_mem_cube (scopes i) hx)
  · intro i l hl x hx
    rw [scopedIncrement_eq_sampleIncrement]
    apply sampleIncrement_error _ _ (ζ i) _ l hl
    intro k hk
    exact hsamples i k hk _ (Integral.restrictTo_mem_cube (scopes i) hx)

end Paper08.Quadrature
