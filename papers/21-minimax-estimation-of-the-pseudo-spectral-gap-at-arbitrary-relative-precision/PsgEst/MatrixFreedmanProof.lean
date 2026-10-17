import PsgEst.EdgeMatrix
import PsgEst.Regularizer
import PsgEst.ProbabilityThinning
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Finite-path ingredients for matrix Freedman's inequality

This file proves the finite conditional-expectation, Laplace/Markov and
Bennett optimization steps. It does not postulate the matrix concentration
inequality. The remaining genuinely noncommutative analysis is the finite
Lieb trace-exponential Jensen step, studied in `TraceExponential.lean`.
-/
open Matrix BigOperators Real Finset
namespace PsgEst
namespace MatrixFreedman

attribute [local instance] Classical.propDecidable

section FiniteConditioning
variable {Ω α : Type*} [Fintype Ω] [Fintype α] [DecidableEq α]

/-- Mass of one atom of a finite observation. -/
noncomputable def fiberMass (p : Ω → α) (w : Ω → ℝ) (a : α) : ℝ :=
  ∑ x, if p x = a then w x else 0

/-- Unnormalized integral over one atom of a finite observation. -/
noncomputable def fiberIntegral (p : Ω → α) (w f : Ω → ℝ) (a : α) : ℝ :=
  ∑ x, if p x = a then w x * f x else 0

/-- Conditional expectation, with value zero on zero-mass atoms. -/
noncomputable def finiteCondExp (p : Ω → α) (w f : Ω → ℝ) (x : Ω) : ℝ :=
  (fiberMass p w (p x))⁻¹ * fiberIntegral p w f (p x)

lemma fiberMass_nonneg (p : Ω → α) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (a : α) :
    0 ≤ fiberMass p w a := sum_nonneg (fun x _ => by split_ifs; exact hw x; exact le_rfl)

lemma weight_le_fiberMass (p : Ω → α) (w : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) (x : Ω) :
    w x ≤ fiberMass p w (p x) := by
  have h := single_le_sum (f := fun y => if p y = p x then w y else 0)
    (fun y _ => by dsimp only; split_ifs; exact hw y; exact le_rfl) (mem_univ x)
  simpa only [if_pos rfl] using h

lemma fiberIntegral_eq_zero_of_mass_zero (p : Ω → α) (w f : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x) (a : α) (ha : fiberMass p w a = 0) :
    fiberIntegral p w f a = 0 := by
  unfold fiberIntegral
  apply sum_eq_zero
  intro x _
  by_cases hx : p x = a
  · have h := weight_le_fiberMass p w hw x
    rw [hx, ha] at h
    have hz : w x = 0 := le_antisymm h (hw x)
    simp [hx, hz]
  · simp [hx]

/-- A finite sum is the sum of its observation fibers. -/
lemma sum_eq_sum_fibers (p : Ω → α) (f : Ω → ℝ) :
    ∑ x, f x = ∑ a : α, ∑ x : Ω, if p x = a then f x else 0 := by
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  simp [eq_comm]

/-- The finite tower identity, including null atoms. -/
theorem finiteCondExp_total (p : Ω → α) (w f : Ω → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ x, w x * finiteCondExp p w f x) = ∑ x, w x * f x := by
  calc _ = ∑ a : α, ∑ x : Ω, if p x = a then w x * finiteCondExp p w f x else 0 :=
      sum_eq_sum_fibers p _
    _ = ∑ a : α, fiberMass p w a * ((fiberMass p w a)⁻¹ * fiberIntegral p w f a) := by
      apply sum_congr rfl
      intro a _
      unfold fiberMass
      rw [sum_mul]
      apply sum_congr rfl
      intro x _
      by_cases hx : p x = a
      · simp [finiteCondExp, hx, fiberMass]
      · simp [hx]
    _ = ∑ a : α, fiberIntegral p w f a := by
      apply sum_congr rfl
      intro a _
      by_cases ha : fiberMass p w a = 0
      · rw [ha, zero_mul, fiberIntegral_eq_zero_of_mass_zero p w f hw a ha]
      · rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
    _ = _ := (sum_eq_sum_fibers p (fun x => w x*f x)).symm

/-- A conditional mean comparison on positive-mass atoms integrates to the
corresponding comparison of expectations. Null atoms contribute no mass. -/
theorem expectation_le_of_finiteCondExp_le (p : Ω → α) (w f g : Ω → ℝ)
    (hw : ∀ x, 0 ≤ w x)
    (hcond : ∀ x, 0 < fiberMass p w (p x) → finiteCondExp p w f x ≤ g x) :
    (∑ x, w x*f x) ≤ ∑ x, w x*g x := by
  rw [← finiteCondExp_total p w f hw]
  apply sum_le_sum
  intro x _
  by_cases hx : w x = 0
  · simp [hx]
  · have hxpos : 0 < w x := lt_of_le_of_ne (hw x) (Ne.symm hx)
    exact mul_le_mul_of_nonneg_left (hcond x (hxpos.trans_le (weight_le_fiberMass p w hw x))) (hw x)

end FiniteConditioning

/-- Freeze a path after time `t`; equality of these projections is exactly
membership in one atom of the original prefix filtration. -/
def prefixProjection {d m : ℕ} (t : ℕ) (Y : Fin (m+1) → Fin d) : Fin (m+1) → Fin d :=
  fun k => Y ⟨min k.val t, lt_of_le_of_lt (min_le_left _ _) k.isLt⟩

lemma samePrefix_iff_projection {d m : ℕ} (t : ℕ) (Y W : Fin (m+1) → Fin d) :
    samePrefix t Y W ↔ prefixProjection t Y = prefixProjection t W := by
  constructor
  · intro h
    funext k
    exact h ⟨min k.val t, lt_of_le_of_lt (min_le_left _ _) k.isLt⟩ (min_le_right _ _)
  · intro h k hk
    have hi := congrFun h k
    simpa only [prefixProjection, min_eq_left hk] using hi

noncomputable def pathExpectation {d m : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (f : (Fin (m+1) → Fin d) → ℝ) : ℝ := ∑ Y, pathProb Q.P mu Y * f Y

noncomputable def pathScalarCondExp {d m : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (t : ℕ) (f : (Fin (m+1) → Fin d) → ℝ) (Y : Fin (m+1) → Fin d) : ℝ :=
  (eventProb Q.P mu (samePrefix t Y))⁻¹ *
    ∑ W ∈ univ.filter (samePrefix t Y), pathProb Q.P mu W * f W

lemma prefix_atom_mass {d m : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (t : ℕ) (Y : Fin (m+1) → Fin d) :
    fiberMass (prefixProjection t) (pathProb Q.P mu) (prefixProjection t Y) =
      eventProb Q.P mu (samePrefix t Y) := by
  unfold fiberMass eventProb pathMeasure
  rw [sum_filter]
  apply sum_congr rfl
  intro W _
  simp only [samePrefix_iff_projection, eq_comm]

lemma pathScalarCondExp_eq_finite {d m : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (t : ℕ) (f : (Fin (m+1) → Fin d) → ℝ) (Y : Fin (m+1) → Fin d) :
    pathScalarCondExp Q mu t f Y =
      finiteCondExp (prefixProjection t) (pathProb Q.P mu) f Y := by
  unfold pathScalarCondExp finiteCondExp
  rw [prefix_atom_mass]
  congr 1
  unfold fiberIntegral
  rw [sum_filter]
  apply sum_congr rfl
  intro W _
  simp only [samePrefix_iff_projection, eq_comm]

/-- Tower identity for the same finite prefix conditional expectation used by
the matrix Freedman statement. -/
theorem pathScalarCondExp_total {d m : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (t : ℕ) (f : (Fin (m+1) → Fin d) → ℝ) :
    pathExpectation Q mu (pathScalarCondExp Q mu t f) = pathExpectation Q mu f := by
  unfold pathExpectation
  simp_rw [pathScalarCondExp_eq_finite]
  exact finiteCondExp_total _ _ _ (pathProb_nonneg Q.P mu Q.nonneg hmu)

/-- Integrating a local prefix conditional inequality is valid without
conditioning the original process on any additional event. -/
theorem pathExpectation_le_of_conditional {d m : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (t : ℕ) (f g : (Fin (m+1) → Fin d) → ℝ)
    (hcond : ∀ Y, 0 < eventProb Q.P mu (samePrefix t Y) → pathScalarCondExp Q mu t f Y ≤ g Y) :
    pathExpectation Q mu f ≤ pathExpectation Q mu g := by
  apply expectation_le_of_finiteCondExp_le (prefixProjection t) _ _ _
    (pathProb_nonneg Q.P mu Q.nonneg hmu)
  intro Y hY
  rw [prefix_atom_mass] at hY
  simpa only [pathScalarCondExp_eq_finite] using hcond Y hY

/-- Finite induction for the expectation of a potential process. -/
theorem path_potential_expectation_le {d m : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (N : ℕ) (F : ℕ → (Fin (m+1) → Fin d) → ℝ)
    (hstep : ∀ k < N, ∀ Y, 0 < eventProb Q.P mu (samePrefix k Y) →
      pathScalarCondExp Q mu k (F (k+1)) Y ≤ F k Y) :
    pathExpectation Q mu (F N) ≤ pathExpectation Q mu (F 0) := by
  induction N with
  | zero => exact le_rfl
  | succ N ih =>
    exact (pathExpectation_le_of_conditional Q mu hmu N _ _ (hstep N (Nat.lt_succ_self N))).trans
      (ih (fun k hk => hstep k (Nat.lt.step hk)))

/-- Finite Markov inequality for a nonnegative path potential. -/
theorem eventProb_le_expectation_div {d m : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (F : (Fin (m+1) → Fin d) → ℝ)
    (hF : ∀ Y, 0 ≤ F Y) (E : (Fin (m+1) → Fin d) → Prop)
    (a : ℝ) (ha : 0 < a) (hE : ∀ Y, E Y → a ≤ F Y) :
    eventProb Q.P mu E ≤ pathExpectation Q mu F / a := by
  apply (le_div_iff₀ ha).mpr
  unfold eventProb pathMeasure pathExpectation
  rw [sum_filter, sum_mul]
  apply sum_le_sum
  intro Y _
  have hw := pathProb_nonneg Q.P mu Q.nonneg hmu Y
  by_cases h : E Y
  · simp only [if_pos h]
    exact mul_le_mul_of_nonneg_left (hE Y h) hw
  · simp only [if_neg h, zero_mul]
    exact mul_nonneg hw (hF Y)

/-- The Laplace/Markov rearrangement used after the trace-potential bound. -/
theorem eventProb_le_dim_exp {d m : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (F : (Fin (m+1) → Fin d) → ℝ)
    (hF : ∀ Y, 0 ≤ F Y) (E : (Fin (m+1) → Fin d) → Prop)
    (D a : ℝ) (hmean : pathExpectation Q mu F ≤ D)
    (hE : ∀ Y, E Y → exp a ≤ F Y) :
    eventProb Q.P mu E ≤ D * exp (-a) := by
  calc _ ≤ pathExpectation Q mu F / exp a := eventProb_le_expectation_div Q mu hmu F hF E _ (exp_pos a) hE
    _ ≤ D / exp a := div_le_div_of_nonneg_right hmean (exp_pos a).le
    _ = _ := by rw [div_eq_mul_inv, ← exp_neg]

/-- The scalar Bennett rate used by the optimal exponential parameter. -/
noncomputable def bennettRate (x : ℝ) : ℝ := (1+x)*log (1+x)-x

lemma bennettRate_hasDerivAt (x : ℝ) (hx : 0 ≤ x) :
    HasDerivAt bennettRate (log (1+x)) x := by
  have hp : 0 < 1+x := by linarith
  have hlin : HasDerivAt (fun y : ℝ => 1+y) 1 x := (hasDerivAt_id x).const_add 1
  have hlog := hlin.log hp.ne'
  have h := (hlin.mul hlog).sub (hasDerivAt_id x)
  convert h using 1
  field_simp
  <;> ring

/-- The exact scalar inequality responsible for the denominator `v+Ru/3`.
A first-derivative argument uses `2x/(x+2) ≤ log(1+x)`. -/
theorem bennettRate_lower (x : ℝ) (hx : 0 ≤ x) :
    x^2 / (2*(1+x/3)) ≤ bennettRate x := by
  let F : ℝ → ℝ := fun y => 2*(y+3)*bennettRate y-3*y^2
  have hderiv (y : ℝ) (hy : 0 ≤ y) :
      HasDerivAt F (4*(y+2)*log (1+y)-8*y) y := by
    have hlin : HasDerivAt (fun z : ℝ => z+3) 1 y := (hasDerivAt_id y).add_const 3
    have h := ((hlin.mul (bennettRate_hasDerivAt y hy)).const_mul 2).sub
      (((hasDerivAt_id y).pow 2).const_mul 3)
    convert h using 1
    · ext z
      dsimp [F]
      ring
    · dsimp only [bennettRate, id_eq]
      norm_num
      ring
  have hmono : MonotoneOn F (Set.Ici 0) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    · intro y hy
      exact (hderiv y hy).continuousAt.continuousWithinAt
    · intro y hy
      have hy' : 0 ≤ y := by rw [interior_Ici, Set.mem_Ioi] at hy; exact hy.le
      exact (hderiv y hy').hasDerivWithinAt
    · intro y hy
      have hy' : 0 ≤ y := by rw [interior_Ici, Set.mem_Ioi] at hy; exact hy.le
      have hlog := Real.le_log_one_add_of_nonneg hy'
      have hp : 0 < y+2 := by linarith
      have hl := (div_le_iff₀ hp).mp hlog
      nlinarith
  have hF := hmono (by simp) (by exact hx) hx
  have hzero : F 0 = 0 := by simp [F, bennettRate]
  rw [hzero] at hF
  have hp : 0 < 2*(1+x/3) := by positivity
  apply (div_le_iff₀ hp).mpr
  dsimp only [F] at hF
  nlinarith

/-- The positive exponential parameter minimizing the Bennett bound. -/
noncomputable def optimalTheta (R u v : ℝ) : ℝ := log (1+R*u/v)/R

/-- The true bounded-increment exponential coefficient. -/
noncomputable def bennettCoefficient (R θ : ℝ) : ℝ := (exp (θ*R)-θ*R-1)/R^2

lemma optimalTheta_pos (R u v : ℝ) (hR : 0 < R) (hu : 0 < u) (hv : 0 < v) :
    0 < optimalTheta R u v := by
  unfold optimalTheta
  have hpos : 0 < R*u/v := div_pos (mul_pos hR hu) hv
  exact div_pos (Real.log_pos (by linarith)) hR

lemma bennettCoefficient_nonneg (R θ : ℝ) : 0 ≤ bennettCoefficient R θ := by
  apply div_nonneg _ (sq_nonneg _)
  have h := Real.add_one_le_exp (θ*R)
  linarith

/-- Exact value of the exponential objective at the optimizing parameter. -/
theorem optimal_exponent_identity (R u v : ℝ) (hR : 0 < R) (hu : 0 < u) (hv : 0 < v) :
    -(optimalTheta R u v)*u + bennettCoefficient R (optimalTheta R u v)*v =
      -(v/R^2)*bennettRate (R*u/v) := by
  have hp : 0 < 1+R*u/v := by positivity
  have hθR : optimalTheta R u v*R = log (1+R*u/v) := by
    unfold optimalTheta
    field_simp
  unfold bennettCoefficient
  rw [hθR, exp_log hp]
  unfold optimalTheta bennettRate
  field_simp
  <;> ring

/-- The optimized Bennett exponent implies the paper's Bernstein/Freedman
exponent with the sharp factor `1/3` in the denominator. -/
theorem optimal_exponent_le (R u v : ℝ) (hR : 0 < R) (hu : 0 < u) (hv : 0 < v) :
    -(optimalTheta R u v)*u + bennettCoefficient R (optimalTheta R u v)*v ≤
      -(u^2)/(2*(v+R*u/3)) := by
  rw [optimal_exponent_identity R u v hR hu hv]
  have hRate := bennettRate_lower (R*u/v) (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hRate (show 0 ≤ v/R^2 by positivity)
  have heq : v/R^2*((R*u/v)^2/(2*(1+(R*u/v)/3))) = u^2/(2*(v+R*u/3)) := by
    field_simp
    <;> ring
  rw [heq] at hmul
  convert neg_le_neg hmul using 1 <;> ring

/-- Scalar optimization of a Laplace bound. The premise is a bound on the
expectation of a nonnegative potential, rather than a tail bound. -/
theorem eventProb_le_freedman_of_potential {d m : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (F : (Fin (m+1) → Fin d) → ℝ)
    (hF : ∀ Y, 0 ≤ F Y) (E : (Fin (m+1) → Fin d) → Prop)
    (D R u v : ℝ) (hD : 0 ≤ D) (hR : 0 < R) (hu : 0 < u) (hv : 0 < v)
    (hmean : pathExpectation Q mu F ≤ D)
    (hE : ∀ Y, E Y → exp (optimalTheta R u v*u-bennettCoefficient R (optimalTheta R u v)*v) ≤ F Y) :
    eventProb Q.P mu E ≤ D*exp (-(u^2)/(2*(v+R*u/3))) := by
  calc _ ≤ D*exp (-(optimalTheta R u v*u-bennettCoefficient R (optimalTheta R u v)*v)) :=
      eventProb_le_dim_exp Q mu hmu F hF E D _ hmean hE
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hD
      apply Real.exp_le_exp.mpr
      convert optimal_exponent_le R u v hR hu hv using 1 <;> ring

lemma samePrefix_refl {d m : ℕ} (t : ℕ) (Y : Fin (m+1) → Fin d) : samePrefix t Y Y :=
  fun _ _ => rfl

lemma samePrefix_symm {d m : ℕ} {t : ℕ} {Y W : Fin (m+1) → Fin d}
    (h : samePrefix t Y W) : samePrefix t W Y := fun k hk => (h k hk).symm

lemma samePrefix_trans {d m : ℕ} {t : ℕ} {Y W V : Fin (m+1) → Fin d}
    (hYW : samePrefix t Y W) (hWV : samePrefix t W V) : samePrefix t Y V :=
  fun k hk => (hYW k hk).trans (hWV k hk)

lemma pathMatrixCondExp_adapted {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (t : ℕ) (A : (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (Y W : Fin (m+1) → Fin d) (h : samePrefix t Y W) :
    pathMatrixCondExp Q mu t A Y = pathMatrixCondExp Q mu t A W := by
  have heq : samePrefix t Y = samePrefix t W := by
    funext V
    apply propext
    exact ⟨fun hYV => samePrefix_trans (samePrefix_symm h) hYV,
      fun hWV => samePrefix_trans h hWV⟩
  unfold pathMatrixCondExp
  rw [heq]

lemma pathMatrixCondExp_entry {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (t : ℕ) (A : (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (Y : Fin (m+1) → Fin d) (a b : Fin D) :
    pathMatrixCondExp Q mu t A Y a b = pathScalarCondExp Q mu t (fun W => A W a b) Y := by
  unfold pathMatrixCondExp pathScalarCondExp
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]

lemma pathMatrixCondExp_total {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (t : ℕ)
    (A : (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ) :
    (∑ Y, pathProb Q.P mu Y • pathMatrixCondExp Q mu t A Y) =
      ∑ Y, pathProb Q.P mu Y • A Y := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, pathMatrixCondExp_entry]
  exact pathScalarCondExp_total Q mu hmu t (fun Y => A Y a b)

lemma pathMatrixCondExp_neg {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (t : ℕ) (A : (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (Y : Fin (m+1) → Fin d) :
    pathMatrixCondExp Q mu t (fun W => -A W) Y = -pathMatrixCondExp Q mu t A Y := by
  unfold pathMatrixCondExp
  simp only [smul_neg, sum_neg_distrib]

lemma posSemidef_finset_sum {α ι : Type*} [Fintype ι] (s : Finset α)
    (A : α → Matrix ι ι ℝ) (hA : ∀ a, (A a).PosSemidef) : (∑ a ∈ s, A a).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℝ).PosSemidef)
  | @insert a s ha ih =>
    rw [sum_insert ha]
    exact (hA a).add ih

/-- The conditional second moment is PSD on every prefix atom, including
zero-mass atoms. -/
theorem conditional_square_posSemidef {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i) (t : ℕ)
    (A : (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (hA : ∀ Y, (A Y).IsHermitian) (Y : Fin (m+1) → Fin d) :
    (pathMatrixCondExp Q mu t (fun W => A W * A W) Y).PosSemidef := by
  have hmass : 0 ≤ eventProb Q.P mu (samePrefix t Y) :=
    pathMeasure_nonneg Q.P mu Q.nonneg hmu _
  unfold pathMatrixCondExp
  apply Matrix.PosSemidef.smul _ (inv_nonneg.mpr hmass)
  exact posSemidef_finset_sum _ _ (fun W =>
    (hermitian_square_posSemidef _ (hA W)).smul (pathProb_nonneg Q.P mu Q.nonneg hmu W))

/-- Predictable quadratic variation is unchanged by negating every increment. -/
theorem predictableVariationNorm_neg {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (Y : Fin (m+1) → Fin d) :
    predictableVariationNorm Q mu (fun t W => -Z t W) Y = predictableVariationNorm Q mu Z Y := by
  simp only [predictableVariationNorm, neg_mul_neg]

/-- The terminal martingale sum norm is also unchanged by negation. -/
theorem martingaleSumNorm_neg {d m D : ℕ}
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (Y : Fin (m+1) → Fin d) :
    martingaleSumNorm (fun t W => -Z t W) Y = martingaleSumNorm Z Y := by
  simp only [martingaleSumNorm, sum_neg_distrib, euclideanMatrixNorm, map_neg, norm_neg]

/-- Actual partial sum of an increment array, on the fixed terminal sample
space. Values after the available horizon are harmlessly truncated. -/
noncomputable def prefixSum {Ω A : Type*} [AddCommMonoid A] {m : ℕ}
    (Z : Fin m → Ω → A) (k : ℕ) (Y : Ω) : A :=
  ∑ t : Fin m, if t.val < k then Z t Y else 0

@[simp] lemma prefixSum_zero {Ω A : Type*} [AddCommMonoid A] {m : ℕ}
    (Z : Fin m → Ω → A) (Y : Ω) : prefixSum Z 0 Y = 0 := by simp [prefixSum]

@[simp] lemma prefixSum_terminal {Ω A : Type*} [AddCommMonoid A] {m : ℕ}
    (Z : Fin m → Ω → A) (Y : Ω) : prefixSum Z m Y = ∑ t : Fin m, Z t Y := by
  simp only [prefixSum, Fin.is_lt, if_true]

/-- Exact partial-sum recursion on the terminal path space. -/
lemma prefixSum_succ {Ω A : Type*} [AddCommMonoid A] {m : ℕ}
    (Z : Fin m → Ω → A) (k : ℕ) (hk : k < m) (Y : Ω) :
    prefixSum Z (k+1) Y = prefixSum Z k Y + Z ⟨k,hk⟩ Y := by
  classical
  have hterm (t : Fin m) : (if t.val < k+1 then Z t Y else 0) =
      (if t.val < k then Z t Y else 0) + (if t = ⟨k,hk⟩ then Z ⟨k,hk⟩ Y else 0) := by
    by_cases ht : t.val < k
    · have hne : t ≠ ⟨k,hk⟩ := by intro h; have he := congrArg Fin.val h; dsimp at he; omega
      simp [ht, hne, show t.val < k+1 by omega]
    · by_cases he : t = ⟨k,hk⟩
      · subst t
        simp
      · have hval : t.val ≠ k := by intro h; exact he (Fin.ext h)
        simp [ht, he, show ¬ t.val < k+1 by omega]
  unfold prefixSum
  simp_rw [hterm]
  rw [sum_add_distrib]
  simp

lemma prefixSum_isHermitian {d m D : ℕ}
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (hZ : ∀ t Y, (Z t Y).IsHermitian) (k : ℕ) (Y : Fin (m+1) → Fin d) :
    (prefixSum Z k Y).IsHermitian := by
  change (∑ t : Fin m, if t.val < k then Z t Y else 0)ᴴ = _
  rw [Matrix.conjTranspose_sum]
  apply sum_congr rfl
  intro t _
  split_ifs
  · exact hZ t Y
  · exact Matrix.isHermitian_zero

/-- The martingale sum up to time `k` is measurable with respect to the
actual observation prefix at time `k`. -/
theorem prefixSum_adapted {d m D : ℕ}
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (hZ : ∀ t Y W, samePrefix (t.val+1) Y W → Z t Y = Z t W)
    (k : ℕ) (Y W : Fin (m+1) → Fin d) (h : samePrefix k Y W) :
    prefixSum Z k Y = prefixSum Z k W := by
  unfold prefixSum
  apply sum_congr rfl
  intro t _
  split_ifs with ht
  · exact hZ t Y W (fun i hi => h i (by omega))
  · rfl

/-- Actual predictable quadratic variation, before taking its norm. -/
noncomputable def partialVariation {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (k : ℕ) (Y : Fin (m+1) → Fin d) : Matrix (Fin D) (Fin D) ℝ :=
  prefixSum (fun t W => pathMatrixCondExp Q mu t.val (fun V => Z t V*Z t V) W) k Y

@[simp] lemma partialVariation_zero {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (Y : Fin (m+1) → Fin d) : partialVariation Q mu Z 0 Y = 0 := by
  exact prefixSum_zero _ Y

lemma partialVariation_succ {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (k : ℕ) (hk : k < m) (Y : Fin (m+1) → Fin d) :
    partialVariation Q mu Z (k+1) Y = partialVariation Q mu Z k Y +
      pathMatrixCondExp Q mu k (fun V => Z ⟨k,hk⟩ V * Z ⟨k,hk⟩ V) Y :=
  prefixSum_succ _ k hk Y

/-- Predictable variation at time `k+1` is already determined by the prefix
at time `k`; this is the previsibility needed in Lieb's conditional step. -/
theorem partialVariation_previsible {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (k : ℕ) (Y W : Fin (m+1) → Fin d) (h : samePrefix k Y W) :
    partialVariation Q mu Z (k+1) Y = partialVariation Q mu Z (k+1) W := by
  unfold partialVariation prefixSum
  apply sum_congr rfl
  intro t _
  split_ifs with ht
  · exact pathMatrixCondExp_adapted Q mu t.val _ Y W (fun i hi => h i (by omega))
  · rfl

/-- Every actual partial predictable quadratic variation is PSD. -/
theorem partialVariation_posSemidef {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (hmu : ∀ i, 0 ≤ mu i)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (hZ : ∀ t Y, (Z t Y).IsHermitian) (k : ℕ) (Y : Fin (m+1) → Fin d) :
    (partialVariation Q mu Z k Y).PosSemidef := by
  unfold partialVariation prefixSum
  apply posSemidef_sum
  intro t
  split_ifs
  · exact conditional_square_posSemidef Q mu hmu t.val (Z t) (hZ t) Y
  · exact Matrix.PosSemidef.zero

lemma partialVariation_terminal_norm {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (Y : Fin (m+1) → Fin d) :
    euclideanMatrixNorm (partialVariation Q mu Z m Y) = predictableVariationNorm Q mu Z Y := by
  simp only [partialVariation, prefixSum_terminal, predictableVariationNorm]

/-- Centering, predictability and variation are preserved under the sign
change used to pass from one-sided spectral tails to the two-sided norm tail. -/
theorem neg_process_hypotheses {d m D : ℕ} (Q : Stoch d) (mu : Fin d → ℝ)
    (Z : Fin m → (Fin (m+1) → Fin d) → Matrix (Fin D) (Fin D) ℝ)
    (R : ℝ) (hsa : ∀ t Y, (Z t Y).IsHermitian)
    (hadapted : ∀ t Y W, samePrefix (t.val+1) Y W → Z t Y = Z t W)
    (hcentered : ∀ t Y, pathMatrixCondExp Q mu t.val (Z t) Y = 0)
    (hbound : ∀ t Y, euclideanMatrixNorm (Z t Y) ≤ R) :
    (∀ t Y, (-Z t Y).IsHermitian) ∧
    (∀ t Y W, samePrefix (t.val+1) Y W → -Z t Y = -Z t W) ∧
    (∀ t Y, pathMatrixCondExp Q mu t.val (fun W => -Z t W) Y = 0) ∧
    (∀ t Y, euclideanMatrixNorm (-Z t Y) ≤ R) := by
  refine ⟨fun t Y => (hsa t Y).neg, ?_, ?_, ?_⟩
  · intro t Y W h
    rw [hadapted t Y W h]
  · intro t Y
    rw [pathMatrixCondExp_neg, hcentered, neg_zero]
  · intro t Y
    simpa only [euclideanMatrixNorm, map_neg, norm_neg] using hbound t Y

/-- An actual finite spectral bound controls the Euclidean operator norm. -/
theorem matrix_norm_le_of_eigenvalue_bounds {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ)
    (hS : S.IsHermitian) (R : ℝ) (hR : 0 ≤ R)
    (heig : ∀ i, |hS.eigenvalues i| ≤ R) : euclideanMatrixNorm S ≤ R := by
  have hupper : (R • (1 : Matrix (Fin D) (Fin D) ℝ) - S).PosSemidef := by
    have hp : (spectralMultiplier hS (fun i => R-hS.eigenvalues i)).PosSemidef :=
      (Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (le_abs_self _ |>.trans (heig i)))).mul_mul_conjTranspose_same _
    have heq : spectralMultiplier hS (fun i => R-hS.eigenvalues i) = R • (1 : Matrix (Fin D) (Fin D) ℝ) - S := by
      unfold spectralMultiplier
      rw [← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]
      change spectralMultiplier hS (fun _ => R) - spectralMultiplier hS hS.eigenvalues = _
      rw [spectralMultiplier_const, spectralMultiplier_eigenvalues]
    rwa [heq] at hp
  have hlower : (R • (1 : Matrix (Fin D) (Fin D) ℝ) + S).PosSemidef := by
    have hp : (spectralMultiplier hS (fun i => R+hS.eigenvalues i)).PosSemidef := by
      apply Matrix.PosSemidef.mul_mul_conjTranspose_same
      apply Matrix.PosSemidef.diagonal
      intro i
      change 0 ≤ R+hS.eigenvalues i
      have hi := abs_le.mp (heig i)
      linarith
    rwa [spectralMultiplier_add, spectralMultiplier_const, spectralMultiplier_eigenvalues] at hp
  apply matrixEuclideanNorm_le_of_quadratic S hS R hR
  intro x
  have hu := hupper.2 x
  have hl := hlower.2 x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul] at hu hl
  rw [abs_le]
  constructor <;> linarith

/-- A norm excursion of a self-adjoint matrix is covered by a positive
spectral excursion of the matrix or its negative. This supplies exactly the
two events needed for the norm form of matrix Freedman. -/
theorem norm_event_covered_by_signed_eigenvalues {D : ℕ} (S : Matrix (Fin D) (Fin D) ℝ)
    (hS : S.IsHermitian) (u : ℝ) (hu : 0 < u) (hnorm : u ≤ euclideanMatrixNorm S) :
    (∃ i, u ≤ hS.eigenvalues i) ∨ (∃ i, u ≤ hS.neg.eigenvalues i) := by
  classical
  cases D with
  | zero =>
    have hzero : S = 0 := Subsingleton.elim _ _
    simp only [hzero, euclideanMatrixNorm, map_zero, norm_zero] at hnorm
    linarith
  | succ D =>
    obtain ⟨i, -, hmax⟩ := Finset.exists_max_image
      (s := (univ : Finset (Fin (D+1)))) (f := fun j => |hS.eigenvalues j|) univ_nonempty
    have hbound := matrix_norm_le_of_eigenvalue_bounds S hS |hS.eigenvalues i| (abs_nonneg _)
      (fun j => hmax j (mem_univ j))
    have hi : u ≤ |hS.eigenvalues i| := hnorm.trans hbound
    by_cases hs : 0 ≤ hS.eigenvalues i
    · exact Or.inl ⟨i, by simpa only [abs_of_nonneg hs] using hi⟩
    · right
      have hm : -hS.eigenvalues i ∈ spectrum ℝ (-S) := by
        rw [← spectrum.neg_eq]
        simpa only [Set.mem_neg, neg_neg] using hS.eigenvalues_mem_spectrum_real i
      rw [hS.neg.spectrum_real_eq_range_eigenvalues] at hm
      obtain ⟨j, hj⟩ := hm
      refine ⟨j, ?_⟩
      rw [hj]
      simpa only [abs_of_neg (lt_of_not_ge hs)] using hi

end MatrixFreedman
end PsgEst
