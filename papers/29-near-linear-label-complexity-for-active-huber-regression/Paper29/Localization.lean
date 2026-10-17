import Paper29.Geometry
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

/-!
# Deterministic localization for the second batch

This file proves the deterministic implications (3.39)--(3.44). The centered
sampling event, pilot bound, and minimizing points are explicit hypotheses;
no probability or sampling-complexity claim is made here.
-/
noncomputable section
open scoped BigOperators

namespace Paper29.Localization

/-- Huber loss is continuous, including the two joining points. -/
theorem continuous_huber : Continuous huber := by
  apply Continuous.if_le (by fun_prop) (by fun_prop)
    continuous_abs continuous_const
  intro t ht
  have ht2 : t ^ 2 = 1 := by nlinarith [sq_abs t]
  simp only [ht2, ht]
  norm_num

/-- Every affine quadratic support with slope in `[-1,1]` lies below Huber. -/
theorem huber_support (u t : ℝ) (hu : |u| ≤ 1) :
    u * t - u ^ 2 / 2 ≤ huber t := by
  by_cases ht : |t| ≤ 1
  · rw [huber, if_pos ht]
    nlinarith [sq_nonneg (t - u)]
  · rw [huber, if_neg ht]
    have hut := le_abs_self (u * t)
    rw [abs_mul] at hut
    have hprod := mul_nonneg (sub_nonneg.mpr hu)
      (sub_nonneg.mpr (le_of_lt (lt_of_not_ge ht)))
    nlinarith [sq_abs u, sq_nonneg (1 - |u|)]

/-- A support of slope in `[-1,1]` attains the Huber value at each point. -/
theorem huber_support_attained (t : ℝ) :
    ∃ u : ℝ, |u| ≤ 1 ∧ huber t = u * t - u ^ 2 / 2 := by
  by_cases ht : |t| ≤ 1
  · refine ⟨t, ht, ?_⟩
    rw [huber, if_pos ht]
    ring
  · by_cases ht0 : 0 ≤ t
    · refine ⟨1, by norm_num, ?_⟩
      rw [huber, if_neg ht, abs_of_nonneg ht0]
      ring
    · refine ⟨-1, by norm_num, ?_⟩
      rw [huber, if_neg ht, abs_of_neg (lt_of_not_ge ht0)]
      ring

/-- Convexity of the actual width-one Huber loss. -/
theorem convex_huber : ConvexOn ℝ Set.univ huber := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  obtain ⟨u, hu, he⟩ := huber_support_attained (a * x + b * y)
  have hsx := mul_le_mul_of_nonneg_left (huber_support u x hu) ha
  have hsy := mul_le_mul_of_nonneg_left (huber_support u y hu) hb
  have hcancel : a * (u ^ 2 / 2) + b * (u ^ 2 / 2) = u ^ 2 / 2 := by
    rw [← add_mul, hab, one_mul]
  rw [he]
  nlinarith

/-- A finite weighted Huber objective with fixed residual offset. -/
def shifted {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w z : Fin n → ℝ) (h : Fin d → ℝ) : ℝ :=
  weightedHuber w (fun i => (A.mulVec h) i + z i)

/-- Every finite weighted sampled Huber objective is convex when its weights
are nonnegative. Thus no abstract convexity oracle is needed in localization. -/
theorem convex_shifted {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (v z : Fin n → ℝ) (hv : ∀ i, 0 ≤ v i) :
    ConvexOn ℝ Set.univ (shifted A v z) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [smul_eq_mul]
  unfold shifted weightedHuber
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  calc
    (∑ i, v i * huber (a * (A.mulVec x) i + b * (A.mulVec y) i + z i)) ≤
        ∑ i, v i * (a * huber ((A.mulVec x) i + z i) +
          b * huber ((A.mulVec y) i + z i)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (hv i)
      have hc := convex_huber.2 (Set.mem_univ ((A.mulVec x) i + z i))
        (Set.mem_univ ((A.mulVec y) i + z i)) ha hb hab
      simp only [smul_eq_mul] at hc
      have he : a * ((A.mulVec x) i + z i) + b * ((A.mulVec y) i + z i) =
          a * (A.mulVec x) i + b * (A.mulVec y) i + z i := by
        nlinarith [congrArg (fun t : ℝ => t * z i) hab]
      rwa [he] at hc
    _ = a * (∑ i, v i * huber ((A.mulVec x) i + z i)) +
        b * (∑ i, v i * huber ((A.mulVec y) i + z i)) := by
      simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

/-- The corresponding unshifted Huber radius function. -/
def phi {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w : Fin n → ℝ) (h : Fin d → ℝ) : ℝ :=
  weightedHuber w (A.mulVec h)

@[simp] theorem phi_zero {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w : Fin n → ℝ) : phi A w 0 = 0 := by
  simp [phi, weightedHuber, Matrix.mulVec]

@[simp] theorem shifted_zero {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w z : Fin n → ℝ) : shifted A w z 0 = weightedHuber w z := by
  simp [shifted, Matrix.mulVec]

theorem shifted_nonneg {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w z : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (h : Fin d → ℝ) :
    0 ≤ shifted A w z h := weightedHuber_nonneg _ _ hw

theorem phi_nonneg {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (h : Fin d → ℝ) :
    0 ≤ phi A w h := weightedHuber_nonneg _ _ hw

/-- The radius is continuous along every segment from the origin. -/
theorem continuous_phi_segment {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w : Fin n → ℝ) (h : Fin d → ℝ) :
    Continuous (fun t : ℝ => phi A w (t • h)) := by
  unfold phi weightedHuber Matrix.mulVec dotProduct
  apply continuous_finset_sum
  intro i hi
  apply continuous_const.mul
  apply continuous_huber.comp
  apply continuous_finset_sum
  intro j hj
  change Continuous (fun t : ℝ => A i j * (t * h j))
  fun_prop

/-- Triangle inequality in residual coordinates. -/
theorem radius_triangle {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w z : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (h : Fin d → ℝ) :
    Real.sqrt (phi A w h) ≤ Real.sqrt (shifted A w z h) +
      Real.sqrt (shifted A w z 0) := by
  have ht := weightedHuber_triangle w
    (fun i => (A.mulVec h) i + z i) (fun i => -z i) hw
  have he : (fun i => (A.mulVec h) i + z i + -z i) = A.mulVec h := by
    funext i
    ring
  rw [he, weightedHuber_neg] at ht
  simpa only [phi, shifted_zero] using ht

/-- Equation (3.39): any point whose true objective is no larger than the
pilot objective lies in the unshifted ball of radius four times that value. -/
theorem comparator_in_four_radius {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w z : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (h : Fin d → ℝ)
    {R : ℝ} (hR : shifted A w z 0 = R)
    (hcomp : shifted A w z h ≤ R) : phi A w h ≤ 4 * R := by
  have hR0 : 0 ≤ R := hR ▸ shifted_nonneg A w z hw 0
  have htri := radius_triangle A w z hw h
  rw [hR] at htri
  have hs : Real.sqrt (shifted A w z h) ≤ Real.sqrt R := Real.sqrt_le_sqrt hcomp
  have hrad : Real.sqrt (phi A w h) ≤ 2 * Real.sqrt R := by linarith
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ 2 * Real.sqrt R)).mpr hrad
  rw [Real.sq_sqrt (phi_nonneg A w hw h), mul_pow, Real.sq_sqrt hR0] at hsq
  norm_num at hsq
  exact hsq

/-- Equation (3.40): the true centered objective has gap at least `8 * R`
on the unshifted boundary `phi = 16 * R`. -/
theorem boundary_true_gap {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w z : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (h : Fin d → ℝ)
    {R : ℝ} (hR : shifted A w z 0 = R) (hR0 : 0 ≤ R)
    (hboundary : phi A w h = 16 * R) :
    8 * R ≤ shifted A w z h - shifted A w z 0 := by
  have hsqrt : Real.sqrt (phi A w h) = 4 * Real.sqrt R := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (phi_nonneg A w hw h), mul_pow, Real.sq_sqrt hR0, hboundary]
    ring
  have htri := radius_triangle A w z hw h
  rw [hsqrt, hR] at htri
  have hlower : 3 * Real.sqrt R ≤ Real.sqrt (shifted A w z h) := by linarith
  have hsq := (sq_le_sq₀ (by positivity : 0 ≤ 3 * Real.sqrt R)
    (Real.sqrt_nonneg _)).mpr hlower
  rw [mul_pow, Real.sq_sqrt hR0,
    Real.sq_sqrt (shifted_nonneg A w z hw h)] at hsq
  rw [hR]
  nlinarith

/-- The centered uniform event (3.27) at the radius used in the proof. -/
def CenteredEvent {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w v z : Fin n → ℝ) (η R : ℝ) : Prop :=
  ∀ h, phi A w h ≤ 16 * R →
    |(shifted A v z h - shifted A v z 0) -
      (shifted A w z h - shifted A w z 0)| ≤ η * R

/-- Equation (3.41): the centered event makes the sampled boundary strictly
worse than the origin. -/
theorem boundary_sample_gap {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w v z : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    {η R : ℝ} (hR : shifted A w z 0 = R) (hRpos : 0 < R)
    (hη : η < 8) (hevent : CenteredEvent A w v z η R)
    (h : Fin d → ℝ) (hboundary : phi A w h = 16 * R) :
    shifted A v z 0 < shifted A v z h := by
  have ht := boundary_true_gap A w z hw h hR hRpos.le hboundary
  have he := (abs_le.mp (hevent h hboundary.le)).1
  have hstrict : 0 < (8 - η) * R := mul_pos (by linarith) hRpos
  nlinarith

/-- The segment and intermediate-value argument for equation (3.42).
The radius continuity and convexity of the nonnegative weighted sampled
Huber objective are both proved from their definitions. -/
theorem sampled_minimizer_localized {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w v z : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    {η R : ℝ} (hR : shifted A w z 0 = R) (hRpos : 0 < R)
    (hη : η < 8) (hevent : CenteredEvent A w v z η R)
    (hv : ∀ i, 0 ≤ v i)
    (hhat : Fin d → ℝ) (hmin : ∀ h, shifted A v z hhat ≤ shifted A v z h) :
    phi A w hhat ≤ 16 * R := by
  by_contra hout
  have hout' : 16 * R < phi A w hhat := lt_of_not_ge hout
  have hinterval : 16 * R ∈ Set.Icc (phi A w ((0 : ℝ) • hhat))
      (phi A w ((1 : ℝ) • hhat)) := by
    simp only [zero_smul, phi_zero, one_smul, Set.mem_Icc]
    exact ⟨by linarith, hout'.le⟩
  obtain ⟨t, ht, hboundary⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    (continuous_phi_segment A w hhat).continuousOn hinterval
  have hstrict := boundary_sample_gap A w v z hw hR hRpos hη hevent
    (t • hhat) hboundary
  have hconvex := (convex_shifted A v z hv).2 (Set.mem_univ (0 : Fin d → ℝ))
    (Set.mem_univ hhat) (sub_nonneg.mpr ht.2) ht.1 (by ring : 1 - t + t = 1)
  simp only [smul_zero, zero_add, smul_eq_mul] at hconvex
  have hmul := mul_le_mul_of_nonneg_left (hmin 0) ht.1
  nlinarith

/-- Equation (3.43), before inserting the pilot approximation factor. -/
theorem additive_error_of_centered_event {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (w v z : Fin n → ℝ)
    {η R : ℝ} (hevent : CenteredEvent A w v z η R)
    (hstar hhat : Fin d → ℝ)
    (hstar_ball : phi A w hstar ≤ 16 * R)
    (hhat_ball : phi A w hhat ≤ 16 * R)
    (hmin : shifted A v z hhat ≤ shifted A v z hstar) :
    shifted A w z hhat - shifted A w z hstar ≤ 2 * η * R := by
  have hehat := (abs_le.mp (hevent hhat hhat_ball)).1
  have hestar := (abs_le.mp (hevent hstar hstar_ball)).2
  linarith

/-- The deterministic positive-radius component of the upper-bound proof.
The optimal comparator, pilot radius, sample optimality, nonnegative sample weights,
and uniform centered event are all stated on the actual Huber objectives. -/
theorem deterministic_localization {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (w v z : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) {η R : ℝ}
    (hR : shifted A w z 0 = R) (hRpos : 0 < R) (hη : η < 8)
    (hevent : CenteredEvent A w v z η R)
    (hv : ∀ i, 0 ≤ v i)
    (hstar hhat : Fin d → ℝ)
    (hopt : ∀ h, shifted A w z hstar ≤ shifted A w z h)
    (hmin : ∀ h, shifted A v z hhat ≤ shifted A v z h) :
    phi A w hstar ≤ 4 * R ∧ phi A w hhat ≤ 16 * R ∧
      shifted A w z hhat - shifted A w z hstar ≤ 2 * η * R := by
  have hstar_ball := comparator_in_four_radius A w z hw hstar hR
    (by rw [← hR]; exact hopt 0)
  have hhat_ball := sampled_minimizer_localized A w v z hw hR hRpos hη hevent
    hv hhat hmin
  refine ⟨hstar_ball, hhat_ball, ?_⟩
  apply additive_error_of_centered_event A w v z hevent hstar hhat
    (hstar_ball.trans (by linarith)) hhat_ball (hmin hstar)

/-- Equations (3.43)--(3.44), followed by the square-root relative guarantee.
This is conditional on the two deterministic good events and does not assert
that either event occurs with any particular probability. -/
theorem deterministic_relative_guarantee {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (w v z : Fin n → ℝ)
    (hw : ∀ i, 0 ≤ w i) {η R C₀ ε : ℝ}
    (hR : shifted A w z 0 = R) (hRpos : 0 < R) (hη : η < 8)
    (hC : 0 < C₀) (hε : 0 ≤ ε)
    (hηdef : η = (2 * ε + ε ^ 2) / (2 * C₀))
    (hevent : CenteredEvent A w v z η R)
    (hv : ∀ i, 0 ≤ v i)
    (hstar hhat : Fin d → ℝ)
    (hopt : ∀ h, shifted A w z hstar ≤ shifted A w z h)
    (hmin : ∀ h, shifted A v z hhat ≤ shifted A v z h)
    (hpilot : R ≤ C₀ * shifted A w z hstar) :
    shifted A w z hhat ≤ (1 + ε) ^ 2 * shifted A w z hstar ∧
      Real.sqrt (shifted A w z hhat) ≤
        (1 + ε) * Real.sqrt (shifted A w z hstar) := by
  have hadd := (deterministic_localization A w v z hw hR hRpos hη hevent
    hv hstar hhat hopt hmin).2.2
  have hη0 : 0 ≤ η := by rw [hηdef]; positivity
  have hp := mul_le_mul_of_nonneg_left hpilot (show 0 ≤ 2 * η by positivity)
  have hηeq : 2 * η * C₀ = 2 * ε + ε ^ 2 := by
    rw [hηdef]
    field_simp [ne_of_gt hC]
  have hp' : 2 * η * R ≤ (2 * ε + ε ^ 2) * shifted A w z hstar := by
    calc
      _ ≤ (2 * η) * (C₀ * shifted A w z hstar) := hp
      _ = _ := by rw [← mul_assoc, hηeq]
  have hbound : shifted A w z hhat ≤ (1 + ε) ^ 2 * shifted A w z hstar := by
    nlinarith
  refine ⟨hbound, ?_⟩
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (by linarith) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt (shifted_nonneg A w z hw hhat), mul_pow,
    Real.sq_sqrt (shifted_nonneg A w z hw hstar)]
  exact hbound

/-- Residualization is an exact identity on the source objective (2.1). -/
theorem shifted_residualization {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b : Fin n → ℝ) (yc h : Fin d → ℝ) :
    shifted A (fun _ => 1) (fun i => (A.mulVec yc) i - b i) h =
      objective A b (yc + h) := by
  unfold shifted weightedHuber objective
  simp only [Matrix.mulVec_add, Pi.add_apply, one_mul]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

/-- The positive-radius deterministic guarantee expressed directly for the
matrix and response vector of equation (2.1). The probability and construction
of the event remain separate obligations. -/
theorem regression_relative_guarantee {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (b v : Fin n → ℝ)
    (yc ystar hhat : Fin d → ℝ) {η C₀ ε : ℝ}
    (hRpos : 0 < objective A b yc) (hη : η < 8)
    (hC : 0 < C₀) (hε : 0 ≤ ε)
    (hηdef : η = (2 * ε + ε ^ 2) / (2 * C₀))
    (hv : ∀ i, 0 ≤ v i)
    (hevent : CenteredEvent A (fun _ => 1) v
      (fun i => (A.mulVec yc) i - b i) η (objective A b yc))
    (hopt : ∀ y, objective A b ystar ≤ objective A b y)
    (hmin : ∀ h, shifted A v (fun i => (A.mulVec yc) i - b i) hhat ≤
      shifted A v (fun i => (A.mulVec yc) i - b i) h)
    (hpilot : objective A b yc ≤ C₀ * objective A b ystar) :
    objective A b (yc + hhat) ≤ (1 + ε) ^ 2 * objective A b ystar ∧
      Real.sqrt (objective A b (yc + hhat)) ≤
        (1 + ε) * Real.sqrt (objective A b ystar) := by
  have htranslate : yc + (ystar - yc) = ystar := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hR : shifted A (fun _ => 1) (fun i => (A.mulVec yc) i - b i) 0 =
      objective A b yc := by
    rw [shifted_residualization, add_zero]
  have hstar : shifted A (fun _ => 1) (fun i => (A.mulVec yc) i - b i)
      (ystar - yc) = objective A b ystar := by
    rw [shifted_residualization, htranslate]
  have hopt' : ∀ h, shifted A (fun _ => 1) (fun i => (A.mulVec yc) i - b i)
      (ystar - yc) ≤ shifted A (fun _ => 1) (fun i => (A.mulVec yc) i - b i) h := by
    intro h
    rw [hstar, shifted_residualization]
    exact hopt (yc + h)
  have hp : objective A b yc ≤ C₀ * shifted A (fun _ => 1)
      (fun i => (A.mulVec yc) i - b i) (ystar - yc) := by
    rwa [hstar]
  have hresult := deterministic_relative_guarantee A (fun _ => 1) v
    (fun i => (A.mulVec yc) i - b i) (fun _ => by norm_num)
    hR hRpos hη hC hε hηdef hevent hv (ystar - yc) hhat hopt' hmin hp
  simpa only [hstar, shifted_residualization] using hresult

/-- Unit weights give exactly the source unshifted objective. -/
theorem phi_unit {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (h : Fin d → ℝ) : phi A (fun _ => 1) h = unshifted A h := by
  simp only [phi, weightedHuber, unshifted, one_mul]

/-- The fixed offset `-b` gives exactly the source affine objective. -/
theorem shifted_unit_neg {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (b : Fin n → ℝ) (x : Fin d → ℝ) :
    shifted A (fun _ => 1) (fun i => -b i) x = objective A b x := by
  simp only [shifted, weightedHuber, objective, one_mul, sub_eq_add_neg]

/-- Weighted affine triangle inequality, using the actual residuals. -/
theorem affine_objective_triangle {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w b : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (x y : Fin d → ℝ) :
    Real.sqrt (shifted A w (fun i => -b i) x) ≤
      Real.sqrt (phi A w (x - y)) + Real.sqrt (shifted A w (fun i => -b i) y) := by
  have ht := weightedHuber_triangle w (A.mulVec (x - y))
    (fun i => (A.mulVec y) i + -b i) hw
  have he : (fun i => (A.mulVec (x - y)) i + ((A.mulVec y) i + -b i)) =
      (fun i => (A.mulVec x) i + -b i) := by
    funext i
    rw [Matrix.mulVec_sub]
    simp only [Pi.sub_apply]
    ring
  rw [he] at ht
  exact ht

/-- Weighted triangle bound on the distance between two affine residuals. -/
theorem affine_distance_triangle {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (w b : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (x y : Fin d → ℝ) :
    Real.sqrt (phi A w (x - y)) ≤
      Real.sqrt (shifted A w (fun i => -b i) x) +
        Real.sqrt (shifted A w (fun i => -b i) y) := by
  have ht := weightedHuber_triangle w
    (fun i => (A.mulVec x) i + -b i) (fun i => -((A.mulVec y) i + -b i)) hw
  have he : (fun i => ((A.mulVec x) i + -b i) + -((A.mulVec y) i + -b i)) =
      A.mulVec (x - y) := by
    funext i
    rw [Matrix.mulVec_sub]
    simp only [Pi.sub_apply]
    ring
  rw [he, weightedHuber_neg] at ht
  exact ht

/-- The deterministic part of Lemma 3.9. Only the lower unshifted embedding,
the Markov bound at the fixed comparator, and actual sample optimality are
assumed. In particular, the pilot approximation conclusion is derived here.
The statement includes the zero-optimum case. -/
theorem deterministic_pilot_bound {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (b v : Fin n → ℝ)
    (xc xstar : Fin d → ℝ) {ρ δ : ℝ}
    (hv : ∀ i, 0 ≤ v i) (hρ : ρ < 1) (hδ : 0 < δ)
    (hembed : ∀ h, (1 - ρ) * unshifted A h ≤ phi A v h)
    (hmarkov : shifted A v (fun i => -b i) xstar ≤ objective A b xstar / δ)
    (hmin : ∀ x, shifted A v (fun i => -b i) xc ≤ shifted A v (fun i => -b i) x) :
    objective A b xc ≤
      (1 + 2 / Real.sqrt ((1 - ρ) * δ)) ^ 2 * objective A b xstar := by
  have hF0 : 0 ≤ objective A b xstar :=
    Finset.sum_nonneg (fun i _ => huber_nonneg ((A.mulVec xstar) i - b i))
  have hU0 : 0 ≤ unshifted A (xc - xstar) :=
    Finset.sum_nonneg (fun i _ => huber_nonneg ((A.mulVec (xc - xstar)) i))
  have hS0 := shifted_nonneg A v (fun i => -b i) hv xstar
  have hP0 := phi_nonneg A v hv (xc - xstar)
  have htri := affine_distance_triangle A v b hv xc xstar
  have hminsqrt := Real.sqrt_le_sqrt (hmin xstar)
  have hdist : Real.sqrt (phi A v (xc - xstar)) ≤
      2 * Real.sqrt (shifted A v (fun i => -b i) xstar) := by linarith
  have hdist_sq := (sq_le_sq₀ (Real.sqrt_nonneg _)
    (by positivity : 0 ≤ 2 * Real.sqrt (shifted A v (fun i => -b i) xstar))).mpr hdist
  rw [Real.sq_sqrt hP0, mul_pow, Real.sq_sqrt hS0] at hdist_sq
  have hM := (le_div_iff₀ hδ).mp hmarkov
  have hδdist := mul_le_mul_of_nonneg_left hdist_sq hδ.le
  have hδembed := mul_le_mul_of_nonneg_left (hembed (xc - xstar)) hδ.le
  have hdistance : ((1 - ρ) * δ) * unshifted A (xc - xstar) ≤
      4 * objective A b xstar := by nlinarith
  have hcpos : 0 < (1 - ρ) * δ := mul_pos (by linarith) hδ
  have hkpos : 0 < Real.sqrt ((1 - ρ) * δ) := Real.sqrt_pos.2 hcpos
  have hprod : Real.sqrt ((1 - ρ) * δ) * Real.sqrt (unshifted A (xc - xstar)) ≤
      2 * Real.sqrt (objective A b xstar) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow, mul_pow, Real.sq_sqrt hcpos.le, Real.sq_sqrt hU0,
      Real.sq_sqrt hF0]
    norm_num
    exact hdistance
  have hfull_dist : Real.sqrt (unshifted A (xc - xstar)) ≤
      (2 / Real.sqrt ((1 - ρ) * δ)) * Real.sqrt (objective A b xstar) := by
    calc
      _ ≤ (2 * Real.sqrt (objective A b xstar)) / Real.sqrt ((1 - ρ) * δ) :=
        (le_div_iff₀ hkpos).mpr (by nlinarith)
      _ = _ := by ring
  have hfull := affine_objective_triangle A (fun _ => 1) b
    (fun _ => by norm_num) xc xstar
  rw [shifted_unit_neg, phi_unit, shifted_unit_neg] at hfull
  have hrelative : Real.sqrt (objective A b xc) ≤
      (1 + 2 / Real.sqrt ((1 - ρ) * δ)) * Real.sqrt (objective A b xstar) := by
    nlinarith
  have hsq := (sq_le_sq₀ (Real.sqrt_nonneg _)
    (by positivity : 0 ≤ (1 + 2 / Real.sqrt ((1 - ρ) * δ)) *
      Real.sqrt (objective A b xstar))).mpr hrelative
  have hC0 : 0 ≤ objective A b xc :=
    Finset.sum_nonneg (fun i _ => huber_nonneg ((A.mulVec xc) i - b i))
  rwa [Real.sq_sqrt hC0, mul_pow, Real.sq_sqrt hF0] at hsq

/-- A zero true Huber objective forces every residual to vanish. -/
theorem residual_zero_of_objective_zero {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) (y : Fin d → ℝ)
    (hy : objective A b y = 0) : ∀ i, (A.mulVec y) i - b i = 0 := by
  have he := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      huber_nonneg ((A.mulVec y) i - b i))).mp hy
  intro i
  exact (huber_eq_zero_iff _).mp (he i (Finset.mem_univ i))

/-- The zero-optimum branch of the deterministic argument. The squared
Euclidean-norm comparison states the algorithm's minimum-norm selection rule
on the sampled argmin, rather than presupposing the selected vector is zero. -/
theorem regression_zero_optimum {n d : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (b v : Fin n → ℝ)
    (yc ystar hhat : Fin d → ℝ) {C₀ : ℝ}
    (hv : ∀ i, 0 ≤ v i) (hstar : objective A b ystar = 0)
    (hpilot : objective A b yc ≤ C₀ * objective A b ystar)
    (hnorm : ∀ h, (∀ k, shifted A v (fun i => (A.mulVec yc) i - b i) h ≤
        shifted A v (fun i => (A.mulVec yc) i - b i) k) →
      (∑ j, (hhat j) ^ 2) ≤ ∑ j, (h j) ^ 2) :
    hhat = 0 ∧ objective A b (yc + hhat) = 0 := by
  have hR0 : objective A b yc = 0 := by
    have hnonneg : 0 ≤ objective A b yc :=
      Finset.sum_nonneg (fun i _ => huber_nonneg ((A.mulVec yc) i - b i))
    rw [hstar, mul_zero] at hpilot
    exact le_antisymm hpilot hnonneg
  have hz := residual_zero_of_objective_zero A b yc hR0
  have hs0 : shifted A v (fun i => (A.mulVec yc) i - b i) 0 = 0 := by
    simp [shifted_zero, weightedHuber, hz]
  have hmin0 : ∀ k, shifted A v (fun i => (A.mulVec yc) i - b i) 0 ≤
      shifted A v (fun i => (A.mulVec yc) i - b i) k := by
    intro k
    rw [hs0]
    exact shifted_nonneg A v _ hv k
  have hn := hnorm 0 hmin0
  simp only [Pi.zero_apply, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    Finset.sum_const_zero] at hn
  have hsum : (∑ j, (hhat j) ^ 2) = 0 :=
    le_antisymm hn (Finset.sum_nonneg (fun j _ => sq_nonneg (hhat j)))
  have hhat0 : hhat = 0 := by
    funext j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (hhat i))).mp
      hsum j (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp hj
  refine ⟨hhat0, ?_⟩
  rwa [hhat0, add_zero]

end Paper29.Localization
