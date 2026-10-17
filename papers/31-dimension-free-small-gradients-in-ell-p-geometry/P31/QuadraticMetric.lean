import P31.NormTargets
import P31.LpEstimates
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Proposition 7.1.  Known SDP duality and Gaussian moment/Jensen theorems
are explicit inputs on actual matrices and integrals.  The diagonal bound,
strictly positive perturbation and metric conversions are proved here. -/

noncomputable section
open scoped BigOperators Matrix
open MeasureTheory

namespace P31.QuadraticMetric

abbrev Vec (d : ℕ) := Fin d → ℝ
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

def quad {d : ℕ} (A : Mat d) (v : Vec d) : ℝ := v ⬝ᵥ (A *ᵥ v)
def objective {d : ℕ} (A : Mat d) (b x : Vec d) : ℝ := quad A x / 2 - b ⬝ᵥ x
def gradient {d : ℕ} (A : Mat d) (b x : Vec d) : Vec d := A *ᵥ x - b

/-- The actual finite ℓₚ→ℓ_q operator norm in the statement. -/
def operatorNorm {d : ℕ} (p : ℝ) (A : Mat d) : ℝ :=
  sSup {t : ℝ | ∃v : Vec d, lpNorm p v ≤ 1 ∧ t = lpNorm (dualExponent p) (A *ᵥ v)}

/-- Inverse of `sₚ`, including the `s₂=∞` convention. -/
def invMetricExponent (p : ℝ) : ℝ := (p-2)/p
def metricExponent (p : ℝ) : ℝ := p/(p-2)

/-- Actual ℓ_{sₚ} norm; the endpoint uses the genuine finite supremum norm. -/
def metricNorm {d : ℕ} (p : ℝ) (w : Vec d) : ℝ :=
  if p=2 then ‖w‖ else lpNorm (metricExponent p) w

lemma metricNorm_nonneg {d : ℕ} (p : ℝ) (w : Vec d) : 0 ≤ metricNorm p w := by
  unfold metricNorm
  split_ifs
  · exact norm_nonneg _
  · exact lpNorm_nonneg _ _

lemma metricExponent_ge_one {p : ℝ} (hp : 2 < p) : 1 ≤ metricExponent p := by
  apply (le_div_iff₀ (by linarith : 0 < p-2)).2
  linarith

lemma metricNorm_add_le {d : ℕ} {p : ℝ} (hp : 2 ≤ p) (u v : Vec d) :
    metricNorm p (u+v) ≤ metricNorm p u + metricNorm p v := by
  unfold metricNorm
  split_ifs with h
  · exact norm_add_le _ _
  · exact lpNorm_add_le (metricExponent_ge_one (lt_of_le_of_ne hp (Ne.symm h))) _ _

lemma metricNorm_constant {d : ℕ} (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p) (a : ℝ) :
    metricNorm p (fun _ : Fin d => a) = (d:ℝ)^invMetricExponent p * |a| := by
  letI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  by_cases h : p=2
  · subst p
    simp [metricNorm, invMetricExponent, Real.norm_eq_abs]
  · have hsp : 0 < metricExponent p := lt_of_lt_of_le zero_lt_one
      (metricExponent_ge_one (lt_of_le_of_ne hp (Ne.symm h)))
    rw [metricNorm, if_neg h, lpNorm_constant d hsp]
    congr 2
    dsimp [metricExponent, invMetricExponent]
    field_simp

/-- The precise standard Gaussian moment used in the paper. -/
def normalMoment (p : ℝ) : ℝ :=
  ∫ t : ℝ, |t|^p ∂ProbabilityTheory.gaussianReal 0 1

def gamma (p : ℝ) : ℝ := normalMoment p ^ (2/p)

/-- Known Gaussian covariance, coordinate-moment and Jensen inputs.
No trace upper bound or diagonal-majorant conclusion is an input. -/
structure GaussianInput (d : ℕ) (p : ℝ) where
  law : (X : Mat d) → X.PosSemidef → Measure (Vec d)
  probability : ∀ X (hX : X.PosSemidef), IsProbabilityMeasure (law X hX)
  moment_pos : 0 < normalMoment p
  quad_integrable : ∀ A X (hX : X.PosSemidef), Integrable (quad A) (law X hX)
  norm_sq_integrable : ∀ X (hX : X.PosSemidef),
    Integrable (fun z => (lpNorm p z)^2) (law X hX)
  covariance : ∀ A X (hX : X.PosSemidef),
    (∫ z, quad A z ∂law X hX) = Matrix.trace (A*X)
  coordinate_moment : ∀ X (hX : X.PosSemidef),
    (∫ z, (lpNorm p z)^p ∂law X hX) = normalMoment p * ∑ j, (X j j)^(p/2)
  jensen : ∀ X (hX : X.PosSemidef),
    (∫ z, (lpNorm p z)^2 ∂law X hX) ≤
      (∫ z, (lpNorm p z)^p ∂law X hX)^(2/p)

/-- Exact known SDP strong-duality and attainment interface for (7.12).
It supplies no numerical bound on the primal optimizer. -/
structure SDPInput (d : ℕ) (p : ℝ) (A : Mat d) where
  optimum : ℝ
  primal_attained : ∃w : Vec d, (Matrix.diagonal w-A).PosSemidef ∧ metricNorm p w=optimum
  dual_support : ∀ t : ℝ,
    (∀ X : Mat d, X.PosSemidef → lpNorm (p/2) (Matrix.diag X) ≤ 1 → Matrix.trace (A*X) ≤ t) →
      optimum ≤ t

lemma psd_diagonal_nonneg {d : ℕ} {X : Mat d} (hX : X.PosSemidef) (i : Fin d) :
    0 ≤ X i i := by
  simpa using hX.2 (Pi.single i 1)

/-- Hölder's standard inequality, used before taking Gaussian expectations. -/
lemma pairing_le {d : ℕ} {p : ℝ} (hp : 1 < p) (v z : Vec d) :
    v ⬝ᵥ z ≤ lpNorm p v * lpNorm (dualExponent p) z := by
  simpa [dotProduct, lpNorm, lpPower, dualExponent, Real.conjExponent] using
    Real.inner_le_Lp_mul_Lq Finset.univ v z (Real.HolderConjugate.conjExponent hp)

/-- The usual operator-norm bound is explicit because `operatorNorm` is a supremum.
From that standard norm fact, this is the paper's own pointwise quadratic bound. -/
lemma quad_le_operatorNorm {d : ℕ} {p : ℝ} (hp : 2 ≤ p) (A : Mat d)
    (hop : ∀v, lpNorm (dualExponent p) (A *ᵥ v) ≤ operatorNorm p A * lpNorm p v)
    (v : Vec d) : quad A v ≤ operatorNorm p A * (lpNorm p v)^2 := by
  calc
    _ ≤ lpNorm p v * lpNorm (dualExponent p) (A *ᵥ v) := pairing_le (by linarith) _ _
    _ ≤ lpNorm p v * (operatorNorm p A * lpNorm p v) :=
      mul_le_mul_of_nonneg_left (hop v) (lpNorm_nonneg _ _)
    _ = operatorNorm p A * (lpNorm p v)^2 := by ring

lemma gaussian_norm_moment {d : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (G : GaussianInput d p) (X : Mat d) (hX : X.PosSemidef) :
    (∫ z, (lpNorm p z)^p ∂G.law X hX)^(2/p) =
      gamma p * lpNorm (p/2) (Matrix.diag X) := by
  rw [G.coordinate_moment, Real.mul_rpow (le_of_lt G.moment_pos)
    (Finset.sum_nonneg (fun j _ => Real.rpow_nonneg (psd_diagonal_nonneg hX j) (p/2)))]
  unfold gamma lpNorm lpPower
  congr 1
  have habs : (∑ j, |X j j|^(p/2)) = ∑ j, (X j j)^(p/2) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [abs_of_nonneg (psd_diagonal_nonneg hX j)]
  simp only [Matrix.diag_apply]
  rw [habs]
  congr 1
  field_simp

/-- The substantive Gaussian-to-SDP connecting inequality in Proposition 7.1. -/
theorem trace_bound {d : ℕ} {p : ℝ} (hp : 2 ≤ p) (A : Mat d)
    (hL : 0 ≤ operatorNorm p A)
    (hop : ∀v, lpNorm (dualExponent p) (A *ᵥ v) ≤ operatorNorm p A * lpNorm p v)
    (G : GaussianInput d p) (X : Mat d) (hX : X.PosSemidef)
    (hdiag : lpNorm (p/2) (Matrix.diag X) ≤ 1) :
    Matrix.trace (A*X) ≤ gamma p * operatorNorm p A := by
  have hγ : 0 ≤ gamma p := Real.rpow_nonneg (le_of_lt G.moment_pos) _
  calc
    _ = ∫ z, quad A z ∂G.law X hX := (G.covariance A X hX).symm
    _ ≤ ∫ z, operatorNorm p A * (lpNorm p z)^2 ∂G.law X hX :=
      integral_mono (G.quad_integrable A X hX)
        ((G.norm_sq_integrable X hX).const_mul _) (quad_le_operatorNorm hp A hop)
    _ = operatorNorm p A * ∫ z, (lpNorm p z)^2 ∂G.law X hX := integral_const_mul _ _
    _ ≤ operatorNorm p A * (∫ z, (lpNorm p z)^p ∂G.law X hX)^(2/p) :=
      mul_le_mul_of_nonneg_left (G.jensen X hX) hL
    _ = gamma p * operatorNorm p A * lpNorm (p/2) (Matrix.diag X) := by
      rw [gaussian_norm_moment hp G X hX]; ring
    _ ≤ gamma p * operatorNorm p A := by
      simpa using mul_le_mul_of_nonneg_left hdiag (mul_nonneg hγ hL)

/-- The unperturbed majorant is derived from duality and the Gaussian bound. -/
theorem exists_semidefinite_majorant {d : ℕ} {p : ℝ} (hp : 2 ≤ p) (A : Mat d)
    (hL : 0 ≤ operatorNorm p A)
    (hop : ∀v, lpNorm (dualExponent p) (A *ᵥ v) ≤ operatorNorm p A * lpNorm p v)
    (G : GaussianInput d p) (S : SDPInput d p A) :
    ∃w : Vec d, (Matrix.diagonal w-A).PosSemidef ∧ metricNorm p w ≤ gamma p*operatorNorm p A := by
  obtain ⟨w, hw, hopt⟩ := S.primal_attained
  exact ⟨w, hw, hopt.le.trans (S.dual_support _ (fun X hX hdiag => trace_bound hp A hL hop G X hX hdiag))⟩

/-- Adding the normalized constant diagonal gives strict positivity and exactly
one additional copy of `γₚ L_A` in its norm, including at `p=2`. -/
theorem exists_positive_majorant {d : ℕ} (hd : 0 < d) {p : ℝ} (hp : 2 ≤ p)
    (A : Mat d) (hA : A.PosSemidef) (hL : 0 < operatorNorm p A)
    (hop : ∀v, lpNorm (dualExponent p) (A *ᵥ v) ≤ operatorNorm p A * lpNorm p v)
    (G : GaussianInput d p) (S : SDPInput d p A) :
    ∃w : Vec d, (∀i, 0 < w i) ∧ (Matrix.diagonal w).PosDef ∧
      (Matrix.diagonal w-A).PosSemidef ∧ metricNorm p w ≤ 2*gamma p*operatorNorm p A := by
  obtain ⟨w, hw, hnorm⟩ := exists_semidefinite_majorant hp A hL.le hop G S
  have hw0 : ∀i, 0 ≤ w i := Matrix.posSemidef_diagonal_iff.mp (by
    convert hw.add hA using 1
    abel)
  let c : ℝ := gamma p*operatorNorm p A*(d:ℝ)^(-invMetricExponent p)
  have hd0 : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have hγ : 0 < gamma p := Real.rpow_pos_of_pos G.moment_pos _
  have hc : 0 < c := mul_pos (mul_pos hγ hL) (Real.rpow_pos_of_pos hd0 _)
  have hconst : metricNorm p (fun _ : Fin d => c) = gamma p*operatorNorm p A := by
    rw [metricNorm_constant hd hp, abs_of_pos hc]
    dsimp [c]
    calc
      _ = gamma p*operatorNorm p A*((d:ℝ)^invMetricExponent p*(d:ℝ)^(-invMetricExponent p)) := by ring
      _ = gamma p*operatorNorm p A := by rw [← Real.rpow_add hd0]; simp
  refine ⟨w+(fun _ => c), (fun i => add_pos_of_nonneg_of_pos (hw0 i) hc),
    Matrix.PosDef.diagonal (fun i => add_pos_of_nonneg_of_pos (hw0 i) hc), ?_, ?_⟩
  · convert hw.add (Matrix.PosSemidef.diagonal (fun _ => hc.le)) using 1
    ext i j
    by_cases hij : i=j
    · subst j
      simp [Matrix.diagonal]
      ring
    · simp [Matrix.diagonal, hij]
  · calc
      _ ≤ metricNorm p w + metricNorm p (fun _ : Fin d => c) := metricNorm_add_le hp _ _
      _ ≤ gamma p*operatorNorm p A + gamma p*operatorNorm p A := add_le_add hnorm hconst.le
      _ = 2*gamma p*operatorNorm p A := by ring

/-- The actual squared Hilbert norm induced by a diagonal matrix. -/
def energy {d : ℕ} (w v : Vec d) : ℝ := ∑ i, w i*(v i)^2

def hilbertNorm {d : ℕ} (w v : Vec d) : ℝ := Real.sqrt (energy w v)
def inverseWeights {d : ℕ} (w : Vec d) : Vec d := fun i => 1/w i
def dualHilbertNorm {d : ℕ} (w g : Vec d) : ℝ := hilbertNorm (inverseWeights w) g

lemma energy_nonneg {d : ℕ} {w : Vec d} (hw : ∀i, 0 ≤ w i) (v : Vec d) :
    0 ≤ energy w v := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))

lemma diagonal_quad {d : ℕ} (w v : Vec d) : quad (Matrix.diagonal w) v = energy w v := by
  simp only [quad, Matrix.mulVec_diagonal, dotProduct, energy]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Hölder's inequality gives the radius conversion, before taking square roots. -/
lemma energy_le_metricNorm {d : ℕ} {p : ℝ} (hp : 2 ≤ p) (w v : Vec d) :
    energy w v ≤ metricNorm p w*(lpNorm p v)^2 := by
  by_cases hp2 : p=2
  · subst p
    have hsum : (∑ i, (v i)^2) = (lpNorm 2 v)^2 := by
      have h := lpNorm_rpow 2 (by norm_num) v
      simpa [lpPower, Real.rpow_two, sq_abs] using h.symm
    calc
      _ ≤ ‖w‖ * ∑ i, (v i)^2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w i)) (sq_nonneg _)
      _ = metricNorm 2 w*(lpNorm 2 v)^2 := by simp [metricNorm, hsum]
  · have hpgt : 2 < p := lt_of_le_of_ne hp (Ne.symm hp2)
    have hconj : (metricExponent p).HolderConjugate (p/2) := by
      apply Real.holderConjugate_iff.mpr
      constructor
      · apply (lt_div_iff₀ (by linarith : 0 < p-2)).2
        linarith
      · dsimp [metricExponent]
        field_simp
        ring
    have hsquare : lpNorm (p/2) (fun i => (v i)^2) = (lpNorm p v)^2 := by
      unfold lpNorm lpPower
      have hsum : (∑ i, |(v i)^2|^(p/2)) = ∑ i, |v i|^p := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_sq, ← sq_abs (v i), ← Real.rpow_two, ← Real.rpow_mul (abs_nonneg (v i))]
        congr 1
        ring
      rw [hsum, ← Real.rpow_natCast, ← Real.rpow_mul (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) p))]
      congr 1
      field_simp; norm_num
    have h := Real.inner_le_Lp_mul_Lq Finset.univ w (fun i => (v i)^2) hconj
    change energy w v ≤ lpNorm (metricExponent p) w * lpNorm (p/2) (fun i => (v i)^2) at h
    rw [hsquare] at h
    simpa only [metricNorm, if_neg hp2] using h

/-- First conversion in the last display of the proof of Proposition 7.1. -/
theorem hilbert_radius_conversion {d : ℕ} {p : ℝ} (hp : 2 ≤ p) (w v : Vec d) :
    hilbertNorm w v ≤ Real.sqrt (metricNorm p w)*lpNorm p v := by
  unfold hilbertNorm
  calc
    _ ≤ Real.sqrt (metricNorm p w*(lpNorm p v)^2) := Real.sqrt_le_sqrt (energy_le_metricNorm hp w v)
    _ = Real.sqrt (metricNorm p w)*lpNorm p v := by
      rw [Real.sqrt_mul (metricNorm_nonneg _ _), Real.sqrt_sq (lpNorm_nonneg _ _)]

/-- Cauchy--Schwarz in an actual positive-semidefinite quadratic form,
proved from nonnegativity of the scalar quadratic discriminant. -/
lemma psd_cauchy_sq {d : ℕ} {A : Mat d} (hA : A.PosSemidef) (u v : Vec d) :
    (u ⬝ᵥ (A *ᵥ v))^2 ≤ quad A u*quad A v := by
  have hsym : A.transpose=A := by simpa using hA.1
  have hcross : v ⬝ᵥ (A *ᵥ u) = u ⬝ᵥ (A *ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, dotProduct_comm]
  have hpol : ∀t : ℝ, 0 ≤ quad A v*(t*t)+(2*(u ⬝ᵥ (A *ᵥ v)))*t+quad A u := by
    intro t
    have h := hA.2 (u+t • v)
    simp only [star_trivial, Matrix.mulVec_add, Matrix.mulVec_smul,
      add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, hcross] at h
    dsimp [quad]
    nlinarith
  have h := discrim_le_zero hpol
  dsimp [discrim] at h
  nlinarith

/-- Majorization converts the PSD quadratic form to the diagonal energy. -/
lemma quad_le_energy {d : ℕ} {A : Mat d} {w : Vec d}
    (hmajor : (Matrix.diagonal w-A).PosSemidef) (v : Vec d) :
    quad A v ≤ energy w v := by
  have h := hmajor.2 v
  have h' : quad A v ≤ quad (Matrix.diagonal w) v := by
    simpa only [quad, star_trivial, Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] using h
  simpa only [diagonal_quad] using h'

/-- The paper's `A D⁻¹ A ≼ A ≼ D` implication as a bound on actual norms.
It follows from the internally proved PSD Cauchy--Schwarz inequality. -/
theorem quadratic_hilbert_smooth {d : ℕ} {A : Mat d} (hA : A.PosSemidef)
    {w : Vec d} (hw : ∀i, 0 < w i) (hmajor : (Matrix.diagonal w-A).PosSemidef) (v : Vec d) :
    dualHilbertNorm w (A *ᵥ v) ≤ hilbertNorm w v := by
  let z : Vec d := fun i => (A *ᵥ v) i / w i
  let t := energy (inverseWeights w) (A *ᵥ v)
  have ht : 0 ≤ t := energy_nonneg (fun i => div_nonneg zero_le_one (hw i).le) _
  have hzenergy : energy w z=t := by
    dsimp [energy, z, t, inverseWeights]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have hzpair : z ⬝ᵥ (A *ᵥ v)=t := by
    dsimp [dotProduct, z, t, energy, inverseWeights]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hcz : quad A z ≤ t := (quad_le_energy hmajor z).trans_eq hzenergy
  have hcs := psd_cauchy_sq hA z v
  rw [hzpair] at hcs
  have hqv : 0 ≤ quad A v := by simpa only [quad, star_trivial] using hA.2 v
  have htq : t ≤ quad A v := by
    nlinarith [mul_le_mul_of_nonneg_right hcz hqv]
  exact Real.sqrt_le_sqrt (htq.trans (quad_le_energy hmajor v))

/-- Weighted finite Cauchy--Schwarz for the diagonal metric and its actual inverse. -/
lemma weighted_pairing_le {d : ℕ} {w : Vec d} (hw : ∀i, 0 < w i) (g v : Vec d) :
    |g ⬝ᵥ v| ≤ dualHilbertNorm w g * hilbertNorm w v := by
  have hwinv : ∀i, 0 ≤ inverseWeights w i := fun i => div_nonneg zero_le_one (hw i).le
  have hE := energy_nonneg (fun i => (hw i).le) v
  have hI := energy_nonneg hwinv g
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => g i / Real.sqrt (w i)) (fun i => Real.sqrt (w i)*v i)
  have hpair : (∑ i, (g i/Real.sqrt (w i))*(Real.sqrt (w i)*v i))=g ⬝ᵥ v := by
    apply Finset.sum_congr rfl
    intro i _
    have hs : Real.sqrt (w i) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (hw i))
    field_simp
  have hleft : (∑ i, (g i/Real.sqrt (w i))^2)=energy (inverseWeights w) g := by
    apply Finset.sum_congr rfl
    intro i _
    rw [div_pow, Real.sq_sqrt (hw i).le]
    dsimp [inverseWeights]
    ring
  have hright : (∑ i, (Real.sqrt (w i)*v i)^2)=energy w v := by
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_pow, Real.sq_sqrt (hw i).le]
  rw [hpair, hleft, hright] at hCS
  have hsq : (dualHilbertNorm w g*hilbertNorm w v)^2=
      energy (inverseWeights w) g*energy w v := by
    rw [mul_pow, dualHilbertNorm, hilbertNorm, hilbertNorm,
      Real.sq_sqrt hI, Real.sq_sqrt hE]
  have hnon : 0 ≤ dualHilbertNorm w g*hilbertNorm w v :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  nlinarith [sq_abs (g ⬝ᵥ v), abs_nonneg (g ⬝ᵥ v)]

/-- The standard finite ℓₚ/ℓ_q dual-norm theorem, stated as a precise external
known theorem.  It quantifies arbitrary vectors and pairing bounds. -/
def LpDualityInput (d : ℕ) (p : ℝ) : Prop :=
  ∀g : Vec d, ∀C : ℝ, 0 ≤ C →
    (∀v : Vec d, |g ⬝ᵥ v| ≤ C*lpNorm p v) → lpNorm (dualExponent p) g ≤ C

/-- Second conversion in the last display of the proof of Proposition 7.1.
The diagonal-metric dependence is proved here from weighted Cauchy--Schwarz,
Hölder, and the standard universal norm-duality theorem. -/
theorem hilbert_gradient_conversion {d : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (dual : LpDualityInput d p) {w : Vec d} (hw : ∀i, 0 < w i) (g : Vec d) :
    lpNorm (dualExponent p) g ≤ Real.sqrt (metricNorm p w)*dualHilbertNorm w g := by
  apply dual g _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  intro v
  calc
    _ ≤ dualHilbertNorm w g*hilbertNorm w v := weighted_pairing_le hw g v
    _ ≤ dualHilbertNorm w g*(Real.sqrt (metricNorm p w)*lpNorm p v) :=
      mul_le_mul_of_nonneg_left (hilbert_radius_conversion hp w v) (Real.sqrt_nonneg _)
    _ = (Real.sqrt (metricNorm p w)*dualHilbertNorm w g)*lpNorm p v := by ring

/-- A quadratic oracle exposes values and gradients, without providing the
full Hessian to the external Hilbert-space method. -/
def oracle {d : ℕ} (A : Mat d) (b : Vec d) (x : Vec d) : ℝ × Vec d :=
  (objective A b x, gradient A b x)

/-- Known external Hilbert theorem: the `p_src = 2` specialization of
Corollary 3, Section 4.1, https://arxiv.org/html/2311.17296v2.
This is its normalized uniform numerical-constant `N`-query consequence:
changing the source's `2N` iterations to `N` queries changes only that universal
constant (split the budget with `floor(N/2)`; the small-budget case is absorbed).
Its guarantee is in the supplied metric's dual norm.  The paper's ℓ_q target
and the constructed majorant bound are not inputs. -/
structure HilbertRateInput (d : ℕ) (C : ℝ) where
  run : Vec d → (Vec d → ℝ × Vec d) → Vec d → ℕ → Vec d
  calls : Vec d → (Vec d → ℝ × Vec d) → Vec d → ℕ → ℕ
  rate : ∀ (A : Mat d), A.PosSemidef → ∀ (b x₀ xstar w : Vec d),
    (∀i, 0 < w i) → (∀v, dualHilbertNorm w (A *ᵥ v) ≤ hilbertNorm w v) →
    (∀x, objective A b xstar ≤ objective A b x) →
    ∀ (N : ℕ), 0 < N → ∀ (RD : ℝ), 0 ≤ RD → hilbertNorm w (x₀-xstar) ≤ RD →
      calls w (oracle A b) x₀ N ≤ N ∧
      dualHilbertNorm w (gradient A b (run w (oracle A b) x₀ N)) ≤ C*RD/(N:ℝ)^2

/-- Proposition 7.1's supplied-metric gradient conclusion, with the exact
constant `2 γₚ C_H` obtained by the paper's two conversions. -/
theorem supplied_metric_rate {d : ℕ} {p C R : ℝ} (hp : 2 ≤ p) (hC : 0 ≤ C)
    (dual : LpDualityInput d p) (H : HilbertRateInput d C)
    (A : Mat d) (hA : A.PosSemidef) (b x₀ xstar w : Vec d)
    (hw : ∀i, 0 < w i) (hmajor : (Matrix.diagonal w-A).PosSemidef)
    (hnorm : metricNorm p w ≤ 2*gamma p*operatorNorm p A)
    (hmin : ∀x, objective A b xstar ≤ objective A b x)
    (hR : 0 ≤ R) (hradius : lpNorm p (x₀-xstar) ≤ R)
    (N : ℕ) (hN : 0 < N) :
    H.calls w (oracle A b) x₀ N ≤ N ∧
    lpNorm (dualExponent p) (gradient A b (H.run w (oracle A b) x₀ N)) ≤
      (2*gamma p*C)*operatorNorm p A*R/(N:ℝ)^2 := by
  let W := metricNorm p w
  have hW : 0 ≤ W := metricNorm_nonneg p w
  have hRD : 0 ≤ Real.sqrt W*R := mul_nonneg (Real.sqrt_nonneg _) hR
  have hstart : hilbertNorm w (x₀-xstar) ≤ Real.sqrt W*R :=
    (hilbert_radius_conversion hp w _).trans
      (mul_le_mul_of_nonneg_left hradius (Real.sqrt_nonneg _))
  obtain ⟨hcount, hgrad⟩ := H.rate A hA b x₀ xstar w hw
    (quadratic_hilbert_smooth hA hw hmajor) hmin N hN _ hRD hstart
  refine ⟨hcount, ?_⟩
  have hN0 : 0 ≤ (N:ℝ)^2 := sq_nonneg _
  calc
    _ ≤ Real.sqrt W*dualHilbertNorm w (gradient A b (H.run w (oracle A b) x₀ N)) :=
      hilbert_gradient_conversion hp dual hw _
    _ ≤ Real.sqrt W*(C*(Real.sqrt W*R)/(N:ℝ)^2) :=
      mul_le_mul_of_nonneg_left hgrad (Real.sqrt_nonneg _)
    _ = C*W*R/(N:ℝ)^2 := by
      rw [← mul_div_assoc]
      congr 1
      calc
        Real.sqrt W*(C*(Real.sqrt W*R)) = C*(Real.sqrt W*Real.sqrt W)*R := by ring
        _ = C*W*R := by rw [Real.mul_self_sqrt hW]
    _ ≤ C*(2*gamma p*operatorNorm p A)*R/(N:ℝ)^2 :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm hC) hR) hN0
    _ = (2*gamma p*C)*operatorNorm p A*R/(N:ℝ)^2 := by ring

/-- Standard boundedness and homogeneity facts for the actual operator norm,
recorded as an explicit known finite-dimensional norm theorem. -/
structure OperatorNormInput (d : ℕ) (p : ℝ) (A : Mat d) : Prop where
  bounded : BddAbove {t : ℝ | ∃v : Vec d, lpNorm p v ≤ 1 ∧ t = lpNorm (dualExponent p) (A *ᵥ v)}
  bound : ∀v, lpNorm (dualExponent p) (A *ᵥ v) ≤ operatorNorm p A * lpNorm p v

lemma operatorNorm_nonneg {d : ℕ} {p : ℝ} (hp : 2 ≤ p) (A : Mat d)
    (O : OperatorNormInput d p A) : 0 ≤ operatorNorm p A := by
  apply le_csSup O.bounded
  refine ⟨0, ?_, ?_⟩
  · simpa only [lpNorm_zero (by linarith : 0 < p)] using (zero_le_one : (0:ℝ) ≤ 1)
  · simp only [Matrix.mulVec_zero, lpNorm_zero (dualExponent_pos (by linarith : 1 < p))]

/-- The zero-operator case includes the nontrivial implication that an attained
minimum of the remaining linear objective forces its linear term to vanish. -/
theorem zero_operator_gradient {d : ℕ} {p : ℝ} (hp : 2 ≤ p)
    (A : Mat d) (O : OperatorNormInput d p A) (hL : operatorNorm p A=0)
    (b xstar : Vec d) (hmin : ∀x, objective A b xstar ≤ objective A b x) :
    A=0 ∧ b=0 ∧ ∀x, gradient A b x=0 := by
  have hAv (v : Vec d) : A *ᵥ v=0 := by
    ext i
    apply abs_nonpos_iff.mp
    exact (abs_coordinate_le_lpNorm (dualExponent_pos (by linarith : 1 < p)) _ i).trans
      (by simpa [hL] using O.bound v)
  have hA0 : A=0 := by
    ext i j
    have h := congrFun (hAv (Pi.single j 1)) i
    simpa using h
  have hbpair (v : Vec d) : b ⬝ᵥ v=0 := by
    have hplus := hmin (xstar+v)
    have hminus := hmin (xstar-v)
    simp only [objective, hA0, quad, Matrix.zero_mulVec, dotProduct_zero, zero_div,
      zero_sub, dotProduct_add, dotProduct_sub] at hplus hminus
    linarith
  have hb0 : b=0 := by
    ext i
    simpa using hbpair (Pi.single i 1)
  refine ⟨hA0, hb0, ?_⟩
  intro x
  simp [gradient, hA0, hb0]

/-- Proposition 7.1 with exact external dependencies and the actual supplied
metric algorithm.  Its positive diagonal and ℓ_q guarantee are conclusions. -/
theorem proposition71_positive {d : ℕ} (hd : 0 < d) {p C R : ℝ}
    (hp : 2 ≤ p) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (A : Mat d) (hA : A.PosSemidef) (O : OperatorNormInput d p A)
    (hL : 0 < operatorNorm p A) (G : GaussianInput d p) (S : SDPInput d p A)
    (dual : LpDualityInput d p) (H : HilbertRateInput d C)
    (b x₀ xstar : Vec d) (hmin : ∀x, objective A b xstar ≤ objective A b x)
    (hradius : lpNorm p (x₀-xstar) ≤ R) :
    ∃w : Vec d, (∀i, 0 < w i) ∧ (Matrix.diagonal w).PosDef ∧
      (Matrix.diagonal w-A).PosSemidef ∧ metricNorm p w ≤ 2*gamma p*operatorNorm p A ∧
      ∀N : ℕ, 0 < N → H.calls w (oracle A b) x₀ N ≤ N ∧
        lpNorm (dualExponent p) (gradient A b (H.run w (oracle A b) x₀ N)) ≤
          (2*gamma p*C)*operatorNorm p A*R/(N:ℝ)^2 := by
  obtain ⟨w, hw, hpos, hmajor, hnorm⟩ := exists_positive_majorant hd hp A hA hL O.bound G S
  exact ⟨w, hw, hpos, hmajor, hnorm, fun N hN =>
    supplied_metric_rate hp hC dual H A hA b x₀ xstar w hw hmajor hnorm hmin hR hradius N hN⟩

/-- The same numerical Hilbert constant is used in every finite dimension. -/
def HilbertUniformRateInput (C : ℝ) := ∀d : ℕ, HilbertRateInput d C

/-- Complete zero/positive split of Proposition 7.1.  The only rate input uses a
single numerical constant in every dimension; all `p` dependence in the final
coefficient is displayed through the actual standard Gaussian moment `gamma p`. -/
theorem proposition71 {d : ℕ} (hd : 0 < d) {p C R : ℝ}
    (hp : 2 ≤ p) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (A : Mat d) (hA : A.PosSemidef) (O : OperatorNormInput d p A)
    (G : GaussianInput d p) (S : SDPInput d p A)
    (dual : LpDualityInput d p) (H : HilbertUniformRateInput C)
    (b x₀ xstar : Vec d) (hmin : ∀x, objective A b xstar ≤ objective A b x)
    (hradius : lpNorm p (x₀-xstar) ≤ R) :
    (operatorNorm p A=0 ∧ A=0 ∧ b=0 ∧ ∀x, gradient A b x=0) ∨
    (∃w : Vec d, (∀i, 0 < w i) ∧ (Matrix.diagonal w).PosDef ∧
      (Matrix.diagonal w-A).PosSemidef ∧ metricNorm p w ≤ 2*gamma p*operatorNorm p A ∧
      ∀N : ℕ, 0 < N → (H d).calls w (oracle A b) x₀ N ≤ N ∧
        lpNorm (dualExponent p) (gradient A b ((H d).run w (oracle A b) x₀ N)) ≤
          (2*gamma p*C)*operatorNorm p A*R/(N:ℝ)^2) := by
  rcases eq_or_lt_of_le (operatorNorm_nonneg hp A O) with hzero | hpos
  · exact Or.inl ⟨hzero.symm, zero_operator_gradient hp A O hzero.symm b xstar hmin⟩
  · exact Or.inr (proposition71_positive hd hp hC hR A hA O hpos G S dual (H d)
      b x₀ xstar hmin hradius)

end P31.QuadraticMetric
