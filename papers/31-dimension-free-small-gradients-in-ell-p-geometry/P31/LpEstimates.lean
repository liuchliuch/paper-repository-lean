import P31.PowerGeometry
import P31.Terminal
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Positivity

/-! Norm estimates for the actual finite-coordinate ℓₚ objects, used to
connect the general normed-space analysis to the vector statements. -/
noncomputable section
open scoped BigOperators
namespace P31
variable {ι : Type*} [Fintype ι]

lemma coordinateFunctional_injective :
    Function.Injective (coordinateFunctional (ι := ι)) := by
  classical
  intro u v huv
  funext j
  have h := congrArg (fun f : (ι → ℝ) →L[ℝ] ℝ => f (Pi.single j 1)) huv
  simpa [coordinateFunctional_apply, Pi.single_apply] using h

lemma coordinateFunctional_add (u v : ι → ℝ) :
    coordinateFunctional (u + v) = coordinateFunctional u + coordinateFunctional v := by
  ext h
  simp [coordinateFunctional_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma coordinateFunctional_smul (a : ℝ) (u : ι → ℝ) :
    coordinateFunctional (a • u) = a • coordinateFunctional u := by
  ext h
  simp [coordinateFunctional_apply, Finset.mul_sum, mul_assoc]

lemma coordinateFunctional_neg (u : ι → ℝ) :
    coordinateFunctional (-u) = -coordinateFunctional u := by
  ext h
  simp [coordinateFunctional_apply, Finset.sum_neg_distrib]

lemma coordinateFunctional_sum {κ : Type*} (s : Finset κ) (v : κ → ι → ℝ) :
    coordinateFunctional (∑ k ∈ s, v k) = ∑ k ∈ s, coordinateFunctional (v k) := by
  classical
  induction s using Finset.induction_on with
  | empty => ext h; simp [coordinateFunctional_apply]
  | @insert k s hk ih => simp [Finset.sum_insert hk, coordinateFunctional_add, ih]

lemma lpNorm_add_le {p : ℝ} (hp : 1 ≤ p) (u v : ι → ℝ) :
    lpNorm p (u + v) ≤ lpNorm p u + lpNorm p v := by
  simpa [lpNorm, lpPower, Pi.add_apply] using Real.Lp_add_le Finset.univ u v hp

lemma lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → ℝ) = 0 := by
  simp [lpNorm, lpPower, hp.ne']

lemma lpNorm_neg (p : ℝ) (u : ι → ℝ) : lpNorm p (-u) = lpNorm p u := by
  simp [lpNorm, lpPower]

lemma lpNorm_smul {p : ℝ} (hp : 0 < p) (a : ℝ) (u : ι → ℝ) :
    lpNorm p (a • u) = |a| * lpNorm p u := by
  unfold lpNorm lpPower
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, Real.mul_rpow (abs_nonneg a) (abs_nonneg _),
    ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg a) _) (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)),
    ← Real.rpow_mul (abs_nonneg a), mul_one_div_cancel hp.ne', Real.rpow_one]

lemma lpNorm_sum_le {κ : Type*} {p : ℝ} (hp : 1 ≤ p)
    (s : Finset κ) (v : κ → ι → ℝ) :
    lpNorm p (∑ k ∈ s, v k) ≤ ∑ k ∈ s, lpNorm p (v k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [lpNorm_zero (lt_of_lt_of_le zero_lt_one hp)]
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk]
    exact (lpNorm_add_le hp _ _).trans (add_le_add_left ih _)

/-- The ordinary coordinate pairing, represented on the genuine ℓₚ space. -/
def coordinateFunctionalLp (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (v : ι → ℝ) : PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ) →L[ℝ] ℝ :=
  (coordinateFunctional v).comp (PiLp.continuousLinearEquiv (ENNReal.ofReal p) ℝ
    (fun _ : ι => ℝ)).toContinuousLinearMap

lemma coordinateFunctionalLp_apply (p : ℝ) [Fact (1 ≤ ENNReal.ofReal p)]
    (v : ι → ℝ) (x : PiLp (ENNReal.ofReal p) (fun _ : ι => ℝ)) :
    coordinateFunctionalLp p v x = ∑ i, v i * x i := by
  simp [coordinateFunctionalLp, coordinateFunctional_apply]

/-- Hölder identifies an upper bound on the operator norm with the paper's
actual ℓ_q gradient target, without a dimension factor. -/
theorem coordinateFunctionalLp_norm_le {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (hp : 1 < p) (v : ι → ℝ) :
    ‖coordinateFunctionalLp p v‖ ≤ lpNorm (dualExponent p) v := by
  apply ContinuousLinearMap.opNorm_le_bound _ (lpNorm_nonneg _ _)
  intro x
  rw [Real.norm_eq_abs, coordinateFunctionalLp_apply]
  have hpair : |∑ i, v i * x i| ≤ lpNorm (dualExponent p) v * lpNorm p (fun i => x i) := by
    apply abs_le.mpr
    constructor
    · have hn := Real.inner_le_Lp_mul_Lq Finset.univ (-v) (fun i => x i)
        (Real.HolderConjugate.conjExponent hp).symm
      have hn' : -(∑ i, v i * x i) ≤ lpNorm (dualExponent p) v * lpNorm p (fun i => x i) := by
        simpa [lpNorm, lpPower, dualExponent, Real.conjExponent, Finset.sum_neg_distrib] using hn
      linarith
    · simpa [lpNorm, lpPower, dualExponent, Real.conjExponent] using
        Real.inner_le_Lp_mul_Lq Finset.univ v (fun i => x i)
          (Real.HolderConjugate.conjExponent hp).symm
  have hx : lpNorm p (fun i => x i) = ‖x‖ := by
    rw [lpNorm_eq_piLp_norm p (by linarith)]
    rfl
  simpa only [hx] using hpair

end P31
