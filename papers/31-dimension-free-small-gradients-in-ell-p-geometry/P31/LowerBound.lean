import P31.VectorLocalization
import P31.QueryProgram
import P31.OracleModel
import Mathlib.Data.PNat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# The conditional local-oracle lower bound (Assumption 6.1 and Corollary 1.3)

The sole hard-family input is objective hardness at queried points, together
with the simultaneous normalized realization stated in Assumption 6.1.  The
localization, scaling, exact simulation, appended output query, and the
resulting gradient lower bound are proved here.
-/

noncomputable section
open scoped BigOperators
namespace P31.LowerBound
open Set QueryProgram

abbrev Point (p : ℝ) (d : ℕ) := PiLp (ENNReal.ofReal p) (fun _ : Fin d => ℝ)
abbrev Reply (d : ℕ) := ℝ × (Fin d → ℝ)
abbrev Method (p : ℝ) (d : ℕ) := Program (Point p d) (Reply d) (Point p d)

def exponent (p κ : ℝ) : ℝ := p / (κ * p + κ - p)

lemma exponent_pos {p κ : ℝ} (hp : 2 ≤ p) (hκ : 1 < κ) : 0 < exponent p κ := by
  unfold exponent
  apply div_pos (by linarith)
  have : 0 < p * (κ - 1) := mul_pos (by linarith) (by linarith)
  nlinarith

/-- A genuine differentiable convex finite-dimensional ℓₚ objective, with its
gradient in the ordinary coordinate pairing. -/
structure VectorInstance (p κ : ℝ) (d : ℕ) [Fact (1 ≤ ENNReal.ofReal p)] where
  value : Point p d → ℝ
  gradient : Point p d → Fin d → ℝ
  derivative : ∀ x, HasFDerivAt value (coordinateFunctionalLp p (gradient x)) x
  convex : ConvexOn ℝ univ value

namespace VectorInstance
variable {p κ : ℝ} {d : ℕ} [Fact (1 ≤ ENNReal.ofReal p)]

def oracle (I : VectorInstance p κ d) (x : Point p d) : Reply d := (I.value x, I.gradient x)

/-- The source class with initial point zero.  Convexity and differentiability
are already part of `VectorInstance`. -/
def InClass (I : VectorInstance p κ d) (L R : ℝ) : Prop :=
  (∀ x y, lpNorm (dualExponent p) (I.gradient x - I.gradient y) ≤
    L * ‖x - y‖ ^ (κ - 1)) ∧
  ∃ y, (∀ x, I.value y ≤ I.value x) ∧ ‖y‖ ≤ R

end VectorInstance

/-- Locality of a smoothing operator: its value at a point depends only on
the function on the stated norm ball.  The reduction itself needs only its
convexity, differentiability, and approximation properties. -/
def LocalSmoother {E : Type*} [NormedAddCommGroup E]
    (r : ℝ) (S : (E → ℝ) → E → ℝ) : Prop :=
  ∀ f g x, EqOn f g (Metric.closedBall x r) → S f x = S g x

/-- Every analytic property in the simultaneous normalized realization of
Assumption 6.1, including the exact finite max formula (6.3).  No objective
or gradient lower-bound conclusion is contained in this record. -/
structure NormalizedHardInstance (p κ : ℝ) (d : ℕ)
    [Fact (1 ≤ ENNReal.ofReal p)] (ζ : ℝ) extends VectorInstance p κ d where
  M : ℕ+
  δ : ℝ
  μ : ℝ
  η : ℝ
  r : ℝ
  delta_pos : 0 < δ
  mu_pos : 0 < μ
  eta_nonneg : 0 ≤ η
  radius_nonneg : 0 ≤ r
  z : Fin M → Fin d → ℝ
  z_norm : ∀ i, lpNorm (dualExponent p) (z i) ≤ 1
  S : ((Point p d) → ℝ) → (Point p d) → ℝ
  preserves_convex : ∀ f, ConvexOn ℝ univ f → ConvexOn ℝ univ (S f)
  local_smoother : LocalSmoother r S
  smooth : Differentiable ℝ (S (vectorHardLift p z δ r))
  uniform_error : ∀ x, |S (vectorHardLift p z δ r) x - vectorHardLift p z δ r x| ≤ η
  normalized_value : value = fun x => S (vectorHardLift p z δ r) x / μ
  holder : ∀ x y, lpNorm (dualExponent p) (gradient x - gradient y) ≤ ‖x - y‖ ^ (κ - 1)
  locality_bound : r ≤ δ / 8
  margin_bound : (M : ℝ) * δ ≤ μ * ζ
  error_bound : η ≤ μ * ζ / 4
  target_bound : 4 * μ * ζ ≤ 1

namespace NormalizedHardInstance
variable {p κ ζ : ℝ} {d : ℕ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- All normalized analytic conclusions are derived from the simultaneous
realization, using the already-proved localization argument. -/
theorem reduction (I : NormalizedHardInstance p κ d ζ) (hp : 1 < p) (hζ : 0 ≤ ζ) :
    ∃ y : Point p d, (∀ x, I.value y ≤ I.value x) ∧ ‖y‖ < 2 ∧
      ∀ x, lpNorm (dualExponent p) (I.gradient x) ≤ ζ / 8 →
        ‖x‖ < 4 ∧ I.value x - I.value y ≤ ζ := by
  let s := I.S (vectorHardLift p I.z I.δ I.r)
  have hs : ConvexOn ℝ univ s := I.preserves_convex _ (vectorHardLift_convex (by linarith) _ _ _)
  have he : ∀ x : Point p d,
      |s x - hardFunction (fun i => coordinateFunctionalLp p (I.z i)) I.δ I.r x| ≤ I.η := by
    intro x
    rw [← vectorHardLift_eq_hardFunction (by linarith : 0 < p) I.z I.δ I.r]
    exact I.uniform_error x
  obtain ⟨y, hy, hyr, hout⟩ := normalized_hard_family_reduction
    (fun i => coordinateFunctionalLp p (I.z i)) I.δ I.μ I.η I.r ζ
    I.delta_pos I.mu_pos hζ I.radius_nonneg I.locality_bound I.margin_bound
    I.error_bound I.target_bound s hs I.smooth he
  have hv : I.value = fun x => s x / I.μ := I.normalized_value
  refine ⟨y, ?_, hyr, ?_⟩
  · simpa only [hv] using hy
  · intro x hg
    have hd : HasFDerivAt (fun t => s t / I.μ) (coordinateFunctionalLp p (I.gradient x)) x := by
      simpa only [← hv] using I.derivative x
    have hb := (coordinateFunctionalLp_norm_le hp (I.gradient x)).trans hg
    simpa only [hv] using hout x (coordinateFunctionalLp p (I.gradient x)) hd hb

end NormalizedHardInstance

/-- Objective hardness is stated at each actual query position, not at an
arbitrary output.  The prefix decomposition counts the query being tested. -/
def QueriedObjectiveHard {p κ ζ : ℝ} {d : ℕ} [Fact (1 ≤ ENNReal.ofReal p)]
    (I : NormalizedHardInstance p κ d ζ) (P : Method p d) (threshold : ℝ) : Prop :=
  ∀ (pre : List (Point p d)) (x : Point p d) (post : List (Point p d)),
    (P.run I.toVectorInstance.oracle).queries = pre ++ x :: post →
    ((pre.length + 1 : ℕ) : ℝ) < threshold →
    ∀ y, (∀ w, I.value y ≤ I.value w) → ζ < I.value x - I.value y

/-- The precise external/source premise, Assumption 6.1.  It asserts only an
objective hard family with a simultaneous analytic realization.  In
particular, the gradient lower bound proved below is not an input field. -/
structure SimultaneousHardFamily (p κ : ℝ) [Fact (1 ≤ ENNReal.ofReal p)] where
  cObjective : ℝ
  CObjective : ℝ
  cQueries : ℝ
  cObjective_pos : 0 < cObjective
  CObjective_pos : 0 < CObjective
  cQueries_pos : 0 < cQueries
  realize : ∀ (d : ℕ), 1 ≤ d → ∀ ζ : ℝ, 0 < ζ → ζ ≤ cObjective →
    p ≤ Real.log (d : ℝ) → CObjective * ζ ^ (-exponent p κ) ≤ d →
    ∀ P : Method p d, ∃ I : NormalizedHardInstance p κ d ζ,
      QueriedObjectiveHard I P (cQueries * ζ ^ (-exponent p κ))

lemma coordinateFunctionalLp_smul {p : ℝ} {d : ℕ} [Fact (1 ≤ ENNReal.ofReal p)]
    (a : ℝ) (v : Fin d → ℝ) :
    coordinateFunctionalLp p (a • v) = a • coordinateFunctionalLp p v := by
  ext x
  simp only [coordinateFunctionalLp_apply, ContinuousLinearMap.smul_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

namespace VectorInstance
variable {p κ : ℝ} {d : ℕ} [Fact (1 ≤ ENNReal.ofReal p)]

/-- The actual scaled objective and its coordinate gradient from (6.7). -/
def scaled (I : VectorInstance p κ d) (L R : ℝ) (hL : 0 < L) (hR : 0 < R) :
    VectorInstance p κ d where
  value := rescaledHardObjective L R κ I.value
  gradient := fun x => rescaledGradientCoefficient L R κ • I.gradient ((4 / R) • x)
  derivative := by
    intro x
    rw [coordinateFunctionalLp_smul]
    exact rescaled_hard_hasFDerivAt L R κ hR I.value x _ (I.derivative _)
  convex := rescaled_hard_convex L R κ hL hR I.value I.convex

end VectorInstance

namespace NormalizedHardInstance
variable {p κ ζ : ℝ} {d : ℕ} [Fact (1 ≤ ENNReal.ofReal p)]

theorem scaled_inClass (I : NormalizedHardInstance p κ d ζ)
    (hp : 1 < p) (hζ : 0 ≤ ζ) (L R : ℝ) (hL : 0 < L) (hR : 0 < R) :
    (I.toVectorInstance.scaled L R hL hR).InClass L R := by
  constructor
  · intro x y
    change lpNorm (dualExponent p)
      (rescaledGradientCoefficient L R κ • I.gradient ((4 / R) • x) -
        rescaledGradientCoefficient L R κ • I.gradient ((4 / R) • y)) ≤ _
    have hc := rescaledGradientCoefficient_pos L R κ hL hR
    have hb : 0 < (4 : ℝ) / R := div_pos (by norm_num) hR
    rw [← smul_sub, lpNorm_smul (dualExponent_pos hp), abs_of_pos hc]
    have hh := I.holder ((4 / R) • x) ((4 / R) • y)
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hb,
      Real.mul_rpow hb.le (norm_nonneg _)] at hh
    exact (mul_le_mul_of_nonneg_left hh hc.le).trans_eq (by
      rw [← mul_assoc, rescaling_holder_coefficient L R κ hR])
  · obtain ⟨y, hy, hyr, hout⟩ := I.reduction hp hζ
    have hscaled := rescaled_minimizer L R κ hL hR I.value y hy (by linarith)
    exact ⟨(R / 4) • y, hscaled.1, hscaled.2⟩

/-- A small gradient on the scaled objective gives objective accuracy on
its normalized counterpart. -/
theorem scaled_output_gap (I : NormalizedHardInstance p κ d ζ)
    (hp : 1 < p) (hζ : 0 ≤ ζ) (L R ε : ℝ) (hL : 0 < L) (hR : 0 < R)
    (hζeq : ζ = normalizedObjectiveTarget L R κ ε)
    (x : Point p d)
    (hg : lpNorm (dualExponent p)
      ((I.toVectorInstance.scaled L R hL hR).gradient x) ≤ ε) :
    ∃ y, (∀ w, I.value y ≤ I.value w) ∧
      I.value ((4 / R) • x) - I.value y ≤ ζ := by
  obtain ⟨y, hy, hyr, hout⟩ := I.reduction hp hζ
  have hc := rescaledGradientCoefficient_pos L R κ hL hR
  change lpNorm (dualExponent p)
    (rescaledGradientCoefficient L R κ • I.gradient ((4 / R) • x)) ≤ ε at hg
  rw [lpNorm_smul (dualExponent_pos hp), abs_of_pos hc] at hg
  have hgn : lpNorm (dualExponent p) (I.gradient ((4 / R) • x)) ≤ ζ / 8 := by
    apply (mul_le_mul_iff_right₀ hc).mp
    have he : rescaledGradientCoefficient L R κ * (ζ / 8) = ε := by
      rw [hζeq, normalized_target_gradient_identity L R κ ε hL hR]
    rw [he]
    exact hg
  exact ⟨y, hy, (hout _ hgn).2⟩

end NormalizedHardInstance

/-- Simulate each scaled value-gradient reply from one normalized query;
then perform exactly one query at the arbitrary normalized output. -/
def normalizedSimulation {p κ : ℝ} {d : ℕ} [Fact (1 ≤ ENNReal.ofReal p)]
    (L R : ℝ) (P : Method p d) : Method p d :=
  ((Program.simulate (fun x : Point p d => (4 / R) • x)
    (fun (_ : Point p d) (reply : Reply d) =>
      ((L * R ^ κ / (4 : ℝ) ^ κ) * reply.1,
        rescaledGradientCoefficient L R κ • reply.2)) P).map
    (fun x => (4 / R) • x)).appendOutputQuery

lemma run_map {E G A B : Type*} (P : Program E G A) (f : A → B) (o : E → G) :
    (P.map f).run o = ⟨f (P.run o).value, (P.run o).queries, (P.run o).calls⟩ := by
  simp [Program.map, Program.run_bind]

/-- The simulation preserves every adaptive answer and call, and the only
extra call is the final output query.  This is an exact execution identity. -/
theorem normalizedSimulation_run {p κ : ℝ} {d : ℕ} [Fact (1 ≤ ENNReal.ofReal p)]
    (L R : ℝ) (hL : 0 < L) (hR : 0 < R) (P : Method p d)
    (I : VectorInstance p κ d) :
    (normalizedSimulation (κ := κ) L R P).run I.oracle =
      let r := P.run (I.scaled L R hL hR).oracle
      ⟨(4 / R) • r.value, r.queries.map (fun x => (4 / R) • x) ++ [(4 / R) • r.value],
        r.calls + 1⟩ := by
  unfold normalizedSimulation Program.appendOutputQuery
  rw [Program.run_bind]
  simp only [Program.run_query, Program.run_pure]
  simp only [run_map, Program.run_simulate]
  rfl

/-- Correctness is uniform over the entire source class; the program is
constructed without access to the unknown objective or its gradient. -/
def Correct {p κ : ℝ} {d : ℕ} [Fact (1 ≤ ENNReal.ofReal p)]
    (P : Method p d) (L R ε : ℝ) : Prop :=
  ∀ I : VectorInstance p κ d, I.InClass L R →
    lpNorm (dualExponent p) (I.gradient (P.run I.oracle).value) ≤ ε

/-- The actual conditional adversary argument: scaled gradient correctness
would solve the normalized objective, and the appended queried output forces
`Q + 1` past the source objective-hardness threshold. -/
theorem conditional_adversary {p κ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (H : SimultaneousHardFamily p κ) (hp : 1 < p)
    (d : ℕ) (hd : 1 ≤ d) (L R ε : ℝ) (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hz : normalizedObjectiveTarget L R κ ε ≤ H.cObjective)
    (hlog : p ≤ Real.log (d : ℝ))
    (hdim : H.CObjective * normalizedObjectiveTarget L R κ ε ^ (-exponent p κ) ≤ d)
    (P : Method p d) (hcorrect : Correct (κ := κ) P L R ε) :
    ∃ I : VectorInstance p κ d, I.InClass L R ∧
      H.cQueries * normalizedObjectiveTarget L R κ ε ^ (-exponent p κ) ≤
        ((P.run I.oracle).calls : ℝ) + 1 := by
  let ζ := normalizedObjectiveTarget L R κ ε
  have hζ : 0 < ζ := normalizedObjectiveTarget_pos L R κ ε hL hR hε
  obtain ⟨I, hhard⟩ := H.realize d hd ζ hζ hz hlog hdim
    (normalizedSimulation (κ := κ) L R P)
  let J := I.toVectorInstance.scaled L R hL hR
  have hJ : J.InClass L R := I.scaled_inClass hp hζ.le L R hL hR
  have hg := hcorrect J hJ
  obtain ⟨y, hy, hgap⟩ := I.scaled_output_gap hp hζ.le L R ε hL hR rfl
    (P.run J.oracle).value hg
  refine ⟨J, hJ, ?_⟩
  by_contra h
  have hlt : ((P.run J.oracle).calls : ℝ) + 1 < H.cQueries * ζ ^ (-exponent p κ) :=
    lt_of_not_ge h
  let pre := (P.run J.oracle).queries.map (fun x => (4 / R) • x)
  have hquery : ((normalizedSimulation (κ := κ) L R P).run I.toVectorInstance.oracle).queries =
      pre ++ (4 / R) • (P.run J.oracle).value :: [] := by
    have hh := congrArg (fun r : Execution (Point p d) (Point p d) => r.queries)
      (normalizedSimulation_run L R hL hR P I.toVectorInstance)
    exact hh
  have hlen : pre.length = (P.run J.oracle).calls := by
    rw [List.length_map, ← Program.calls_eq_length]
  have hposition : ((pre.length + 1 : ℕ) : ℝ) < H.cQueries * ζ ^ (-exponent p κ) := by
    simpa only [hlen, Nat.cast_add, Nat.cast_one] using hlt
  have hbad := hhard pre ((4 / R) • (P.run J.oracle).value) [] hquery hposition y hy
  exact (not_lt_of_ge hgap) hbad

/-- The `(p,κ)`-dependent factor converting the normalized objective target
to the original gradient target. -/
def accuracyFactor (κ : ℝ) : ℝ := 2 * (4 : ℝ) ^ κ

lemma accuracyFactor_pos (κ : ℝ) : 0 < accuracyFactor κ := by
  unfold accuracyFactor
  positivity

/-- Explicit source constants after shrinking the allowed accuracy. -/
def accuracyConstant {p κ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (H : SimultaneousHardFamily p κ) : ℝ :=
  min 1 (min (H.cObjective / accuracyFactor κ)
    ((H.cQueries / 2) ^ (1 / exponent p κ) / accuracyFactor κ))

def dimensionConstant {p κ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (H : SimultaneousHardFamily p κ) : ℝ :=
  H.CObjective * accuracyFactor κ ^ (-exponent p κ)

def queryConstant {p κ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (H : SimultaneousHardFamily p κ) : ℝ :=
  (H.cQueries / 2) * accuracyFactor κ ^ (-exponent p κ)

lemma lower_constants_pos {p κ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (H : SimultaneousHardFamily p κ) :
    0 < accuracyConstant H ∧ 0 < dimensionConstant H ∧ 0 < queryConstant H := by
  have hA := accuracyFactor_pos κ
  unfold accuracyConstant dimensionConstant queryConstant
  constructor
  · exact lt_min (by norm_num) (lt_min (div_pos H.cObjective_pos hA)
      (div_pos (Real.rpow_pos_of_pos (div_pos H.cQueries_pos (by norm_num)) _) hA))
  · exact ⟨mul_pos H.CObjective_pos (Real.rpow_pos_of_pos hA _),
      mul_pos (div_pos H.cQueries_pos (by norm_num)) (Real.rpow_pos_of_pos hA _)⟩

/-- The exact exponent identity in the final paragraph of Section 6. -/
lemma target_power_identity {p κ L R ε : ℝ}
    (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε) :
    normalizedObjectiveTarget L R κ ε ^ (-exponent p κ) =
      accuracyFactor κ ^ (-exponent p κ) *
        (L * R ^ (κ - 1) / ε) ^ exponent p κ := by
  have hT : 0 < L * R ^ (κ - 1) := mul_pos hL (Real.rpow_pos_of_pos hR _)
  have hA := accuracyFactor_pos κ
  have he : normalizedObjectiveTarget L R κ ε =
      accuracyFactor κ / (L * R ^ (κ - 1) / ε) := by
    unfold normalizedObjectiveTarget accuracyFactor
    field_simp
  rw [he, Real.div_rpow hA.le (div_pos hT hε).le,
    Real.rpow_neg (div_pos hT hε).le, div_inv_eq_mul]

/-- The source small-accuracy and dimension hypotheses follow from the
explicit constants in Corollary 1.3, and the hardness threshold is at least
two, allowing the one appended query to be absorbed. -/
theorem convert_source_conditions {p κ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (H : SimultaneousHardFamily p κ) (hβ : 0 < exponent p κ)
    (d : ℕ) (L R ε : ℝ) (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyConstant H * (L * R ^ (κ - 1)))
    (hdim : dimensionConstant H * (L * R ^ (κ - 1) / ε) ^ exponent p κ ≤ d) :
    normalizedObjectiveTarget L R κ ε ≤ H.cObjective ∧
      H.CObjective * normalizedObjectiveTarget L R κ ε ^ (-exponent p κ) ≤ d ∧
      2 ≤ H.cQueries * normalizedObjectiveTarget L R κ ε ^ (-exponent p κ) := by
  let T := L * R ^ (κ - 1)
  let A := accuracyFactor κ
  let ζ := normalizedObjectiveTarget L R κ ε
  have hT : 0 < T := mul_pos hL (Real.rpow_pos_of_pos hR _)
  have hA : 0 < A := accuracyFactor_pos κ
  have hζ : 0 < ζ := normalizedObjectiveTarget_pos L R κ ε hL hR hε
  have hzdef : ζ = A * ε / T := by rfl
  have hs1 : ε ≤ (H.cObjective / A) * T :=
    hsmall.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) hT.le)
  have hs2 : ε ≤ ((H.cQueries / 2) ^ (1 / exponent p κ) / A) * T :=
    hsmall.trans (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) hT.le)
  have hz1 : ζ ≤ H.cObjective := by
    rw [hzdef, div_le_iff₀ hT]
    calc
      A * ε ≤ A * ((H.cObjective / A) * T) := mul_le_mul_of_nonneg_left hs1 hA.le
      _ = H.cObjective * T := by field_simp
  have hz2 : ζ ≤ (H.cQueries / 2) ^ (1 / exponent p κ) := by
    rw [hzdef, div_le_iff₀ hT]
    calc
      A * ε ≤ A * (((H.cQueries / 2) ^ (1 / exponent p κ) / A) * T) :=
        mul_le_mul_of_nonneg_left hs2 hA.le
      _ = (H.cQueries / 2) ^ (1 / exponent p κ) * T := by field_simp
  have hzpow : ζ ^ exponent p κ ≤ H.cQueries / 2 := by
    have hh := Real.rpow_le_rpow hζ.le hz2 hβ.le
    rw [← Real.rpow_mul (div_pos H.cQueries_pos (by norm_num)).le,
      one_div_mul_cancel hβ.ne', Real.rpow_one] at hh
    exact hh
  refine ⟨hz1, ?_, ?_⟩
  · rw [target_power_identity hL hR hε]
    simpa only [dimensionConstant, mul_assoc] using hdim
  · change 2 ≤ H.cQueries * ζ ^ (-exponent p κ)
    rw [Real.rpow_neg hζ.le, ← div_eq_mul_inv,
      le_div_iff₀ (Real.rpow_pos_of_pos hζ _)]
    linarith

/-- Corollary 1.3, lower-bound half: every uniformly correct deterministic
value-gradient method has an actual source-class instance costing at least
the matching power.  The extra output query is absorbed into the constant. -/
theorem conditional_gradient_lower_bound {p κ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (H : SimultaneousHardFamily p κ) (hp : 2 ≤ p) (hκ : 1 < κ)
    (d : ℕ) (hd : 1 ≤ d) (L R ε : ℝ) (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyConstant H * (L * R ^ (κ - 1)))
    (hlog : p ≤ Real.log (d : ℝ))
    (hdim : dimensionConstant H * (L * R ^ (κ - 1) / ε) ^ exponent p κ ≤ d)
    (P : Method p d) (hcorrect : Correct (κ := κ) P L R ε) :
    ∃ I : VectorInstance p κ d, I.InClass L R ∧
      queryConstant H * (L * R ^ (κ - 1) / ε) ^ exponent p κ ≤ (P.run I.oracle).calls := by
  obtain ⟨hz, hd', htwo⟩ := convert_source_conditions H (exponent_pos hp hκ)
    d L R ε hL hR hε hsmall hdim
  obtain ⟨I, hI, hcount⟩ := conditional_adversary H (by linarith) d hd L R ε hL hR hε
    hz hlog hd' P hcorrect
  refine ⟨I, hI, ?_⟩
  have habsorb : (H.cQueries / 2) * normalizedObjectiveTarget L R κ ε ^ (-exponent p κ) ≤
      ((P.run I.oracle).calls : ℝ) := by nlinarith
  rw [target_power_identity hL hR hε] at habsorb
  simpa only [queryConstant, mul_assoc] using habsorb

/-- A feasible worst-case query budget for a deterministic value-gradient
method.  Real budgets are convenient for the asymptotic constants; actual
execution costs remain natural numbers and count repeated calls. -/
def FeasibleBudget {p κ : ℝ} {d : ℕ} [Fact (1 ≤ ENNReal.ofReal p)]
    (L R ε budget : ℝ) : Prop :=
  0 ≤ budget ∧ ∃ P : Method p d, Correct (κ := κ) P L R ε ∧
    ∀ I : VectorInstance p κ d, I.InClass L R → (P.run I.oracle).calls ≤ budget

/-- The infimum in the source minimax definition, over deterministic local
value-gradient methods with uniform finite query budgets. -/
def complexity {p κ : ℝ} {d : ℕ} [Fact (1 ≤ ENNReal.ofReal p)] (L R ε : ℝ) : ℝ :=
  sInf {budget : ℝ | FeasibleBudget (p := p) (κ := κ) (d := d) L R ε budget}

lemma feasible_bounded_below {p κ : ℝ} {d : ℕ} [Fact (1 ≤ ENNReal.ofReal p)] (L R ε : ℝ) :
    BddBelow {budget : ℝ | FeasibleBudget (p := p) (κ := κ) (d := d) L R ε budget} :=
  ⟨0, fun _ hb => hb.1⟩

/-- The adversarial instance lower-bounds every feasible worst-case budget. -/
theorem feasible_budget_lower_bound {p κ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (H : SimultaneousHardFamily p κ) (hp : 2 ≤ p) (hκ : 1 < κ)
    (d : ℕ) (hd : 1 ≤ d) (L R ε : ℝ) (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyConstant H * (L * R ^ (κ - 1)))
    (hlog : p ≤ Real.log (d : ℝ))
    (hdim : dimensionConstant H * (L * R ^ (κ - 1) / ε) ^ exponent p κ ≤ d)
    (budget : ℝ) (hb : FeasibleBudget (p := p) (κ := κ) (d := d) L R ε budget) :
    queryConstant H * (L * R ^ (κ - 1) / ε) ^ exponent p κ ≤ budget := by
  obtain ⟨hb0, P, hcorrect, hcost⟩ := hb
  obtain ⟨I, hI, hlower⟩ := conditional_gradient_lower_bound H hp hκ d hd L R ε hL hR hε
    hsmall hlog hdim P hcorrect
  exact hlower.trans (hcost I hI)

/-- Pointwise minimax comparison.  The upper hypothesis is precisely a
base upper-theorem budget, and the lower conclusion is derived entirely from
the objective-only Assumption 6.1. -/
theorem conditional_matching {p κ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (H : SimultaneousHardFamily p κ) (hp : 2 ≤ p) (hκ : 1 < κ)
    (d : ℕ) (hd : 1 ≤ d) (L R ε : ℝ) (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyConstant H * (L * R ^ (κ - 1)))
    (hlog : p ≤ Real.log (d : ℝ))
    (hdim : dimensionConstant H * (L * R ^ (κ - 1) / ε) ^ exponent p κ ≤ d)
    (CUpper : ℝ)
    (hupper : FeasibleBudget (p := p) (κ := κ) (d := d) L R ε
      (CUpper * (1 + (L * R ^ (κ - 1) / ε) ^ exponent p κ))) :
    queryConstant H * (L * R ^ (κ - 1) / ε) ^ exponent p κ ≤
      complexity (p := p) (κ := κ) (d := d) L R ε ∧
    complexity (p := p) (κ := κ) (d := d) L R ε ≤
      (2 * CUpper) * (L * R ^ (κ - 1) / ε) ^ exponent p κ := by
  have hne : {budget : ℝ | FeasibleBudget (p := p) (κ := κ) (d := d) L R ε budget}.Nonempty :=
    ⟨_, hupper⟩
  constructor
  · apply le_csInf hne
    intro b hb
    exact feasible_budget_lower_bound H hp hκ d hd L R ε hL hR hε hsmall hlog hdim b hb
  · have hu : complexity (p := p) (κ := κ) (d := d) L R ε ≤
        CUpper * (1 + (L * R ^ (κ - 1) / ε) ^ exponent p κ) :=
      csInf_le (feasible_bounded_below L R ε) hupper
    have hT : 0 < L * R ^ (κ - 1) := mul_pos hL (Real.rpow_pos_of_pos hR _)
    have heT : ε ≤ L * R ^ (κ - 1) :=
      hsmall.trans (mul_le_of_le_one_left hT.le (min_le_left _ _))
    have hr : 1 ≤ L * R ^ (κ - 1) / ε := (le_div_iff₀ hε).mpr (by simpa using heT)
    have hpw := Real.one_le_rpow hr (exponent_pos hp hκ).le
    have hc : 0 ≤ CUpper := by
      have hpw0 : 0 < 1 + (L * R ^ (κ - 1) / ε) ^ exponent p κ := by positivity
      exact (mul_nonneg_iff_of_pos_right hpw0).mp hupper.1
    nlinarith

/-- Uniform form of Corollary 1.3.  All lower constants depend only on the
fixed geometry and the constants of Assumption 6.1; the upper half is passed
as the independently established base theorem. -/
theorem corollary1_3 {p κ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (H : SimultaneousHardFamily p κ) (hp : 2 ≤ p) (hκ : 1 < κ) (hκhi : κ ≤ 2)
    (CUpper : ℝ) (hCUpper : 0 < CUpper)
    (upper : ∀ (d : ℕ), 1 ≤ d → ∀ (L R ε : ℝ), 0 < L → 0 < R → 0 < ε →
      FeasibleBudget (p := p) (κ := κ) (d := d) L R ε
        (CUpper * (1 + (L * R ^ (κ - 1) / ε) ^ exponent p κ))) :
    ∃ cAccuracy CLowerDimension cLower CUpper' : ℝ,
      0 < cAccuracy ∧ 0 < CLowerDimension ∧ 0 < cLower ∧ 0 < CUpper' ∧
      ∀ (d : ℕ), 1 ≤ d → ∀ (L R ε : ℝ), 0 < L → 0 < R → 0 < ε →
        ε ≤ cAccuracy * (L * R ^ (κ - 1)) → p ≤ Real.log (d : ℝ) →
        CLowerDimension * (L * R ^ (κ - 1) / ε) ^ exponent p κ ≤ d →
        cLower * (L * R ^ (κ - 1) / ε) ^ exponent p κ ≤
          complexity (p := p) (κ := κ) (d := d) L R ε ∧
        complexity (p := p) (κ := κ) (d := d) L R ε ≤
          CUpper' * (L * R ^ (κ - 1) / ε) ^ exponent p κ := by
  have hκrange : 1 < κ ∧ κ ≤ 2 := ⟨hκ, hκhi⟩
  obtain ⟨hc, hD, hq⟩ := lower_constants_pos H
  refine ⟨accuracyConstant H, dimensionConstant H, queryConstant H, 2 * CUpper,
    hc, hD, hq, mul_pos (by norm_num) hCUpper, ?_⟩
  intro d hd L R ε hL hR hε hsmall hlog hdim
  exact conditional_matching H hp hκrange.1 d hd L R ε hL hR hε hsmall hlog hdim CUpper
    (upper d hd L R ε hL hR hε)

/-- Compile any bounded exact-transcript controller from Definition 1.1
into its finite adaptive query tree.  Exhausted fuel returns `none` and
performs no extra oracle invocation. -/
def protocolProgram {E G : Type*} (P : OracleModel.Protocol E G) :
    ℕ → OracleModel.Transcript E G → Program E G (Option E)
  | 0, _ => .pure none
  | fuel + 1, tr => match P.next tr with
    | .output x => .pure (some x)
    | .query x => .query x (fun g => protocolProgram P fuel (tr ++ [(x, g)]))

/-- The compiler preserves both the original controller's output and its
invocation counter, including repeated queries. -/
theorem protocolProgram_run {E G : Type*} (P : OracleModel.Protocol E G)
    (o : E → G) (fuel : ℕ) (tr : OracleModel.Transcript E G) :
    ((protocolProgram P fuel tr).run o).value = (OracleModel.run P o fuel tr).output ∧
      ((protocolProgram P fuel tr).run o).calls = (OracleModel.run P o fuel tr).calls := by
  induction fuel generalizing tr with
  | zero => simp [protocolProgram, OracleModel.run]
  | succ fuel ih =>
    simp only [protocolProgram, OracleModel.run]
    split
    · rename_i x h
      simp [h]
    · rename_i x h
      simp only [h, Program.run_query]
      obtain ⟨hv, hc⟩ := ih (tr ++ [(x, o x)])
      exact ⟨hv, congrArg (fun n : ℕ => n + 1) hc⟩

/-- Turn a bounded transcript controller into a point-output method.  The
fallback is relevant only when its stated termination guarantee fails. -/
def protocolMethod {p : ℝ} {d : ℕ} (P : OracleModel.Protocol (Point p d) (Reply d))
    (fuel : ℕ) (fallback : Point p d) : Method p d :=
  (protocolProgram P fuel []).map (fun out => out.getD fallback)

lemma protocolMethod_calls {p κ : ℝ} {d : ℕ} [Fact (1 ≤ ENNReal.ofReal p)]
    (P : OracleModel.Protocol (Point p d) (Reply d)) (fuel : ℕ) (fallback : Point p d)
    (I : VectorInstance p κ d) :
    ((protocolMethod P fuel fallback).run I.oracle).calls =
      (OracleModel.run P I.oracle fuel []).calls := by
  rw [protocolMethod, run_map]
  exact (protocolProgram_run P I.oracle fuel []).2

/-- Consequently the lower bound also applies directly to the original
transcript protocols whenever they terminate correctly within a uniform
finite budget.  No query-tree restriction on that controller is assumed. -/
theorem conditional_protocol_lower_bound {p κ : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]
    (H : SimultaneousHardFamily p κ) (hp : 2 ≤ p) (hκ : 1 < κ)
    (d : ℕ) (hd : 1 ≤ d) (L R ε : ℝ) (hL : 0 < L) (hR : 0 < R) (hε : 0 < ε)
    (hsmall : ε ≤ accuracyConstant H * (L * R ^ (κ - 1)))
    (hlog : p ≤ Real.log (d : ℝ))
    (hdim : dimensionConstant H * (L * R ^ (κ - 1) / ε) ^ exponent p κ ≤ d)
    (P : OracleModel.Protocol (Point p d) (Reply d)) (fuel : ℕ)
    (hcorrect : ∀ I : VectorInstance p κ d, I.InClass L R → ∃ x,
      (OracleModel.run P I.oracle fuel []).output = some x ∧
      lpNorm (dualExponent p) (I.gradient x) ≤ ε) :
    ∃ I : VectorInstance p κ d, I.InClass L R ∧
      queryConstant H * (L * R ^ (κ - 1) / ε) ^ exponent p κ ≤
        (OracleModel.run P I.oracle fuel []).calls := by
  have hc : Correct (κ := κ) (protocolMethod P fuel (0 : Point p d)) L R ε := by
    intro I hI
    obtain ⟨x, hx, hg⟩ := hcorrect I hI
    have he := (protocolProgram_run P I.oracle fuel []).1
    rw [hx] at he
    simpa only [protocolMethod, run_map, he, Option.getD_some] using hg
  obtain ⟨I, hI, hcount⟩ := conditional_gradient_lower_bound H hp hκ d hd L R ε hL hR hε
    hsmall hlog hdim (protocolMethod P fuel 0) hc
  exact ⟨I, hI, by simpa only [protocolMethod_calls] using hcount⟩

end P31.LowerBound
