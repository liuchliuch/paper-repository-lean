import Paper27.Geometry.TangentConnection
import Paper27.Geometry.RetractionAtlas
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# Taylor germs of actual retraction coordinate functions

The polynomial root-gap argument is proved here. The only Taylor interface is
universal over analytic scalar germs: finite truncation, ordinary operations,
composition, derivative coefficients, and a monomial order bound. The geometric
data are actual analytic coordinate functions with their exact germ identities;
neither equation (7), a connection, nor existence of compatible jets is a field.
-/

noncomputable section
open scoped Manifold Topology
open Filter Polynomial Finset

namespace Paper27.Geometry.TaylorGerms

/-- Equality through degree `d`, as an actual polynomial ideal congruence. -/
def JetEq (d : ℕ) (P Q : ℂ[X]) : Prop := X ^ (d + 1) ∣ P - Q

namespace JetEq

theorem refl (d : ℕ) (P : ℂ[X]) : JetEq d P P := by simp [JetEq]
theorem symm {d : ℕ} {P Q : ℂ[X]} (h : JetEq d P Q) : JetEq d Q P := by
  simpa only [JetEq, neg_sub] using dvd_neg.mpr h
theorem trans {d : ℕ} {P Q R : ℂ[X]} (h : JetEq d P Q) (h' : JetEq d Q R) :
    JetEq d P R := by
  have hh := dvd_add h h'
  simpa only [sub_add_sub_cancel] using hh

theorem coefficient {d : ℕ} {P Q : ℂ[X]} (h : JetEq d P Q) (k : ℕ) (hk : k ≤ d) :
    P.coeff k = Q.coeff k := by
  have hz := (X_pow_dvd_iff.mp h) k (by omega)
  simpa only [coeff_sub, sub_eq_zero] using hz

end JetEq

/-- The geometric-sum factor in a difference of powers has nonzero constant
term at a nonzero root, so the prime `X` cannot divide that factor. -/
theorem unit_root_gap {n : ℕ} (hn : 0 < n) (Q : ℂ[X]) (hQ : Q.coeff 0 ≠ 0)
    (hpower : X ^ n ∣ Q ^ n - C ((Q.coeff 0) ^ n)) :
    X ^ n ∣ Q - C (Q.coeff 0) := by
  let S : ℂ[X] := ∑ i ∈ range n, Q ^ i * C (Q.coeff 0) ^ (n - 1 - i)
  have hconstant : S.coeff 0 = (n : ℂ) * (Q.coeff 0) ^ (n - 1) := by
    change constantCoeff S = _
    dsimp only [S]
    rw [map_sum]
    simp only [map_mul, map_pow]
    rw [show constantCoeff (C (Q.coeff 0)) = Q.coeff 0 from coeff_C_zero]
    change (∑ i ∈ range n, (Q.coeff 0) ^ i * (Q.coeff 0) ^ (n - 1 - i)) = _
    calc
      _ = ∑ i ∈ range n, (Q.coeff 0) ^ (n - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← pow_add, show i + (n - 1 - i) = n - 1 by
          have := Finset.mem_range.mp hi
          omega]
      _ = (n : ℂ) * (Q.coeff 0) ^ (n - 1) := by simp [nsmul_eq_mul]
  have hS : ¬ (X : ℂ[X]) ∣ S := by
    rw [X_dvd_iff, hconstant]
    exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hn)) (pow_ne_zero _ hQ)
  have hfactor : (Q - C (Q.coeff 0)) * S = Q ^ n - C ((Q.coeff 0) ^ n) := by
    simpa only [S, C_pow] using (Commute.all Q (C (Q.coeff 0))).mul_geom_sum₂ n
  exact (prime_X : Prime (X : ℂ[X])).pow_dvd_of_dvd_mul_right n hS (hfactor ▸ hpower)

/-- A normal jet is forced to have its gap; sparseness is a conclusion. The
input is only the raw nth-power congruence and its nonzero first derivative. -/
theorem normal_root_gap {n : ℕ} (hn : 0 < n) (Y H : ℂ[X]) (p : ℂ)
    (hzero : Y.coeff 0 = 0) (hlinear : Y.coeff 1 ≠ 0)
    (hpower : JetEq (2 * n) (Y ^ n) (X ^ n * (C p + X ^ n * H))) :
    ∃ R : ℂ[X], Y = NormalJets.normalChange n (Y.coeff 1) R := by
  obtain ⟨Q, hY⟩ := X_dvd_iff.mpr hzero
  have hfirst : Y.coeff 1 = Q.coeff 0 := by
    rw [hY]
    exact coeff_X_mul Q 0
  have hQ : Q.coeff 0 ≠ 0 := by rwa [← hfirst]
  have heq : Y ^ n - X ^ n * (C p + X ^ n * H) =
      X ^ n * (Q ^ n - C p - X ^ n * H) := by
    rw [hY, mul_pow]
    ring
  have hmod := hpower
  unfold JetEq at hmod
  rw [heq, show 2 * n + 1 = n + (n + 1) by omega, pow_add] at hmod
  have hdiv : X ^ (n + 1) ∣ Q ^ n - C p - X ^ n * H :=
    (mul_dvd_mul_iff_left (pow_ne_zero n (X_ne_zero : (X : ℂ[X]) ≠ 0))).mp hmod
  have hlow : X ^ n ∣ Q ^ n - C p := by
    have hd := dvd_trans (pow_dvd_pow (X : ℂ[X]) (by omega : n ≤ n + 1)) hdiv
    have hh := dvd_add hd (dvd_mul_right (X ^ n) H)
    simpa only [sub_add_cancel] using hh
  have hleading : (Q.coeff 0) ^ n = p := by
    have hc := (X_pow_dvd_iff.mp hlow) 0 hn
    have hp : (Q ^ n).coeff 0 = (Q.coeff 0) ^ n := map_pow constantCoeff Q n
    simpa only [coeff_sub, hp, coeff_C_zero, sub_eq_zero] using hc
  have hgap : X ^ n ∣ Q - C (Q.coeff 0) :=
    unit_root_gap hn Q hQ (by simpa only [hleading] using hlow)
  obtain ⟨R, hR⟩ := hgap
  refine ⟨R, ?_⟩
  have hQeq : Q = C (Q.coeff 0) + X ^ n * R := by
    linear_combination hR
  rw [hfirst, hY]
  calc
    X * Q = X * (C (Q.coeff 0) + X ^ n * R) := congrArg (fun A : ℂ[X] => X * A) hQeq
    _ = NormalJets.normalChange n (Q.coeff 0) R := by
      simp only [NormalJets.normalChange, pow_succ]
      ring

/-- The raw power congruence already forces the zero constant term, so the
root-gap conclusion needs only the nonzero linear coefficient. -/
theorem normal_root_gap_from_power {n : ℕ} (hn : 0 < n) (Y H : ℂ[X]) (p : ℂ)
    (hlinear : Y.coeff 1 ≠ 0)
    (hpower : JetEq (2 * n) (Y ^ n) (X ^ n * (C p + X ^ n * H))) :
    ∃ R : ℂ[X], Y = NormalJets.normalChange n (Y.coeff 1) R := by
  have hc := hpower.coefficient 0 (by omega)
  have hconstant : (Y ^ n).coeff 0 = (Y.coeff 0) ^ n := map_pow constantCoeff Y n
  have hright : (X ^ n * (C p + X ^ n * H)).coeff 0 = 0 := by
    rw [coeff_X_pow_mul', if_neg (by omega)]
  have hzero : Y.coeff 0 = 0 :=
    (pow_eq_zero_iff (Nat.ne_of_gt hn)).mp (hconstant.symm.trans (hc.trans hright))
  exact normal_root_gap hn Y H p hzero hlinear hpower

/-- The ordinary quadratic decomposition of a polynomial, with all higher
coefficients retained in an actual divisible remainder. -/
theorem quadratic_decomposition (B : ℂ[X]) :
    ∃ R : ℂ[X], B = C (B.coeff 0) + C (B.coeff 1) * X +
      C (B.coeff 2) * X ^ 2 + X ^ 3 * R := by
  have hd : X ^ 3 ∣ B - (C (B.coeff 0) + C (B.coeff 1) * X + C (B.coeff 2) * X ^ 2) := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2) with rfl | rfl | rfl <;> simp
  obtain ⟨R, hR⟩ := hd
  refine ⟨R, ?_⟩
  linear_combination hR

/-- Substitution of an order-at-least-`n` polynomial kills the entire cubic
remainder through degree `2n`. This is proved here, not a Taylor interface law. -/
theorem quadratic_composition_mod {n : ℕ} (hn : 0 < n) (B P : ℂ[X])
    (hB : B.coeff 0 = 0) (hP : X ^ n ∣ P) :
    JetEq (2 * n) (B.comp P)
      (C (B.coeff 1) * P + C (B.coeff 2) * P ^ 2) := by
  obtain ⟨R, hR⟩ := quadratic_decomposition B
  have heq : B.comp P - (C (B.coeff 1) * P + C (B.coeff 2) * P ^ 2) =
      P ^ 3 * R.comp P := by
    have hc := congrArg (fun A : ℂ[X] => A.comp P) hR
    simp only [add_comp, mul_comp, pow_comp, C_comp, X_comp, hB, map_zero, zero_add] at hc
    linear_combination hc
  unfold JetEq
  rw [heq]
  have hp : X ^ (n * 3) ∣ P ^ 3 := by
    simpa only [← pow_mul] using pow_dvd_pow_of_dvd hP 3
  exact dvd_mul_of_dvd_left
    (dvd_trans (pow_dvd_pow (X : ℂ[X]) (by omega : 2 * n + 1 ≤ n * 3)) hp) _

/-- Universal finite Taylor calculus for scalar analytic germs at zero.
These are ordinary power-series truncation laws, independently of any curve,
retraction, ramification component, connection, or obstruction. A classical
source is Lebl, Tasty Bits of Several Complex Variables v4.4, Theorem 1.2.1,
with the usual one-variable Taylor coefficient and substitution formulas. -/
structure TaylorCalculus where
  jet : ℕ → (ℂ → ℂ) → ℂ[X]
  bounded : ∀ d f, (jet d f).natDegree ≤ d
  congr : ∀ d {f g : ℂ → ℂ}, f =ᶠ[𝓝 0] g → jet d f = jet d g
  constant : ∀ d f, AnalyticAt ℂ f 0 → (jet d f).coeff 0 = f 0
  first : ∀ d f, AnalyticAt ℂ f 0 → 1 ≤ d → (jet d f).coeff 1 = deriv f 0
  second : ∀ d f, AnalyticAt ℂ f 0 → 2 ≤ d → (jet d f).coeff 2 = deriv (deriv f) 0 / 2
  polynomial : ∀ d (P : ℂ[X]), P.natDegree ≤ d → jet d (fun z => P.eval z) = P
  add : ∀ d f g, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 →
    jet d (fun z => f z + g z) = jet d f + jet d g
  mul : ∀ d f g, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 →
    JetEq d (jet d (fun z => f z * g z)) (jet d f * jet d g)
  power : ∀ d f m, AnalyticAt ℂ f 0 →
    JetEq d (jet d (fun z => f z ^ m)) (jet d f ^ m)
  composition : ∀ d f g, AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 → g 0 = 0 →
    JetEq d (jet d (f ∘ g)) ((jet d f).comp (jet d g))
  order_factor : ∀ d m f h, m ≤ d → AnalyticAt ℂ f 0 → AnalyticAt ℂ h 0 →
    f =ᶠ[𝓝 0] (fun z => z ^ m * h z) →
    X ^ m ∣ jet d f ∧ (jet d f).coeff m = h 0

/-- The actual centred base chart transition. -/
def baseChange (D : Curve) (i j p : D) (z : ℂ) : ℂ :=
  D.chartChange i j ((chartAt ℂ i) p + z) - D.chartChange i j ((chartAt ℂ i) p)

@[simp] theorem baseChange_zero (D : Curve) (i j p : D) : baseChange D i j p 0 = 0 := by
  simp [baseChange]

theorem baseChange_first (D : Curve) (i j p : D) :
    deriv (baseChange D i j p) 0 = D.chartJacobian i j p := by
  change deriv (fun z => D.chartChange i j ((chartAt ℂ i) p + z) -
    D.chartChange i j ((chartAt ℂ i) p)) 0 = _
  rw [deriv_sub_const, deriv_comp_const_add, add_zero]
  rfl

/-- Base transitions are analytic by actual chart differentiability on a
neighbourhood and Mathlib's one-variable Cauchy theorem. -/
theorem baseChange_analytic (D : Curve) (i j p : D)
    (hi : p ∈ D.chartDomain i) (hj : p ∈ D.chartDomain j) :
    AnalyticAt ℂ (baseChange D i j p) 0 := by
  have ht : ∀ᶠ z in 𝓝 ((chartAt ℂ i) p), z ∈ (chartAt ℂ i).target :=
    (chartAt ℂ i).open_target.mem_nhds ((chartAt ℂ i).map_source hi)
  have hto : Tendsto (chartAt ℂ i).symm (𝓝 ((chartAt ℂ i) p)) (𝓝 p) := by
    simpa only [(chartAt ℂ i).left_inv hi] using
      ((chartAt ℂ i).continuousAt_symm ((chartAt ℂ i).map_source hi)).tendsto
  have hd : ∀ᶠ z in 𝓝 ((chartAt ℂ i) p), DifferentiableAt ℂ (D.chartChange i j) z := by
    filter_upwards [ht, hto ((chartAt ℂ j).open_source.mem_nhds hj)] with z hz hjz
    exact mdifferentiableAt_iff_differentiableAt.mp
      (((mdifferentiable_chart (I := 𝓘(ℂ, ℂ)) j).mdifferentiableAt hjz).comp z
        ((mdifferentiable_chart (I := 𝓘(ℂ, ℂ)) i).mdifferentiableAt_symm hz))
  have hf : AnalyticAt ℂ (D.chartChange i j) ((chartAt ℂ i) p) :=
    Complex.analyticAt_iff_eventually_differentiableAt.mpr hd
  have hs : AnalyticAt ℂ (fun z : ℂ => (chartAt ℂ i) p + z) 0 :=
    analyticAt_const.fun_add analyticAt_id
  have ho : AnalyticAt ℂ (D.chartChange i j) ((fun z : ℂ => (chartAt ℂ i) p + z) 0) := by
    simpa only [add_zero] using hf
  exact (ho.comp hs).fun_sub analyticAt_const

/-- The actual tangent transition in a source coordinate is the derivative
of the actual base chart change, as a germ on every actual overlap. -/
theorem tangent_transition_germ (D : Curve) (T : TangentLineCocycle D) (i j p : D)
    (hi : p ∈ D.chartDomain i) (hj : p ∈ D.chartDomain j) :
    (T.bundle.transition i j ∘ (chartAt ℂ i).symm) =ᶠ[𝓝 ((chartAt ℂ i) p)]
      deriv (D.chartChange i j) := by
  have ht : ∀ᶠ z in 𝓝 ((chartAt ℂ i) p), z ∈ (chartAt ℂ i).target :=
    (chartAt ℂ i).open_target.mem_nhds ((chartAt ℂ i).map_source hi)
  have hto : Tendsto (chartAt ℂ i).symm (𝓝 ((chartAt ℂ i) p)) (𝓝 p) := by
    simpa only [(chartAt ℂ i).left_inv hi] using
      ((chartAt ℂ i).continuousAt_symm ((chartAt ℂ i).map_source hi)).tendsto
  filter_upwards [ht, hto ((chartAt ℂ j).open_source.mem_nhds hj)] with z hz hjz
  have hh := T.transition_eq i j ((chartAt ℂ i).symm z)
    ((chartAt ℂ i).map_target hz) hjz
  simpa only [Function.comp_apply, Curve.chartJacobian, (chartAt ℂ i).right_inv hz] using hh

/-- The second derivative of the actual centred chart change equals the
coordinate derivative of its actual tangent transition. -/
theorem baseChange_second (D : Curve) (T : TangentLineCocycle D) (i j p : D)
    (hi : p ∈ D.chartDomain i) (hj : p ∈ D.chartDomain j) :
    deriv (deriv (baseChange D i j p)) 0 =
      D.coordinateDerivative i (T.bundle.transition i j) p := by
  have hd : deriv (baseChange D i j p) =
      fun z => deriv (D.chartChange i j) ((chartAt ℂ i) p + z) := by
    funext z
    change deriv (fun w => D.chartChange i j ((chartAt ℂ i) p + w) -
      D.chartChange i j ((chartAt ℂ i) p)) z = _
    rw [deriv_sub_const, deriv_comp_const_add]
  rw [hd, deriv_comp_const_add, add_zero]
  exact (tangent_transition_germ D T i j p hi hj).deriv_eq.symm

/-- Actual analytic retraction coordinate functions and their exact
transformation identities, before applying any Taylor truncation functor. -/
structure RetractionGerms (D : Curve) (T : TangentLineCocycle D) (n : ℕ) (a : ℂ) where
  third : D → D → ℂ → ℂ
  thirdFactor : D → D → ℂ → ℂ
  normal : D → D → D → ℂ → ℂ
  third_analytic : ∀ i p, p ∈ D.chartDomain i → AnalyticAt ℂ (third i p) 0
  factor_analytic : ∀ i p, p ∈ D.chartDomain i → AnalyticAt ℂ (thirdFactor i p) 0
  factor_leading : ∀ i p, p ∈ D.chartDomain i → thirdFactor i p 0 = a
  third_factor : ∀ i p, p ∈ D.chartDomain i →
    third i p =ᶠ[𝓝 0] fun z => z ^ n * thirdFactor i p z
  normal_analytic : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
    AnalyticAt ℂ (normal i j p) 0
  normal_zero : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j → normal i j p 0 = 0
  normal_derivative_ne_zero : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
    deriv (normal i j p) 0 ≠ 0
  normal_identity : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
    (fun z => normal i j p z ^ n) =ᶠ[𝓝 0] baseChange D i j p ∘ (fun z => z ^ n)
  third_identity : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
    third j p ∘ normal i j p =ᶠ[𝓝 0] baseChange D i j p ∘ third i p

namespace RetractionGerms

variable {D : Curve} {T : TangentLineCocycle D} {n : ℕ} {a : ℂ}

def jet (J : TaylorCalculus) (R : RetractionGerms D T n a) (i p : D) : ℂ[X] := J.jet (2 * n) (R.third i p)
def normalJet (J : TaylorCalculus) (R : RetractionGerms D T n a) (i j p : D) : ℂ[X] :=
  J.jet (2 * n) (R.normal i j p)
def baseJet (J : TaylorCalculus) (i j p : D) : ℂ[X] := J.jet (2 * n) (baseChange D i j p)
def doubleCoefficient (J : TaylorCalculus) (R : RetractionGerms D T n a) (i p : D) : ℂ :=
  (R.jet J i p).coeff (2 * n)

 theorem jet_order_leading (J : TaylorCalculus) (R : RetractionGerms D T n a)
    (hn : 0 < n) (i p : D) (hi : p ∈ D.chartDomain i) :
    X ^ n ∣ R.jet J i p ∧ (R.jet J i p).coeff n = a := by
  have h := J.order_factor (2 * n) n (R.third i p) (R.thirdFactor i p) (by omega)
    (R.third_analytic i p hi) (R.factor_analytic i p hi) (R.third_factor i p hi)
  exact ⟨h.1, h.2.trans (R.factor_leading i p hi)⟩

 theorem normal_power_mod (J : TaylorCalculus) (R : RetractionGerms D T n a)
    (hn : 0 < n) (i j p : D) (hi : p ∈ D.chartDomain i) (hj : p ∈ D.chartDomain j) :
    JetEq (2 * n) (R.normalJet J i j p ^ n)
      (C (D.chartJacobian i j p) * X ^ n +
        C (D.coordinateDerivative i (T.bundle.transition i j) p / 2) * (X ^ n) ^ 2) := by
  let B := baseJet (D := D) (n := n) J i j p
  have hB0 : B.coeff 0 = 0 := (J.constant _ _ (baseChange_analytic D i j p hi hj)).trans (baseChange_zero D i j p)
  have hB1 : B.coeff 1 = D.chartJacobian i j p :=
    (J.first _ _ (baseChange_analytic D i j p hi hj) (by omega)).trans (baseChange_first D i j p)
  have hB2 : B.coeff 2 = D.coordinateDerivative i (T.bundle.transition i j) p / 2 := by
    change (J.jet (2 * n) (baseChange D i j p)).coeff 2 = _
    rw [J.second (2 * n) _ (baseChange_analytic D i j p hi hj) (by omega),
      baseChange_second D T i j p hi hj]
  have hmono : J.jet (2 * n) (fun z : ℂ => z ^ n) = X ^ n := by
    have hh := J.polynomial (2 * n) (X ^ n) (by simp; omega)
    simpa only [eval_pow, eval_X] using hh
  have hpow := (J.power (2 * n) (R.normal i j p) n (R.normal_analytic i j p hi hj)).symm
  have hcomp := J.composition (2 * n) (baseChange D i j p) (fun z => z ^ n)
    (baseChange_analytic D i j p hi hj) (analyticAt_id.pow n) (zero_pow (Nat.ne_of_gt hn))
  rw [hmono] at hcomp
  have hraw : JetEq (2 * n) (R.normalJet J i j p ^ n) (B.comp (X ^ n)) := by
    rw [← J.congr (2 * n) (R.normal_identity i j p hi hj)] at hcomp
    exact hpow.trans hcomp
  have hquad := quadratic_composition_mod hn B (X ^ n) hB0 (dvd_refl _)
  rw [hB1, hB2] at hquad
  exact hraw.trans hquad

 theorem normal_form_exists (J : TaylorCalculus) (R : RetractionGerms D T n a)
    (hn : 0 < n) (i j p : D) (hi : p ∈ D.chartDomain i) (hj : p ∈ D.chartDomain j) :
    ∃ H : ℂ[X], R.normalJet J i j p =
      NormalJets.normalChange n (deriv (R.normal i j p) 0) H := by
  have hmod := R.normal_power_mod J hn i j p hi hj
  have heq : C (D.chartJacobian i j p) * X ^ n +
      C (D.coordinateDerivative i (T.bundle.transition i j) p / 2) * (X ^ n) ^ 2 =
      X ^ n * (C (D.chartJacobian i j p) + X ^ n *
        C (D.coordinateDerivative i (T.bundle.transition i j) p / 2)) := by ring
  rw [heq] at hmod
  have hzero : (R.normalJet J i j p).coeff 0 = 0 :=
    (J.constant _ _ (R.normal_analytic i j p hi hj)).trans (R.normal_zero i j p hi hj)
  have hfirst : (R.normalJet J i j p).coeff 1 = deriv (R.normal i j p) 0 :=
    J.first _ _ (R.normal_analytic i j p hi hj) (by omega)
  have hfirstne : (R.normalJet J i j p).coeff 1 ≠ 0 := by
    rw [hfirst]
    exact R.normal_derivative_ne_zero i j p hi hj
  obtain ⟨H, hH⟩ := normal_root_gap hn (R.normalJet J i j p)
    (C (D.coordinateDerivative i (T.bundle.transition i j) p / 2))
    (D.chartJacobian i j p) hzero hfirstne hmod
  exact ⟨H, by simpa only [hfirst] using hH⟩

 def normalRemainder (J : TaylorCalculus) (R : RetractionGerms D T n a) (hn : 0 < n)
    (i j p : D) : ℂ[X] := by
  classical
  exact if h : p ∈ D.chartDomain i ∧ p ∈ D.chartDomain j then
    Classical.choose (R.normal_form_exists J hn i j p h.1 h.2) else 0

 theorem normalRemainder_spec (J : TaylorCalculus) (R : RetractionGerms D T n a) (hn : 0 < n)
    (i j p : D) (hi : p ∈ D.chartDomain i) (hj : p ∈ D.chartDomain j) :
    R.normalJet J i j p = NormalJets.normalChange n (deriv (R.normal i j p) 0)
      (R.normalRemainder J hn i j p) := by
  classical
  unfold normalRemainder
  rw [dif_pos ⟨hi, hj⟩]
  exact Classical.choose_spec (R.normal_form_exists J hn i j p hi hj)

/-- The actual compatible polynomial jets are constructed from the actual
analytic coordinate functions and the general Taylor calculus. -/
def compatibleJets (J : TaylorCalculus) (R : RetractionGerms D T n a) (hn : 2 ≤ n) :
    CompatibleRetractionJets D T n a (R.doubleCoefficient J) where
  jet := R.jet J
  remainder := R.normalRemainder J (by omega)
  normalLinear i j p := deriv (R.normal i j p) 0
  order_bound i p hi := (R.jet_order_leading J (by omega) i p hi).1
  leading i p hi := (R.jet_order_leading J (by omega) i p hi).2
  double i p hi := rfl
  normal_power_leading i j p hi hj := by
    have hh := (R.normal_power_mod J (by omega) i j p hi hj).coefficient n (by omega)
    rw [R.normalRemainder_spec J (by omega) i j p hi hj,
      NormalJets.normalChange_power_leading (by omega)] at hh
    have hne : n ≠ 2 * n := by omega
    simpa [coeff_add, coeff_C_mul, coeff_X_pow, ← pow_mul, Nat.mul_comm n 2, hne] using hh
  normal_power_double i j p hi hj := by
    have hh := (R.normal_power_mod J (by omega) i j p hi hj).coefficient (2 * n) le_rfl
    rw [R.normalRemainder_spec J (by omega) i j p hi hj] at hh
    have hne : 2 * n ≠ n := by omega
    simpa [coeff_add, coeff_C_mul, coeff_X_pow, ← pow_mul, Nat.mul_comm n 2, hne] using hh
  composition i j p hi hj := by
    let B := baseJet (D := D) (n := n) J i j p
    have hB0 : B.coeff 0 = 0 := (J.constant _ _ (baseChange_analytic D i j p hi hj)).trans (baseChange_zero D i j p)
    have hB1 : B.coeff 1 = D.chartJacobian i j p :=
      (J.first _ _ (baseChange_analytic D i j p hi hj) (by omega)).trans (baseChange_first D i j p)
    have hB2 : B.coeff 2 = D.coordinateDerivative i (T.bundle.transition i j) p / 2 := by
      change (J.jet (2 * n) (baseChange D i j p)).coeff 2 = _
      rw [J.second (2 * n) _ (baseChange_analytic D i j p hi hj) (by omega),
        baseChange_second D T i j p hi hj]
    have hthird0 : R.third i p 0 = 0 := by
      have hh := (R.third_factor i p hi).self_of_nhds
      simpa only [zero_pow (by omega : n ≠ 0), zero_mul] using hh
    have hleft := (J.composition (2 * n) (R.third j p) (R.normal i j p)
      (R.third_analytic j p hj) (R.normal_analytic i j p hi hj) (R.normal_zero i j p hi hj)).symm
    have hright := J.composition (2 * n) (baseChange D i j p) (R.third i p)
      (baseChange_analytic D i j p hi hj) (R.third_analytic i p hi) hthird0
    rw [← J.congr (2 * n) (R.third_identity i j p hi hj)] at hright
    have hraw : JetEq (2 * n) ((R.jet J j p).comp (R.normalJet J i j p))
        (B.comp (R.jet J i p)) := hleft.trans hright
    have hquad := quadratic_composition_mod (by omega) B (R.jet J i p) hB0
      (R.jet_order_leading J (by omega) i p hi).1
    rw [hB1, hB2] at hquad
    have hh := (hraw.trans hquad).coefficient (2 * n) le_rfl
    rw [R.normalRemainder_spec J (by omega) i j p hi hj] at hh
    exact hh

/-- Equation (7) follows from the actual retraction germ identities after the
proved truncation, root-gap, and full coefficient calculations. -/
theorem equation_seven_from_germs (J : TaylorCalculus) (R : RetractionGerms D T n a)
    (hn : 2 ≤ n) (i j p : D) (hi : p ∈ D.chartDomain i) (hj : p ∈ D.chartDomain j) :
    R.doubleCoefficient J j p * D.chartJacobian i j p ^ 2 =
      D.chartJacobian i j p * R.doubleCoefficient J i p + (a ^ 2 - a) / 2 *
        D.coordinateDerivative i (T.bundle.transition i j) p :=
  (R.compatibleJets J hn).equation_seven hn i j p hi hj

/-- The tangent connection is constructed from these actual germ coefficients.
Holomorphic dependence of the coefficient on the base parameter is the usual
remaining parameter-Taylor regularity hypothesis, not connection existence. -/
def connection (J : TaylorCalculus) (R : RetractionGerms D T n a)
    (hn : 2 ≤ n) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hb : ∀ i, MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      (R.doubleCoefficient J i) (D.chartDomain i)) : T.bundle.Connection :=
  (R.compatibleJets J hn).tangentConnection hn ha0 ha1 hb

end RetractionGerms
end Paper27.Geometry.TaylorGerms
