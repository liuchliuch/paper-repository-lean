import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Data.Fintype.Option

/-! Existence and uniqueness of the actual multicenter power prox. A radial
norm can be represented as a continuous function on an existing proper
finite-dimensional topology; this accommodates the genuine Schatten norm
without changing the ambient matrix topology. -/
noncomputable section
open scoped BigOperators
namespace P31
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Jensen convention, with the actual radial norm explicitly supplied. -/
def RadialPowerJensen (ρ : E → ℝ) (p μ : ℝ) (F : E → ℝ) : Prop :=
  ∀ x y (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
    F ((1 - θ) • x + θ • y) ≤ (1 - θ) * F x + θ * F y -
      μ / p * θ * (1 - θ) * ρ (x - y) ^ p

def radialPowerAtom (ρ : E → ℝ) (p k : ℝ) (c x : E) : ℝ := k / p * ρ (x - c) ^ p

omit [NormedSpace ℝ E] in
lemma radialPowerAtom_nonneg {ρ : E → ℝ} (hρ : ∀ x, 0 ≤ ρ x)
    {p k : ℝ} (hp : 0 < p) (hk : 0 ≤ k) (c x : E) :
    0 ≤ radialPowerAtom ρ p k c x :=
  mul_nonneg (div_nonneg hk hp.le) (Real.rpow_nonneg (hρ _) _)

omit [NormedSpace ℝ E] in
lemma radialPowerAtom_continuous {ρ : E → ℝ} (hρ : Continuous ρ)
    {p k : ℝ} (hp : 0 ≤ p) (c : E) : Continuous (radialPowerAtom ρ p k c) :=
  continuous_const.mul ((Real.continuous_rpow_const hp).comp
    (hρ.comp (continuous_id.sub continuous_const)))

omit [NormedSpace ℝ E] in
/-- A p-power with p≥2 dominates a linear term outside an explicit radius. -/
theorem radial_power_lower_sublevel_ball {ρ : E → ℝ}
    (hρ : ∀ x, 0 ≤ ρ x) {p a b L K r : ℝ}
    (hp : 2 ≤ p) (ha : 0 < a) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hdom : ∀ x, ‖x‖ ≤ K * ρ x) {F : E → ℝ} (c : E)
    (hlower : ∀ x, b + a * ρ (x - c) ^ p - L * ρ (x - c) ≤ F x) :
    {x | F x ≤ r} ⊆ Metric.closedBall c (K * (1 + (L + |r - b| + 1) / a)) := by
  intro x hx
  let t := ρ (x - c)
  let R := 1 + (L + |r - b| + 1) / a
  have ht : 0 ≤ t := hρ _
  have hR : 1 ≤ R := le_add_of_nonneg_right
    (div_nonneg (by positivity) ha.le)
  have htR : t ≤ R := by
    by_contra hfail
    have hlarge : R < t := lt_of_not_ge hfail
    have ht1 : 1 ≤ t := hR.trans hlarge.le
    have htp : t ^ (2 : ℝ) ≤ t ^ p := Real.rpow_le_rpow_of_exponent_le ht1 hp
    rw [Real.rpow_two] at htp
    have hscaled := mul_le_mul_of_nonneg_left htp ha.le
    have hl := hlower x
    change F x ≤ r at hx
    change b + a * t ^ p - L * t ≤ F x at hl
    have hquad : a * t ^ 2 - L * t ≤ r - b := by nlinarith
    have hRa : a * R = a + L + |r - b| + 1 := by
      dsimp [R]
      rw [mul_add, mul_one, mul_div_cancel₀ _ ha.ne']
      ring
    have hmult := mul_lt_mul_of_pos_left hlarge ha
    have hlinear : L + |r - b| + 1 < a * t := by linarith
    have hstrict := mul_lt_mul_of_pos_right hlinear (lt_of_lt_of_le zero_lt_one ht1)
    have hbase := mul_le_mul_of_nonneg_left ht1 (show 0 ≤ |r - b| + 1 by positivity)
    nlinarith [le_abs_self (r - b)]
  have hd := (hdom (x - c)).trans (mul_le_mul_of_nonneg_left htR hK)
  simpa only [Metric.mem_closedBall, dist_eq_norm] using hd

omit [NormedSpace ℝ E] in
/-- Every sublevel is compact, proved from the power-versus-linear estimate. -/
theorem radial_power_lower_sublevel_compact [ProperSpace E] {ρ : E → ℝ}
    (hρ : ∀ x, 0 ≤ ρ x) {p a b L K : ℝ}
    (hp : 2 ≤ p) (ha : 0 < a) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hdom : ∀ x, ‖x‖ ≤ K * ρ x) {F : E → ℝ} (hF : Continuous F) (c : E)
    (hlower : ∀ x, b + a * ρ (x - c) ^ p - L * ρ (x - c) ≤ F x) (r : ℝ) :
    IsCompact {x | F x ≤ r} :=
  (isCompact_closedBall c _).of_isClosed_subset (isClosed_le hF continuous_const)
    (radial_power_lower_sublevel_ball hρ hp ha hL hK hdom c hlower)

omit [NormedSpace ℝ E] in
/-- Actual attainment follows from a nonempty compact sublevel. -/
theorem radial_power_lower_exists_min [ProperSpace E] {ρ : E → ℝ}
    (hρ : ∀ x, 0 ≤ ρ x) {p a b L K : ℝ}
    (hp : 2 ≤ p) (ha : 0 < a) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hdom : ∀ x, ‖x‖ ≤ K * ρ x) {F : E → ℝ} (hF : Continuous F) (c : E)
    (hlower : ∀ x, b + a * ρ (x - c) ^ p - L * ρ (x - c) ≤ F x) :
    ∃ z, ∀ y, F z ≤ F y := by
  have hc := radial_power_lower_sublevel_compact hρ hp ha hL hK hdom hF c hlower (F c)
  obtain ⟨z, hz, hmin⟩ := hc.exists_isMinOn
    ⟨c, (by change F c ≤ F c; exact le_rfl)⟩ hF.continuousOn
  refine ⟨z, fun y => ?_⟩
  by_cases hy : F y ≤ F c
  · exact hmin hy
  · exact hz.trans (lt_of_not_ge hy).le

/-- The actual continuous linear functional is bounded below in radial distance. -/
lemma linear_lower_in_radial {ρ : E → ℝ} {K : ℝ}
    (hdom : ∀ x, ‖x‖ ≤ K * ρ x) (g : E →L[ℝ] ℝ) (c x : E) :
    g c - (‖g‖ * K) * ρ (x - c) ≤ g x := by
  have hg := (le_abs_self (g (c - x))).trans (g.le_opNorm (c - x))
  have hd := mul_le_mul_of_nonneg_left (hdom (x - c)) (norm_nonneg g)
  rw [map_sub, norm_sub_rev] at hg
  nlinarith

lemma radialPowerJensen_add_linear {ρ : E → ℝ} {p μ : ℝ} {F : E → ℝ}
    (hJ : RadialPowerJensen ρ p μ F) (g : E →L[ℝ] ℝ) :
    RadialPowerJensen ρ p μ (fun x => g x + F x) := by
  intro x y θ hθ0 hθ1
  have hj := hJ x y θ hθ0 hθ1
  have hl : g ((1 - θ) • x + θ • y) = (1 - θ) * g x + θ * g y := by
    rw [map_add, map_smul, map_smul]
    rfl
  dsimp only
  rw [hl]
  linarith

lemma radialPowerJensen_weighted_sum {κ : Type*} {ρ : E → ℝ}
    (s : Finset κ) (p : ℝ) (μ w : κ → ℝ) (F : κ → E → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hF : ∀ i ∈ s, RadialPowerJensen ρ p (μ i) (F i)) :
    RadialPowerJensen ρ p (∑ i ∈ s, w i * μ i) (fun x => ∑ i ∈ s, w i * F i x) := by
  intro x y θ hθ0 hθ1
  have hs := Finset.sum_le_sum (fun i hi =>
    mul_le_mul_of_nonneg_left (hF i hi x y θ hθ0 hθ1) (hw i hi))
  apply hs.trans_eq
  simp only [div_eq_mul_inv, Finset.mul_sum, Finset.sum_mul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma radialPowerJensen_add {ρ : E → ℝ} {p μ ν : ℝ} {F G : E → ℝ}
    (hF : RadialPowerJensen ρ p μ F) (hG : RadialPowerJensen ρ p ν G) :
    RadialPowerJensen ρ p (μ + ν) (fun x => F x + G x) := by
  intro x y θ hθ0 hθ1
  have h := add_le_add (hF x y θ hθ0 hθ1) (hG x y θ hθ0 hθ1)
  dsimp only
  apply h.trans_eq
  ring

lemma radialPowerJensen_scale {ρ : E → ℝ} {p μ w : ℝ} {F : E → ℝ}
    (hJ : RadialPowerJensen ρ p μ F) (hw : 0 ≤ w) :
    RadialPowerJensen ρ p (w * μ) (fun x => w * F x) := by
  intro x y θ hθ0 hθ1
  have h := mul_le_mul_of_nonneg_left (hJ x y θ hθ0 hθ1) hw
  apply h.trans_eq
  ring

/-- Positive Jensen modulus yields uniqueness directly at the midpoint. -/
theorem radialPowerJensen_unique_minimizer {ρ : E → ℝ}
    (hρ : ∀ x, 0 ≤ ρ x) (hρeq : ∀ x, ρ x = 0 ↔ x = 0)
    {p μ : ℝ} (hp : 0 < p) (hμ : 0 < μ) {F : E → ℝ}
    (hJ : RadialPowerJensen ρ p μ F) {z y : E}
    (hz : ∀ x, F z ≤ F x) (hy : ∀ x, F y ≤ F x) : y = z := by
  by_contra hne
  have hpos : 0 < ρ (z - y) := lt_of_le_of_ne (hρ _) (by
    intro he
    have hzero := (hρeq _).mp he.symm
    exact hne (sub_eq_zero.mp hzero).symm)
  have hpower := Real.rpow_pos_of_pos hpos p
  have hJm := hJ z y (1 / 2) (by norm_num) (by norm_num)
  have hmin := hz ((1 - (1 / 2 : ℝ)) • z + (1 / 2 : ℝ) • y)
  have heq : F z = F y := le_antisymm (hz y) (hy z)
  have hc : 0 < μ / p := div_pos hμ hp
  have hpenalty := mul_pos hc hpower
  rw [heq] at hJm hmin
  nlinarith

/-- A finite multicenter power objective with one positive weight attains
one and only one global minimum. No minimizer or coercivity is assumed. -/
theorem radialMulticenter_existsUnique_minimizer [ProperSpace E]
    (ρ : E → ℝ) (hρcont : Continuous ρ) (hρ : ∀ x, 0 ≤ ρ x)
    (hρeq : ∀ x, ρ x = 0 ↔ x = 0) (K : ℝ) (hK : 0 < K)
    (hdom : ∀ x, ‖x‖ ≤ K * ρ x) {κ : Type*} (s : Finset κ)
    {p k : ℝ} (hp : 2 ≤ p) (hk : 0 < k) (g : E →L[ℝ] ℝ)
    (w : κ → ℝ) (c : κ → E) (hw : ∀ i ∈ s, 0 ≤ w i)
    (i₀ : κ) (hi₀ : i₀ ∈ s) (hw₀ : 0 < w i₀)
    (hAtoms : ∀ i ∈ s, RadialPowerJensen ρ p 1 (radialPowerAtom ρ p k (c i))) :
    ∃! z : E, ∀ x, g z + ∑ i ∈ s, w i * radialPowerAtom ρ p k (c i) z ≤
      g x + ∑ i ∈ s, w i * radialPowerAtom ρ p k (c i) x := by
  classical
  have hp0 : 0 < p := by linarith
  let F := fun x => g x + ∑ i ∈ s, w i * radialPowerAtom ρ p k (c i) x
  have hF : Continuous F := g.continuous.add
    (continuous_finset_sum _ (fun i _ => continuous_const.mul (radialPowerAtom_continuous hρcont hp0.le (c i))))
  have hA : 0 < w i₀ * (k / p) := mul_pos hw₀ (div_pos hk hp0)
  have hlower : ∀ x, g (c i₀) + (w i₀ * (k / p)) * ρ (x - c i₀) ^ p -
      (‖g‖ * K) * ρ (x - c i₀) ≤ F x := by
    intro x
    have hsum : w i₀ * radialPowerAtom ρ p k (c i₀) x ≤
        ∑ i ∈ s, w i * radialPowerAtom ρ p k (c i) x :=
      Finset.single_le_sum (fun i hi => mul_nonneg (hw i hi)
        (radialPowerAtom_nonneg hρ hp0 hk.le _ _)) hi₀
    have hg := linear_lower_in_radial hdom g (c i₀) x
    have he : w i₀ * radialPowerAtom ρ p k (c i₀) x =
        (w i₀ * (k / p)) * ρ (x - c i₀) ^ p := by unfold radialPowerAtom; ring
    rw [he] at hsum
    dsimp [F]
    nlinarith
  obtain ⟨z, hz⟩ := radial_power_lower_exists_min hρ hp hA
    (mul_nonneg (norm_nonneg g) hK.le) hK.le hdom hF (c i₀) hlower
  have hJ : RadialPowerJensen ρ p (∑ i ∈ s, w i) F := by
    apply radialPowerJensen_add_linear (g := g)
    simpa only [mul_one] using radialPowerJensen_weighted_sum s p (fun _ => 1) w
      (fun i => radialPowerAtom ρ p k (c i)) hw hAtoms
  have hW : 0 < ∑ i ∈ s, w i := hw₀.trans_le (Finset.single_le_sum hw hi₀)
  refine ⟨z, hz, ?_⟩
  intro y hy
  exact radialPowerJensen_unique_minimizer hρ hρeq hp0 hW hJ hz hy

/-- The usual normed-space specialization, with no separate radial norm data. -/
theorem powerMulticenter_existsUnique_minimizer [ProperSpace E]
    {κ : Type*} (s : Finset κ) {p k : ℝ} (hp : 2 ≤ p) (hk : 0 < k)
    (g : E →L[ℝ] ℝ) (w : κ → ℝ) (c : κ → E) (hw : ∀ i ∈ s, 0 ≤ w i)
    (i₀ : κ) (hi₀ : i₀ ∈ s) (hw₀ : 0 < w i₀)
    (hAtoms : ∀ i ∈ s, RadialPowerJensen (fun x : E => ‖x‖) p 1
      (fun x => k / p * ‖x - c i‖ ^ p)) :
    ∃! z : E, ∀ x, g z + ∑ i ∈ s, w i * (k / p * ‖z - c i‖ ^ p) ≤
      g x + ∑ i ∈ s, w i * (k / p * ‖x - c i‖ ^ p) := by
  simpa only [radialPowerAtom] using radialMulticenter_existsUnique_minimizer
    (fun x : E => ‖x‖) continuous_norm (fun x => norm_nonneg x) (fun _ => norm_eq_zero)
    1 (by norm_num) (fun x => by simp) s hp hk g w c hw i₀ hi₀ hw₀ hAtoms

section Composite
variable [ProperSpace E]

def radialCompositeWeights {κ : Type*} (s : Finset κ) (w : κ → ℝ) (A m : ℝ) : Option s → ℝ :=
  fun i => i.elim m (fun j => A * w j)

def radialCompositeCenters {κ : Type*} (s : Finset κ) (c : κ → E) (center : E) :
    Option s → E := fun i => i.elim center (fun j => c j)

lemma radialCompositeWeights_nonneg {κ : Type*} (s : Finset κ) (w : κ → ℝ) (A m : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hA : 0 ≤ A) (hm : 0 ≤ m) :
    ∀ i, 0 ≤ radialCompositeWeights s w A m i := by
  intro i
  cases i with
  | none => exact hm
  | some j => exact mul_nonneg hA (hw j j.property)

omit [NormedSpace ℝ E] [ProperSpace E] in
lemma radialComposite_sum_eq {κ : Type*} (s : Finset κ) (w : κ → ℝ) (c : κ → E)
    (center : E) (ρ : E → ℝ) (p k A m : ℝ) (x : E) :
    (∑ i, radialCompositeWeights s w A m i *
      radialPowerAtom ρ p k (radialCompositeCenters s c center i) x) =
    A * (∑ i ∈ s, w i * radialPowerAtom ρ p k (c i) x) + m * radialPowerAtom ρ p k center x := by
  classical
  simp only [univ_option, Finset.sum_insertNone, radialCompositeWeights, radialCompositeCenters,
    Option.elim_none, Option.elim_some]
  have hs : (∑ i : s, (A * w i) * radialPowerAtom ρ p k (c i) x) =
      A * (∑ i ∈ s, w i * radialPowerAtom ρ p k (c i) x) := by
    calc
      _ = ∑ i ∈ s, (A * w i) * radialPowerAtom ρ p k (c i) x := Finset.sum_coe_sort s _
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [hs]
  ring

/-- The actual internal composite objective has a unique minimizer, including
an empty history: its positive new atom supplies coercivity and modulus. -/
theorem radialComposite_existsUnique_minimizer
    (ρ : E → ℝ) (hρcont : Continuous ρ) (hρ : ∀ x, 0 ≤ ρ x)
    (hρeq : ∀ x, ρ x = 0 ↔ x = 0) (K : ℝ) (hK : 0 < K)
    (hdom : ∀ x, ‖x‖ ≤ K * ρ x) {p k : ℝ} (hp : 2 ≤ p) (hk : 0 < k)
    (hAtoms : ∀ c, RadialPowerJensen ρ p 1 (radialPowerAtom ρ p k c))
    {κ : Type*} (s : Finset κ) (w : κ → ℝ) (c : κ → E) (hw : ∀ i ∈ s, 0 ≤ w i)
    (center : E) (g : E →L[ℝ] ℝ) (A m : ℝ) (hA : 0 ≤ A) (hm : 0 < m) :
    ∃! z : E, ∀ x,
      g z + A * (∑ i ∈ s, w i * radialPowerAtom ρ p k (c i) z) + m * radialPowerAtom ρ p k center z ≤
      g x + A * (∑ i ∈ s, w i * radialPowerAtom ρ p k (c i) x) + m * radialPowerAtom ρ p k center x := by
  classical
  have hn := radialCompositeWeights_nonneg s w A m hw hA hm.le
  have h := radialMulticenter_existsUnique_minimizer ρ hρcont hρ hρeq K hK hdom
    (Finset.univ : Finset (Option s)) hp hk g (radialCompositeWeights s w A m)
    (radialCompositeCenters s c center) (fun i _ => hn i) none (Finset.mem_univ none) hm
    (fun i _ => hAtoms _)
  simpa only [radialComposite_sum_eq, add_assoc] using h

/-- A total known-data exact-real prox. The legal branch is chosen only from
the proved unique minimizer of the explicit power objective; f never occurs. -/
def radialCompositeProx
    (ρ : E → ℝ) (hρcont : Continuous ρ) (hρ : ∀ x, 0 ≤ ρ x)
    (hρeq : ∀ x, ρ x = 0 ↔ x = 0) (K : ℝ) (hK : 0 < K)
    (hdom : ∀ x, ‖x‖ ≤ K * ρ x) {p k : ℝ} (hp : 2 ≤ p) (hk : 0 < k)
    (hAtoms : ∀ c, RadialPowerJensen ρ p 1 (radialPowerAtom ρ p k c))
    {κ : Type*} (s : Finset κ) (w : κ → ℝ) (c : κ → E) (hw : ∀ i ∈ s, 0 ≤ w i)
    (center : E) (g : E →L[ℝ] ℝ) (A m : ℝ) : E := by
  classical
  exact if h : 0 ≤ A ∧ 0 < m then
    Classical.choose (radialComposite_existsUnique_minimizer ρ hρcont hρ hρeq K hK hdom hp hk
      hAtoms s w c hw center g A m h.1 h.2)
    else 0

/-- The total prox map attains the exact multicenter composite minimum. -/
theorem radialCompositeProx_minimizes
    (ρ : E → ℝ) (hρcont : Continuous ρ) (hρ : ∀ x, 0 ≤ ρ x)
    (hρeq : ∀ x, ρ x = 0 ↔ x = 0) (K : ℝ) (hK : 0 < K)
    (hdom : ∀ x, ‖x‖ ≤ K * ρ x) {p k : ℝ} (hp : 2 ≤ p) (hk : 0 < k)
    (hAtoms : ∀ c, RadialPowerJensen ρ p 1 (radialPowerAtom ρ p k c))
    {κ : Type*} (s : Finset κ) (w : κ → ℝ) (c : κ → E) (hw : ∀ i ∈ s, 0 ≤ w i)
    (center : E) (g : E →L[ℝ] ℝ) (A m : ℝ) (hA : 0 ≤ A) (hm : 0 < m) :
    let z := radialCompositeProx ρ hρcont hρ hρeq K hK hdom hp hk hAtoms s w c hw center g A m
    ∀ x, g z + A * (∑ i ∈ s, w i * radialPowerAtom ρ p k (c i) z) + m * radialPowerAtom ρ p k center z ≤
      g x + A * (∑ i ∈ s, w i * radialPowerAtom ρ p k (c i) x) + m * radialPowerAtom ρ p k center x := by
  classical
  have h := (Classical.choose_spec (radialComposite_existsUnique_minimizer ρ hρcont hρ hρeq K hK hdom hp hk
    hAtoms s w c hw center g A m hA hm)).1
  simpa only [radialCompositeProx, dif_pos (show 0 ≤ A ∧ 0 < m from ⟨hA, hm⟩)] using h

end Composite

end P31
