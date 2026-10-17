import MEJF.TieRemoval
import Mathlib.Data.Fin.VecNotation

/-! Concrete affine constraints sufficient to remove every relevant tie in a
finite pair-prediction table. The constraints quantify over every possible
coordinate selected by an inner order statistic. -/
namespace MEJF.TieFreeTable
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Atom (N n : ℕ) := (Fin N × Fin n) ⊕ (Fin N × Fin N × Fin n)
abbrev Vector (N n : ℕ) := Atom N n → ℝ

def response {N n : ℕ} (u : Fin N) (j : Fin n) : Vector N n →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (Sum.inl (u,j))

def prediction {N n : ℕ} (u v : Fin N) (j : Fin n) : Vector N n →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (Sum.inr (u,v,j))

def residual {N n : ℕ} (u v : Fin N) (j : Fin n) : Vector N n →L[ℝ] ℝ :=
  prediction u v j - response u j

def endpoint {N n : ℕ} (upper : Bool) (u v : Fin N) (j q : Fin n) :
    Vector N n →L[ℝ] ℝ :=
  if upper then prediction u v j + residual v u q
  else prediction u v j - residual v u q

abbrev ResidualConstraint (N n : ℕ) :=
  {x : (Fin 2 → Fin N) × (Fin 2 → Fin n) // x.2 0 ≠ x.2 1}
abbrev ComparisonConstraint (N n : ℕ) :=
  {x : (Fin 2 → Fin N) × (Fin 2 → Fin n) // x.1 0 ≠ x.1 1}
abbrev EndpointConstraint (N n : ℕ) :=
  {x : Bool × (Fin 3 → Fin N) × (Fin 3 → Fin n) //
    x.2.1 0 ≠ x.2.1 1 ∧ x.2.1 0 ≠ x.2.1 2 ∧ x.2.1 1 ≠ x.2.1 2}
abbrev ResponseConstraint (N n : ℕ) :=
  {x : Bool × (Fin 2 → Fin N) × (Fin 2 → Fin n) // x.2.1 0 ≠ x.2.1 1}

abbrev Constraint (N n : ℕ) :=
  (ResidualConstraint N n ⊕ ComparisonConstraint N n) ⊕
    (EndpointConstraint N n ⊕ ResponseConstraint N n)

def relation {N n : ℕ} : Constraint N n → Vector N n →L[ℝ] ℝ
  | .inl (.inl x) => residual (x.1.1 0) (x.1.1 1) (x.1.2 0) -
      residual (x.1.1 0) (x.1.1 1) (x.1.2 1)
  | .inl (.inr x) => residual (x.1.1 0) (x.1.1 1) (x.1.2 0) -
      residual (x.1.1 1) (x.1.1 0) (x.1.2 1)
  | .inr (.inl x) => endpoint x.1.1 (x.1.2.1 0) (x.1.2.1 1)
      (x.1.2.2 0) (x.1.2.2 1) - endpoint x.1.1 (x.1.2.1 0) (x.1.2.1 2)
      (x.1.2.2 0) (x.1.2.2 2)
  | .inr (.inr x) => endpoint x.1.1 (x.1.2.1 0) (x.1.2.1 1)
      (x.1.2.2 0) (x.1.2.2 1) - response (x.1.2.1 0) (x.1.2.2 0)

/-- Each concrete forbidden relation has a prediction entry whose coefficient
is one and which is absent from all the other terms. -/
lemma relation_ne_zero {N n : ℕ} (c : Constraint N n) : relation c ≠ 0 := by
  intro hz
  rcases c with (a | b) | (a | b)
  · have h := congrArg (fun L : Vector N n →L[ℝ] ℝ =>
      L (Pi.single (Sum.inr (a.1.1 0, a.1.1 1, a.1.2 0)) 1)) hz
    have hne := a.2
    simp [relation, residual, prediction, response, Pi.single_apply, hne, Ne.symm hne] at h
  · have h := congrArg (fun L : Vector N n →L[ℝ] ℝ =>
      L (Pi.single (Sum.inr (b.1.1 0, b.1.1 1, b.1.2 0)) 1)) hz
    have hne := b.2
    simp [relation, residual, prediction, response, Pi.single_apply, hne, Ne.symm hne] at h
  · have h := congrArg (fun L : Vector N n →L[ℝ] ℝ =>
      L (Pi.single (Sum.inr (a.1.2.1 0, a.1.2.1 1, a.1.2.2 0)) 1)) hz
    obtain ⟨h01,h02,h12⟩ := a.2
    cases hb : a.1.1 <;>
      simp [relation, endpoint, residual, prediction, response, Pi.single_apply,
        hb, h01, h02, h12, Ne.symm h01, Ne.symm h02, Ne.symm h12] at h
  · have h := congrArg (fun L : Vector N n →L[ℝ] ℝ =>
      L (Pi.single (Sum.inr (b.1.2.1 0, b.1.2.1 1, b.1.2.2 0)) 1)) hz
    have hne := b.2
    cases hb : b.1.1 <;>
      simp [relation, endpoint, residual, prediction, response, Pi.single_apply,
        hb, hne, Ne.symm hne] at h

/-- Concrete primitive general position is dense around every finite table. -/
theorem exists_general_position {N n : ℕ} (z : Vector N n) (η : ℝ) (hη : 0 < η) :
    ∃ z' : Vector N n, (∀ a, |z' a - z a| < η) ∧
      ∀ c : Constraint N n, relation c z' ≠ 0 := by
  exact TieRemoval.exists_avoid_affine relation (fun _ => 0)
    (fun c => Or.inl (relation_ne_zero c)) z η hη


abbrev GeneralPosition {N n : ℕ} (z : Vector N n) : Prop :=
  ∀ c : Constraint N n, relation c z ≠ 0

lemma residual_ne {N n : ℕ} {z : Vector N n} (h : GeneralPosition z)
    (u v : Fin N) (j q : Fin n) (hjq : j ≠ q) :
    residual u v j z ≠ residual u v q z := by
  have hh := h (.inl (.inl ⟨(![u,v], ![j,q]), by simpa⟩))
  simpa [relation, sub_ne_zero] using hh

lemma comparison_ne {N n : ℕ} {z : Vector N n} (h : GeneralPosition z)
    (u v : Fin N) (huv : u ≠ v) (j q : Fin n) :
    residual u v j z ≠ residual v u q z := by
  have hh := h (.inl (.inr ⟨(![u,v], ![j,q]), by simpa⟩))
  simpa [relation, sub_ne_zero] using hh

lemma endpoint_ne {N n : ℕ} {z : Vector N n} (h : GeneralPosition z)
    (upper : Bool) (u v w : Fin N) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (j q r : Fin n) : endpoint upper u v j q z ≠ endpoint upper u w j r z := by
  have hh := h (.inr (.inl ⟨(upper, ![u,v,w], ![j,q,r]), by simp [huv,huw,hvw]⟩))
  simpa [relation, sub_ne_zero] using hh

lemma endpoint_ne_response {N n : ℕ} {z : Vector N n} (h : GeneralPosition z)
    (upper : Bool) (u v : Fin N) (huv : u ≠ v) (j q : Fin n) :
    endpoint upper u v j q z ≠ response u j z := by
  have hh := h (.inr (.inr ⟨(upper, ![u,v], ![j,q]), by simpa⟩))
  simpa [relation, sub_ne_zero] using hh

/-- Actual absolute-residual radius at any finite ascending rank. -/
def radius {N n : ℕ} (z : Vector N n) (u v : Fin N) (k : Fin n) : ℝ :=
  OrderStatistics.stat (fun j => |response u j z - prediction u v j z|) k

def candidate {N n : ℕ} (z : Vector N n) (upper : Bool)
    (u v : Fin N) (j k : Fin n) : ℝ :=
  if upper then prediction u v j z + radius z v u k
  else prediction u v j z - radius z v u k

def aggregate {m n : ℕ} (z : Vector (m+1) n) (upper : Bool)
    (u : Fin (m+1)) (j k : Fin n) (outer : Fin m) : ℝ :=
  OrderStatistics.stat (fun v : Fin m => candidate z upper u (u.succAbove v) j k) outer

lemma abs_residual_eq {N n : ℕ} (z : Vector N n) (u v : Fin N) (j : Fin n)
    (hpos : response u j z ≤ prediction u v j z) :
    |response u j z - prediction u v j z| = residual u v j z := by
  rw [abs_of_nonpos (sub_nonpos.mpr hpos)]
  simp only [residual, ContinuousLinearMap.sub_apply]
  ring

lemma radius_eq_residual {N n : ℕ} (z : Vector N n) (u v : Fin N) (k : Fin n)
    (hpos : ∀ j, response u j z ≤ prediction u v j z) :
    ∃ q, radius z u v k = residual u v q z := by
  unfold radius OrderStatistics.stat
  exact ⟨_, abs_residual_eq z u v _ (hpos _)⟩

lemma candidate_eq_endpoint {N n : ℕ} (z : Vector N n) (upper : Bool)
    (u v : Fin N) (j k : Fin n)
    (hpos : ∀ q, response v q z ≤ prediction v u q z) :
    ∃ q, candidate z upper u v j k = endpoint upper u v j q z := by
  obtain ⟨q,hq⟩ := radius_eq_residual z v u k hpos
  refine ⟨q, ?_⟩
  cases upper <;> simp [candidate, endpoint, hq]

/-- Every actual absolute-residual tuple has no repeated entries. -/
lemma residual_injective {N n : ℕ} (z : Vector N n) (hgp : GeneralPosition z)
    (hpos : ∀ u v j, response u j z ≤ prediction u v j z) (u v : Fin N) :
    Function.Injective (fun j => |response u j z - prediction u v j z|) := by
  intro j q he
  by_contra hn
  apply residual_ne hgp u v j q hn
  simpa only [abs_residual_eq _ _ _ _ (hpos _ _ _)] using he

/-- Strict opposite-direction comparison radii, for all finite inner ranks. -/
lemma radius_ne_opposite {N n : ℕ} (z : Vector N n) (hgp : GeneralPosition z)
    (hpos : ∀ u v j, response u j z ≤ prediction u v j z)
    (u v : Fin N) (huv : u ≠ v) (k : Fin n) : radius z u v k ≠ radius z v u k := by
  obtain ⟨q,hq⟩ := radius_eq_residual z u v k (hpos u v)
  obtain ⟨r,hr⟩ := radius_eq_residual z v u k (hpos v u)
  rw [hq, hr]
  exact comparison_ne hgp u v huv q r

/-- No two distinct candidates in the same endpoint list agree. -/
lemma candidate_ne {N n : ℕ} (z : Vector N n) (hgp : GeneralPosition z)
    (hpos : ∀ u v j, response u j z ≤ prediction u v j z)
    (upper : Bool) (u v w : Fin N) (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (j k : Fin n) : candidate z upper u v j k ≠ candidate z upper u w j k := by
  obtain ⟨q,hq⟩ := candidate_eq_endpoint z upper u v j k (hpos v u)
  obtain ⟨r,hr⟩ := candidate_eq_endpoint z upper u w j k (hpos w u)
  rw [hq, hr]
  exact endpoint_ne hgp upper u v w huv huw hvw j q r

lemma candidate_ne_response {N n : ℕ} (z : Vector N n) (hgp : GeneralPosition z)
    (hpos : ∀ u v j, response u j z ≤ prediction u v j z)
    (upper : Bool) (u v : Fin N) (huv : u ≠ v) (j k : Fin n) :
    candidate z upper u v j k ≠ response u j z := by
  obtain ⟨q,hq⟩ := candidate_eq_endpoint z upper u v j k (hpos v u)
  rw [hq]
  exact endpoint_ne_response hgp upper u v huv j q

/-- The response is distinct from both aggregate endpoint order statistics. -/
lemma aggregate_ne_response {m n : ℕ} (z : Vector (m+1) n) (hgp : GeneralPosition z)
    (hpos : ∀ u v j, response u j z ≤ prediction u v j z)
    (upper : Bool) (u : Fin (m+1)) (j k : Fin n) (outer : Fin m) :
    aggregate z upper u j k outer ≠ response u j z := by
  unfold aggregate OrderStatistics.stat
  exact candidate_ne_response z hgp hpos upper u _
    (Fin.succAbove_ne _ _).symm j k


/-- All four kinds of relevant ties, stated using the actual absolute-residual
radii and candidate intervals. -/
structure TieFree {m n : ℕ} (z : Vector (m+1) n) : Prop where
  residuals : ∀ u v, Function.Injective (fun j => |response u j z - prediction u v j z|)
  comparisons : ∀ u v, u ≠ v → ∀ k, radius z u v k ≠ radius z v u k
  candidates : ∀ upper u v w, u ≠ v → u ≠ w → v ≠ w → ∀ j k,
    candidate z upper u v j k ≠ candidate z upper u w j k
  endpoints : ∀ upper u j k outer, aggregate z upper u j k outer ≠ response u j z

lemma tieFree_of_generalPosition {m n : ℕ} (z : Vector (m+1) n)
    (hgp : GeneralPosition z) (hpos : ∀ u v j, response u j z ≤ prediction u v j z) :
    TieFree z :=
  ⟨residual_injective z hgp hpos, radius_ne_opposite z hgp hpos,
    candidate_ne z hgp hpos, aggregate_ne_response z hgp hpos⟩

/-- The source extremizers start with zero responses and positive table entries. -/
def baseline {N n : ℕ} (p : Fin N → Fin N → Fin n → ℝ) : Vector N n
  | .inl _ => 0
  | .inr (u,v,j) => p u v j

/-- Actual finite tables with positive entries admit arbitrarily small
primitive perturbations removing every listed relevant tie simultaneously. -/
theorem exists_tieFree_perturbation {m n : ℕ}
    (p : Fin (m+1) → Fin (m+1) → Fin n → ℝ)
    (hp : ∀ u v j, 1 ≤ p u v j) (η : ℝ) (hη : 0 < η) (hη' : η < 1/4) :
    ∃ z' : Vector (m+1) n,
      (∀ a, |z' a - baseline p a| < η) ∧ TieFree z' := by
  obtain ⟨z',hz',hgp⟩ := exists_general_position (baseline p) η hη
  refine ⟨z',hz',tieFree_of_generalPosition z' hgp ?_⟩
  intro u v j
  change z' (.inl (u,j)) ≤ z' (.inr (u,v,j))
  have hy := hz' (.inl (u,j))
  have hpr := hz' (.inr (u,v,j))
  simp only [baseline, sub_zero] at hy hpr
  have hy' := (abs_lt.mp hy).2
  have hp' := (abs_lt.mp hpr).1
  have h₁ := hp u v j
  linarith

lemma radius_perturbation {N n : ℕ} (z z' : Vector N n) (η : ℝ)
    (hz : ∀ a, |z' a-z a| ≤ η) (u v : Fin N) (k : Fin n) :
    |radius z' u v k-radius z u v k| ≤ 2*η := by
  exact TieRemoval.radius_perturbation
    (fun j => response u j z) (fun j => response u j z')
    (fun j => prediction u v j z) (fun j => prediction u v j z') k η
    (fun j => hz (.inl (u,j))) (fun j => hz (.inr (u,v,j)))

lemma candidate_perturbation {N n : ℕ} (z z' : Vector N n) (η : ℝ)
    (hz : ∀ a, |z' a-z a| ≤ η) (upper : Bool) (u v : Fin N) (j k : Fin n) :
    |candidate z' upper u v j k-candidate z upper u v j k| ≤ 3*η := by
  cases upper
  · exact TieRemoval.lower_candidate_perturbation _ _ _ _ η
      (hz (.inr (u,v,j))) (radius_perturbation z z' η hz v u k)
  · exact TieRemoval.upper_candidate_perturbation _ _ _ _ η
      (hz (.inr (u,v,j))) (radius_perturbation z z' η hz v u k)

lemma aggregate_perturbation {m n : ℕ} (z z' : Vector (m+1) n) (η : ℝ)
    (hz : ∀ a, |z' a-z a| ≤ η) (upper : Bool) (u : Fin (m+1))
    (j k : Fin n) (outer : Fin m) :
    |aggregate z' upper u j k outer-aggregate z upper u j k outer| ≤ 3*η :=
  OrderStatistics.stat_lipschitz _ _ outer _
    (fun v => candidate_perturbation z z' η hz upper u (u.succAbove v) j k)

/-- The actual nested finite-table endpoint rule preserves each unit-margin
lower-side miss, hence preserves every selected failing coordinate of §5. -/
lemma strict_miss_preserved {m n : ℕ} (z z' : Vector (m+1) n) (η : ℝ)
    (hη : η < 1/4) (hz : ∀ a, |z' a-z a| ≤ η) (u : Fin (m+1))
    (j k : Fin n) (outer : Fin m)
    (hmargin : response u j z + 1 ≤ aggregate z false u j k outer) :
    response u j z' < aggregate z' false u j k outer :=
  TieRemoval.unit_failure_margin _ _ _ _ η hη hmargin
    (aggregate_perturbation z z' η hz false u j k outer) (hz (.inl (u,j)))

/-- Proposition 5.3 at the actual finite prediction-table level: one primitive
perturbation removes all relevant ties and simultaneously preserves every
unit-margin failing coordinate at every finite inner and outer rank. -/
theorem quantitative_tie_removal {m n : ℕ}
    (p : Fin (m+1) → Fin (m+1) → Fin n → ℝ)
    (hp : ∀ u v j, 1 ≤ p u v j) (η : ℝ) (hη : 0 < η) (hη' : η < 1/4) :
    ∃ z' : Vector (m+1) n,
      (∀ a, |z' a-baseline p a| ≤ η) ∧ TieFree z' ∧
      ∀ u j k outer,
        response u j (baseline p) + 1 ≤ aggregate (baseline p) false u j k outer →
        response u j z' < aggregate z' false u j k outer := by
  obtain ⟨z',hz',htf⟩ := exists_tieFree_perturbation p hp η hη hη'
  have hz : ∀ a, |z' a-baseline p a| ≤ η := fun a => (hz' a).le
  exact ⟨z',hz,htf,fun u j k outer =>
    strict_miss_preserved (baseline p) z' η hη' hz u j k outer⟩

end
end MEJF.TieFreeTable
