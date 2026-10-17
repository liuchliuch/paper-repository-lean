import Paper29.InformationDefs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.SimpRw

/-! Finite probability and adaptive transcript information.  All logarithms
are natural logarithms; zero probability terms have their usual zero value.
The finite seed theorem below does not claim the general measurable seed
version of Lemma 4.3. -/
noncomputable section
open scoped BigOperators

namespace Paper29.Transcript

attribute [local instance] Classical.propDecidable

structure Law (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  total : ∑ ω, weight ω = 1

namespace Law
variable {Ω A B C : Type*} [Fintype Ω] [Fintype A] [Fintype B] [Fintype C]

def mass (P : Law Ω) (X : Ω → A) (a : A) : ℝ :=
  ∑ ω, if X ω = a then P.weight ω else 0

omit [Fintype A] in
lemma mass_nonneg (P : Law Ω) (X : Ω → A) (a : A) : 0 ≤ P.mass X a := by
  apply Finset.sum_nonneg
  intro ω _
  split_ifs <;> [exact P.nonneg ω; exact le_rfl]

omit [Fintype A] in
lemma weight_le_observed_mass (P : Law Ω) (X : Ω → A) (ω : Ω) :
    P.weight ω ≤ P.mass X (X ω) := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun η => if X η = X ω then P.weight η else 0)
    (fun η _ => by
      change 0 ≤ if X η = X ω then P.weight η else 0
      split_ifs <;> [exact P.nonneg η; exact le_rfl]) (Finset.mem_univ ω)
  simpa using h

lemma mass_total (P : Law Ω) (X : Ω → A) : ∑ a, P.mass X a = 1 := by
  unfold mass
  rw [Finset.sum_comm]
  simpa using P.total

omit [Fintype A] [Fintype B] in
lemma mass_eq_of_fibers (P : Law Ω) (X : Ω → A) (Y : Ω → B) (a : A) (b : B)
    (h : ∀ ω, X ω = a ↔ Y ω = b) : P.mass X a = P.mass Y b := by
  apply Finset.sum_congr rfl
  intro ω _
  simp only [h ω]

lemma sum_mass_mul (P : Law Ω) (X : Ω → A) (f : A → ℝ) :
    ∑ a, P.mass X a * f a = ∑ ω, P.weight ω * f (X ω) := by
  unfold mass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp

omit [Fintype A] in
lemma sum_pair_mass_right (P : Law Ω) (X : Ω → A) (Y : Ω → B) (a : A) :
    ∑ b, P.mass (fun ω => (X ω, Y ω)) (a, b) = P.mass X a := by
  unfold mass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hx : X ω = a <;> simp [Prod.mk.injEq, hx]

omit [Fintype B] in
lemma sum_pair_mass_left (P : Law Ω) (X : Ω → A) (Y : Ω → B) (b : B) :
    ∑ a, P.mass (fun ω => (X ω, Y ω)) (a, b) = P.mass Y b := by
  unfold mass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hy : Y ω = b <;> simp [Prod.mk.injEq, hy]

/-- Shannon entropy as the expectation of negative log probability. -/
def entropy (P : Law Ω) (X : Ω → A) : ℝ :=
  -∑ ω, P.weight ω * Real.log (P.mass X (X ω))

lemma entropy_eq_sum (P : Law Ω) (X : Ω → A) :
    P.entropy X = -∑ a, P.mass X a * Real.log (P.mass X a) := by
  rw [sum_mass_mul]
  rfl

/-- The standard finite joint-versus-product mutual information. -/
def information (P : Law Ω) (X : Ω → A) (Y : Ω → B) : ℝ :=
  ∑ ω, P.weight ω *
    (Real.log (P.mass (fun η => (X η, Y η)) (X ω, Y ω)) -
      Real.log (P.mass X (X ω)) - Real.log (P.mass Y (Y ω)))

lemma information_eq_log_ratio (P : Law Ω) (X : Ω → A) (Y : Ω → B) :
    P.information X Y = ∑ ω, P.weight ω * Real.log
      (P.mass (fun η => (X η, Y η)) (X ω, Y ω) /
        (P.mass X (X ω) * P.mass Y (Y ω))) := by
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hp : P.weight ω = 0
  · simp [hp]
  have hp0 : 0 < P.weight ω := lt_of_le_of_ne (P.nonneg ω) (Ne.symm hp)
  have hx : 0 < P.mass X (X ω) := hp0.trans_le (P.weight_le_observed_mass X ω)
  have hy : 0 < P.mass Y (Y ω) := hp0.trans_le (P.weight_le_observed_mass Y ω)
  have hxy : 0 < P.mass (fun η => (X η, Y η)) (X ω, Y ω) :=
    hp0.trans_le (P.weight_le_observed_mass (fun η => (X η, Y η)) ω)
  rw [Real.log_div hxy.ne' (mul_pos hx hy).ne', Real.log_mul hx.ne' hy.ne']
  ring

omit [Fintype A] [Fintype B] in
lemma information_eq_entropy (P : Law Ω) (X : Ω → A) (Y : Ω → B) :
    P.information X Y = P.entropy X + P.entropy Y -
      P.entropy (fun ω => (X ω, Y ω)) := by
  unfold information entropy
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring

lemma information_eq_joint_sum (P : Law Ω) (X : Ω → A) (Y : Ω → B) :
    P.information X Y = ∑ a, ∑ b,
      P.mass (fun ω => (X ω, Y ω)) (a, b) *
        (Real.log (P.mass (fun ω => (X ω, Y ω)) (a, b)) -
          Real.log (P.mass X a) - Real.log (P.mass Y b)) := by
  have h := P.sum_mass_mul (fun ω => (X ω, Y ω)) (fun z =>
    Real.log (P.mass (fun ω => (X ω, Y ω)) z) -
      Real.log (P.mass X z.1) - Real.log (P.mass Y z.2))
  simpa only [Fintype.sum_prod_type, information] using h.symm

/-- The joint log-density expression in the conditional law of `H = h`. -/
def localLog (P : Law Ω) (X : Ω → A) (Y : Ω → B) (H : Ω → C)
    (h : C) (ω : Ω) : ℝ :=
  Real.log (P.mass (fun η => (X η, (H η, Y η))) (X ω, (h, Y ω))) +
    Real.log (P.mass H h) -
    Real.log (P.mass (fun η => (X η, H η)) (X ω, h)) -
    Real.log (P.mass (fun η => (H η, Y η)) (h, Y ω))

/-- Mutual information under the finite regular conditional law `H = h`.
Its conditional sample weights are `P.weight ω / P.mass H h`. -/
def localInformation (P : Law Ω) (X : Ω → A) (Y : Ω → B) (H : Ω → C)
    (h : C) : ℝ :=
  ∑ ω, if H ω = h then P.weight ω / P.mass H h * P.localLog X Y H h ω else 0

def conditionalInformation (P : Law Ω) (X : Ω → A) (Y : Ω → B) (H : Ω → C) : ℝ :=
  ∑ h, P.mass H h * P.localInformation X Y H h

omit [Fintype A] [Fintype B] in
lemma weighted_localInformation (P : Law Ω) (X : Ω → A) (Y : Ω → B)
    (H : Ω → C) (h : C) :
    P.mass H h * P.localInformation X Y H h =
      ∑ ω, if H ω = h then P.weight ω * P.localLog X Y H h ω else 0 := by
  unfold localInformation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hh : H ω = h
  · simp only [if_pos hh]
    by_cases hm : P.mass H h = 0
    · have hp : P.weight ω = 0 := by
        have := P.weight_le_observed_mass H ω
        rw [hh, hm] at this
        exact le_antisymm this (P.nonneg ω)
      simp [hp]
    · field_simp
  · simp [hh]

lemma conditionalInformation_eq_sample_sum (P : Law Ω) (X : Ω → A) (Y : Ω → B)
    (H : Ω → C) :
    P.conditionalInformation X Y H =
      ∑ ω, P.weight ω * P.localLog X Y H (H ω) ω := by
  unfold conditionalInformation
  simp_rw [P.weighted_localInformation]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ω _
  simp

/-- The Shannon information chain rule, proved from the logarithmic definitions. -/
theorem information_chain_rule (P : Law Ω) (X : Ω → A) (Y : Ω → B)
    (H : Ω → C) :
    P.information X (fun ω => (H ω, Y ω)) =
      P.information X H + P.conditionalInformation X Y H := by
  rw [P.conditionalInformation_eq_sample_sum]
  unfold information localLog
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Independence in terms of the actual finite joint distribution. -/
def Independent (P : Law Ω) (X : Ω → A) (Y : Ω → B) : Prop :=
  ∀ a b, P.mass (fun ω => (X ω, Y ω)) (a, b) = P.mass X a * P.mass Y b

lemma information_zero_of_independent (P : Law Ω) (X : Ω → A) (Y : Ω → B)
    (h : P.Independent X Y) : P.information X Y = 0 := by
  apply Finset.sum_eq_zero
  intro ω _
  by_cases hp : P.weight ω = 0
  · simp [hp]
  have hp0 : 0 < P.weight ω := lt_of_le_of_ne (P.nonneg ω) (Ne.symm hp)
  have hx : 0 < P.mass X (X ω) := hp0.trans_le (P.weight_le_observed_mass X ω)
  have hy : 0 < P.mass Y (Y ω) := hp0.trans_le (P.weight_le_observed_mass Y ω)
  rw [h, Real.log_mul hx.ne' hy.ne']
  ring

omit [Fintype C] in
lemma independent_source (P : Law Ω) (X : Ω → A) (Y : Ω → B) (E : Ω → C)
    (h : P.Independent (fun ω => (X ω, Y ω)) E) : P.Independent X E := by
  unfold Independent at h
  intro a e
  have hsplit : P.mass (fun ω => (X ω, E ω)) (a, e) =
      ∑ b, P.mass (fun ω => ((X ω, Y ω), E ω)) ((a, b), e) := by
    unfold mass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hx : X ω = a <;> by_cases he : E ω = e <;>
      simp [Prod.mk.injEq, hx, he]
  rw [hsplit]
  simp_rw [h]
  rw [← Finset.sum_mul, P.sum_pair_mass_right]

/-- The finite regular conditional law, including its normalization proof. -/
def condition (P : Law Ω) (H : Ω → C) (h : C) (hh : 0 < P.mass H h) : Law Ω where
  weight ω := if H ω = h then P.weight ω / P.mass H h else 0
  nonneg ω := by split_ifs <;> [exact div_nonneg (P.nonneg ω) hh.le; exact le_rfl]
  total := by
    have heq : (∑ ω, if H ω = h then P.weight ω / P.mass H h else 0) =
        P.mass H h / P.mass H h := by
      unfold mass
      simp only [div_eq_mul_inv]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ω _
      split_ifs <;> simp
    rw [heq, div_self hh.ne']

omit [Fintype A] [Fintype C] in
lemma mass_condition (P : Law Ω) (X : Ω → A) (H : Ω → C) (h : C)
    (hh : 0 < P.mass H h) (a : A) :
    (P.condition H h hh).mass X a =
      P.mass (fun ω => (X ω, H ω)) (a, h) / P.mass H h := by
  unfold mass
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hx : X ω = a <;> by_cases he : H ω = h <;>
    simp [condition, Prod.mk.injEq, hx, he, mass, div_eq_mul_inv]

/-- The local formula really is Shannon mutual information under the conditional law. -/
theorem localInformation_eq_condition_information (P : Law Ω) (X : Ω → A)
    (Y : Ω → B) (H : Ω → C) (h : C) (hh : 0 < P.mass H h) :
    P.localInformation X Y H h = (P.condition H h hh).information X Y := by
  apply Finset.sum_congr rfl
  intro ω _
  by_cases he : H ω = h
  · simp only [if_pos he]
    rw [show (P.condition H h hh).weight ω = P.weight ω / P.mass H h from if_pos he]
    by_cases hp : P.weight ω = 0
    · simp [hp]
    have hp0 : 0 < P.weight ω := lt_of_le_of_ne (P.nonneg ω) (Ne.symm hp)
    have hx : 0 < P.mass (fun η => (X η, H η)) (X ω, h) := by
      have := hp0.trans_le (P.weight_le_observed_mass (fun η => (X η, H η)) ω)
      simpa [he] using this
    have hy : 0 < P.mass (fun η => (Y η, H η)) (Y ω, h) := by
      have := hp0.trans_le (P.weight_le_observed_mass (fun η => (Y η, H η)) ω)
      simpa [he] using this
    have hxy : 0 < P.mass (fun η => ((X η, Y η), H η)) ((X ω, Y ω), h) := by
      have := hp0.trans_le (P.weight_le_observed_mass (fun η => ((X η, Y η), H η)) ω)
      simpa [he] using this
    have hyperm : P.mass (fun η => (Y η, H η)) (Y ω, h) =
        P.mass (fun η => (H η, Y η)) (h, Y ω) := by
      apply P.mass_eq_of_fibers
      intro η
      simp [Prod.mk.injEq, and_comm]
    have hxyperm : P.mass (fun η => ((X η, Y η), H η)) ((X ω, Y ω), h) =
        P.mass (fun η => (X η, (H η, Y η))) (X ω, (h, Y ω)) := by
      apply P.mass_eq_of_fibers
      intro η
      simp [Prod.mk.injEq, and_assoc, and_comm]
    rw [P.mass_condition, P.mass_condition, P.mass_condition,
      Real.log_div hxy.ne' hh.ne', Real.log_div hx.ne' hh.ne',
      Real.log_div hy.ne' hh.ne', hxyperm, hyperm]
    unfold localLog
    ring
  · rw [show (P.condition H h hh).weight ω = 0 from if_neg he]
    simp [he]

lemma localInformation_eq_of_fiber {D : Type*} [Fintype D] (P : Law Ω)
    (X : Ω → A) (Y : Ω → B) (Z : Ω → D) (H : Ω → C) (h : C)
    (heq : ∀ ω η, H ω = h → H η = h → (Y ω = Y η ↔ Z ω = Z η)) :
    P.localInformation X Y H h = P.localInformation X Z H h := by
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hh : H ω = h
  · have hm : P.mass (fun η => (H η, Y η)) (h, Y ω) =
        P.mass (fun η => (H η, Z η)) (h, Z ω) := by
      apply P.mass_eq_of_fibers
      intro η
      simp only [Prod.mk.injEq]
      constructor
      · rintro ⟨hη, hy⟩
        exact ⟨hη, (heq η ω hη hh).mp hy⟩
      · rintro ⟨hη, hz⟩
        exact ⟨hη, (heq η ω hη hh).mpr hz⟩
    have hj : P.mass (fun η => (X η, (H η, Y η))) (X ω, (h, Y ω)) =
        P.mass (fun η => (X η, (H η, Z η))) (X ω, (h, Z ω)) := by
      apply P.mass_eq_of_fibers
      intro η
      simp only [Prod.mk.injEq]
      constructor
      · rintro ⟨hx, hη, hy⟩
        exact ⟨hx, hη, (heq η ω hη hh).mp hy⟩
      · rintro ⟨hx, hη, hz⟩
        exact ⟨hx, hη, (heq η ω hη hh).mpr hz⟩
    simp only [if_pos hh]
    unfold localLog
    rw [hm, hj]
  · simp [hh]

lemma localInformation_constant (P : Law Ω) (X : Ω → A) (H : Ω → C)
    (h : C) (b : B) : P.localInformation X (fun _ => b) H h = 0 := by
  apply Finset.sum_eq_zero
  intro ω _
  by_cases hh : H ω = h
  · have hm : P.mass (fun η => (H η, b)) (h, b) = P.mass H h := by
      apply P.mass_eq_of_fibers
      intro η
      simp
    have hj : P.mass (fun η => (X η, (H η, b))) (X ω, (h, b)) =
        P.mass (fun η => (X η, H η)) (X ω, h) := by
      apply P.mass_eq_of_fibers
      intro η
      simp
    simp only [if_pos hh]
    unfold localLog
    rw [hm, hj]
    ring
  · simp [hh]

end Law

/-- The genuine pushforward joint law used to apply the binary rate-distortion lemma. -/
def cubeJoint {Ω : Type*} [Fintype Ω] {r : ℕ} (P : Law Ω)
    (X Y : Ω → RateDistortion.Cube r) : RateDistortion.JointLaw r where
  mass s t := P.mass (fun ω => (X ω, Y ω)) (s, t)
  nonneg s t := P.mass_nonneg _ _
  total := by
    have h := P.mass_total (fun ω => (X ω, Y ω))
    simpa only [Fintype.sum_prod_type] using h

lemma cubeJoint_source {Ω : Type*} [Fintype Ω] {r : ℕ} (P : Law Ω)
    (X Y : Ω → RateDistortion.Cube r) (s : RateDistortion.Cube r) :
    (cubeJoint P X Y).source s = P.mass X s := P.sum_pair_mass_right X Y s

lemma cubeJoint_estimate {Ω : Type*} [Fintype Ω] {r : ℕ} (P : Law Ω)
    (X Y : Ω → RateDistortion.Cube r) (t : RateDistortion.Cube r) :
    (cubeJoint P X Y).estimate t = P.mass Y t := P.sum_pair_mass_left X Y t

lemma information_eq_cubeJoint {Ω : Type*} [Fintype Ω] {r : ℕ} (P : Law Ω)
    (X Y : Ω → RateDistortion.Cube r) :
    P.information X Y = (cubeJoint P X Y).mutualInformation := by
  rw [P.information_eq_joint_sum]
  unfold RateDistortion.JointLaw.mutualInformation
  simp_rw [cubeJoint_source, cubeJoint_estimate]
  rfl

lemma expectedHamming_cubeJoint {Ω : Type*} [Fintype Ω] {r : ℕ} (P : Law Ω)
    (X Y : Ω → RateDistortion.Cube r) :
    RateDistortion.expectedHamming (cubeJoint P X Y) =
      ∑ ω, P.weight ω * RateDistortion.hamming (X ω) (Y ω) := by
  have h := P.sum_mass_mul (fun ω => (X ω, Y ω))
    (fun z => RateDistortion.hamming z.1 z.2)
  simpa only [Fintype.sum_prod_type, RateDistortion.expectedHamming, cubeJoint] using h

universe u

/-- A finite history contains the private seed and every previous padded slot. -/
def History (E I R : Type u) : ℕ → Type u
  | 0 => E
  | t + 1 => History E I R t × Option (I × R)

instance historyFintype {E I R : Type u} [Fintype E] [Fintype I] [Fintype R]
    (t : ℕ) : Fintype (History E I R t) := by
  induction t with
  | zero => exact inferInstanceAs (Fintype E)
  | succ t ih =>
    letI := ih
    exact inferInstanceAs (Fintype (History E I R t × Option (I × R)))

def History.queried {E I R : Type u} : (t : ℕ) → History E I R t → List I
  | 0, _ => []
  | t + 1, (h, z) => History.queried t h ++ match z with
    | none => []
    | some (j, _) => [j]

/-- A genuine finite adaptive query policy.  A choice reads only the seed and
previous slots; stopping is absorbing and all new coordinate queries are fresh. -/
structure Policy (E I R : Type u) where
  choose : (t : ℕ) → History E I R t → Option I
  stopped : ∀ t h, choose (t + 1) (h, none) = none
  fresh : ∀ t h j, choose t h = some j → j ∉ History.queried t h

def Policy.history {E I R : Type u} (p : Policy E I R) (e : E) (b : I → R) :
    (t : ℕ) → History E I R t
  | 0 => e
  | t + 1 => let h := p.history e b t
    (h, (p.choose t h).map (fun j => (j, b j)))

def historyRV {Ω : Type*} {E I R : Type u} (p : Policy E I R) (seed : Ω → E)
    (responses : Ω → I → R) (t : ℕ) (ω : Ω) : History E I R t :=
  p.history (seed ω) (responses ω) t

def slotRV {Ω : Type*} {E I R : Type u} (p : Policy E I R) (seed : Ω → E)
    (responses : Ω → I → R) (t : ℕ) (ω : Ω) : Option (I × R) :=
  (p.choose t (historyRV p seed responses t ω)).map (fun j => (j, responses ω j))

lemma historyRV_succ {Ω : Type*} {E I R : Type u} (p : Policy E I R) (seed : Ω → E)
    (responses : Ω → I → R) (t : ℕ) :
    historyRV p seed responses (t + 1) =
      fun ω => (historyRV p seed responses t ω, slotRV p seed responses t ω) := rfl

def queryCount {E I R : Type u} (p : Policy E I R) (e : E) (b : I → R)
    (n : ℕ) : ℝ :=
  ∑ t ∈ Finset.range n, if p.choose t (p.history e b t) = none then 0 else 1

def expectedQueries {Ω : Type*} {E I R : Type u} [Fintype Ω] (P : Law Ω)
    (p : Policy E I R) (seed : Ω → E) (responses : Ω → I → R) (n : ℕ) : ℝ :=
  ∑ ω, P.weight ω * queryCount p (seed ω) (responses ω) n

def activeProbability {Ω : Type*} {E I R : Type u} [Fintype Ω] [Fintype E] [Fintype I]
    [Fintype R] (P : Law Ω) (p : Policy E I R) (seed : Ω → E)
    (responses : Ω → I → R) (t : ℕ) : ℝ :=
  ∑ h : History E I R t,
    if p.choose t h = none then 0 else P.mass (historyRV p seed responses t) h

/-- Freshness really gives a list of distinct queried coordinates on every run. -/
lemma history_queries_nodup {E I R : Type u} (p : Policy E I R) (e : E)
    (b : I → R) (t : ℕ) : (History.queried t (p.history e b t)).Nodup := by
  induction t with
  | zero => simp [History.queried]
  | succ t ih =>
    cases hc : p.choose t (p.history e b t) with
    | none => simpa [Policy.history, History.queried, hc] using ih
    | some j =>
      have h := List.Nodup.concat (p.fresh t (p.history e b t) j hc) ih
      simpa [Policy.history, History.queried, hc, List.concat_eq_append] using h

lemma queryCount_eq_history_length {E I R : Type u} (p : Policy E I R) (e : E)
    (b : I → R) (t : ℕ) :
    queryCount p e b t = ((History.queried t (p.history e b t)).length : ℝ) := by
  induction t with
  | zero => simp [queryCount, History.queried]
  | succ t ih =>
    unfold queryCount at *
    rw [Finset.sum_range_succ, ih]
    cases hc : p.choose t (p.history e b t) <;>
      simp [Policy.history, History.queried, hc]

lemma queryCount_le_card {E I R : Type u} [Fintype I] (p : Policy E I R) (e : E)
    (b : I → R) (t : ℕ) : queryCount p e b t ≤ Fintype.card I := by
  rw [queryCount_eq_history_length]
  exact_mod_cast (history_queries_nodup p e b t).length_le_card

lemma active_history_full_length {E I R : Type u} (p : Policy E I R) (e : E)
    (b : I → R) (t : ℕ) : ∀ j, p.choose t (p.history e b t) = some j →
      (History.queried t (p.history e b t)).length = t := by
  induction t with
  | zero => intro j _; rfl
  | succ t ih =>
    intro j hj
    cases hc : p.choose t (p.history e b t) with
    | none =>
      have hs : p.choose (t + 1) (p.history e b (t + 1)) = none := by
        simpa [Policy.history, hc] using p.stopped t (p.history e b t)
      rw [hs] at hj
      cases hj
    | some k =>
      have hl := ih k hc
      simp [Policy.history, History.queried, hc, hl]

/-- The cache-normalized policy has stopped by the number of available coordinates. -/
lemma stopped_at_card {E I R : Type u} [Fintype I] (p : Policy E I R) (e : E)
    (b : I → R) : p.choose (Fintype.card I) (p.history e b (Fintype.card I)) = none := by
  cases hc : p.choose (Fintype.card I) (p.history e b (Fintype.card I)) with
  | none => rfl
  | some j =>
    have hl := active_history_full_length p e b (Fintype.card I) j hc
    have hb := (history_queries_nodup p e b (Fintype.card I + 1)).length_le_card
    have hlen : (History.queried (Fintype.card I + 1)
        (p.history e b (Fintype.card I + 1))).length = Fintype.card I + 1 := by
      simp [Policy.history, History.queried, hc, hl]
    rw [hlen] at hb
    exact False.elim ((Nat.not_succ_le_self _) hb)

lemma stopped_after_card {E I R : Type u} [Fintype I] (p : Policy E I R) (e : E)
    (b : I → R) (k : ℕ) :
    p.choose (Fintype.card I + k) (p.history e b (Fintype.card I + k)) = none := by
  induction k with
  | zero => simpa using stopped_at_card p e b
  | succ k ih =>
    change p.choose ((Fintype.card I + k) + 1)
      (p.history e b (Fintype.card I + k),
        (p.choose (Fintype.card I + k) (p.history e b (Fintype.card I + k))).map
          (fun j => (j, b j))) = none
    rw [ih]
    exact p.stopped (Fintype.card I + k) (p.history e b (Fintype.card I + k))

section FiniteTranscript
variable {Ω S : Type*} {E I R : Type u} [Fintype Ω] [Fintype S] [Fintype E]
  [Fintype I] [Fintype R]

lemma activeProbability_eq_sample_sum (P : Law Ω) (p : Policy E I R)
    (seed : Ω → E) (responses : Ω → I → R) (t : ℕ) :
    activeProbability P p seed responses t =
      ∑ ω, P.weight ω *
        (if p.choose t (historyRV p seed responses t ω) = none then 0 else 1) := by
  have h := P.sum_mass_mul (historyRV p seed responses t)
    (fun h => if p.choose t h = none then 0 else 1)
  simpa only [mul_ite, mul_zero, mul_one, activeProbability] using h

lemma sum_activeProbability (P : Law Ω) (p : Policy E I R) (seed : Ω → E)
    (responses : Ω → I → R) (n : ℕ) :
    ∑ t ∈ Finset.range n, activeProbability P p seed responses t =
      expectedQueries P p seed responses n := by
  simp_rw [activeProbability_eq_sample_sum]
  rw [Finset.sum_comm]
  unfold expectedQueries queryCount
  simp only [Finset.mul_sum, historyRV]

lemma stopped_localInformation (P : Law Ω) (source : Ω → S) (p : Policy E I R)
    (seed : Ω → E) (responses : Ω → I → R) (t : ℕ) (h : History E I R t)
    (hs : p.choose t h = none) :
    P.localInformation source (slotRV p seed responses t) (historyRV p seed responses t) h = 0 := by
  have heq := P.localInformation_eq_of_fiber source (slotRV p seed responses t)
    (fun _ => ()) (historyRV p seed responses t) h (by
      intro ω η hω hη
      simp [slotRV, hω, hη, hs])
  rw [heq]
  exact P.localInformation_constant source (historyRV p seed responses t) h ()

lemma active_localInformation (P : Law Ω) (source : Ω → S) (p : Policy E I R)
    (seed : Ω → E) (responses : Ω → I → R) (t : ℕ) (h : History E I R t)
    (j : I) (hs : p.choose t h = some j) :
    P.localInformation source (slotRV p seed responses t) (historyRV p seed responses t) h =
      P.localInformation source (fun ω => responses ω j) (historyRV p seed responses t) h := by
  apply P.localInformation_eq_of_fiber
  intro ω η hω hη
  simp [slotRV, hω, hη, hs]

lemma slot_information_bound (P : Law Ω) (source : Ω → S) (p : Policy E I R)
    (seed : Ω → E) (responses : Ω → I → R) (t : ℕ) (κ : ℝ)
    (hlocal : ∀ h : History E I R t,
      0 < P.mass (historyRV p seed responses t) h → ∀ j,
      p.choose t h = some j →
      P.localInformation source (fun ω => responses ω j)
        (historyRV p seed responses t) h ≤ κ) :
    P.conditionalInformation source (slotRV p seed responses t)
      (historyRV p seed responses t) ≤ κ * activeProbability P p seed responses t := by
  unfold Law.conditionalInformation activeProbability
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro h _
  cases hs : p.choose t h with
  | none =>
    rw [stopped_localInformation P source p seed responses t h hs]
    simp
  | some j =>
    rw [active_localInformation P source p seed responses t h j hs]
    rw [if_neg (show (some j : Option I) ≠ none by simp)]
    by_cases hm : P.mass (historyRV p seed responses t) h = 0
    · simp [hm]
    have hmpos := lt_of_le_of_ne (P.mass_nonneg (historyRV p seed responses t) h)
      (Ne.symm hm)
    have hb := mul_le_mul_of_nonneg_left (hlocal h hmpos j hs) hmpos.le
    simpa only [mul_comm] using hb

/-- The complete finite transcript chain rule is a theorem, not a policy field. -/
theorem information_history_chain (P : Law Ω) (source : Ω → S) (p : Policy E I R)
    (seed : Ω → E) (responses : Ω → I → R) (hind : P.Independent source seed) (n : ℕ) :
    P.information source (historyRV p seed responses n) =
      ∑ t ∈ Finset.range n, P.conditionalInformation source (slotRV p seed responses t)
        (historyRV p seed responses t) := by
  induction n with
  | zero =>
    simpa [historyRV, Policy.history] using P.information_zero_of_independent source seed hind
  | succ n ih =>
    rw [historyRV_succ, P.information_chain_rule, ih, Finset.sum_range_succ]

/-- Finite-law, finite-seed adaptive transcript bound.  The hypothesis refers
to actual conditional mutual information of the next selected response.
The source and the entire response vector are jointly independent of the seed. -/
theorem finite_adaptive_transcript_bound (P : Law Ω) (source : Ω → S)
    (p : Policy E I R) (seed : Ω → E) (responses : Ω → I → R) (n : ℕ) (κ : ℝ)
    (hind : P.Independent (fun ω => (source ω, responses ω)) seed)
    (hlocal : ∀ t ∈ Finset.range n, ∀ h : History E I R t,
      0 < P.mass (historyRV p seed responses t) h → ∀ j,
      p.choose t h = some j →
      P.localInformation source (fun ω => responses ω j)
        (historyRV p seed responses t) h ≤ κ) :
    P.information source (historyRV p seed responses n) ≤
      κ * expectedQueries P p seed responses n := by
  rw [information_history_chain P source p seed responses
    (P.independent_source source responses seed hind)]
  calc
    _ ≤ ∑ t ∈ Finset.range n, κ * activeProbability P p seed responses t := by
      apply Finset.sum_le_sum
      intro t ht
      exact slot_information_bound P source p seed responses t κ (hlocal t ht)
    _ = κ * (∑ t ∈ Finset.range n, activeProbability P p seed responses t) := by
      rw [Finset.mul_sum]
    _ = κ * expectedQueries P p seed responses n := by rw [sum_activeProbability]

end FiniteTranscript

end Paper29.Transcript
