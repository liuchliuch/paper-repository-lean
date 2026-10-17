import Paper36.Complexity
import Mathlib.Tactic.FinCases

/-! The source-specific binary coefficient growth of Appendix E.  A rational
is encoded by a signed numerator and a nonzero signed denominator; the final
positive-denominator conversion preserves both magnitudes.  These are actual
representations of the constructed LP and quadratic polynomial coefficients,
not assumptions of a polynomial-time planning algorithm. -/
namespace Paper36.ComplexityEncoding
open scoped BigOperators
open Paper36.Complexity MvPolynomial
set_option maxHeartbeats 800000
noncomputable section

/-- A raw binary pair with at most b+1 magnitude bits in each component. -/
def HasRep (q : ℚ) (b : ℕ) : Prop :=
  ∃ n d : ℤ, d ≠ 0 ∧ q = (n : ℚ)/(d : ℚ) ∧
    n.natAbs ≤ 2^b ∧ d.natAbs ≤ 2^b

theorem HasRep.mono {q : ℚ} {b c : ℕ} (hq : HasRep q b) (hbc : b ≤ c) : HasRep q c := by
  obtain ⟨n,d,hd,he,hn,hD⟩ := hq
  exact ⟨n,d,hd,he,hn.trans (Nat.pow_le_pow_right (by norm_num) hbc),
    hD.trans (Nat.pow_le_pow_right (by norm_num) hbc)⟩

theorem rep_zero : HasRep 0 0 := by
  refine ⟨0,1,by norm_num,by norm_num,?_,?_⟩ <;> norm_num

theorem rep_one : HasRep 1 0 := by
  refine ⟨1,1,by norm_num,by norm_num,?_,?_⟩ <;> norm_num

theorem HasRep.neg {q : ℚ} {b : ℕ} (hq : HasRep q b) : HasRep (-q) b := by
  obtain ⟨n,d,hd,he,hn,hD⟩ := hq
  exact ⟨-n,d,hd,by simp [he,neg_div],by simpa using hn,hD⟩

theorem HasRep.mul {q r : ℚ} {b c : ℕ} (hq : HasRep q b) (hr : HasRep r c) :
    HasRep (q*r) (b+c) := by
  obtain ⟨n,d,hd,he,hn,hD⟩ := hq
  obtain ⟨m,e,he0,hr,hm,hE⟩ := hr
  refine ⟨n*m,d*e,mul_ne_zero hd he0,?_,?_,?_⟩
  · simp [he,hr,div_mul_div_comm]
  · simpa [Int.natAbs_mul,pow_add] using Nat.mul_le_mul hn hm
  · simpa [Int.natAbs_mul,pow_add] using Nat.mul_le_mul hD hE

theorem HasRep.inv {q : ℚ} {b : ℕ} (hq : HasRep q b) (h0 : q ≠ 0) : HasRep q⁻¹ b := by
  obtain ⟨n,d,hd,he,hn,hD⟩ := hq
  have hn0 : n ≠ 0 := by intro hz; simp [hz] at he; exact h0 he
  exact ⟨d,n,hn0,by simp [he],hD,hn⟩

theorem HasRep.div {q r : ℚ} {b c : ℕ} (hq : HasRep q b) (hr : HasRep r c) (hr0 : r ≠ 0) :
    HasRep (q/r) (b+c) := by simpa [div_eq_mul_inv] using hq.mul (hr.inv hr0)

theorem HasRep.add {q r : ℚ} {b c : ℕ} (hq : HasRep q b) (hr : HasRep r c) :
    HasRep (q+r) (b+c+1) := by
  obtain ⟨n,d,hd,he,hn,hD⟩ := hq
  obtain ⟨m,e,he0,hr,hm,hE⟩ := hr
  refine ⟨n*e+m*d,d*e,mul_ne_zero hd he0,?_,?_,?_⟩
  · rw [he,hr]
    have hdq : (d:ℚ) ≠ 0 := by exact_mod_cast hd
    have heq : (e:ℚ) ≠ 0 := by exact_mod_cast he0
    rw [div_add_div (n:ℚ) (m:ℚ) hdq heq]
    push_cast
    congr 1
    ring
  · have h1 := Nat.mul_le_mul hn hE
    have h2 := Nat.mul_le_mul hm hD
    have h3 := Int.natAbs_add_le (n*e) (m*d)
    simp only [Int.natAbs_mul] at h3
    simp only [pow_succ,pow_add]
    nlinarith
  · have hh := Nat.mul_le_mul hD hE
    simp only [Int.natAbs_mul]
    simp only [pow_succ,pow_add]
    omega

theorem HasRep.sub {q r : ℚ} {b c : ℕ} (hq : HasRep q b) (hr : HasRep r c) :
    HasRep (q-r) (b+c+1) := by simpa [sub_eq_add_neg] using hq.add hr.neg

/-- Uniform finite sums grow linearly in the number of terms, including all
unreduced denominator products and numerator additions. -/
theorem rep_fin_sum {b H : ℕ} (f : Fin H → ℚ) (hf : ∀ i, HasRep (f i) b) :
    HasRep (∑ i, f i) (H*(b+1)) := by
  induction H with
  | zero => simpa using rep_zero
  | succ H ih =>
    rw [Fin.sum_univ_succ]
    have hs := (hf 0).add (ih (fun i => f i.succ) (fun i => hf i.succ))
    convert hs using 1; ring

/-- A positive denominator can always be written without increasing either
component's magnitude. Each size is bounded by b+1, including the value 1. -/
theorem positive_pair_payload {q : ℚ} {b : ℕ} (hq : HasRep q b) :
    ∃ n : ℤ, ∃ d : ℕ, 0 < d ∧ q = (n : ℚ)/(d : ℚ) ∧
      Nat.size n.natAbs + Nat.size d + 2 ≤ 2*b+4 := by
  obtain ⟨n,d,hd,he,hn,hD⟩ := hq
  have hsize (a : ℕ) (ha : a ≤ 2^b) : Nat.size a ≤ b+1 := by
    apply Nat.size_le.2
    have hp : 0 < (2:ℕ)^b := pow_pos (by norm_num) _
    rw [pow_succ]
    nlinarith
  by_cases hp : 0 < d
  · refine ⟨n,d.toNat,by omega,?_,?_⟩
    · have heq : ((d.toNat : ℕ) : ℤ) = d := Int.toNat_of_nonneg hp.le
      rw [← heq] at he
      exact_mod_cast he
    · have heq : d.toNat = d.natAbs := by omega
      rw [heq]
      have h1 := hsize n.natAbs hn
      have h2 := hsize d.natAbs hD
      omega
  · have hneg : 0 < -d := by omega
    refine ⟨-n,(-d).toNat,by omega,?_,?_⟩
    · have heq : (((-d).toNat : ℕ) : ℤ) = -d := Int.toNat_of_nonneg hneg.le
      have hcast : (((-d).toNat : ℕ) : ℚ) = (-d : ℚ) := by exact_mod_cast heq
      rw [hcast]
      simpa using he
    · have heq : (-d).toNat = d.natAbs := by omega
      rw [heq,Int.natAbs_neg]
      have h1 := hsize n.natAbs hn
      have h2 := hsize d.natAbs hD
      omega

/-- The literal binary rational input convention supplies HasRep directly. -/
theorem rep_of_input_bits (q : ℚ) {b : ℕ}
    (hn : Nat.size q.num.natAbs ≤ b) (hd : Nat.size q.den ≤ b) : HasRep q b := by
  refine ⟨q.num,q.den,by exact_mod_cast q.den_pos.ne',q.num_div_den.symm,?_,?_⟩
  · exact (Nat.size_le.1 hn).le
  · simpa only [Int.natAbs_natCast] using (Nat.size_le.1 hd).le

/-- Uniform input-bit premise, with a full quantifier for every rational entry. -/
structure LPInputBound {H : ℕ} (α τ target : ℚ) (c₀ c₁ r₀ r₁ : Fin H → ℚ) (b : ℕ) : Prop where
  tail : HasRep α b
  budget : HasRep τ b
  target : HasRep target b
  cost₀ : ∀ i, HasRep (c₀ i) b
  cost₁ : ∀ i, HasRep (c₁ i) b
  reward₀ : ∀ i, HasRep (r₀ i) b
  reward₁ : ∀ i, HasRep (r₁ i) b

theorem risk_intercept_rep {α d₀ d₁ : ℚ} {b : ℕ}
    (ha : HasRep α b) (h0 : α ≠ 0) (h₀ : HasRep d₀ b) (h₁ : HasRep d₁ b) (piece : Bool) :
    HasRep (riskIntercept α d₀ d₁ piece) (4*b+2) := by
  have hd := (h₀.sub h₁).div ha h0
  have hsum := h₁.add hd
  by_cases h : d₀ ≤ d₁ <;> cases piece <;>
    simp only [riskIntercept,h,Bool.false_eq_true,↓reduceIte]
  · exact h₀.mono (by omega)
  · exact h₁.mono (by omega)
  · exact hsum.mono (by omega)
  · exact h₀.mono (by omega)

theorem risk_slope_rep {α d₀ d₁ : ℚ} {b : ℕ}
    (ha : HasRep α b) (h0 : α ≠ 0) (h₀ : HasRep d₀ b) (h₁ : HasRep d₁ b) (piece : Bool) :
    HasRep (riskSlope α d₀ d₁ piece) (4*b+2) := by
  have hd := (h₁.sub h₀).div ha h0
  have he := ((h₀.sub h₁).div ha h0).neg
  by_cases h : d₀ ≤ d₁ <;> cases piece <;>
    simp only [riskSlope,h,Bool.false_eq_true,↓reduceIte]
  · exact hd.mono (by omega)
  · exact rep_zero.mono (by omega)
  · simpa only [neg_div] using he.mono (show b+b+1+b ≤ 4*b+2 by omega)
  · exact rep_zero.mono (by omega)

/-- Every matrix entry and right-hand side of the actual guessed-piece LP has
an explicit polynomial raw-pair magnitude exponent. No LP coefficient bound is
left as an external theorem. -/
theorem one_state_LP_coefficients_rep {H b : ℕ} {α τ target : ℚ}
    {c₀ c₁ r₀ r₁ : Fin H → ℚ} (input : LPInputBound α τ target c₀ c₁ r₀ r₁ b)
    (ha : α ≠ 0) (piece : Fin H → Bool) :
    (∀ k j, HasRep (oneStateLinearCoefficients α c₀ c₁ r₀ r₁ piece k j) ((H+1)*(4*b+3))) ∧
    (∀ k, HasRep (oneStateLinearBound α τ target c₀ c₁ r₀ r₁ piece k) ((H+1)*(4*b+3))) := by
  have hexp : 4*b+2 ≤ (H+1)*(4*b+3) := by nlinarith
  have hone : HasRep 1 ((H+1)*(4*b+3)) := rep_one.mono (by omega)
  have hzero : HasRep 0 ((H+1)*(4*b+3)) := rep_zero.mono (by omega)
  have hactive (i : Fin H) : HasRep (activeBound α (c₀ i) (c₁ i) (piece i)) (4*b+2) := by
    have h1 := (rep_one.sub input.tail).mono (show 0+b+1 ≤ 4*b+2 by omega)
    have h2 := (input.tail.sub rep_one).mono (show b+0+1 ≤ 4*b+2 by omega)
    by_cases hc : c₀ i ≤ c₁ i <;> cases hb : piece i <;>
      simp only [activeBound,hc,Bool.false_eq_true,↓reduceIte]
    · exact input.tail.mono (by omega)
    · exact input.tail.neg.mono (by omega)
    · exact h2
    · exact h1
  constructor
  · intro k j
    cases k with
    | lower i => simp only [oneStateLinearCoefficients]; split_ifs; exact hone.neg; exact hzero
    | upper i => simp only [oneStateLinearCoefficients]; split_ifs; exact hone; exact hzero
    | active i =>
      simp only [oneStateLinearCoefficients]
      split_ifs
      · by_cases hc : c₀ i ≤ c₁ i <;> cases hb : piece i <;>
          simp only [activeSlope,hc,Bool.false_eq_true,↓reduceIte]
        · exact hone
        · exact hone.neg
        · exact hone.neg
        · exact hone
      · exact hzero
    | risk => exact (risk_slope_rep input.tail ha (input.cost₀ j) (input.cost₁ j) _).mono hexp
    | reward => exact ((input.reward₁ j).sub (input.reward₀ j)).neg.mono (by nlinarith)
  · intro k
    cases k with
    | lower i => exact hzero
    | upper i => exact hone
    | active i => exact (hactive i).mono hexp
    | risk =>
      have hs := rep_fin_sum (fun i => riskIntercept α (c₀ i) (c₁ i) (piece i))
        (fun i => risk_intercept_rep input.tail ha (input.cost₀ i) (input.cost₁ i) _)
      exact (input.budget.sub hs).mono (by nlinarith)
    | reward =>
      have hs := rep_fin_sum r₀ input.reward₀
      exact (hs.sub input.target).mono (by nlinarith)

/-- In the actual dense (3H+2)-by-H rational LP, every scalar including the
right-hand side can be serialized with this polynomial positive-pair payload. -/
theorem one_state_LP_scalar_payload {H b : ℕ} {α τ target : ℚ}
    {c₀ c₁ r₀ r₁ : Fin H → ℚ} (input : LPInputBound α τ target c₀ c₁ r₀ r₁ b)
    (ha : α ≠ 0) (piece : Fin H → Bool) :
    ∀ k, (∀ j, ∃ n : ℤ, ∃ d : ℕ, 0 < d ∧
      oneStateLinearCoefficients α c₀ c₁ r₀ r₁ piece k j = (n:ℚ)/(d:ℚ) ∧
        Nat.size n.natAbs + Nat.size d + 2 ≤ 2*((H+1)*(4*b+3))+4) ∧
    (∃ n : ℤ, ∃ d : ℕ, 0 < d ∧
      oneStateLinearBound α τ target c₀ c₁ r₀ r₁ piece k = (n:ℚ)/(d:ℚ) ∧
        Nat.size n.natAbs + Nat.size d + 2 ≤ 2*((H+1)*(4*b+3))+4) := by
  obtain ⟨hc,hb⟩ := one_state_LP_coefficients_rep input ha piece
  exact fun k => ⟨fun j => positive_pair_payload (hc k j),positive_pair_payload (hb k)⟩

/-! ## An explicit sparse quadratic monomial table for the actual ETR system -/

structure Term (V : Type*) where
  coefficient : ℚ
  first : Option V := none
  second : Option V := none

def Term.polynomial {V : Type*} (t : Term V) : MvPolynomial V ℚ :=
  C t.coefficient * (t.first.elim 1 X) * (t.second.elim 1 X)

def TermIndex (S A : Type*) := Fin 4 ⊕ (A ⊕ A × S)

instance {S A : Type*} [Fintype S] [Fintype A] : Fintype (TermIndex S A) :=
  inferInstanceAs (Fintype (Fin 4 ⊕ (A ⊕ A × S)))

def fourTerms {V : Type*} (t₀ t₁ t₂ t₃ : Term V) : Fin 4 → Term V :=
  Fin.cons t₀ (Fin.cons t₁ (Fin.cons t₂ (Fin.cons t₃ Fin.elim0)))

def rowTerms {V S A : Type*} (f : Fin 4 → Term V) (g : A → Term V)
    (h : A × S → Term V) : TermIndex S A → Term V := Sum.elim f (Sum.elim g h)

/-- A literal monomial table. Duplicate monomials are allowed in its sum;
no exponentially large expanded arithmetic circuit is used. -/
def planningTerm {H : ℕ} {S A : Type*}
    (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S) :
    PlanningConstraint H S A → TermIndex S A → Term (PlanningVar H S A)
  | .policyNonneg h s a => rowTerms
      (fourTerms ⟨1,some (.policy h s a),none⟩ ⟨0,none,none⟩ ⟨0,none,none⟩ ⟨0,none,none⟩)
      (fun _ => ⟨0,none,none⟩) (fun _ => ⟨0,none,none⟩)
  | .policyTotal h s => rowTerms
      (fourTerms ⟨-1,none,none⟩ ⟨0,none,none⟩ ⟨0,none,none⟩ ⟨0,none,none⟩)
      (fun a => ⟨1,some (.policy h s a),none⟩) (fun _ => ⟨0,none,none⟩)
  | .terminalReward s => rowTerms
      (fourTerms ⟨1,some (.reward (Fin.last H) s),none⟩ ⟨0,none,none⟩ ⟨0,none,none⟩ ⟨0,none,none⟩)
      (fun _ => ⟨0,none,none⟩) (fun _ => ⟨0,none,none⟩)
  | .terminalRisk s => rowTerms
      (fourTerms ⟨1,some (.risk (Fin.last H) s),none⟩ ⟨0,none,none⟩ ⟨0,none,none⟩ ⟨0,none,none⟩)
      (fun _ => ⟨0,none,none⟩) (fun _ => ⟨0,none,none⟩)
  | .rewardStep h s => rowTerms
      (fourTerms ⟨1,some (.reward h.castSucc s),none⟩ ⟨0,none,none⟩ ⟨0,none,none⟩ ⟨0,none,none⟩)
      (fun a => ⟨-r h s a,some (.policy h s a),none⟩)
      (fun x => ⟨-p s x.1 x.2,some (.policy h s x.1),some (.reward h.succ x.2)⟩)
  | .positiveNonneg h s a t => rowTerms
      (fourTerms ⟨1,some (.positive h s a t),none⟩ ⟨0,none,none⟩ ⟨0,none,none⟩ ⟨0,none,none⟩)
      (fun _ => ⟨0,none,none⟩) (fun _ => ⟨0,none,none⟩)
  | .positiveGap h s a t => rowTerms
      (fourTerms ⟨1,some (.positive h s a t),none⟩ ⟨-c h s a,none,none⟩
        ⟨-1,some (.risk h.succ t),none⟩ ⟨1,some (.threshold h s),none⟩)
      (fun _ => ⟨0,none,none⟩) (fun _ => ⟨0,none,none⟩)
  | .riskStep h s => rowTerms
      (fourTerms ⟨1,some (.risk h.castSucc s),none⟩ ⟨-1,some (.threshold h s),none⟩ ⟨0,none,none⟩ ⟨0,none,none⟩)
      (fun _ => ⟨0,none,none⟩)
      (fun x => ⟨-(p s x.1 x.2/α),some (.policy h s x.1),some (.positive h s x.1 x.2)⟩)
  | .budget => rowTerms
      (fourTerms ⟨τ,none,none⟩ ⟨-1,some (.risk 0 s₀),none⟩ ⟨0,none,none⟩ ⟨0,none,none⟩)
      (fun _ => ⟨0,none,none⟩) (fun _ => ⟨0,none,none⟩)
  | .target => rowTerms
      (fourTerms ⟨1,some (.reward 0 s₀),none⟩ ⟨-target,none,none⟩ ⟨0,none,none⟩ ⟨0,none,none⟩)
      (fun _ => ⟨0,none,none⟩) (fun _ => ⟨0,none,none⟩)

/-- The generated sparse quadratic table evaluates to precisely the already
proved actual planning polynomial, for every constraint. -/
theorem planningTerm_sum {H : ℕ} {S A : Type*} [Fintype S] [Fintype A]
    (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (s₀ : S) (k : PlanningConstraint H S A) :
    (∑ j : TermIndex S A, (planningTerm r c p α τ target s₀ k j).polynomial) =
      planningPolynomial r c p α τ target s₀ k := by
  cases k <;>
    simp [TermIndex,Fintype.sum_sum_type,Fintype.sum_prod_type,Fin.sum_univ_succ,
      planningTerm,rowTerms,fourTerms,Term.polynomial,planningPolynomial]
  all_goals ring_nf
  all_goals try simp only [Finset.mul_sum,Finset.sum_add_distrib]
  all_goals try simp only [mul_comm,mul_left_comm]
  all_goals ring

/-- Each atom is a sum of exactly this many two-variable monomial slots. -/
theorem planningTerm_count {S A : Type*} [Fintype S] [Fintype A] :
    Fintype.card (TermIndex S A) = 4+Fintype.card A+Fintype.card A*Fintype.card S := by
  simp [TermIndex]
  omega

/-- Input bit bounds quantify every rational entry actually used by the ETR compiler. -/
structure ETRInputBound {H : ℕ} {S A : Type*}
    (r c : Fin H → S → A → ℚ) (p : S → A → S → ℚ)
    (α τ target : ℚ) (b : ℕ) : Prop where
  reward : ∀ h s a, HasRep (r h s a) b
  cost : ∀ h s a, HasRep (c h s a) b
  transition : ∀ s a t, HasRep (p s a t) b
  tail : HasRep α b
  budget : HasRep τ b
  target : HasRep target b

/-- All actual sparse coefficients use at most two input pair multiplications:
p/alpha has raw numerator p.num*alpha.den and denominator p.den*alpha.num.
All other coefficients are signed input entries or 0,1. -/
theorem planningTerm_coefficient_rep {H b : ℕ} {S A : Type*}
    {r c : Fin H → S → A → ℚ} {p : S → A → S → ℚ} {α τ target : ℚ}
    (input : ETRInputBound r c p α τ target b) (ha : α ≠ 0) (s₀ : S)
    (k : PlanningConstraint H S A) (j : TermIndex S A) :
    HasRep (planningTerm r c p α τ target s₀ k j).coefficient (2*b) := by
  have hz := rep_zero.mono (show 0 ≤ 2*b by omega)
  have ho := rep_one.mono (show 0 ≤ 2*b by omega)
  have hr h s a := (input.reward h s a).neg.mono (show b ≤ 2*b by omega)
  have hc h s a := (input.cost h s a).neg.mono (show b ≤ 2*b by omega)
  have hp s a t := (input.transition s a t).neg.mono (show b ≤ 2*b by omega)
  have hs s a t : HasRep (-(p s a t/α)) (2*b) := by
    simpa only [two_mul] using ((input.transition s a t).div input.tail ha).neg
  have ht := input.budget.mono (show b ≤ 2*b by omega)
  have hv := input.target.neg.mono (show b ≤ 2*b by omega)
  rcases j with i | (a | ⟨a,t⟩)
  · fin_cases i <;> cases k <;> simp [planningTerm,rowTerms,fourTerms]
    all_goals first | exact hz | exact ho | exact ho.neg | apply hr | apply hc | apply hp | apply hs | exact ht | exact hv
  · cases k <;> simp [planningTerm,rowTerms,fourTerms]
    all_goals first | exact hz | exact ho | apply hr
  · cases k <;> simp [planningTerm,rowTerms,fourTerms]
    all_goals first | exact hz | apply hp | apply hs


/-- The coefficient payload in each actual quadratic-table slot is linear in
the input scalar bit bound. The table has polynomially many slots by
planning_constraint_count and planningTerm_count. -/
theorem planningTerm_scalar_payload {H b : ℕ} {S A : Type*}
    {r c : Fin H → S → A → ℚ} {p : S → A → S → ℚ} {α τ target : ℚ}
    (input : ETRInputBound r c p α τ target b) (ha : α ≠ 0) (s₀ : S)
    (k : PlanningConstraint H S A) (j : TermIndex S A) :
    ∃ n : ℤ, ∃ d : ℕ, 0 < d ∧
      (planningTerm r c p α τ target s₀ k j).coefficient = (n:ℚ)/(d:ℚ) ∧
        Nat.size n.natAbs + Nat.size d + 2 ≤ 4*b+4 := by
  obtain ⟨n,d,hd,he,hs⟩ := positive_pair_payload (planningTerm_coefficient_rep input ha s₀ k j)
  exact ⟨n,d,hd,he,by omega⟩


/-- A signed raw pair is put over a positive natural denominator without
increasing either magnitude. -/
theorem positive_rep {q : ℚ} {b : ℕ} (hq : HasRep q b) :
    ∃ n : ℤ, ∃ d : ℕ, 0 < d ∧ q = (n:ℚ)/(d:ℚ) ∧ n.natAbs ≤ 2^b ∧ d ≤ 2^b := by
  obtain ⟨n,d,hd,he,hn,hD⟩ := hq
  by_cases hp : 0 < d
  · refine ⟨n,d.toNat,by omega,?_,hn,?_⟩
    · have heq : ((d.toNat : ℕ):ℤ) = d := Int.toNat_of_nonneg hp.le
      rw [← heq] at he
      exact_mod_cast he
    · have heq : d.toNat = d.natAbs := by omega
      simpa [heq] using hD
  · have hp' : 0 < -d := by omega
    refine ⟨-n,(-d).toNat,by omega,?_,by simpa using hn,?_⟩
    · have heq : (((-d).toNat : ℕ):ℤ) = -d := Int.toNat_of_nonneg hp'.le
      have hcast : (((-d).toNat : ℕ):ℚ) = (-d:ℚ) := by exact_mod_cast heq
      rw [hcast]
      simpa using he
    · have heq : (-d).toNat = d.natAbs := by omega
      simpa [heq] using hD

/-- Positive denominator clearing for an actual finite coefficient row. The
integer output has an explicit linear-in-row-length magnitude exponent. -/
theorem clear_finite_denominators {I : Type*} [Fintype I] {b : ℕ}
    (q : I → ℚ) (hq : ∀ i, HasRep (q i) b) :
    ∃ D : ℕ, ∃ N : I → ℤ, 0 < D ∧ D ≤ 2^(b*(Fintype.card I+1)) ∧
      ∀ i, q i = (N i:ℚ)/(D:ℚ) ∧ (N i).natAbs ≤ 2^(b*(Fintype.card I+1)) := by
  classical
  choose n d hd he hn hD using fun i => positive_rep (hq i)
  let D := ∏ i, d i
  let N := fun i => n i * (∏ j ∈ Finset.univ.erase i, (d j:ℤ))
  have hprod (s : Finset I) : (∏ j ∈ s, d j) ≤ 2^(b*Fintype.card I) := by
    calc
      (∏ j ∈ s, d j) ≤ ∏ _j ∈ s, 2^b := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun j _ => hD j)
      _ = (2^b)^s.card := by simp
      _ ≤ (2^b)^Fintype.card I := Nat.pow_le_pow_right (by positivity) (Finset.card_le_univ s)
      _ = 2^(b*Fintype.card I) := by rw [pow_mul]
  have hDpos : 0 < D := Finset.prod_pos fun j _ => hd j
  have hfactor (i : I) : d i * (∏ j ∈ Finset.univ.erase i, d j) = D :=
    Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)
  have hDbound : D ≤ 2^(b*(Fintype.card I+1)) := by
    exact (hprod Finset.univ).trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))
  refine ⟨D,N,hDpos,hDbound,fun i => ⟨?_,?_⟩⟩
  · have hi : (d i:ℚ) ≠ 0 := by exact_mod_cast (hd i).ne'
    have hj : ((∏ j ∈ Finset.univ.erase i, d j):ℚ) ≠ 0 := by
      exact_mod_cast (Finset.prod_pos (fun j _ => hd j)).ne'
    have hNp : (N i:ℚ) = (n i:ℚ)*((∏ j ∈ Finset.univ.erase i, d j):ℕ) := by simp [N]
    rw [hNp,← hfactor i,he i]
    push_cast
    rw [mul_div_mul_right _ _ hj]
  · change (n i * (∏ j ∈ Finset.univ.erase i, (d j:ℤ))).natAbs ≤ _
    simp only [Int.natAbs_mul,← Nat.cast_prod,Int.natAbs_natCast]
    calc
      (n i).natAbs * (∏ j ∈ Finset.univ.erase i, d j) ≤ 2^b * 2^(b*Fintype.card I) :=
        Nat.mul_le_mul (hn i) (hprod _)
      _ = 2^(b*(Fintype.card I+1)) := by rw [← pow_add]; congr 1; ring


/-- The actual ETR atom can be cleared to integer coefficients with a positive
common denominator of polynomial bit length. -/
theorem planningTerm_integer_clear {H b : ℕ} {S A : Type*} [Fintype S] [Fintype A]
    {r c : Fin H → S → A → ℚ} {p : S → A → S → ℚ} {α τ target : ℚ}
    (input : ETRInputBound r c p α τ target b) (ha : α ≠ 0) (s₀ : S)
    (k : PlanningConstraint H S A) :
    ∃ D : ℕ, ∃ N : TermIndex S A → ℤ, 0 < D ∧
      D ≤ 2^(2*b*(5+Fintype.card A+Fintype.card A*Fintype.card S)) ∧
      ∀ j, (planningTerm r c p α τ target s₀ k j).coefficient = (N j:ℚ)/(D:ℚ) ∧
        (N j).natAbs ≤ 2^(2*b*(5+Fintype.card A+Fintype.card A*Fintype.card S)) := by
  have hh := clear_finite_denominators
    (fun j => (planningTerm r c p α τ target s₀ k j).coefficient)
    (fun j => planningTerm_coefficient_rep input ha s₀ k j)
  simpa only [planningTerm_count,show 4+Fintype.card A+Fintype.card A*Fintype.card S+1 =
    5+Fintype.card A+Fintype.card A*Fintype.card S by omega] using hh

/-- The dense restricted LP has a polynomial total coefficient payload, not
merely polynomially many real inequalities. -/
theorem one_state_LP_total_payload {H b : ℕ} {α τ target : ℚ}
    {c₀ c₁ r₀ r₁ : Fin H → ℚ} (input : LPInputBound α τ target c₀ c₁ r₀ r₁ b)
    (ha : α ≠ 0) (piece : Fin H → Bool) :
    let q : OneStateLinearAtom H × Option (Fin H) → ℚ := fun x =>
      x.2.elim (oneStateLinearBound α τ target c₀ c₁ r₀ r₁ piece x.1)
        (oneStateLinearCoefficients α c₀ c₁ r₀ r₁ piece x.1)
    ∃ n : OneStateLinearAtom H × Option (Fin H) → ℤ,
      ∃ d : OneStateLinearAtom H × Option (Fin H) → ℕ,
      (∀ x : OneStateLinearAtom H × Option (Fin H), 0 < d x ∧ q x = (n x:ℚ)/(d x:ℚ)) ∧
      (Finset.sum Finset.univ (fun x : OneStateLinearAtom H × Option (Fin H) => Nat.size ((n x).natAbs) + Nat.size (d x) + 2)) ≤
        ((3*H+2)*(H+1))*(2*((H+1)*(4*b+3))+4) := by
  classical
  dsimp only
  let q : OneStateLinearAtom H × Option (Fin H) → ℚ := fun x =>
    x.2.elim (oneStateLinearBound α τ target c₀ c₁ r₀ r₁ piece x.1)
      (oneStateLinearCoefficients α c₀ c₁ r₀ r₁ piece x.1)
  have hq (x) : HasRep (q x) ((H+1)*(4*b+3)) := by
    obtain ⟨hc,hb⟩ := one_state_LP_coefficients_rep input ha piece
    rcases x with ⟨k,j⟩
    cases j with
    | none => exact hb k
    | some i => exact hc k i
  choose n d hd he hsize using fun x => positive_pair_payload (hq x)
  refine ⟨n,d,fun x => ⟨hd x,he x⟩,?_⟩
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hsize x)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_option,
    Fintype.card_fin,one_state_linear_atom_count,nsmul_eq_mul] using hs

/-- State/action/horizon dimensions are bounded by the number of scalar input
entries in the explicit-table representation, as used in Definition 6.1. -/
theorem planning_dimensions_le_scalar_count (H S A : ℕ) (hS : 0 < S) (hA : 0 < A) :
    H ≤ 2*H*S*A+S*A*S+3 ∧ S ≤ 2*H*S*A+S*A*S+3 ∧ A ≤ 2*H*S*A+S*A*S+3 := by
  have hs : 1 ≤ S := hS
  have ha : 1 ≤ A := hA
  have hh' := Nat.mul_le_mul (Nat.mul_le_mul_left H hs) ha
  have hs' := Nat.mul_le_mul (Nat.mul_le_mul_left S ha) hs
  have ha' := Nat.mul_le_mul (Nat.mul_le_mul_right A hs) hs
  simp only [mul_one,one_mul] at hh' hs' ha'
  constructor
  · nlinarith [Nat.zero_le (H*S*A),Nat.zero_le (S*A*S)]
  constructor <;> nlinarith [Nat.zero_le (H*S*A),Nat.zero_le (S*A*S)]


/-- Finite variable names use their ordinary binary enumeration indices. -/
def Term.variableBits {V : Type*} [Fintype V] (t : Term V) : ℕ :=
  t.first.elim 1 (fun v => Nat.size (Fintype.equivFin V v).val+1) +
  t.second.elim 1 (fun v => Nat.size (Fintype.equivFin V v).val+1)

theorem Term.variableBits_bound {V : Type*} [Fintype V] (t : Term V) :
    t.variableBits ≤ 2*(Nat.size (Fintype.card V)+1) := by
  have hslot (o : Option V) : o.elim 1 (fun v => Nat.size (Fintype.equivFin V v).val+1) ≤
      Nat.size (Fintype.card V)+1 := by
    cases o with
    | none => simp
    | some v =>
      exact Nat.add_le_add_right (Nat.size_le_size (Fintype.equivFin V v).isLt.le) 1
  exact (Nat.add_le_add (hslot t.first) (hslot t.second)).trans (by omega)

/-- A concrete total binary payload bound for the actual ETR table, including
both variable labels of every quadratic monomial. Its sparse-table polynomial
is exactly planningPolynomial, by planningTerm_sum. -/
theorem planningTerm_total_payload {H b : ℕ} {S A : Type*} [Fintype S] [Fintype A]
    {r c : Fin H → S → A → ℚ} {p : S → A → S → ℚ} {α τ target : ℚ}
    (input : ETRInputBound r c p α τ target b) (ha : α ≠ 0) (s₀ : S) :
    ∃ n : PlanningConstraint H S A × TermIndex S A → ℤ,
      ∃ d : PlanningConstraint H S A × TermIndex S A → ℕ,
      (∀ x : PlanningConstraint H S A × TermIndex S A, 0 < d x ∧ (planningTerm r c p α τ target s₀ x.1 x.2).coefficient = (n x:ℚ)/(d x:ℚ)) ∧
      (Finset.sum Finset.univ (fun x : PlanningConstraint H S A × TermIndex S A =>
        Nat.size ((n x).natAbs) + Nat.size (d x) + 2 +
          (planningTerm r c p α τ target s₀ x.1 x.2).variableBits)) ≤
        Fintype.card (PlanningConstraint H S A)*(4+Fintype.card A+Fintype.card A*Fintype.card S)*
          (4*b+4+2*(Nat.size (Fintype.card (PlanningVar H S A))+1)) := by
  classical
  choose n d hd he hs using fun x : PlanningConstraint H S A × TermIndex S A =>
    planningTerm_scalar_payload input ha s₀ x.1 x.2
  refine ⟨n,d,fun x => ⟨hd x,he x⟩,?_⟩
  have hentry (x : PlanningConstraint H S A × TermIndex S A) :
      Nat.size (n x).natAbs + Nat.size (d x) + 2 +
        (planningTerm r c p α τ target s₀ x.1 x.2).variableBits ≤
      4*b+4+2*(Nat.size (Fintype.card (PlanningVar H S A))+1) :=
    Nat.add_le_add (hs x) (Term.variableBits_bound _)
  have htotal := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hentry x)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,planningTerm_count,nsmul_eq_mul] using htotal


end
end Paper36.ComplexityEncoding
