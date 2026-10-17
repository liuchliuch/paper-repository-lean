import Paper36.Simulation
import Paper36.Weights
import Paper36.Counts
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Deterministic hybrid charging for the actual CVaR simulation. Stages use
zero-based time: H transition stages correspond to a source horizon H+1.
The row-radius premise below is local to each high-count row; the complete
risk simulation and the aggregate 4 W sqrt(Lambda K Y) bound are proved. -/
namespace Paper36.HybridCharging
noncomputable section
open scoped BigOperators
open Paper36.CVaR Paper36.Simulation

variable {S A : Type*} [Fintype S] [Fintype A]

/-- Cauchy--Schwarz with nonnegative factors, in the exact square-root form. -/
theorem sum_sqrt_product_le {ι : Type*} (I : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ I, 0 ≤ a i) (hb : ∀ i ∈ I, 0 ≤ b i) :
    (∑ i ∈ I, Real.sqrt (a i * b i)) ≤
      Real.sqrt ((∑ i ∈ I, a i) * (∑ i ∈ I, b i)) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq I (fun i => Real.sqrt (a i))
    (fun i => Real.sqrt (b i))
  have hab : (∑ i ∈ I, Real.sqrt (a i) * Real.sqrt (b i)) =
      ∑ i ∈ I, Real.sqrt (a i * b i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact (Real.sqrt_mul (ha i hi) _).symm
  have haa : (∑ i ∈ I, (Real.sqrt (a i))^2) = ∑ i ∈ I, a i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (ha i hi))
  have hbb : (∑ i ∈ I, (Real.sqrt (b i))^2) = ∑ i ∈ I, b i :=
    Finset.sum_congr rfl (fun i hi => Real.sq_sqrt (hb i hi))
  rw [hab, haa, hbb] at hcs
  exact Real.le_sqrt_of_sq_le hcs

/-- Jensen for sqrt under a genuine finite probability law. -/
theorem law_sqrt_jensen (P : Law S) (X : S → ℝ) (hX : ∀ s, 0 ≤ X s) :
    (∑ s, P.mass s * Real.sqrt (X s)) ≤ Real.sqrt (∑ s, P.mass s * X s) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun s => Real.sqrt (P.mass s))
    (fun s => Real.sqrt (P.mass s) * Real.sqrt (X s))
  have hleft : (∑ s, Real.sqrt (P.mass s) *
      (Real.sqrt (P.mass s) * Real.sqrt (X s))) =
      ∑ s, P.mass s * Real.sqrt (X s) := by
    apply Finset.sum_congr rfl
    intro s _
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt (P.nonneg s)]
  have hfirst : (∑ s, Real.sqrt (P.mass s)^2) = 1 := by
    calc
      _ = ∑ s, P.mass s := Finset.sum_congr rfl (fun s _ => Real.sq_sqrt (P.nonneg s))
      _ = 1 := P.total
  have hsecond : (∑ s, (Real.sqrt (P.mass s) * Real.sqrt (X s))^2) =
      ∑ s, P.mass s * X s := by
    apply Finset.sum_congr rfl
    intro s _
    rw [mul_pow, Real.sq_sqrt (P.nonneg s), Real.sq_sqrt (hX s)]
  rw [hleft, hfirst, hsecond, one_mul] at hcs
  exact Real.le_sqrt_of_sq_le hcs

theorem tv_le_one (P Q : Law S) : tv P Q ≤ 1 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (f := fun s => |P.mass s-Q.mass s|)
    (g := fun s => P.mass s+Q.mass s) (fun s _ => by
      apply abs_le.2
      constructor <;> linarith [P.nonneg s, Q.nonneg s])
  rw [Finset.sum_add_distrib, P.total, Q.total] at h
  unfold tv
  linarith

/-- The exact zero-based form of a summand of W^2 in (4.1). -/
def stageWeight (α : ℝ) (H h : ℕ) : ℝ :=
  ((H-h+1 : ℕ) : ℝ)^2 * (α⁻¹)^(h+1)

theorem stageWeight_nonneg {α : ℝ} (hα : 0 < α) (H h : ℕ) :
    0 ≤ stageWeight α H h := by unfold stageWeight; positivity

theorem sum_stageWeight (α : ℝ) (H : ℕ) :
    (∑ h ∈ Finset.range H, stageWeight α H h) = Weights.Wsq α (H+1) := by
  unfold Weights.Wsq
  simp only [Nat.add_sub_cancel]
  apply Finset.sum_bij (fun h _ => h+1)
  · intro h hh
    simp only [Finset.mem_range] at hh
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · intro h hh j hj heq
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.1 hj
    refine ⟨j-1, Finset.mem_range.2 (by omega), by omega⟩
  · intro h hh
    have heq : H+1-(h+1)+1 = H-h+1 := by omega
    simp only [stageWeight, heq]

/-- The source C.7 Cauchy--Schwarz aggregation, with the actual W definition. -/
theorem high_count_aggregate {α Λ : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ)
    (K H : ℕ) (Y : ℕ → ℕ → ℝ) (hY : ∀ k h, 0 ≤ Y k h) :
    (∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
      4 * Real.sqrt (Λ * stageWeight α H h * Y k h)) ≤
      4 * Weights.W α (H+1) *
        Real.sqrt (Λ * (K : ℝ) * (∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, Y k h)) := by
  let I := (Finset.range K).product (Finset.range H)
  have hcs := sum_sqrt_product_le I (fun z : ℕ × ℕ => Λ * stageWeight α H z.2)
    (fun z => Y z.1 z.2) (fun z _ => mul_nonneg hΛ (stageWeight_nonneg hα H z.2))
    (fun z _ => hY z.1 z.2)
  have hfirst : (∑ z ∈ I, Λ * stageWeight α H z.2) =
      Λ * (K : ℝ) * Weights.Wsq α (H+1) := by
    dsimp [I]
    rw [Finset.sum_product]
    simp only [← Finset.mul_sum, sum_stageWeight, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    ring
  have hsecond : (∑ z ∈ I, Y z.1 z.2) =
      ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, Y k h := by
    dsimp [I]
    rw [Finset.sum_product]
  rw [hfirst, hsecond] at hcs
  have hleft : (∑ z ∈ I, Real.sqrt (Λ * stageWeight α H z.2 * Y z.1 z.2)) =
      ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
        Real.sqrt (Λ * stageWeight α H h * Y k h) := by
    dsimp [I]
    rw [Finset.sum_product]
  rw [hleft] at hcs
  have hroot : Real.sqrt ((Λ * (K : ℝ) * Weights.Wsq α (H+1)) *
      (∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, Y k h)) =
      Weights.W α (H+1) * Real.sqrt (Λ * (K : ℝ) *
        (∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, Y k h)) := by
    unfold Weights.W
    rw [← Real.sqrt_mul (Weights.Wsq_nonneg hα (H+1))]
    congr 1
    ring
  rw [hroot] at hcs
  have hm := mul_le_mul_of_nonneg_left hcs (by norm_num : (0 : ℝ) ≤ 4)
  simpa only [Finset.mul_sum, mul_assoc] using hm

/-- Occupancy-weighted high rows: Jensen, the local Hellinger radius, and
pointwise distorted/nominal domination suffice for the entire stage bound. -/
theorem high_stage_jensen [DecidableEq A] (d dn : Law S) (π : S → Law A)
    (P Q : S → A → Law S) (N : S → A → ℕ) (cutoff : ℕ)
    {κ Λ : ℝ} (hκ : 0 ≤ κ) (hΛ : 0 ≤ Λ)
    (hdom : ∀ s a, d.mass s * (π s).mass a ≤ κ * (dn.mass s * (π s).mass a))
    (hrow : ∀ s a, cutoff ≤ N s a → hellingerSq (P s a) (Q s a) ≤ 2 * Λ / N s a) :
    (∑ s, d.mass s * Real.sqrt (∑ a,
      if cutoff ≤ N s a then (π s).mass a * hellingerSq (P s a) (Q s a) else 0)) ≤
      Real.sqrt (2 * Λ * κ * (∑ s, ∑ a,
        if cutoff ≤ N s a then (dn.mass s * (π s).mass a) / N s a else 0)) := by
  have hX : ∀ s, 0 ≤ ∑ a,
      if cutoff ≤ N s a then (π s).mass a * hellingerSq (P s a) (Q s a) else 0 := by
    intro s
    apply Finset.sum_nonneg
    intro a _
    have hh := hellingerSq_nonneg (P s a) (Q s a)
    split_ifs
    · exact mul_nonneg ((π s).nonneg a) hh
    · exact le_rfl
  apply (law_sqrt_jensen d _ hX).trans
  apply Real.sqrt_le_sqrt
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro a _
  by_cases hi : cutoff ≤ N s a
  · simp only [if_pos hi]
    have hh := mul_le_mul (hdom s a) (hrow s a hi)
      (hellingerSq_nonneg (P s a) (Q s a))
      (mul_nonneg hκ (mul_nonneg (dn.nonneg s) ((π s).nonneg a)))
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hh
  · simp [hi]

/-- Low-count rows need only TV ≤ 1 and the proven occupancy domination. -/
theorem low_stage_domination (d dn : Law S) (π : S → Law A)
    (P Q : S → A → Law S) (N : S → A → ℕ) (cutoff : ℕ)
    {R α κ w : ℝ} (hR : 0 ≤ R) (hα : 0 < α) (hκ : 0 ≤ κ)
    (hcoef : R / α * κ ≤ w)
    (hdom : ∀ s a, d.mass s * (π s).mass a ≤ κ * (dn.mass s * (π s).mass a)) :
    (R / α) * (∑ s, d.mass s * ∑ a,
      if cutoff ≤ N s a then 0 else (π s).mass a * tv (P s a) (Q s a)) ≤
      w * (∑ s, ∑ a, if cutoff ≤ N s a then 0 else dn.mass s * (π s).mass a) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro a _
  by_cases hi : cutoff ≤ N s a
  · simp [hi]
  · simp only [if_neg hi]
    have htv := mul_le_mul_of_nonneg_left (tv_le_one (P s a) (Q s a))
      (mul_nonneg (d.nonneg s) ((π s).nonneg a))
    have hbase : (d.mass s * (π s).mass a) * tv (P s a) (Q s a) ≤
        κ * (dn.mass s * (π s).mass a) := by
      calc
        _ ≤ d.mass s * (π s).mass a := by simpa only [mul_one] using htv
        _ ≤ _ := hdom s a
    have hm := mul_le_mul_of_nonneg_left hbase (div_nonneg hR hα.le)
    have hc := mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg (dn.nonneg s) ((π s).nonneg a))
    calc
      _ = (R / α) * ((d.mass s * (π s).mass a) * tv (P s a) (Q s a)) := by ring
      _ ≤ (R / α) * (κ * (dn.mass s * (π s).mass a)) := hm
      _ = (R / α * κ) * (dn.mass s * (π s).mass a) := by ring
      _ ≤ _ := hc

/-- The zero-based low-count coefficient is a summand of the source maximum w. -/
theorem low_coefficient_le_w {α : ℝ} (hα : 0 < α) (H h : ℕ) (hh : h < H) :
    ((H-h : ℕ) : ℝ) / α * (α⁻¹)^h ≤ Weights.w α (H+1) := by
  have hm : h+1 ∈ insert 0 (Finset.Icc 1 ((H+1)-1)) := by
    apply Finset.mem_insert_of_mem
    simp only [Nat.add_sub_cancel]
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hs := Finset.le_sup' (Weights.lowTerm α (H+1)) hm
  have heq : H+1-(h+1) = H-h := by omega
  simpa only [Weights.w, Weights.lowTerm, Nat.add_eq_zero_iff, Nat.one_ne_zero,
    and_false, ↓reduceIte, heq, pow_succ, div_eq_mul_inv, mul_assoc, mul_comm,
    mul_left_comm] using hs

/-- The local coefficient and distorted occupancy exponent give exactly the
high-count square-root weight; no exponent is hidden in an asymptotic bound. -/
theorem high_coefficient_identity {α Λ Y : ℝ} (hα : 0 < α) (hΛ : 0 ≤ Λ)
    (hY : 0 ≤ Y) (H h : ℕ) :
    (2 * Real.sqrt 2 * (((H-h : ℕ) : ℝ)+1) / Real.sqrt α) *
      Real.sqrt (2 * Λ * (α⁻¹)^h * Y) =
      4 * Real.sqrt (Λ * stageWeight α H h * Y) := by
  have hleft : 0 ≤ (2 * Real.sqrt 2 * (((H-h : ℕ) : ℝ)+1) / Real.sqrt α) *
      Real.sqrt (2 * Λ * (α⁻¹)^h * Y) := by positivity
  have hright : 0 ≤ 4 * Real.sqrt (Λ * stageWeight α H h * Y) := by positivity
  apply (sq_eq_sq₀ hleft hright).1
  rw [mul_pow, div_pow, mul_pow, mul_pow,
    Real.sq_sqrt hα.le, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt (show 0 ≤ 2 * Λ * (α⁻¹)^h * Y by positivity), mul_pow,
    Real.sq_sqrt (mul_nonneg (mul_nonneg hΛ (stageWeight_nonneg hα H h)) hY)]
  unfold stageWeight
  push_cast
  rw [pow_succ]
  simp only [div_eq_mul_inv]
  ring

/-- Actual nominal state--action occupancy, with episode and stage indices. -/
def nominalMass (π : ℕ → Policy S A) (p : Kernel S A) (s₀ : S)
    (k h : ℕ) (x : S × A) : ℝ :=
  (occupancy (nominal (π k) p) (dirac s₀) h).mass x.1 * (π k h x.1).mass x.2

def nominalLow (π : ℕ → Policy S A) (p : Kernel S A) (s₀ : S)
    (N : ℕ → S × A → ℕ) (H k h : ℕ) : ℝ :=
  ∑ x, if N k x < H+1 then nominalMass π p s₀ k h x else 0

def nominalHigh (π : ℕ → Policy S A) (p : Kernel S A) (s₀ : S)
    (N : ℕ → S × A → ℕ) (H k h : ℕ) : ℝ :=
  ∑ x, if H+1 ≤ N k x then nominalMass π p s₀ k h x / N k x else 0

def Ylo (π : ℕ → Policy S A) (p : Kernel S A) (s₀ : S)
    (N : ℕ → S × A → ℕ) (K H : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, nominalLow π p s₀ N H k h

def Yhi (π : ℕ → Policy S A) (p : Kernel S A) (s₀ : S)
    (N : ℕ → S × A → ℕ) (K H : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, nominalHigh π p s₀ N H k h

lemma nominalMass_nonneg (π : ℕ → Policy S A) (p : Kernel S A) (s₀ : S)
    (k h : ℕ) (x : S × A) : 0 ≤ nominalMass π p s₀ k h x := by
  exact mul_nonneg ((occupancy (nominal (π k) p) (dirac s₀) h).nonneg x.1)
    ((π k h x.1).nonneg x.2)

lemma nominalHigh_nonneg (π : ℕ → Policy S A) (p : Kernel S A) (s₀ : S)
    (N : ℕ → S × A → ℕ) (H k h : ℕ) : 0 ≤ nominalHigh π p s₀ N H k h := by
  apply Finset.sum_nonneg
  intro x _
  have := nominalMass_nonneg π p s₀ k h x
  split_ifs <;> positivity

/-- A single stage of the actual local-error recursion, after applying the
hybrid CVaR inequality to the q-model risk continuation. -/
theorem actual_hybrid_stage (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : ℕ → Policy S A) (p : Kernel S A) (q : ℕ → Kernel S A)
    (s₀ : S) (N : ℕ → S × A → ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (H k h : ℕ) (hh : h < H)
    (hrow : ∀ s a, H+1 ≤ N k (s,a) →
      hellingerSq (p s a) (q k s a) ≤ 2 * Λ / N k (s,a)) :
    let d := occupancy (adverseKernel α hα hα1 c (π k) p (H+1)) (dirac s₀) h
    expect d.mass (epsilon α c (π k) p (q k) (H+1) h) ≤
      Weights.w α (H+1) * nominalLow π p s₀ N H k h +
      4 * Real.sqrt (Λ * stageWeight α H h * nominalHigh π p s₀ N H k h) := by
  classical
  let d := occupancy (adverseKernel α hα hα1 c (π k) p (H+1)) (dirac s₀) h
  let dn := occupancy (nominal (π k) p) (dirac s₀) h
  let R : ℝ := ((H-h : ℕ) : ℝ)
  let κ : ℝ := (α⁻¹)^h
  let X : S → ℝ := fun s => ∑ a, if H+1 ≤ N k (s,a) then
    (π k h s).mass a * hellingerSq (p s a) (q k s a) else 0
  let L : ℝ := (R / α) * (∑ s, d.mass s * ∑ a,
    if H+1 ≤ N k (s,a) then 0 else (π k h s).mass a * tv (p s a) (q k s a))
  let C : ℝ := 2 * Real.sqrt 2 * (R+1) / Real.sqrt α
  have hlocal : ∀ s, epsilon α c (π k) p (q k) (H+1) h s ≤
      (R / α) * (∑ a, if H+1 ≤ N k (s,a) then 0 else
        (π k h s).mass a * tv (p s a) (q k s a)) + C * Real.sqrt (X s) := by
    intro s
    have heq : H+1-(h+1) = H-h := by omega
    have hz := value_joint_hybrid (π k h s) (p s) (q k s) hα hα1
      (Nat.cast_nonneg (H-h) : (0 : ℝ) ≤ (H-h : ℕ))
      (c h s) (risk α c (π k) (q k) (H-h) (h+1))
      (fun a => (hc h s a).1) (fun a => (hc h s a).2)
      (fun t => (risk_bounds α hα hα1 c hc (π k) (q k) (H-h) (h+1) t).1)
      (fun t => (risk_bounds α hα hα1 c hc (π k) (q k) (H-h) (h+1) t).2)
      (Finset.univ.filter (fun a => H+1 ≤ N k (s,a)))
    simpa [epsilon, localError, heq, R, C, X] using hz
  have hsim := expect_mono d.nonneg hlocal
  have hsim' : expect d.mass (epsilon α c (π k) p (q k) (H+1) h) ≤
      L + C * (∑ s, d.mass s * Real.sqrt (X s)) := by
    convert hsim using 1 <;>
      simp only [expect, L, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
        mul_assoc, mul_left_comm, mul_comm]
  have hdom : ∀ s a, d.mass s * (π k h s).mass a ≤ κ * (dn.mass s * (π k h s).mass a) :=
    fun s a => distorted_action_domination α hα hα1 c (π k) p (H+1) h s₀ s a
  have hlow := low_stage_domination d dn (π k h) p (q k) (fun s a => N k (s,a)) (H+1)
    (R := R) (κ := κ) (Nat.cast_nonneg _) hα (by dsimp [κ]; positivity)
    (low_coefficient_le_w hα H h hh) hdom
  have hlo : L ≤ Weights.w α (H+1) * nominalLow π p s₀ N H k h := by
    convert hlow using 1
    unfold nominalLow nominalMass
    rw [Fintype.sum_prod_type]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro a _
    by_cases hi : H+1 ≤ N k (s,a)
    · simp [hi, Nat.not_lt.mpr hi]
    · simp [hi, Nat.lt_of_not_ge hi, dn]
  have hhigh := high_stage_jensen d dn (π k h) p (q k) (fun s a => N k (s,a)) (H+1)
    (κ := κ) (Λ := Λ) (by dsimp [κ]; positivity) hΛ hdom hrow
  have hhi : (∑ s, d.mass s * Real.sqrt (X s)) ≤
      Real.sqrt (2 * Λ * κ * nominalHigh π p s₀ N H k h) := by
    convert hhigh using 1
    unfold nominalHigh nominalMass
    rw [Fintype.sum_prod_type]
  have hC : 0 ≤ C := by dsimp [C, R]; positivity
  have hhi' := mul_le_mul_of_nonneg_left hhi hC
  have hid := high_coefficient_identity hα hΛ (nominalHigh_nonneg π p s₀ N H k h) H h
  change C * Real.sqrt (2 * Λ * κ * nominalHigh π p s₀ N H k h) = _ at hid
  dsimp only
  linarith

/-- Equations C.7/C.10 for the actual nested CVaR risk difference, with no
aggregate simulation inequality assumed as a premise. -/
theorem risk_hybrid_sum_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : ℕ → Policy S A) (p : Kernel S A) (q : ℕ → Kernel S A)
    (s₀ : S) (N : ℕ → S × A → ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (K H : ℕ) (hrow : ∀ k, k < K → ∀ s a, H+1 ≤ N k (s,a) →
      hellingerSq (p s a) (q k s a) ≤ 2 * Λ / N k (s,a)) :
    (∑ k ∈ Finset.range K,
      (risk α c (π k) p (H+1) 0 s₀ - risk α c (π k) (q k) (H+1) 0 s₀)) ≤
      Weights.w α (H+1) * Ylo π p s₀ N K H +
      4 * Weights.W α (H+1) * Real.sqrt (Λ * (K : ℝ) * Yhi π p s₀ N K H) := by
  have hsum : (∑ k ∈ Finset.range K,
      (risk α c (π k) p (H+1) 0 s₀ - risk α c (π k) (q k) (H+1) 0 s₀)) ≤
      ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
        (Weights.w α (H+1) * nominalLow π p s₀ N H k h +
         4 * Real.sqrt (Λ * stageWeight α H h * nominalHigh π p s₀ N H k h)) := by
    apply Finset.sum_le_sum
    intro k hk
    apply (distorted_simulation α hα hα1 c (π k) p (q k) H s₀).trans
    apply Finset.sum_le_sum
    intro h hh
    exact actual_hybrid_stage α hα hα1 c hc π p q s₀ N hΛ H k h
      (Finset.mem_range.1 hh) (hrow k (Finset.mem_range.1 hk))
  have hhigh := high_count_aggregate hα hΛ K H (nominalHigh π p s₀ N H)
    (nominalHigh_nonneg π p s₀ N H)
  simp only [Finset.sum_add_distrib] at hsum
  have hloweq : (∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
      Weights.w α (H+1) * nominalLow π p s₀ N H k h) =
      Weights.w α (H+1) * Ylo π p s₀ N K H := by
    simp only [Ylo, Finset.mul_sum]
  rw [hloweq] at hsum
  change _ ≤ 4 * Weights.W α (H+1) * Real.sqrt (Λ * (K : ℝ) * Yhi π p s₀ N K H) at hhigh
  linarith

/-- Generic C.7 aggregation: homogeneous and stage-dependent tail weights use
this same lemma, differing only in the numerical stage weight. -/
theorem high_count_aggregate_generic {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (K H : ℕ) (a : ℕ → ℝ) (ha : ∀ h, 0 ≤ a h)
    (Y : ℕ → ℕ → ℝ) (hY : ∀ k h, 0 ≤ Y k h) :
    (∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, 4 * Real.sqrt (Λ * a h * Y k h)) ≤
      4 * Real.sqrt (∑ h ∈ Finset.range H, a h) *
        Real.sqrt (Λ * (K : ℝ) * (∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, Y k h)) := by
  let I := (Finset.range K).product (Finset.range H)
  have hcs := sum_sqrt_product_le I (fun z : ℕ × ℕ => Λ * a z.2)
    (fun z => Y z.1 z.2) (fun z _ => mul_nonneg hΛ (ha z.2)) (fun z _ => hY z.1 z.2)
  have hfirst : (∑ z ∈ I, Λ * a z.2) = Λ * (K : ℝ) * (∑ h ∈ Finset.range H, a h) := by
    dsimp [I]
    rw [Finset.sum_product]
    simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hsecond : (∑ z ∈ I, Y z.1 z.2) =
      ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, Y k h := by
    dsimp [I]
    rw [Finset.sum_product]
  have hleft : (∑ z ∈ I, Real.sqrt (Λ * a z.2 * Y z.1 z.2)) =
      ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, Real.sqrt (Λ * a h * Y k h) := by
    dsimp [I]
    rw [Finset.sum_product]
  rw [hfirst, hsecond, hleft] at hcs
  have heq : Real.sqrt ((Λ * (K : ℝ) * (∑ h ∈ Finset.range H, a h)) *
      (∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, Y k h)) =
      Real.sqrt (∑ h ∈ Finset.range H, a h) *
        Real.sqrt (Λ * (K : ℝ) * (∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, Y k h)) := by
    rw [← Real.sqrt_mul (Finset.sum_nonneg (fun h _ => ha h))]
    congr 1
    ring
  rw [heq] at hcs
  have hm := mul_le_mul_of_nonneg_left hcs (by norm_num : (0 : ℝ) ≤ 4)
  simpa only [Finset.mul_sum, mul_assoc] using hm

/-- A generic coefficient identity that also applies when the tail mass varies
by stage: C^2 times the preceding density cap equals 8 times the stage weight. -/
theorem high_term_from_square {C κ a Λ Y : ℝ} (hC : 0 ≤ C) (hκ : 0 ≤ κ)
    (ha : 0 ≤ a) (hΛ : 0 ≤ Λ) (hY : 0 ≤ Y) (hcoef : C^2 * κ = 8*a) :
    C * Real.sqrt (2 * Λ * κ * Y) = 4 * Real.sqrt (Λ * a * Y) := by
  apply (sq_eq_sq₀ (mul_nonneg hC (Real.sqrt_nonneg _)) (by positivity)).1
  rw [mul_pow, Real.sq_sqrt (show 0 ≤ 2 * Λ * κ * Y by positivity), mul_pow,
    Real.sq_sqrt (show 0 ≤ Λ * a * Y by positivity)]
  calc
    _ = 2 * Λ * Y * (C^2 * κ) := by ring
    _ = _ := by rw [hcoef]; ring

/-- At mass one the envelope risk is the ordinary expectation. The proof uses
all coordinates of the probability law, including any zero-mass coordinates. -/
theorem value_one_expectation {ι : Type*} [Fintype ι] (P : Law ι) (X : ι → ℝ) :
    value P 1 X = expect P.mass X := by
  obtain ⟨w, hw, hv⟩ := exists_optimizer P (α := 1) (by norm_num) le_rfl X
  have hn : ∀ i ∈ Finset.univ, 0 ≤ P.mass i - w i := by
    intro i _
    have hi := hw.2.1 i
    simp only [div_one] at hi
    linarith
  have hs : (∑ i, (P.mass i-w i)) = 0 := by
    rw [Finset.sum_sub_distrib, P.total, hw.2.2]
    ring
  have heq : w = P.mass := by
    funext i
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hn).1 hs i (Finset.mem_univ i)
    linarith
  rw [hv, heq]

/-- Ordinary expected reward for the same physical-state Markov policy. Its
Bellman recursion below identifies this alpha=1 definition with (2.1). -/
def ordinaryReward (r : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A)
    (n h : ℕ) (s : S) : ℝ := risk 1 r π p n h s

theorem ordinaryReward_bellman (r : ℕ → S → A → ℝ) (π : Policy S A)
    (p : Kernel S A) (n h : ℕ) (s : S) :
    ordinaryReward r π p (n+1) h s =
      ∑ a, (π h s).mass a * (r h s a + ∑ t, (p s a).mass t * ordinaryReward r π p n (h+1) t) := by
  unfold ordinaryReward
  rw [risk, value_one_expectation, expect_joint]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  simp only [expect, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    (p s a).total, one_mul]

/-- Complementing [0,1] rewards turns the signed q-minus-p reward difference
into the p-minus-q cost difference used by the existing nominal simulation. -/
theorem risk_one_complement (r : ℕ → S → A → ℝ) (π : Policy S A) (p : Kernel S A)
    (n h : ℕ) (s : S) :
    risk 1 (fun h s a => 1-r h s a) π p n h s = (n : ℝ) - risk 1 r π p n h s := by
  induction n generalizing h s with
  | zero => simp [risk]
  | succ n ih =>
    simp only [risk, value_one_expectation]
    have heq : (fun x : A × S => (1-r h s x.1) +
        risk 1 (fun h s a => 1-r h s a) π p n (h+1) x.2) =
        (fun x => ((n+1 : ℕ) : ℝ) - (r h s x.1 + risk 1 r π p n (h+1) x.2)) := by
      funext x
      rw [ih]
      push_cast
      ring
    rw [heq]
    simp only [expect, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      (joint (π h s) (p s)).total, one_mul]

/-- The actual C.13 ordinary-reward simulation, derived from the already proved
CVaR simulation at alpha=1 and the expectation/complement identities. -/
theorem reward_nominal_simulation (r : ℕ → S → A → ℝ)
    (hr : ∀ h s a, 0 ≤ r h s a ∧ r h s a ≤ 1)
    (π : Policy S A) (p q : Kernel S A) (H : ℕ) (s₀ : S) :
    ordinaryReward r π q (H+1) 0 s₀ - ordinaryReward r π p (H+1) 0 s₀ ≤
      ∑ h ∈ Finset.range H, ((H-h : ℕ) : ℝ) * ∑ s,
        (occupancy (nominal π p) (dirac s₀) h).mass s *
          ∑ a, (π h s).mass a * tv (p s a) (q s a) := by
  have hc : ∀ h s a, 0 ≤ 1-r h s a ∧ 1-r h s a ≤ 1 := by
    intro h s a
    constructor <;> linarith [(hr h s a).1, (hr h s a).2]
  have hs := nominal_simulation 1 (by norm_num) le_rfl (fun h s a => 1-r h s a)
    hc π p q H s₀
  rw [risk_one_complement, risk_one_complement] at hs
  convert hs using 1 <;> simp [ordinaryReward] <;> ring

/-- Predictable square-root charge for the reward analysis, with the same
full-episode frozen denominator as the logarithmic risk charge. -/
def Ysqrt (π : ℕ → Policy S A) (p : Kernel S A) (s₀ : S)
    (N : ℕ → S × A → ℕ) (K H : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H, ∑ x,
    if H+1 ≤ N k x then nominalMass π p s₀ k h x / Real.sqrt (N k x) else 0

/-- The reward local-model error charge before converting nominal occupancy
into realized visit counts. Only rowwise TV confidence radii are premises. -/
theorem reward_charging_bound (r : ℕ → S → A → ℝ)
    (hr : ∀ h s a, 0 ≤ r h s a ∧ r h s a ≤ 1)
    (π : ℕ → Policy S A) (p : Kernel S A) (q : ℕ → Kernel S A)
    (s₀ : S) (N : ℕ → S × A → ℕ) {L : ℝ} (hL : 0 ≤ L)
    (K H : ℕ) (hrow : ∀ k, k < K → ∀ s a, H+1 ≤ N k (s,a) →
      tv (p s a) (q k s a) ≤ Real.sqrt (2*L / N k (s,a))) :
    (∑ k ∈ Finset.range K,
      (ordinaryReward r (π k) (q k) (H+1) 0 s₀ - ordinaryReward r (π k) p (H+1) 0 s₀)) ≤
      ((H+1 : ℕ) : ℝ) * Ylo π p s₀ N K H +
      ((H+1 : ℕ) : ℝ) * Real.sqrt (2*L) * Ysqrt π p s₀ N K H := by
  have hstep : ∀ k, k < K → ∀ h, h < H →
      ((H-h : ℕ) : ℝ) * (∑ s,
        (occupancy (nominal (π k) p) (dirac s₀) h).mass s *
          ∑ a, (π k h s).mass a * tv (p s a) (q k s a)) ≤
      ((H+1 : ℕ) : ℝ) * nominalLow π p s₀ N H k h +
      ((H+1 : ℕ) : ℝ) * Real.sqrt (2*L) *
        (∑ x, if H+1 ≤ N k x then nominalMass π p s₀ k h x / Real.sqrt (N k x) else 0) := by
    intro k hk h hh
    have hR : ((H-h : ℕ) : ℝ) ≤ ((H+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : H-h ≤ H+1)
    unfold nominalLow nominalMass
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro s _
    apply Finset.sum_le_sum
    intro a _
    let m := (occupancy (nominal (π k) p) (dirac s₀) h).mass s * (π k h s).mass a
    have hm : 0 ≤ m := mul_nonneg
      ((occupancy (nominal (π k) p) (dirac s₀) h).nonneg s) ((π k h s).nonneg a)
    by_cases hi : H+1 ≤ N k (s,a)
    · have hnlo : ¬ N k (s,a) < H+1 := Nat.not_lt.mpr hi
      simp only [if_pos hi, if_neg hnlo, mul_zero, zero_add]
      have hv := hrow k hk s a hi
      rw [Real.sqrt_div (show 0 ≤ 2*L by positivity)] at hv
      have htv : ((H-h : ℕ) : ℝ) * tv (p s a) (q k s a) ≤
          ((H+1 : ℕ) : ℝ) * (Real.sqrt (2*L) / Real.sqrt (N k (s,a))) :=
        mul_le_mul hR hv (tv_nonneg _ _) (by positivity)
      have hmul := mul_le_mul_of_nonneg_right htv hm
      simpa only [m, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul
    · have hlo : N k (s,a) < H+1 := Nat.lt_of_not_ge hi
      simp only [if_neg hi, if_pos hlo, div_zero, mul_zero, add_zero]
      have htv : ((H-h : ℕ) : ℝ) * tv (p s a) (q k s a) ≤ ((H+1 : ℕ) : ℝ) := by
        have hh := mul_le_mul hR (tv_le_one (p s a) (q k s a)) (tv_nonneg _ _) (by positivity)
        simpa only [mul_one] using hh
      have hm' := mul_le_mul_of_nonneg_right htv hm
      simpa only [m, mul_assoc, mul_comm, mul_left_comm] using hm'
  have hs : (∑ k ∈ Finset.range K,
      (ordinaryReward r (π k) (q k) (H+1) 0 s₀ - ordinaryReward r (π k) p (H+1) 0 s₀)) ≤
      ∑ k ∈ Finset.range K, ∑ h ∈ Finset.range H,
        (((H+1 : ℕ) : ℝ) * nominalLow π p s₀ N H k h +
         ((H+1 : ℕ) : ℝ) * Real.sqrt (2*L) *
          (∑ x, if H+1 ≤ N k x then nominalMass π p s₀ k h x / Real.sqrt (N k x) else 0)) := by
    apply Finset.sum_le_sum
    intro k hk
    apply (reward_nominal_simulation r hr (π k) p (q k) H s₀).trans
    exact Finset.sum_le_sum fun h hh => hstep k (Finset.mem_range.1 hk) h (Finset.mem_range.1 hh)
  simpa only [Ylo, Ysqrt, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc] using hs

/-- Episodewise masking keeps the expected proof's global true-prefix failure
and sampled-kernel failures separate. Bad episodes use q'=p, so their actual
model discrepancy vanishes; the nominal occupancy charges are unchanged. -/
theorem masked_risk_hybrid_sum_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : ℕ → Policy S A) (p : Kernel S A) (q : ℕ → Kernel S A)
    (s₀ : S) (N : ℕ → S × A → ℕ) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (K H : ℕ) (good : ℕ → Prop) [DecidablePred good]
    (hrow : ∀ k, k < K → good k → ∀ s a, H+1 ≤ N k (s,a) →
      hellingerSq (p s a) (q k s a) ≤ 2 * Λ / N k (s,a)) :
    (∑ k ∈ Finset.range K, if good k then
      (risk α c (π k) p (H+1) 0 s₀ - risk α c (π k) (q k) (H+1) 0 s₀) else 0) ≤
      Weights.w α (H+1) * Ylo π p s₀ N K H +
      4 * Weights.W α (H+1) * Real.sqrt (Λ * (K : ℝ) * Yhi π p s₀ N K H) := by
  classical
  let q' : ℕ → Kernel S A := fun k => if good k then q k else p
  have hrow' : ∀ k, k < K → ∀ s a, H+1 ≤ N k (s,a) →
      hellingerSq (p s a) (q' k s a) ≤ 2 * Λ / N k (s,a) := by
    intro k hk s a hn
    by_cases hg : good k
    · simpa [q', hg] using hrow k hk hg s a hn
    · simp only [q', if_neg hg, hellingerSq_self]
      positivity
  have hs := risk_hybrid_sum_bound α hα hα1 c hc π p q' s₀ N hΛ K H hrow'
  convert hs using 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hg : good k <;> simp [q', hg]

/-- The same episodewise masking for ordinary reward's TV confidence events. -/
theorem masked_reward_charging_bound (r : ℕ → S → A → ℝ)
    (hr : ∀ h s a, 0 ≤ r h s a ∧ r h s a ≤ 1)
    (π : ℕ → Policy S A) (p : Kernel S A) (q : ℕ → Kernel S A)
    (s₀ : S) (N : ℕ → S × A → ℕ) {L : ℝ} (hL : 0 ≤ L)
    (K H : ℕ) (good : ℕ → Prop) [DecidablePred good]
    (hrow : ∀ k, k < K → good k → ∀ s a, H+1 ≤ N k (s,a) →
      tv (p s a) (q k s a) ≤ Real.sqrt (2*L / N k (s,a))) :
    (∑ k ∈ Finset.range K, if good k then
      (ordinaryReward r (π k) (q k) (H+1) 0 s₀ - ordinaryReward r (π k) p (H+1) 0 s₀) else 0) ≤
      ((H+1 : ℕ) : ℝ) * Ylo π p s₀ N K H +
      ((H+1 : ℕ) : ℝ) * Real.sqrt (2*L) * Ysqrt π p s₀ N K H := by
  classical
  let q' : ℕ → Kernel S A := fun k => if good k then q k else p
  have hrow' : ∀ k, k < K → ∀ s a, H+1 ≤ N k (s,a) →
      tv (p s a) (q' k s a) ≤ Real.sqrt (2*L / N k (s,a)) := by
    intro k hk s a hn
    by_cases hg : good k
    · simpa [q', hg] using hrow k hk hg s a hn
    · simp only [q', if_neg hg, tv_self]
      exact Real.sqrt_nonneg _
  have hs := reward_charging_bound r hr π p q' s₀ N hL K H hrow'
  convert hs using 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hg : good k <;> simp [q', hg]

/-- The source's numerical constant 8 absorbs the low-count term in the
large-K case; small K uses the deterministic H K bound. -/
theorem reward_numerical_envelope {m H K L : ℝ} (hm : 0 ≤ m) (hH : 0 ≤ H)
    (hK : 0 ≤ K) (hL : 1 ≤ L) :
    min (H*K) (2*m*H^2 + 3*Real.sqrt 2*(H*Real.sqrt H*Real.sqrt (m*K*L))) ≤
      8*(H*Real.sqrt H*Real.sqrt (m*K*L)) := by
  let B := H*Real.sqrt H*Real.sqrt (m*K*L)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hroot : Real.sqrt H * Real.sqrt (m*K*L) = Real.sqrt (H*(m*K*L)) :=
    (Real.sqrt_mul hH _).symm
  by_cases hsmall : K ≤ m*H
  · have hsq : K^2 ≤ H*(m*K*L) := by
      have h1 := mul_le_mul_of_nonneg_right hsmall hK
      have h2 := mul_le_mul_of_nonneg_left hL (show 0 ≤ m*H*K by positivity)
      nlinarith
    have hkroot := Real.le_sqrt_of_sq_le hsq
    have hbound : H*K ≤ B := by
      dsimp [B]
      rw [mul_assoc H, hroot]
      exact mul_le_mul_of_nonneg_left hkroot hH
    exact (min_le_left _ _).trans (hbound.trans (by change B ≤ 8*B; nlinarith))
  · have hlarge : m*H ≤ K := le_of_lt (lt_of_not_ge hsmall)
    have hsq : (m*H)^2 ≤ H*(m*K*L) := by
      have h1 := mul_le_mul_of_nonneg_left hlarge (show 0 ≤ m*H by positivity)
      have h2 := mul_le_mul_of_nonneg_left hL (show 0 ≤ m*H*K by positivity)
      nlinarith
    have hmroot := Real.le_sqrt_of_sq_le hsq
    have hlow : m*H^2 ≤ B := by
      dsimp [B]
      rw [mul_assoc H, hroot]
      have hh := mul_le_mul_of_nonneg_left hmroot hH
      nlinarith
    have hs2 : Real.sqrt (2 : ℝ) ≤ 2 := by
      apply Real.sqrt_le_iff.2
      norm_num
    have hhigh := mul_le_mul_of_nonneg_right hs2 hB
    apply (min_le_right _ _).trans
    change 2*m*H^2 + 3*Real.sqrt 2*B ≤ 8*B
    nlinarith

section Expected
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- Integrability of sqrt is derived from that of the nonnegative variable. -/
theorem integrable_sqrt_of_nonneg {Y : Ω → ℝ} (hY : Integrable Y μ)
    (hY0 : ∀ᵐ ω ∂μ, 0 ≤ Y ω) : Integrable (fun ω => Real.sqrt (Y ω)) μ := by
  apply (hY.add (integrable_const (1 : ℝ))).mono'
    (Real.continuous_sqrt.comp_aestronglyMeasurable hY.aestronglyMeasurable)
  filter_upwards [hY0] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  change Real.sqrt (Y ω) ≤ Y ω + 1
  have hs := Real.sq_sqrt hω
  nlinarith [sq_nonneg (Real.sqrt (Y ω)-1), Real.sqrt_nonneg (Y ω)]

/-- The expectation Jensen step used after C.7, on an arbitrary probability
space. It is proved from the nonnegative squared deviation, not assumed. -/
theorem expected_sqrt_le_sqrt_expected {Y : Ω → ℝ} (hY : Integrable Y μ)
    (hY0 : ∀ᵐ ω ∂μ, 0 ≤ Y ω) :
    (∫ ω, Real.sqrt (Y ω) ∂μ) ≤ Real.sqrt (∫ ω, Y ω ∂μ) := by
  have hs := integrable_sqrt_of_nonneg μ hY hY0
  let a := ∫ ω, Real.sqrt (Y ω) ∂μ
  have hpos : 0 ≤ ∫ ω, (Y ω - (2*a) * Real.sqrt (Y ω) + a^2) ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hY0] with ω hω
    change 0 ≤ Y ω - (2*a) * Real.sqrt (Y ω) + a^2
    nlinarith [sq_nonneg (Real.sqrt (Y ω)-a), Real.sq_sqrt hω]
  have hadd := integral_add (hY.sub (hs.const_mul (2*a))) (integrable_const (a^2))
  simp only [Pi.sub_apply] at hadd
  rw [hadd] at hpos
  have hsub := integral_sub hY (hs.const_mul (2*a))
  simp only [Pi.sub_apply] at hsub
  rw [hsub, integral_const_mul, integral_const] at hpos
  simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul] at hpos
  apply Real.le_sqrt_of_sq_le
  change a^2 ≤ _
  change 0 ≤ (∫ ω, Y ω ∂μ) - (2*a)*a + a^2 at hpos
  nlinarith

/-- Expected charging after a proved pointwise decomposition. This lemma is
pure integration; the actual risk decomposition is risk_hybrid_sum_bound. -/
theorem expected_charging_bound {F L Y : Ω → ℝ} {w W Λ : ℝ}
    (hF : Integrable F μ) (hL : Integrable L μ) (hY : Integrable Y μ)
    (hY0 : ∀ᵐ ω ∂μ, 0 ≤ Y ω) (hW : 0 ≤ W) (hΛ : 0 ≤ Λ) (K : ℕ)
    (hpath : ∀ᵐ ω ∂μ, F ω ≤ w * L ω + 4 * W * Real.sqrt (Λ * (K : ℝ) * Y ω)) :
    (∫ ω, F ω ∂μ) ≤ w * (∫ ω, L ω ∂μ) +
      4 * W * Real.sqrt (Λ * (K : ℝ) * (∫ ω, Y ω ∂μ)) := by
  have hZ : Integrable (fun ω => Λ * (K : ℝ) * Y ω) μ := hY.const_mul _
  have hZ0 : ∀ᵐ ω ∂μ, 0 ≤ Λ * (K : ℝ) * Y ω := by
    filter_upwards [hY0] with ω hω
    positivity
  have hs := integrable_sqrt_of_nonneg μ hZ hZ0
  have hi := integral_mono_ae hF ((hL.const_mul w).add (hs.const_mul (4*W))) hpath
  simp only [Pi.add_apply] at hi
  rw [integral_add (hL.const_mul w) (hs.const_mul (4*W)), integral_const_mul,
    integral_const_mul] at hi
  have hj := expected_sqrt_le_sqrt_expected μ hZ hZ0
  rw [integral_const_mul] at hj
  have hh := mul_le_mul_of_nonneg_left hj (show 0 ≤ 4*W by positivity)
  linarith

end Expected

end
end Paper36.HybridCharging
