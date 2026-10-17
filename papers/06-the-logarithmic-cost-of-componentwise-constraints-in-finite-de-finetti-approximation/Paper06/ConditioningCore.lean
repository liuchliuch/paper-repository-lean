import Paper06.Conditioning
import Paper06.Divergence
import Mathlib.Tactic

open Real BigOperators
open scoped Classical

namespace Paper06
namespace ConditioningFull

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- Finite pushforward, used for all block marginals. -/
noncomputable def push (P : FinProb α) (f : α → β) : FinProb β where
  w b := ∑ a, if f a = b then P.w a else 0
  nonneg b := Finset.sum_nonneg (fun a _ => by split_ifs; exact P.nonneg a; rfl)
  sum_eq_one := by
    rw [Finset.sum_comm]
    simpa using P.sum_eq_one

@[simp] theorem push_w (P : FinProb α) (f : α → β) (b : β) :
    (push P f).w b = ∑ a, if f a = b then P.w a else 0 := rfl

/-- Change of variables for finite pushforwards. -/
theorem push_sum (P : FinProb α) (f : α → β) (g : β → ℝ) :
    ∑ b, (push P f).w b * g b = ∑ a, P.w a * g (f a) := by
  simp only [push_w, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

@[simp] theorem push_id (P : FinProb α) : push P id = P := by
  apply FinProb.ext
  intro a
  simp [push_w]

@[simp] theorem push_comp (P : FinProb α) (f : α → β) (g : β → γ) :
    push (push P f) g = push P (g ∘ f) := by
  apply FinProb.ext
  intro c
  change (∑ b, if g b = c then (push P f).w b else 0) = _
  have h := push_sum P f (fun b => if g b = c then 1 else 0)
  simpa [Function.comp_def, mul_ite] using h

theorem w_le_one (P : FinProb α) (a : α) : P.w a ≤ 1 := by
  calc P.w a ≤ ∑ b, P.w b := Finset.single_le_sum (fun b _ => P.nonneg b) (Finset.mem_univ a)
    _ = 1 := P.sum_eq_one

/-- Shannon entropy is nonnegative, including at zero masses. -/
theorem entropy_nonneg (P : FinProb α) : 0 ≤ FinProb.entropy P := by
  unfold FinProb.entropy
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro a _
  by_cases ha : P.w a = 0
  · simp [ha]
  · exact mul_nonpos_of_nonneg_of_nonpos (P.nonneg a)
      (Real.log_nonpos (P.nonneg a) (w_le_one P a))

/-- A positive source atom has positive mass under every pushforward. -/
theorem push_pos (P : FinProb α) (f : α → β) (a : α) (ha : 0 < P.w a) :
    0 < (push P f).w (f a) := by
  apply lt_of_lt_of_le ha
  change P.w a ≤ ∑ b, if f b = f a then P.w b else 0
  simpa using (Finset.single_le_sum (f := fun b => if f b = f a then P.w b else 0)
    (fun b _ => by dsimp; split_ifs; exact P.nonneg b; rfl) (Finset.mem_univ a))

/-- Entropy cannot increase under a deterministic observation. -/
theorem entropy_push_le (P : FinProb α) (f : α → β) :
    FinProb.entropy (push P f) ≤ FinProb.entropy P := by
  unfold FinProb.entropy
  rw [push_sum]
  apply neg_le_neg
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : P.w a = 0
  · simp [ha]
  · have hpa : 0 < P.w a := lt_of_le_of_ne (P.nonneg a) (Ne.symm ha)
    have hle : P.w a ≤ (push P f).w (f a) := by
      change P.w a ≤ ∑ b, if f b = f a then P.w b else 0
      simpa using (Finset.single_le_sum (f := fun b => if f b = f a then P.w b else 0)
        (fun b _ => by dsimp; split_ifs; exact P.nonneg b; rfl) (Finset.mem_univ a))
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hpa hle) (P.nonneg a)

/-- Uniform law on a nonempty finite alphabet. -/
noncomputable def uniform [Nonempty α] : FinProb α where
  w _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_eq_one := by
    simp [Fintype.card_ne_zero]

/-- The exact finite-alphabet entropy ceiling. -/
theorem entropy_le_log_card (P : FinProb α) :
    FinProb.entropy P ≤ Real.log (Fintype.card α) := by
  have hcard : 0 < Fintype.card α := by
    by_contra h
    have he : IsEmpty α := Fintype.card_eq_zero_iff.mp (by omega)
    letI := he
    have := P.sum_eq_one
    simp at this
  haveI : Nonempty α := Fintype.card_pos_iff.mp hcard
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast hcard
  have hg := FinProb.klPos_nonneg (p := P) (q := uniform)
    (fun _ => inv_pos.mpr hc)
  have heq : FinProb.klPos P uniform = Real.log (Fintype.card α) - FinProb.entropy P := by
    unfold FinProb.klPos FinProb.entropy
    have hterm : ∀ a, P.w a * log (P.w a / (uniform (α := α)).w a) =
        P.w a * log (P.w a) + P.w a * log (Fintype.card α) := by
      intro a
      by_cases ha : P.w a = 0
      · simp [ha]
      · change P.w a * log (P.w a / (Fintype.card α : ℝ)⁻¹) = _
        rw [div_inv_eq_mul, log_mul ha (ne_of_gt hc)]
        ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, P.sum_eq_one]
    ring
  linarith

/-- Entropy is preserved by a recoverable observation. -/
theorem entropy_push_eq (P : FinProb α) (f : α → β) (g : β → α)
    (h : ∀ a, g (f a) = a) : FinProb.entropy (push P f) = FinProb.entropy P := by
  apply le_antisymm (entropy_push_le P f)
  have he : push (push P f) g = P := by
    rw [push_comp]
    have hf : g ∘ f = id := funext h
    rw [hf, push_id]
  simpa [he] using entropy_push_le (push P f) g

/-- Conditional law at a positive-probability observation. -/
noncomputable def cond (P : FinProb (α × β)) (b : β) (hb : 0 < (margR P).w b) :
    FinProb α where
  w a := P.w (a, b) / (margR P).w b
  nonneg a := div_nonneg (P.nonneg _) ((margR P).nonneg b)
  sum_eq_one := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hb)

/-- The joint atom is bounded by its observed marginal atom. -/
theorem joint_le_margR (P : FinProb (α × β)) (a : α) (b : β) :
    P.w (a, b) ≤ (margR P).w b := by
  exact Finset.single_le_sum (f := fun a => P.w (a, b)) (fun a _ => P.nonneg _) (Finset.mem_univ a)

/-- A zero-probability observation contains no positive joint atom. -/
theorem joint_eq_zero_of_margR (P : FinProb (α × β)) (a : α) (b : β)
    (hb : (margR P).w b = 0) : P.w (a, b) = 0 := by
  exact le_antisymm (hb ▸ joint_le_margR P a b) (P.nonneg _)

/-- Conditional entropy from the raw finite mass formula. -/
noncomputable def condEntropy (P : FinProb (α × β)) : ℝ :=
  -∑ z, P.w z * log (P.w z / (margR P).w z.2)

/-- Shannon's chain rule, with all zero-probability cases handled explicitly. -/
theorem condEntropy_eq (P : FinProb (α × β)) :
    condEntropy P = FinProb.entropy P - FinProb.entropy (margR P) := by
  have hterm : ∀ z : α × β, P.w z * log (P.w z / (margR P).w z.2) =
      P.w z * log (P.w z) - P.w z * log ((margR P).w z.2) := by
    intro z
    by_cases hz : P.w z = 0
    · simp [hz]
    · have hp : 0 < P.w z := lt_of_le_of_ne (P.nonneg _) (Ne.symm hz)
      have hm : 0 < (margR P).w z.2 := hp.trans_le (joint_le_margR P _ _)
      rw [log_div hz (ne_of_gt hm)]
      ring
  unfold condEntropy FinProb.entropy
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  have hm : (∑ z : α × β, P.w z * log ((margR P).w z.2)) =
      ∑ b, (margR P).w b * log ((margR P).w b) := by
    rw [Fintype.sum_prod_type_right' (fun a b => P.w (a, b) * log ((margR P).w b))]
    apply Finset.sum_congr rfl
    intro b _
    exact (Finset.sum_mul _ _ _).symm
  rw [hm]
  ring

/-- Conditional entropy is nonnegative on finite alphabets. -/
theorem condEntropy_nonneg (P : FinProb (α × β)) : 0 ≤ condEntropy P := by
  unfold condEntropy
  apply neg_nonneg.mpr
  apply Finset.sum_nonpos
  intro z _
  by_cases hz : P.w z = 0
  · simp [hz]
  · have hp : 0 < P.w z := lt_of_le_of_ne (P.nonneg _) (Ne.symm hz)
    have hm : 0 < (margR P).w z.2 := hp.trans_le (joint_le_margR P _ _)
    exact mul_nonpos_of_nonneg_of_nonpos (P.nonneg _)
      (Real.log_nonpos (le_of_lt (div_pos hp hm)) ((div_le_one hm).mpr (joint_le_margR P _ _)))

/-- A version of a conditional law defined even on null observations. -/
noncomputable def conditional [Nonempty α] (P : FinProb (α × β)) (b : β) : FinProb α :=
  if hb : 0 < (margR P).w b then cond P b hb else uniform

@[simp] theorem conditional_w [Nonempty α] (P : FinProb (α × β)) (b : β)
    (hb : 0 < (margR P).w b) (a : α) :
    (conditional P b).w a = P.w (a, b) / (margR P).w b := by
  simp [conditional, hb, cond]

/-- Conditional entropy is the probability weighted entropy of the posterior laws. -/
theorem condEntropy_expect [Nonempty α] (P : FinProb (α × β)) :
    condEntropy P = ∑ b, (margR P).w b * FinProb.entropy (conditional P b) := by
  unfold condEntropy
  rw [Fintype.sum_prod_type_right' (fun a b => P.w (a, b) * log (P.w (a, b) / (margR P).w b))]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : 0 < (margR P).w b
  · unfold FinProb.entropy
    rw [mul_neg, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    rw [conditional_w P b hb]
    field_simp
  · have hz : (margR P).w b = 0 := le_antisymm (le_of_not_gt hb) ((margR P).nonneg _)
    simp [hz, joint_eq_zero_of_margR P _ _ hz]

theorem margR_eq_push (P : FinProb (α × β)) : margR P = push P Prod.snd := by
  apply FinProb.ext
  intro b
  simp [push_w, margR, Fintype.sum_prod_type]

theorem margL_eq_push (P : FinProb (α × β)) : margL P = push P Prod.fst := by
  apply FinProb.ext
  intro a
  simp only [push_w, margL, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

/-- Mapping the unobserved variable commutes with taking its positive posterior. -/
theorem conditional_push [Nonempty α] [Nonempty γ]
    (P : FinProb (α × β)) (f : α → γ) (b : β) (hb : 0 < (margR P).w b) :
    conditional (push P (fun z => (f z.1, z.2))) b = push (conditional P b) f := by
  have hm : margR (push P (fun z => (f z.1, z.2))) = margR P := by
    simp only [margR_eq_push, push_comp]
    rfl
  have hmb : 0 < (margR (push P (fun z => (f z.1, z.2)))).w b := by rwa [hm]
  have hraw : ∀ c, (push P (fun z => (f z.1, z.2))).w (c, b) =
      ∑ a, if f a = c then P.w (a, b) else 0 := by
    intro c
    simp only [push_w, Fintype.sum_prod_type, Prod.mk.injEq]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : f a = c <;> simp [ha]
  apply FinProb.ext
  intro c
  rw [conditional_w _ b hmb, hm, hraw, push_w]
  simp_rw [conditional_w P b hb]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

/-- The unconditional product divergence equals total correlation. -/
theorem klPos_product_eq {k : ℕ} (P : FinProb (Fin k → α)) (q : FinProb α)
    (hq : ∀ i : Fin k, push P (fun z => z i) = q) :
    FinProb.klPos P (productFinProb k q) = (k : ℝ) * FinProb.entropy q - FinProb.entropy P := by
  have hterm : ∀ z, P.w z * log (P.w z / (productFinProb k q).w z) =
      P.w z * log (P.w z) - ∑ i : Fin k, P.w z * log (q.w (z i)) := by
    intro z
    by_cases hz : P.w z = 0
    · simp [hz]
    · have hp : 0 < P.w z := lt_of_le_of_ne (P.nonneg _) (Ne.symm hz)
      have hqpos : ∀ i : Fin k, 0 < q.w (z i) := by
        intro i
        rw [← hq i]
        exact push_pos P (fun z => z i) z hp
      have hprod : (∏ i : Fin k, q.w (z i)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (hqpos i))
      rw [productFinProb_w, log_div hz hprod, Real.log_prod _ _ (fun i _ => ne_of_gt (hqpos i))]
      rw [mul_sub, Finset.mul_sum]
  unfold FinProb.klPos
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  have hcross : ∀ i : Fin k, (∑ z, P.w z * log (q.w (z i))) =
      -FinProb.entropy q := by
    intro i
    have h := push_sum P (fun z => z i) (fun a => log (q.w a))
    rw [hq i] at h
    simpa [FinProb.entropy] using h.symm
  simp_rw [hcross]
  simp [FinProb.entropy]
  ring

/-- Positive atoms of the joint law are absolutely continuous with respect
its conditional product whenever its coordinate posteriors coincide. -/
theorem product_support {k : ℕ} (P : FinProb (Fin k → α)) (q : FinProb α)
    (hq : ∀ i : Fin k, push P (fun z => z i) = q) (z : Fin k → α)
    (hz : 0 < P.w z) : 0 < (productFinProb k q).w z := by
  change 0 < ∏ i : Fin k, q.w (z i)
  apply Finset.prod_pos
  intro i _
  rw [← hq i]
  exact push_pos P (fun z => z i) z hz

/-- Disintegrating and remixing a finite law recovers its unobserved marginal. -/
theorem mixture_conditional [Nonempty α] (P : FinProb (α × β)) :
    mixture (margR P).w (margR P).nonneg (margR P).sum_eq_one (conditional P) = margL P := by
  apply FinProb.ext
  intro a
  change (∑ b, (margR P).w b * (conditional P b).w a) = ∑ b, P.w (a, b)
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : 0 < (margR P).w b
  · rw [conditional_w P b hb, mul_div_cancel₀ _ (ne_of_gt hb)]
  · have hz : (margR P).w b = 0 := le_antisymm (le_of_not_gt hb) ((margR P).nonneg _)
    simp [hz, joint_eq_zero_of_margR P _ _ hz]

/-- Finite conditional product mixtures, with the actual joint-convexity
inequality and support guarantee required for finite relative entropy. -/
theorem conditional_product_mixture_bound [Nonempty α] {k : ℕ} (hk : 0 < k)
    (P : FinProb ((Fin k → α) × β)) (R : FinProb (α × β))
    (hR : ∀ i : Fin k, push P (fun z => (z.1 i, z.2)) = R) :
    let M := mixtureProduct k (margR P).w (margR P).nonneg (margR P).sum_eq_one (conditional R)
    FinProb.Supports (margL P) M ∧
    FinProb.klPos (margL P) M ≤
      (k : ℝ) * (FinProb.entropy R - FinProb.entropy (margR P)) -
        (FinProb.entropy P - FinProb.entropy (margR P)) := by
  have hm : margR R = margR P := by
    rw [← hR ⟨0, hk⟩]
    simp only [margR_eq_push, push_comp]
    rfl
  have hpost : ∀ b, 0 < (margR P).w b → ∀ i : Fin k,
      push (conditional P b) (fun z => z i) = conditional R b := by
    intro b hb i
    rw [← hR i, conditional_push P (fun z => z i) b hb]
  have hsupport : ∀ b, 0 < (margR P).w b →
      FinProb.Supports (conditional P b) (productFinProb k (conditional R b)) := by
    intro b hb z hz
    by_contra hp
    have hpos : 0 < (conditional P b).w z :=
      lt_of_le_of_ne ((conditional P b).nonneg _) (Ne.symm hp)
    have := product_support (conditional P b) (conditional R b) (hpost b hb) z hpos
    rw [hz] at this
    linarith
  have hs := FinProb.supports_mixture (margR P).w (margR P).nonneg (margR P).sum_eq_one
    (conditional P) (fun b => productFinProb k (conditional R b)) hsupport
  have hbound := FinProb.klPos_mixture_le (margR P).w (margR P).nonneg (margR P).sum_eq_one
    (conditional P) (fun b => productFinProb k (conditional R b)) hsupport
  rw [mixture_conditional] at hs hbound
  refine ⟨hs, hbound.trans_eq ?_⟩
  have he : ∀ b, (margR P).w b * FinProb.klPos (conditional P b) (productFinProb k (conditional R b)) =
      (k : ℝ) * ((margR P).w b * FinProb.entropy (conditional R b)) -
        (margR P).w b * FinProb.entropy (conditional P b) := by
    intro b
    by_cases hb : 0 < (margR P).w b
    · rw [klPos_product_eq _ _ (hpost b hb)]
      ring
    · have hz : (margR P).w b = 0 := le_antisymm (le_of_not_gt hb) ((margR P).nonneg _)
      simp [hz]
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← condEntropy_expect P]
  have hcondR : (∑ b, (margR P).w b * FinProb.entropy (conditional R b)) = condEntropy R := by
    rw [condEntropy_expect R, hm]
  rw [hcondR, condEntropy_eq P, condEntropy_eq R, hm]

/-- Telescoping identity for shifted entropy increments. -/
theorem sum_shift_increments (H : ℕ → ℝ) (m k : ℕ) :
    ∑ i ∈ Finset.range k, (H (m + i + 1) - H (m + i)) = H (m + k) - H m := by
  have h := Finset.sum_range_sub (fun i => H (m + i)) k
  simpa [Nat.add_assoc] using h

/-- The exact entropy average in (4).  It only needs monotonicity of
block entropy and the finite alphabet entropy ceiling. -/
theorem entropy_average (H : ℕ → ℝ) (N k : ℕ) (c : ℝ)
    (h0 : 0 ≤ H 0) (hmono : ∀ i < k, H N ≤ H (N + i))
    (hcap : ∀ i < k, H i ≤ (i : ℝ) * c) :
    ∑ m ∈ Finset.range N,
      ((k : ℝ) * (H (m + 1) - H m) - (H (m + k) - H m))
      ≤ ((k : ℝ) * (k - 1) / 2) * c := by
  have hrewrite : ∀ m, (k : ℝ) * (H (m + 1) - H m) - (H (m + k) - H m) =
      ∑ i ∈ Finset.range k,
        ((H (m + 1) - H m) - (H (m + i + 1) - H (m + i))) := by
    intro m
    rw [Finset.sum_sub_distrib, sum_shift_increments]
    simp
    ring
  simp_rw [hrewrite]
  rw [Finset.sum_comm]
  have hbound : ∀ i ∈ Finset.range k,
      (∑ m ∈ Finset.range N,
        ((H (m + 1) - H m) - (H (m + i + 1) - H (m + i))))
      ≤ (i : ℝ) * c := by
    intro i hi
    rw [Finset.sum_sub_distrib]
    have hleft : (∑ m ∈ Finset.range N, (H (m + 1) - H m)) = H N - H 0 := by
      simpa using Finset.sum_range_sub H N
    have hright : (∑ m ∈ Finset.range N, (H (m + i + 1) - H (m + i))) =
        H (N + i) - H i := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        sum_shift_increments H i N
    rw [hleft, hright]
    have hm := hmono i (Finset.mem_range.mp hi)
    have hc := hcap i (Finset.mem_range.mp hi)
    linarith
  apply (Finset.sum_le_sum hbound).trans_eq
  rw [← Finset.sum_mul]
  have hsum : (∑ i ∈ Finset.range k, (i : ℝ)) = (k : ℝ) * (k - 1) / 2 := by
    by_cases hk : k = 0
    · simp [hk]
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      have h := congrArg (Nat.cast : ℕ → ℝ) (Finset.sum_range_id_mul_two k)
      rw [Nat.cast_mul, Nat.cast_two, Nat.cast_mul, Nat.cast_pred hkpos, Nat.cast_sum] at h
      linarith
  rw [hsum]

/-- A block with at most the entropy average exists among the `N` choices. -/
theorem exists_entropy_average (H : ℕ → ℝ) (N k : ℕ) (c : ℝ) (hN : 0 < N)
    (h0 : 0 ≤ H 0) (hmono : ∀ i < k, H N ≤ H (N + i))
    (hcap : ∀ i < k, H i ≤ (i : ℝ) * c) :
    ∃ m < N, (k : ℝ) * (H (m + 1) - H m) - (H (m + k) - H m)
      ≤ ((k : ℝ) * (k - 1) / (2 * N)) * c := by
  have hsum := entropy_average H N k c h0 hmono hcap
  have hc : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hsum' : (∑ m ∈ Finset.range N,
      ((k : ℝ) * (H (m + 1) - H m) - (H (m + k) - H m)))
      ≤ ∑ _m ∈ Finset.range N, ((k : ℝ) * (k - 1) / (2 * N)) * c := by
    calc _ ≤ ((k : ℝ) * (k - 1) / 2) * c := hsum
      _ = _ := by simp; field_simp
  obtain ⟨m, hm, hle⟩ := Finset.exists_le_of_sum_le (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hN)) hsum'
  exact ⟨m, Finset.mem_range.mp hm, hle⟩

end ConditioningFull
end Paper06
