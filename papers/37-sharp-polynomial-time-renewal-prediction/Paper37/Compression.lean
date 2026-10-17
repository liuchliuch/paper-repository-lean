import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Finite compression and information identities for P37

The distributions in this file are normalized, nonnegative real mass functions.
`kl` uses the conventional `0 * log 0 = 0`; the nonnegativity theorem explicitly
requires absolute continuity, so no infinite-divergence case is silently treated
as finite. These finite identities are the information-theoretic ingredients of
(D.3), (G.4), and the truncated-countdown bounds. They do not themselves assert
that a renewal process has the required regeneration or stationarity property.
-/

namespace Paper37.Compression

open Finset

/-- A probability distribution on a finite alphabet. -/
structure Distribution (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  total : ∑ a, mass a = 1

namespace Distribution

variable {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]

instance : CoeFun (Distribution α) (fun _ => α → ℝ) := ⟨mass⟩

lemma mass_le_one (p : Distribution α) (a : α) : p a ≤ 1 := by
  rw [← p.total]
  exact single_le_sum (fun b _ => p.nonneg b) (mem_univ a)

@[ext] lemma ext (p q : Distribution α) (h : ∀ a, p a = q a) : p = q := by
  cases p
  cases q
  congr
  exact funext h

/-- Relative entropy, in nats, on its finite domain of absolute continuity. -/
noncomputable def kl (p q : Distribution α) : ℝ :=
  ∑ a, p a * (Real.log (p a) - Real.log (q a))

/-- Shannon entropy, in nats. -/
noncomputable def entropy (p : Distribution α) : ℝ :=
  - ∑ a, p a * Real.log (p a)

lemma entropy_nonneg (p : Distribution α) : 0 ≤ entropy p := by
  apply neg_nonneg.mpr
  apply sum_nonpos
  intro a _
  exact Real.mul_log_nonpos (p.nonneg a) (p.mass_le_one a)

/-- The scalar log inequality used in Gibbs' inequality, including zero masses. -/
lemma scalar_kl_ge_sub {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hac : 0 < p → 0 < q) : p - q ≤ p * (Real.log p - Real.log q) := by
  by_cases hp0 : p = 0
  · simp only [hp0, zero_sub, zero_mul]
    linarith
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hq' : 0 < q := hac hp'
  have hlog := Real.log_le_sub_one_of_pos (div_pos hq' hp')
  rw [Real.log_div hq'.ne' hp'.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hp
  have hdiv : p * (q / p - 1) = q - p := by field_simp
  rw [hdiv] at hmul
  nlinarith

/-- Gibbs' inequality, with the essential support condition made explicit. -/
theorem kl_nonneg (p q : Distribution α)
    (hac : ∀ a, 0 < p a → 0 < q a) : 0 ≤ kl p q := by
  have h := sum_le_sum (fun a (_ : a ∈ (univ : Finset α)) =>
    scalar_kl_ge_sub (p.nonneg a) (q.nonneg a) (hac a))
  simpa [sum_sub_distrib, p.total, q.total, kl] using h

/-- A finite mixture of genuine probability distributions. -/
noncomputable def mixture (w : Distribution ι) (p : ι → Distribution α) : Distribution α where
  mass a := ∑ i, w i * p i a
  nonneg a := sum_nonneg (fun i _ => mul_nonneg (w.nonneg i) ((p i).nonneg a))
  total := by
    rw [sum_comm]
    simp_rw [← mul_sum, (p _).total, mul_one]
    exact w.total

@[simp] lemma mixture_apply (w : Distribution ι) (p : ι → Distribution α) (a : α) :
    mixture w p a = ∑ i, w i * p i a := rfl

/-- The conditional KL loss averaged over the conditioning distribution. -/
noncomputable def conditionalKL (w : Distribution ι) (p : ι → Distribution α)
    (q : Distribution α) : ℝ := ∑ i, w i * kl (p i) q

/-- Mutual information between the mixture index and its sampled outcome. -/
noncomputable def mutualInformation (w : Distribution ι) (p : ι → Distribution α) : ℝ :=
  conditionalKL w p (mixture w p)

/-- The exact Bayes/Pythagorean identity behind (D.3) and (G.4). -/
theorem conditionalKL_decomposition (w : Distribution ι) (p : ι → Distribution α)
    (q : Distribution α) :
    conditionalKL w p q = mutualInformation w p + kl (mixture w p) q := by
  unfold mutualInformation conditionalKL kl
  simp only [mixture_apply]
  simp_rw [mul_sum]
  rw [sum_comm (f := fun i a => w i * (p i a * (Real.log (p i a) - Real.log (q a)))),
    sum_comm (f := fun i a => w i * (p i a *
      (Real.log (p i a) - Real.log (∑ j, w j * p j a))))]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro a _
  rw [sum_mul, ← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  ring


/-- A positive mixture weight preserves the support of its component. -/
lemma mixture_pos (w : Distribution ι) (p : ι → Distribution α) (i : ι) (a : α)
    (hw : 0 < w i) (hp : 0 < p i a) : 0 < mixture w p a := by
  have hle : w i * p i a ≤ mixture w p a :=
    single_le_sum (fun j _ => mul_nonneg (w.nonneg j) ((p j).nonneg a)) (mem_univ i)
  exact lt_of_lt_of_le (mul_pos hw hp) hle

/-- Mutual information is nonnegative, including zero-probability indices. -/
theorem mutualInformation_nonneg (w : Distribution ι) (p : ι → Distribution α) :
    0 ≤ mutualInformation w p := by
  unfold mutualInformation conditionalKL
  apply sum_nonneg
  intro i _
  by_cases hw : w i = 0
  · simp [hw]
  · have hw' : 0 < w i := lt_of_le_of_ne (w.nonneg i) (Ne.symm hw)
    exact mul_nonneg (w.nonneg i)
      (kl_nonneg _ _ (fun a ha => mixture_pos w p i a hw' ha))

/-- The entropy identity for a mixture and its latent index. -/
theorem mutualInformation_eq_entropy_sub (w : Distribution ι)
    (p : ι → Distribution α) :
    mutualInformation w p = entropy (mixture w p) - ∑ i, w i * entropy (p i) := by
  unfold mutualInformation conditionalKL kl entropy
  simp only [mixture_apply]
  simp_rw [mul_sum, mul_sub, sum_sub_distrib]
  simp_rw [mul_neg, sum_neg_distrib]
  rw [sum_comm (f := fun i a => w i * (p i a * Real.log (∑ j, w j * p j a)))]
  simp_rw [← mul_assoc, ← sum_mul]
  simp_rw [mul_sum, ← mul_assoc]
  ring

/-- Entropy is concave under finite mixtures. -/
theorem entropy_mixture_ge (w : Distribution ι) (p : ι → Distribution α) :
    ∑ i, w i * entropy (p i) ≤ entropy (mixture w p) := by
  have h := mutualInformation_nonneg w p
  rw [mutualInformation_eq_entropy_sub] at h
  linarith

/-- Information cannot exceed the entropy of the observed outcome. -/
theorem mutualInformation_le_output_entropy (w : Distribution ι)
    (p : ι → Distribution α) : mutualInformation w p ≤ entropy (mixture w p) := by
  rw [mutualInformation_eq_entropy_sub]
  have h : 0 ≤ ∑ i, w i * entropy (p i) :=
    sum_nonneg (fun i _ => mul_nonneg (w.nonneg i) (entropy_nonneg (p i)))
  linarith

/-- Information cannot exceed the entropy of the latent index. -/
theorem mutualInformation_le_entropy (w : Distribution ι)
    (p : ι → Distribution α) : mutualInformation w p ≤ entropy w := by
  have hterm : ∀ i a, w i * (p i a *
      (Real.log (p i a) - Real.log (mixture w p a))) ≤
      -(w i * p i a * Real.log (w i)) := by
    intro i a
    by_cases hw : w i = 0
    · simp [hw]
    by_cases hp : p i a = 0
    · simp [hp]
    have hw' : 0 < w i := lt_of_le_of_ne (w.nonneg i) (Ne.symm hw)
    have hp' : 0 < p i a := lt_of_le_of_ne ((p i).nonneg a) (Ne.symm hp)
    have hle : w i * p i a ≤ mixture w p a :=
      single_le_sum (fun j _ => mul_nonneg (w.nonneg j) ((p j).nonneg a)) (mem_univ i)
    have hlog := Real.log_le_log (mul_pos hw' hp') hle
    rw [Real.log_mul hw hp] at hlog
    have h := mul_le_mul_of_nonneg_left hlog (mul_nonneg (w.nonneg i) ((p i).nonneg a))
    nlinarith
  unfold mutualInformation conditionalKL kl
  simp_rw [mul_sum]
  have h := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) =>
    sum_le_sum (fun a (_ : a ∈ (univ : Finset α)) => hterm i a))
  have heq : (∑ i, ∑ a, -(w i * p i a * Real.log (w i))) = entropy w := by
    unfold entropy
    simp_rw [sum_neg_distrib, mul_assoc]
    congr 1
    apply sum_congr rfl
    intro i _
    rw [← mul_sum, ← sum_mul, (p i).total, one_mul]
  rw [heq] at h
  exact h

/-- The uniform distribution on a nonempty finite alphabet. -/
noncomputable def uniform [Nonempty α] : Distribution α where
  mass _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by
    simp only [sum_const, card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Fintype.card_ne_zero))

@[simp] lemma uniform_apply [Nonempty α] (a : α) :
    uniform (α := α) a = (Fintype.card α : ℝ)⁻¹ := rfl

/-- Maximum entropy on a finite alphabet is its logarithmic cardinality. -/
theorem entropy_le_log_card [Nonempty α] (p : Distribution α) :
    entropy p ≤ Real.log (Fintype.card α) := by
  have h := kl_nonneg p (uniform (α := α)) (fun _ _ =>
    inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  have heq : kl p (uniform (α := α)) = Real.log (Fintype.card α) - entropy p := by
    unfold kl entropy
    simp only [uniform_apply, Real.log_inv, sub_neg_eq_add, mul_add, sum_add_distrib]
    rw [← sum_mul, p.total, one_mul]
    ring
  rw [heq] at h
  linarith

/-- The finite-state information bound used by a truncated countdown. -/
theorem mutualInformation_le_log_card [Nonempty ι] (w : Distribution ι)
    (p : ι → Distribution α) : mutualInformation w p ≤ Real.log (Fintype.card ι) :=
  (mutualInformation_le_entropy w p).trans (entropy_le_log_card w)

/-- Associativity of normalized finite mixtures. -/
theorem mixture_assoc (w : Distribution ι) (r : ι → Distribution β)
    (p : β → Distribution α) :
    mixture w (fun i => mixture (r i) p) = mixture (mixture w r) p := by
  apply Distribution.ext
  intro a
  simp only [mixture_apply]
  simp_rw [mul_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  apply sum_congr rfl
  intro i _
  ring

/-- Data processing for the actual finite Markov kernel `ι → β → α`. -/
theorem data_processing (w : Distribution ι) (r : ι → Distribution β)
    (p : β → Distribution α) :
    mutualInformation w (fun i => mixture (r i) p) ≤
      mutualInformation (mixture w r) p := by
  rw [mutualInformation_eq_entropy_sub, mutualInformation_eq_entropy_sub, mixture_assoc]
  have h := sum_le_sum (fun i (_ : i ∈ (univ : Finset ι)) =>
    mul_le_mul_of_nonneg_left (entropy_mixture_ge (r i) p) (w.nonneg i))
  have heq : ∑ i, w i * ∑ b, r i b * entropy (p b) =
      ∑ b, mixture w r b * entropy (p b) := by
    simp only [mixture_apply]
    simp_rw [mul_sum, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro b _
    apply sum_congr rfl
    intro i _
    ring
  rw [heq] at h
  linarith

/-- Information across any finite mediating state is at most its entropy. -/
theorem markov_information_le_entropy (w : Distribution ι) (r : ι → Distribution β)
    (p : β → Distribution α) :
    mutualInformation w (fun i => mixture (r i) p) ≤ entropy (mixture w r) :=
  (data_processing w r p).trans (mutualInformation_le_entropy (mixture w r) p)

/-- In particular, a truncated countdown with `m + 1` values costs at most `log (m + 1)`. -/
theorem truncated_countdown_information_bound (m : ℕ) (w : Distribution ι)
    (r : ι → Distribution (Fin (m + 1))) (p : Fin (m + 1) → Distribution α) :
    mutualInformation w (fun i => mixture (r i) p) ≤ Real.log (m + 1) := by
  exact (markov_information_le_entropy w r p).trans (by simpa using
    (entropy_le_log_card (mixture w r)))


/-- Convexity in the predicted distribution, for full-support component predictions. -/
theorem kl_mixture_right_le (w : Distribution ι) (p : Distribution α)
    (q : ι → Distribution α) (hq : ∀ i a, 0 < q i a) :
    kl p (mixture w q) ≤ ∑ i, w i * kl p (q i) := by
  have hscalar : ∀ a, p a * (Real.log (p a) - Real.log (mixture w q a)) ≤
      ∑ i, w i * (p a * (Real.log (p a) - Real.log (q i a))) := by
    intro a
    have hj := strictConcaveOn_log_Ioi.concaveOn.le_map_sum
      (t := (univ : Finset ι)) (w := fun i => w i) (p := fun i => q i a)
      (fun i _ => w.nonneg i) w.total (fun i _ => hq i a)
    simp only [smul_eq_mul] at hj
    have hmul := mul_le_mul_of_nonneg_left hj (p.nonneg a)
    have heq : ∑ i, w i * (p a * (Real.log (p a) - Real.log (q i a))) =
        p a * Real.log (p a) - p a * ∑ i, w i * Real.log (q i a) := by
      calc
        _ = (p a * Real.log (p a)) * (∑ i, w i) -
            p a * (∑ i, w i * Real.log (q i a)) := by
          rw [mul_sum, mul_sum, ← sum_sub_distrib]
          apply sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [w.total, mul_one]
    rw [heq]
    change p a * (Real.log (p a) - Real.log (∑ i, w i * q i a)) ≤ _
    nlinarith
  unfold kl
  have h := sum_le_sum (fun a (_ : a ∈ (univ : Finset α)) => hscalar a)
  rw [sum_comm] at h
  simpa only [mul_sum] using h

/-- An honest joint distribution sampled from an index and a normalized kernel. -/
noncomputable def joint (w : Distribution ι) (p : ι → Distribution α) :
    Distribution (ι × α) where
  mass x := w x.1 * p x.1 x.2
  nonneg x := mul_nonneg (w.nonneg x.1) ((p x.1).nonneg x.2)
  total := by
    rw [Fintype.sum_prod_type]
    simp_rw [← mul_sum, (p _).total, mul_one]
    exact w.total

@[simp] lemma joint_apply (w : Distribution ι) (p : ι → Distribution α) (i : ι) (a : α) :
    joint w p (i, a) = w i * p i a := rfl

/-- KL chain rule for full-support predicted joint laws. -/
theorem kl_joint_chain_rule (w v : Distribution ι) (p q : ι → Distribution α)
    (hv : ∀ i, 0 < v i) (hq : ∀ i a, 0 < q i a) :
    kl (joint w p) (joint v q) = kl w v + ∑ i, w i * kl (p i) (q i) := by
  have hterm : ∀ i a,
      (w i * p i a) * (Real.log (w i * p i a) - Real.log (v i * q i a)) =
      p i a * (w i * (Real.log (w i) - Real.log (v i))) +
        w i * (p i a * (Real.log (p i a) - Real.log (q i a))) := by
    intro i a
    by_cases hw : w i = 0
    · simp [hw]
    by_cases hp : p i a = 0
    · simp [hp]
    rw [Real.log_mul hw hp, Real.log_mul (hv i).ne' (hq i a).ne']
    ring
  unfold kl
  rw [Fintype.sum_prod_type]
  simp only [joint_apply]
  simp_rw [hterm, sum_add_distrib, ← sum_mul, (p _).total, one_mul, ← mul_sum]

/-- Conditional mutual information for a suffix `s` and a hidden older history `i`. -/
noncomputable def conditionalMutualInformation (w : Distribution β)
    (r : β → Distribution ι) (p : β → ι → Distribution α) : ℝ :=
  ∑ s, w s * mutualInformation (r s) (p s)

/-- The full conditional Pythagorean decomposition (D.3), averaged over suffixes. -/
theorem conditional_pythagorean (w : Distribution β) (r : β → Distribution ι)
    (p : β → ι → Distribution α) (q : β → Distribution α) :
    (∑ s, w s * conditionalKL (r s) (p s) (q s)) =
      conditionalMutualInformation w r p +
        ∑ s, w s * kl (mixture (r s) (p s)) (q s) := by
  simp_rw [conditionalKL_decomposition, mul_add, sum_add_distrib]
  rfl

/-- The entropy cost of each actual finite mediating state, conditioned on a suffix. -/
theorem conditional_data_processing_bound (w : Distribution β)
    (r : β → Distribution ι) {κ : Type*} [Fintype κ]
    (transition : β → ι → Distribution κ) (output : β → κ → Distribution α) :
    conditionalMutualInformation w r (fun s i => mixture (transition s i) (output s)) ≤
      ∑ s, w s * entropy (mixture (r s) (transition s)) := by
  unfold conditionalMutualInformation
  apply sum_le_sum
  intro s _
  exact mul_le_mul_of_nonneg_left
    (markov_information_le_entropy (r s) (transition s) (output s)) (w.nonneg s)

/-- Nonnegativity is preserved when the conditional information is averaged. -/
theorem conditionalMutualInformation_nonneg (w : Distribution β)
    (r : β → Distribution ι) (p : β → ι → Distribution α) :
    0 ≤ conditionalMutualInformation w r p :=
  sum_nonneg (fun s _ => mul_nonneg (w.nonneg s) (mutualInformation_nonneg (r s) (p s)))


/-- A pointwise likelihood envelope bounds its expected log loss. -/
theorem kl_le_of_pointwise_domination (p q : Distribution α) (B : ℝ)
    (hdom : ∀ a, p a ≤ Real.exp B * q a) : kl p q ≤ B := by
  have hterm : ∀ a, p a * (Real.log (p a) - Real.log (q a)) ≤ p a * B := by
    intro a
    by_cases hp : p a = 0
    · simp [hp]
    have hp' : 0 < p a := lt_of_le_of_ne (p.nonneg a) (Ne.symm hp)
    have hq' : 0 < q a := by
      by_contra hq
      have hq0 : q a = 0 := le_antisymm (le_of_not_gt hq) (q.nonneg a)
      have := hdom a
      rw [hq0, mul_zero] at this
      linarith
    have hlog := Real.log_le_log hp' (hdom a)
    rw [Real.log_mul (Real.exp_ne_zero B) hq'.ne', Real.log_exp] at hlog
    exact mul_le_mul_of_nonneg_left (by linarith) (p.nonneg a)
  unfold kl
  calc
    _ ≤ ∑ a, p a * B := sum_le_sum (fun a _ => hterm a)
    _ = B := by rw [← sum_mul, p.total, one_mul]

/-- Pushforward of an actual probability mass function. -/
noncomputable def map (p : Distribution α) (f : α → β) : Distribution β := by
  classical
  exact {
    mass := fun b => ∑ a, if f a = b then p a else 0
    nonneg := fun b => sum_nonneg (fun a _ => by split_ifs; exact p.nonneg a; exact le_rfl)
    total := by
      rw [sum_comm]
      simpa using p.total }

@[simp] lemma map_apply [DecidableEq β] (p : Distribution α) (f : α → β) (b : β) :
    map p f b = ∑ a, if f a = b then p a else 0 := by
  classical
  simp only [map]
  apply sum_congr rfl
  intro a _
  by_cases h : f a = b <;> simp [h]

/-- Summing over extensions preserves a pointwise likelihood envelope. -/
theorem map_preserves_domination (p q : Distribution α) (f : α → β) (B : ℝ)
    (hdom : ∀ a, p a ≤ Real.exp B * q a) :
    ∀ b, map p f b ≤ Real.exp B * map q f b := by
  classical
  intro b
  simp only [map_apply, mul_sum]
  apply sum_le_sum
  intro a _
  split_ifs
  · exact hdom a
  · simp

/-- The KL bound remains valid for every prefix or other finite observation. -/
theorem map_kl_le_of_domination (p q : Distribution α) (f : α → β) (B : ℝ)
    (hdom : ∀ a, p a ≤ Real.exp B * q a) : kl (map p f) (map q f) ≤ B :=
  kl_le_of_pointwise_domination _ _ B (map_preserves_domination p q f B hdom)

/-- The exact finite version of an epoch's risk bound in the proof of (G.2).

Here `w` is the earlier history, `r` the conditional truncated countdown, and
`p` the law of the epoch given that countdown. All three are normalized laws;
the factorization is an actual Markov kernel, rather than an assumed MI bound.
The envelope hypothesis is precisely the pointwise block domination input.
-/
theorem epoch_risk_bound (m : ℕ) (w : Distribution ι)
    (r : ι → Distribution (Fin (m + 1))) (p : Fin (m + 1) → Distribution α)
    (q : Distribution α) (B : ℝ)
    (hdom : ∀ a, mixture w (fun i => mixture (r i) p) a ≤ Real.exp B * q a) :
    conditionalKL w (fun i => mixture (r i) p) q ≤ B + Real.log (m + 1) := by
  rw [conditionalKL_decomposition]
  have hi := truncated_countdown_information_bound m w r p
  have hk := kl_le_of_pointwise_domination (mixture w (fun i => mixture (r i) p)) q B hdom
  linarith


/-- A deterministic distribution, needed for the empty history. -/
noncomputable def point (a : α) : Distribution α := by
  classical
  exact {
    mass := fun b => if b = a then 1 else 0
    nonneg := fun b => by split_ifs <;> positivity
    total := by simp }

@[simp] lemma point_apply [DecidableEq α] (a b : α) : point a b = if b = a then 1 else 0 := by
  classical
  simp [point]

@[simp] lemma kl_self (p : Distribution α) : kl p p = 0 := by simp [kl]


/-- Entropy written as a sum, useful at zero probability masses. -/
lemma entropy_eq_sum_negMulLog (p : Distribution α) :
    entropy p = ∑ a, Real.negMulLog (p a) := by
  simp [entropy, Real.negMulLog, sum_neg_distrib]

/-- Entropy chain rule for a normalized joint law. -/
theorem entropy_joint (w : Distribution ι) (p : ι → Distribution α) :
    entropy (joint w p) = entropy w + ∑ i, w i * entropy (p i) := by
  simp only [entropy_eq_sum_negMulLog, Fintype.sum_prod_type, joint_apply,
    Real.negMulLog_mul]
  simp_rw [sum_add_distrib, ← sum_mul, (p _).total, one_mul, ← mul_sum]

/-- A component contribution is bounded by the whole mixture mass. -/
lemma component_le_mixture (w : Distribution ι) (p : ι → Distribution α) (i : ι) (a : α) :
    w i * p i a ≤ mixture w p a :=
  single_le_sum (fun j _ => mul_nonneg (w.nonneg j) ((p j).nonneg a)) (mem_univ i)

/-- The actual posterior of the latent mixture index, with an arbitrary normalized
version on null observations. -/
noncomputable def posterior (w : Distribution ι) (p : ι → Distribution α) (a : α) :
    Distribution ι := by
  classical
  exact {
    mass := fun i => if 0 < mixture w p a then w i * p i a / mixture w p a else w i
    nonneg := fun i => by
      split_ifs
      · exact div_nonneg (mul_nonneg (w.nonneg i) ((p i).nonneg a)) ((mixture w p).nonneg a)
      · exact w.nonneg i
    total := by
      split_ifs with h
      · simp only [div_eq_mul_inv]
        rw [← sum_mul]
        exact mul_inv_cancel₀ h.ne'
      · exact w.total }

/-- Bayes' rule, including observations of probability zero. -/
theorem posterior_bayes (w : Distribution ι) (p : ι → Distribution α) (a : α) (i : ι) :
    mixture w p a * posterior w p a i = w i * p i a := by
  classical
  by_cases h : 0 < mixture w p a
  · simp only [posterior, h, ↓reduceIte]
    exact mul_div_cancel₀ _ h.ne'
  · have hm : mixture w p a = 0 :=
      le_antisymm (le_of_not_gt h) ((mixture w p).nonneg a)
    have hc : w i * p i a = 0 :=
      le_antisymm (hm ▸ component_le_mixture w p i a)
        (mul_nonneg (w.nonneg i) ((p i).nonneg a))
    rw [hm, zero_mul, hc]

/-- Actual disintegration of a two-stage observation through its first coordinate. -/
theorem mixture_joint (w : Distribution ι) (p : ι → Distribution α)
    (q : ι → α → Distribution β) :
    mixture w (fun i => joint (p i) (q i)) =
      joint (mixture w p) (fun a => mixture (posterior w p a) (fun i => q i a)) := by
  apply Distribution.ext
  rintro ⟨a, b⟩
  change (∑ i, w i * (p i a * q i a b)) = mixture w p a *
    ∑ i, posterior w p a i * q i a b
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  simp only [← mul_assoc]
  rw [posterior_bayes]

/-- Mutual-information chain rule, with the conditional law computed by Bayes' rule. -/
theorem mutualInformation_chain_rule (w : Distribution ι) (p : ι → Distribution α)
    (q : ι → α → Distribution β) :
    mutualInformation w (fun i => joint (p i) (q i)) = mutualInformation w p +
      ∑ a, mixture w p a * mutualInformation (posterior w p a) (fun i => q i a) := by
  have heq : (∑ a, mixture w p a *
      ∑ i, posterior w p a i * entropy (q i a)) =
      ∑ i, w i * ∑ a, p i a * entropy (q i a) := by
    simp_rw [mul_sum, ← mul_assoc, posterior_bayes]
    rw [sum_comm]
  rw [mutualInformation_eq_entropy_sub, mixture_joint, entropy_joint]
  simp_rw [entropy_joint, mul_add, sum_add_distrib]
  rw [mutualInformation_eq_entropy_sub]
  simp_rw [mutualInformation_eq_entropy_sub, mul_sub, sum_sub_distrib]
  rw [heq]
  ring

/-- A constant observation kernel carries no information about its latent index. -/
theorem mixture_const (w : Distribution ι) (p : Distribution α) :
    mixture w (fun _ => p) = p := by
  apply Distribution.ext
  intro a
  simp only [mixture_apply, ← sum_mul, w.total, one_mul]

@[simp] theorem mutualInformation_const (w : Distribution ι) (p : Distribution α) :
    mutualInformation w (fun _ => p) = 0 := by
  unfold mutualInformation conditionalKL
  rw [mixture_const]
  simp

end Distribution

/-- Histories are nested finite products, with the last coordinate being the next symbol. -/
def History (α : Type*) : ℕ → Type _
  | 0 => PUnit
  | n + 1 => History α n × α

instance historyFintype (α : Type*) [Fintype α] (n : ℕ) : Fintype (History α n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih => exact inferInstanceAs (Fintype (History α n × α))

/-- A sequential predictor provides a normalized next-symbol law for each finite history. -/
abbrev SequentialLaw (α : Type*) [Fintype α] := (n : ℕ) → History α n → Distribution α

namespace SequentialLaw

open Distribution

variable {α : Type*} [Fintype α]

/-- The full block assignment induced by the sequential kernels. -/
noncomputable def block (P : SequentialLaw α) : (n : ℕ) → Distribution (History α n)
  | 0 => point PUnit.unit
  | n + 1 => joint (block P n) (P n)

/-- The cumulative expected excess logarithmic loss, with the actual history law. -/
noncomputable def cumulativeKL (P Q : SequentialLaw α) : ℕ → ℝ
  | 0 => 0
  | n + 1 => cumulativeKL P Q n + ∑ h, block P n h * kl (P n h) (Q n h)

/-- Positive sequential conditionals produce a full-support block assignment. -/
lemma block_pos (Q : SequentialLaw α) (hQ : ∀ n h a, 0 < Q n h a) :
    ∀ n h, 0 < block Q n h := by
  intro n
  induction n with
  | zero =>
    intro h
    cases h
    simp [block, point]
  | succ n ih =>
    rintro ⟨h, a⟩
    exact mul_pos (ih h) (hQ n h a)

/-- The exact sequential KL chain rule used in Appendix G.

No stationarity or renewal assumption is needed for this identity.
-/
theorem cumulativeKL_eq_blockKL (P Q : SequentialLaw α)
    (hQ : ∀ n h a, 0 < Q n h a) :
    ∀ n, cumulativeKL P Q n = kl (block P n) (block Q n) := by
  intro n
  induction n with
  | zero => simp [cumulativeKL, block]
  | succ n ih =>
    change cumulativeKL P Q n + _ = kl (joint (block P n) (P n)) (joint (block Q n) (Q n))
    rw [kl_joint_chain_rule _ _ _ _ (block_pos Q hQ n) (hQ n), ih]


/-- Information in the next symbol about a latent state, after the actual history. -/
noncomputable def conditionalInformation {ι : Type*} [Fintype ι]
    (w : Distribution ι) (P : ι → SequentialLaw α) (n : ℕ) : ℝ :=
  ∑ h, mixture w (fun i => block (P i) n) h *
    mutualInformation (posterior w (fun i => block (P i) n) h) (fun i => P i n h)

/-- The exact information increment at each time. -/
theorem block_information_succ {ι : Type*} [Fintype ι]
    (w : Distribution ι) (P : ι → SequentialLaw α) (n : ℕ) :
    mutualInformation w (fun i => block (P i) (n + 1)) =
      mutualInformation w (fun i => block (P i) n) + conditionalInformation w P n := by
  exact mutualInformation_chain_rule w (fun i => block (P i) n) (fun i => P i n)

/-- Chain rule summed over an actual sequential observation block. -/
theorem block_information_eq_sum {ι : Type*} [Fintype ι]
    (w : Distribution ι) (P : ι → SequentialLaw α) :
    ∀ n, mutualInformation w (fun i => block (P i) n) =
      ∑ t ∈ range n, conditionalInformation w P t := by
  intro n
  induction n with
  | zero => simp [block]
  | succ n ih => rw [block_information_succ, ih, sum_range_succ]

/-- The entire sum of memory increments is paid for by the latent state's entropy. -/
theorem information_sum_le_entropy {ι : Type*} [Fintype ι]
    (w : Distribution ι) (P : ι → SequentialLaw α) (n : ℕ) :
    (∑ t ∈ range n, conditionalInformation w P t) ≤ entropy w := by
  rw [← block_information_eq_sum]
  exact mutualInformation_le_entropy w (fun i => block (P i) n)

/-- In particular the information accumulated from a finite truncated countdown
has a logarithmic, rather than a sum-of-logarithms, bound. -/
theorem countdown_information_sum_le (m n : ℕ)
    (w : Distribution (Fin (m + 1))) (P : Fin (m + 1) → SequentialLaw α) :
    (∑ t ∈ range n, conditionalInformation w P t) ≤ Real.log (m + 1) := by
  exact (information_sum_le_entropy w P n).trans (by simpa using entropy_le_log_card w)


lemma conditionalInformation_nonneg {ι : Type*} [Fintype ι]
    (w : Distribution ι) (P : ι → SequentialLaw α) (n : ℕ) :
    0 ≤ conditionalInformation w P n := by
  apply sum_nonneg
  intro h _
  exact mul_nonneg ((mixture w (fun i => block (P i) n)).nonneg h)
    (mutualInformation_nonneg _ _)

/-- Omitting the first information increment preserves the entropy budget. -/
theorem information_tail_sum_le_entropy {ι : Type*} [Fintype ι]
    (w : Distribution ι) (P : ι → SequentialLaw α) (n : ℕ) :
    (∑ t ∈ range n, conditionalInformation w P (t + 1)) ≤ entropy w := by
  have h := information_sum_le_entropy w P (n + 1)
  rw [sum_range_succ'] at h
  have h0 := conditionalInformation_nonneg w P 0
  linarith

/-- The `log (n + 2)` memory budget in (D.2), for an actual latent state with
`n + 2` values and its normalized conditional sequential law. -/
theorem countdown_memory_tail_bound (n : ℕ) (w : Distribution (Fin (n + 2)))
    (P : Fin (n + 2) → SequentialLaw α) :
    (∑ t ∈ range n, conditionalInformation w P (t + 1)) ≤ Real.log (n + 2) :=
  (information_tail_sum_le_entropy w P n).trans (by simpa using entropy_le_log_card w)

end SequentialLaw
end Paper37.Compression
