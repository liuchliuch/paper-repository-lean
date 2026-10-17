import GeometricMedianCoresets.BernoulliAffinity

/-! Symmetry of the fair product law and the perturbed majority probability. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace GeometricMedianCoresets.FiniteLaw

def trueCount {m : ℕ} (w : Fin m → Bool) : ℕ := (Finset.univ.filter (fun i => w i = true)).card
def majority {m : ℕ} (w : Fin m → Bool) : Prop := m ≤ 2 * trueCount w

def flipEquiv (m : ℕ) : (Fin m → Bool) ≃ (Fin m → Bool) where
  toFun w := fun i => !(w i)
  invFun w := fun i => !(w i)
  left_inv w := by funext i; simp
  right_inv w := by funext i; simp

lemma trueCount_flip {m : ℕ} (w : Fin m → Bool) :
    trueCount w + trueCount (flipEquiv m w) = m := by
  have hcard := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin m))) (fun i => w i = true)
  have heq : (Finset.univ.filter (fun i => ¬ w i = true)) =
      Finset.univ.filter (fun i => (flipEquiv m w) i = true) := by
    ext i
    simp [flipEquiv]
  unfold trueCount
  simpa only [heq, Finset.card_univ, Fintype.card_fin] using hcard

lemma fairProduct_const (m : ℕ) (w : Fin m → Bool) : bernProduct m (1/2) w = (1/2:ℝ) ^ m := by
  unfold bernProduct
  have heq : ∀ i : Fin m, bern (1/2:ℝ) (w i) = 1/2 := by
    intro i
    cases w i <;> norm_num [bern]
  simp_rw [heq]
  simp

/-- Fair Bernoulli majority has probability at least one half, including even sample sizes. -/
theorem fair_majority (m : ℕ) : event (bernProduct m (1/2)) majority ≥ 1/2 := by
  have hsym : event (bernProduct m (1/2)) (fun w => majority (flipEquiv m w)) =
      event (bernProduct m (1/2)) majority := by
    unfold event
    simp only [fairProduct_const]
    simpa only [Finset.sum_ite, Finset.sum_const_zero, add_zero] using
      (flipEquiv m).sum_comp (fun w => if majority w then (1/2:ℝ)^m else 0)
  have hpoint : ∀ w : Fin m → Bool,
      bernProduct m (1/2) w ≤ (if majority w then bernProduct m (1/2) w else 0) +
        (if majority (flipEquiv m w) then bernProduct m (1/2) w else 0) := by
    intro w
    have hor : majority w ∨ majority (flipEquiv m w) := by
      have hc := trueCount_flip w
      unfold majority
      omega
    have hnonneg := bernProduct_nonneg (p := (1/2:ℝ)) (by norm_num) (by norm_num) m w
    rcases hor with h | h <;> simp only [h, if_true] <;> split_ifs <;> linarith
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun w _ => hpoint w)
  rw [bernProduct_sum, Finset.sum_add_distrib] at hs
  have h1 : (∑ w : Fin m → Bool, if majority w then bernProduct m (1/2) w else 0) =
      event (bernProduct m (1/2)) majority := by simp [event, Finset.sum_ite]
  have h2 : (∑ w : Fin m → Bool, if majority (flipEquiv m w) then bernProduct m (1/2) w else 0) =
      event (bernProduct m (1/2)) (fun w => majority (flipEquiv m w)) := by
    simp [event, Finset.sum_ite]
  rw [h1, h2, hsym] at hs
  linarith

/-- The biased counting event retains probability at least `9/20`. -/
theorem biased_majority {m : ℕ} {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (hmθ : (m:ℝ) * θ ^ 2 ≤ 1/200) :
    event (bernProduct m ((1 - θ) / 2)) majority ≥ 9/20 := by
  have htv := bernProduct_tv_bound m hθ hθ'
  have hsqrt : Real.sqrt ((m:ℝ) * θ ^ 2 / 2) ≤ 1/20 := by
    apply (Real.sqrt_le_iff).2
    constructor <;> nlinarith
  have he := event_sub_le_tv (bernProduct m ((1 - θ) / 2)) (bernProduct m (1/2))
    (by rw [bernProduct_sum, bernProduct_sum]) majority
  have hf := fair_majority m
  have hlo := (abs_le.1 he).1
  linarith

end GeometricMedianCoresets.FiniteLaw
