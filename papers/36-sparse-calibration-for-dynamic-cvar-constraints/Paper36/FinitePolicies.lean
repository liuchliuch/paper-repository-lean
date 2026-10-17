import Paper36.Nested

/-! Exact finite-horizon policy quantifiers. The infinite row family used for
convenient absolute-stage recursion has exactly the same horizon-H behaviors
as the source's product over Fin H and physical states. -/
namespace Paper36.FinitePolicies
open Paper36.Regularity Paper36.Nested
noncomputable section
variable {S A : Type*} [Fintype S] [Fintype A]

abbrev FinitePolicy (S A : Type*) [Fintype A] (H : ℕ) := Fin H → S → Law A

def restrict (H : ℕ) (π : Policy S A) : FinitePolicy S A H := fun h => π h.val

def extend [Nonempty A] {H : ℕ} (π : FinitePolicy S A H) : Policy S A :=
  fun h s => if hh : h < H then π ⟨h,hh⟩ s else Nested.pure (Classical.arbitrary A)

lemma risk_congr_window (α : ℝ) (c : ℕ → S → A → ℝ) (q : Kernel S A)
    (π π' : Policy S A) (n h : ℕ)
    (heq : ∀ j, h ≤ j → j < h+n → π j = π' j) (s : S) :
    risk α c π q n h s = risk α c π' q n h s := by
  induction n generalizing h s with
  | zero => rfl
  | succ n ih =>
    rw [risk, risk, heq h le_rfl (by omega)]
    congr 1
    funext x
    rw [ih (h+1) (fun j hj hj' => heq j (by omega) (by omega)) x.2]

lemma reward_congr_window (r : ℕ → S → A → ℝ) (q : Kernel S A)
    (π π' : Policy S A) (n h : ℕ)
    (heq : ∀ j, h ≤ j → j < h+n → π j = π' j) (s : S) :
    reward r π q n h s = reward r π' q n h s := by
  induction n generalizing h s with
  | zero => rfl
  | succ n ih =>
    rw [reward, reward, heq h le_rfl (by omega)]
    congr 1
    funext a
    congr 2
    apply Finset.sum_congr rfl
    intro t _
    rw [ih (h+1) (fun j hj hj' => heq j (by omega) (by omega)) t]

/-- Extending a finite policy does not alter any of its H source action rows. -/
lemma extend_apply [Nonempty A] {H : ℕ} (π : FinitePolicy S A H) (h : Fin H) (s : S) :
    extend π h.val s = π h s := by simp [extend, h.isLt]

/-- Every row family has a finite source policy with exactly its risk and reward. -/
theorem finite_horizon_equivalence [Nonempty A] (α : ℝ)
    (c r : ℕ → S → A → ℝ) (q : Kernel S A) (π : Policy S A) (H : ℕ) (s : S) :
    risk α c (extend (restrict H π)) q H 0 s = risk α c π q H 0 s ∧
      reward r (extend (restrict H π)) q H 0 s = reward r π q H 0 s := by
  have heq : ∀ j, 0 ≤ j → j < 0+H → extend (restrict H π) j = π j := by
    intro j _ hj
    funext t
    simp [extend, (show j < H by omega), restrict]
  exact ⟨risk_congr_window α c q _ _ H 0 heq s,
    reward_congr_window r q _ _ H 0 heq s⟩

end
end Paper36.FinitePolicies
