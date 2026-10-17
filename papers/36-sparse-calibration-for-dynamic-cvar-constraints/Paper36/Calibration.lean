import Paper36.Nested

/-! Minimum-risk dynamic programming over the source's randomized Markov class. -/
namespace Paper36.Calibration
open Set Finset Paper36.Regularity Paper36.Nested
noncomputable section
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

private def argmin (f : A → ℝ) : A := Classical.choose (Finite.exists_min f)
private lemma argmin_le (f : A → ℝ) (a : A) : f (argmin f) ≤ f a :=
  Classical.choose_spec (Finite.exists_min f) a

/-- The exact minimum-over-actions backward recursion (4.6). -/
def dp (α : ℝ) (c : ℕ → S → A → ℝ) (q : Kernel S A) : ℕ → ℕ → S → ℝ
  | 0, _, _ => 0
  | n+1, h, s =>
    let row := fun a => compactCVaR α (n+1 : ℕ) (q s a)
      (fun t => c h s a + dp α c q n (h+1) t)
    row (argmin row)

lemma dp_le_row (α : ℝ) (c : ℕ → S → A → ℝ) (q : Kernel S A)
    (n h : ℕ) (s : S) (a : A) :
    dp α c q (n+1) h s ≤ compactCVaR α (n+1 : ℕ) (q s a)
      (fun t => c h s a + dp α c q n (h+1) t) := by
  rw [dp]
  exact argmin_le (fun a => compactCVaR α (n+1 : ℕ) (q s a)
    (fun t => c h s a + dp α c q n (h+1) t)) a

/-- Randomizing the current action cannot improve minimum nested risk. -/
theorem dp_le_risk (α : ℝ) (hα : 0 ≤ α) (c : ℕ → S → A → ℝ)
    (q : Kernel S A) (π : Policy S A) (n h : ℕ) (s : S) :
    dp α c q n h s ≤ risk α c π q n h s := by
  induction n generalizing h s with
  | zero => exact le_rfl
  | succ n ih =>
    have hlow := compactCVaR_joint_lower α (n+1 : ℕ) (by positivity)
      (π h s) (q s) (fun a t => c h s a + dp α c q n (h+1) t)
      (dp α c q (n+1) h s) (fun a => dp_le_row α c q n h s a)
    have hmono := compactCVaR_mono α (n+1 : ℕ) hα (by positivity)
      (joint (π h s) (q s))
      (X := fun x : A × S => c h s x.1 + dp α c q n (h+1) x.2)
      (Y := fun x : A × S => c h s x.1 + risk α c π q n (h+1) x.2)
      (fun x => add_le_add_left (ih (h+1) x.2) _)
    exact hlow.trans hmono

def Deterministic (π : Policy S A) : Prop := ∀ h s, ∃ a, π h s = Nested.pure a

/-- One deterministic Markov tail policy attains the recursion simultaneously at every state. -/
theorem exists_deterministic_minimizer (α : ℝ) (c : ℕ → S → A → ℝ)
    (q : Kernel S A) (n h : ℕ) :
    ∃ π : Policy S A, Deterministic π ∧ ∀ s, risk α c π q n h s = dp α c q n h s := by
  classical
  induction n generalizing h with
  | zero =>
    refine ⟨fun _ _ => Nested.pure (Classical.arbitrary A), ?_, fun _ => rfl⟩
    intro _ _
    exact ⟨_, rfl⟩
  | succ n ih =>
    obtain ⟨tail, hdet, hatt⟩ := ih (h+1)
    let greedy : S → A := fun s => argmin (fun a => compactCVaR α (n+1 : ℕ) (q s a)
      (fun t => c h s a + dp α c q n (h+1) t))
    let π : Policy S A := fun j s => if j = h then Nested.pure (greedy s) else tail j s
    have htail : ∀ s, risk α c π q n (h+1) s = dp α c q n (h+1) s := by
      intro s
      rw [risk_congr α c q π tail n (h+1) (fun j hj => ?_) s, hatt s]
      funext t
      simp only [π, if_neg (show j ≠ h by omega)]
    refine ⟨π, ?_, ?_⟩
    · intro j s
      by_cases hj : j = h
      · exact ⟨greedy s, by simp [π, hj]⟩
      · obtain ⟨a, ha⟩ := hdet j s
        exact ⟨a, by simpa [π, hj] using ha⟩
    · intro s
      rw [risk]
      have hπ : π h s = Nested.pure (greedy s) := by simp only [π, if_pos rfl]
      rw [hπ]
      have hx : (fun x : A × S => c h s x.1 + risk α c π q n (h+1) x.2) =
          (fun x : A × S => c h s x.1 + dp α c q n (h+1) x.2) := by
        funext x
        rw [htail]
      rw [hx]
      rw [compactCVaR_joint_pure α (n+1 : ℕ) (greedy s) (q s)
        (fun a t => c h s a + dp α c q n (h+1) t)]
      rfl

/-- Proposition 4.1, semantic part: the recursion equals the minimum over all randomized tails. -/
theorem minimumRisk_eq_dp (α : ℝ) (hα : 0 ≤ α) (c : ℕ → S → A → ℝ)
    (q : Kernel S A) (n h : ℕ) (s : S) :
    minimumRisk α c n h s q = dp α c q n h s := by
  obtain ⟨π, hdet, hatt⟩ := exists_deterministic_minimizer α c q n h
  have hb : BddBelow ((fun π : Policy S A => risk α c π q n h s) '' univ) := by
    refine ⟨dp α c q n h s, ?_⟩
    rintro _ ⟨π', _, rfl⟩
    exact dp_le_risk α hα c q π' n h s
  apply le_antisymm
  · calc
      _ ≤ risk α c π q n h s := csInf_le hb ⟨π, mem_univ _, rfl⟩
      _ = _ := hatt s
  · change dp α c q n h s ≤ sInf ((fun π : Policy S A => risk α c π q n h s) '' univ)
    have hne : ((fun π : Policy S A => risk α c π q n h s) '' univ).Nonempty :=
      ⟨risk α c π q n h s, ⟨π, mem_univ _, rfl⟩⟩
    apply le_csInf hne
    rintro _ ⟨π', _, rfl⟩
    exact dp_le_risk α hα c q π' n h s

end
end Paper36.Calibration
