import Paper36.FinitePolicies
import Paper36.FiniteStages
import Paper36.Algorithm

/-! Finite known cost/reward tables. Total natural-stage indexing introduces
no hypothesis on unused stages: any valid source table is padded by zero, and
all finite-horizon risks, rewards, minima and constrained values are invariant. -/
namespace Paper36.FiniteData
open Paper36.Regularity Paper36.Nested
noncomputable section
variable {S A : Type*} [Fintype S] [Fintype A]

def extend {H : ℕ} (f : Fin H → S → A → ℝ) (h : ℕ) (s : S) (a : A) : ℝ :=
  if hh : h < H then f ⟨h,hh⟩ s a else 0

lemma extend_valid {H : ℕ} (f : Fin H → S → A → ℝ)
    (hf : ∀ h s a, f h s a ∈ Set.Icc 0 1) :
    ∀ h s a, extend f h s a ∈ Set.Icc 0 1 := by
  intro h s a
  unfold extend
  split_ifs
  · exact hf _ s a
  · exact ⟨le_rfl, by norm_num⟩

lemma extend_at {H : ℕ} (f : Fin H → S → A → ℝ) (h : Fin H) :
    extend f h.val = f h := by
  funext s a
  simp only [extend, dif_pos h.isLt]

lemma risk_data_congr (α : ℝ) (c d : ℕ → S → A → ℝ)
    (π : Policy S A) (q : Kernel S A) (n h : ℕ) (s : S)
    (hcd : ∀ j, h ≤ j → j < h+n → c j = d j) :
    risk α c π q n h s = risk α d π q n h s := by
  induction n generalizing h s with
  | zero => rfl
  | succ n ih =>
    rw [risk, risk, hcd h le_rfl (by omega)]
    congr 1
    funext x
    rw [ih (h+1) x.2 (fun j hj hj' => hcd j (by omega) (by omega))]

lemma reward_data_congr (r t : ℕ → S → A → ℝ)
    (π : Policy S A) (q : Kernel S A) (n h : ℕ) (s : S)
    (hrt : ∀ j, h ≤ j → j < h+n → r j = t j) :
    reward r π q n h s = reward t π q n h s := by
  induction n generalizing h s with
  | zero => rfl
  | succ n ih =>
    rw [reward, reward, hrt h le_rfl (by omega)]
    apply Finset.sum_congr rfl
    intro a _
    congr 2
    apply Finset.sum_congr rfl
    intro u _
    rw [ih (h+1) u (fun j hj hj' => hrt j (by omega) (by omega))]

lemma stageRisk_data_congr (β : ℕ → ℝ) (c d : ℕ → S → A → ℝ)
    (π : Simulation.Policy S A) (q : Simulation.Kernel S A) (n h : ℕ) (s : S)
    (hcd : ∀ j, h ≤ j → j < h+n → c j = d j) :
    StageRisk.risk β c π q n h s = StageRisk.risk β d π q n h s := by
  induction n generalizing h s with
  | zero => rfl
  | succ n ih =>
    rw [StageRisk.risk, StageRisk.risk, hcd h le_rfl (by omega)]
    congr 1
    funext x
    rw [ih (h+1) x.2 (fun j hj hj' => hcd j (by omega) (by omega))]

/-- Exactly the finite source table determines both value recursions. -/
theorem finite_data_representation {H : ℕ} (c r : Fin H → S → A → ℝ)
    (c' r' : ℕ → S → A → ℝ)
    (hc : ∀ h : Fin H, c' h.val = c h) (hr : ∀ h : Fin H, r' h.val = r h)
    (α : ℝ) (π : Policy S A) (q : Kernel S A) (s : S) :
    risk α c' π q H 0 s = risk α (extend c) π q H 0 s ∧
      reward r' π q H 0 s = reward (extend r) π q H 0 s := by
  have hec : ∀ j, 0 ≤ j → j < 0+H → c' j = extend c j := by
    intro j _ hj
    have hJ : j < H := by omega
    rw [hc ⟨j,hJ⟩, extend_at c ⟨j,hJ⟩]
  have her : ∀ j, 0 ≤ j → j < 0+H → r' j = extend r j := by
    intro j _ hj
    have hJ : j < H := by omega
    rw [hr ⟨j,hJ⟩, extend_at r ⟨j,hJ⟩]
  exact ⟨risk_data_congr α c' (extend c) π q H 0 s hec,
    reward_data_congr r' (extend r) π q H 0 s her⟩

/-- Minima and the actual constrained comparator use no hidden future rows. -/
theorem planning_data_congr (α τ : ℝ) (c d r t : ℕ → S → A → ℝ)
    (H : ℕ) (s : S) (q : Kernel S A)
    (hcd : ∀ j, 0 ≤ j → j < 0+H → c j = d j)
    (hrt : ∀ j, 0 ≤ j → j < 0+H → r j = t j) :
    minimumRisk α c H 0 s q = minimumRisk α d H 0 s q ∧
      Algorithm.constrainedValue α c r H s τ q = Algorithm.constrainedValue α d t H s τ q := by
  have hR (π : Policy S A) : risk α c π q H 0 s = risk α d π q H 0 s :=
    risk_data_congr α c d π q H 0 s hcd
  have hV (π : Policy S A) : reward r π q H 0 s = reward t π q H 0 s :=
    reward_data_congr r t π q H 0 s hrt
  constructor
  · unfold minimumRisk
    apply congrArg sInf
    apply congrArg (fun f : Policy S A → ℝ => f '' Set.univ)
    exact funext hR
  · unfold Algorithm.constrainedValue
    apply congrArg sSup
    apply Set.ext
    intro v
    change (∃ π : Policy S A, risk α c π q H 0 s ≤ τ ∧ reward r π q H 0 s = v) ↔
      (∃ π : Policy S A, risk α d π q H 0 s ≤ τ ∧ reward t π q H 0 s = v)
    simp_rw [hR, hV]

end
end Paper36.FiniteData
