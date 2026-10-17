import Paper12.OneHotAmplify

noncomputable section
namespace Paper12
open Matrix Classical
variable {J : Type*} [Fintype J]

theorem Threshold.apply_eq (g : Threshold J) (ψ : Vec J) (b : Basis J) :
    applyOp g.unitary ψ b = ψ (g.act b) := by
  exact apply_involutive_matrix _ g.act_involutive ψ b

def flipThreshold (x : J) : Threshold J := ⟨x, ∅, 0, by simp⟩

theorem pmatX_entry (a b : Fin 2) : pmat .X a b = if a = 1 - b then (1 : ℂ) else 0 := by
  fin_cases a <;> fin_cases b <;> simp [pmat]

theorem flipThreshold_unitary (x : J) :
    (flipThreshold x).unitary = (Gate.one (⟨x, pmat .X, pmat_unitary .X⟩ : OneQubit J)).unitary := by
  ext i j
  have ha : Function.update j x (1 - j x) = i ↔
      (∀ w, w ≠ x → i w = j w) ∧ i x = 1 - j x := by
    constructor
    · intro h
      constructor
      · intro w hw
        have hh := congrFun h w
        simpa [hw] using hh.symm
      · have hh := congrFun h x
        simpa using hh.symm
    · rintro ⟨hoff, hx⟩
      funext w
      by_cases hw : w = x
      · subst w; simpa using hx.symm
      · simp [hw, (hoff w hw).symm]
  simp only [Threshold.unitary, Threshold.act, flipThreshold, Matrix.of_apply,
    Finset.sum_empty, Nat.le_refl, ite_true, Gate.unitary, OneQubit.unitary]
  simp only [ha, pmatX_entry]
  by_cases hoff : ∀ w, w ≠ x → i w = j w <;>
    by_cases hx : i x = 1 - j x <;> simp [hoff, hx]

theorem oneQubitX_apply (x : J) (ψ : Vec J) (b : Basis J) :
    applyOp (Gate.one (⟨x, pmat .X, pmat_unitary .X⟩ : OneQubit J)).unitary ψ b =
      ψ (Function.update b x (1 - b x)) := by
  rw [← flipThreshold_unitary, Threshold.apply_eq]
  simp [flipThreshold, Threshold.act]

section CNOT
variable {Q X : Type*} [Fintype Q] [Fintype X]
local instance : DecidableEq (X ⊕ Q) := Classical.decEq _

def cnotThreshold (q : Q) (x : X) : Threshold (X ⊕ Q) where
  head := Sum.inl x
  controls := {Sum.inr q}
  threshold := 1
  head_not := by simp

theorem cnot_act (q : Q) (x : X) (b : Basis (X ⊕ Q)) :
    (cnotThreshold q x).act b =
      if b (Sum.inr q) = 1 then Function.update b (Sum.inl x) (1 - b (Sum.inl x)) else b := by
  have hp : (1 ≤ (b (Sum.inr q) : ℕ)) ↔ b (Sum.inr q) = 1 := by
    have hlt := (b (Sum.inr q)).isLt
    omega
  simp only [Threshold.act, cnotThreshold, Finset.sum_singleton, hp]

theorem cnot_control (q r : Q) (x : X) (b : Basis (X ⊕ Q)) :
    (cnotThreshold q x).act b (Sum.inr r) = b (Sum.inr r) := by
  rw [cnot_act]
  split_ifs <;> simp

theorem cnot_act_commute (q r : Q) (x y : X) (b : Basis (X ⊕ Q)) :
    (cnotThreshold q x).act ((cnotThreshold r y).act b) =
      (cnotThreshold r y).act ((cnotThreshold q x).act b) := by
  by_cases hq : b (Sum.inr q) = 1 <;> by_cases hr : b (Sum.inr r) = 1
  all_goals
    by_cases hxy : x = y
    · subst y
      funext z
      by_cases hz : z = Sum.inl x
      · subst z; simp [cnot_act, hq, hr]
      · simp [cnot_act, hq, hr, hz]
    · have hn : (Sum.inl x : X ⊕ Q) ≠ Sum.inl y := fun h => hxy (Sum.inl.inj h)
      funext z
      by_cases hz : z = Sum.inl x
      · subst z; simp [cnot_act, hq, hr, hn, hn.symm]
      · by_cases hzy : z = Sum.inl y
        · subst z; simp [cnot_act, hq, hr, hn, hn.symm]
        · simp [cnot_act, hq, hr, hz, hzy]

theorem cnot_unitary_commute (q r : Q) (x y : X) :
    (cnotThreshold q x).unitary * (cnotThreshold r y).unitary =
      (cnotThreshold r y).unitary * (cnotThreshold q x).unitary := by
  apply matrix_eq_of_apply
  intro ψ
  rw [applyOp_mul, applyOp_mul]
  funext b
  simp only [Threshold.apply_eq]
  rw [cnot_act_commute]
end CNOT
end Paper12
