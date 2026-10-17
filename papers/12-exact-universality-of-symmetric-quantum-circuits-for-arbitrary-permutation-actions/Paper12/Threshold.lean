import Paper12.CircuitTools

/-! Reversible threshold semantics and equality expansion (paper equation (2)). -/
noncomputable section
namespace Paper12
open Matrix Complex Classical
variable {J : Type*}

theorem Threshold.act_control (g : Threshold J) (b : Basis J) {x : J}
    (hx : x ∈ g.controls) : g.act b x = b x := by
  have hne : x ≠ g.head := fun h => g.head_not (h ▸ hx)
  simp only [Threshold.act]
  split_ifs <;> simp [hne]

theorem Threshold.act_weight (g : Threshold J) (b : Basis J) :
    (∑ x ∈ g.controls, (g.act b x : ℕ)) = ∑ x ∈ g.controls, (b x : ℕ) := by
  apply Finset.sum_congr rfl
  intro x hx
  rw [g.act_control b hx]

@[simp] theorem bitFlip_involutive (b : Fin 2) : 1 - (1 - b) = b := by
  fin_cases b <;> decide

theorem Threshold.act_involutive (g : Threshold J) : Function.Involutive g.act := by
  intro b
  unfold Threshold.act
  have hweight := g.act_weight b
  unfold Threshold.act at hweight
  rw [hweight]
  by_cases h : g.threshold ≤ ∑ x ∈ g.controls, (b x : ℕ)
  · simp only [if_pos h]
    funext x
    by_cases hx : x = g.head
    · subst x; simp
    · simp [hx]
  · simp [h]

theorem Threshold.adjoint_eq [Fintype J] (g : Threshold J) : g.unitaryᴴ = g.unitary := by
  ext i j
  have hiff : g.act i = j ↔ g.act j = i := by
    constructor <;> intro h
    · rw [← h, g.act_involutive i]
    · rw [← h, g.act_involutive j]
  simp only [Threshold.unitary, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : g.act i = j
  · simp [h, hiff.mp h]
  · have hn : g.act j ≠ i := fun hh => h (hiff.mpr hh)
    simp [h, hn]

theorem Threshold.isUnitary [Fintype J] (g : Threshold J) : g.unitaryᴴ * g.unitary = 1 := by
  rw [g.adjoint_eq]
  ext i j
  simp only [Matrix.mul_apply, Threshold.unitary, Matrix.of_apply]
  rw [Finset.sum_eq_single (g.act j)]
  · rw [if_pos rfl, mul_one, g.act_involutive j, Matrix.one_apply]
    simp [eq_comm]
  · intro b _ hb
    rw [if_neg (Ne.symm hb), mul_zero]
  · intro hb
    exact (hb (Finset.mem_univ _)).elim

/-- Equality is a semantic abbreviation, not an additional primitive gate. -/
def equalityAct (g : Threshold J) (b : Basis J) : Basis J :=
  if (∑ x ∈ g.controls, (b x : ℕ)) = g.threshold then
    Function.update b g.head (1 - b g.head) else b

def nextThreshold (g : Threshold J) : Threshold J := {g with threshold := g.threshold + 1}

theorem equalityAct_expansion (g : Threshold J) (b : Basis J) :
    g.act ((nextThreshold g).act b) = equalityAct g b := by
  have hw := (nextThreshold g).act_weight b
  change (∑ x ∈ g.controls, ((nextThreshold g).act b x : ℕ)) = _ at hw
  change (if (∑ x ∈ g.controls, ((nextThreshold g).act b x : ℕ)) ≥ g.threshold then
    Function.update ((nextThreshold g).act b) g.head
      (1 - (nextThreshold g).act b g.head) else (nextThreshold g).act b) = _
  rw [hw]
  unfold nextThreshold equalityAct Threshold.act
  change (if (∑ x ∈ g.controls, (b x : ℕ)) ≥ g.threshold then
    Function.update
      (if (∑ x ∈ g.controls, (b x : ℕ)) ≥ g.threshold + 1 then
        Function.update b g.head (1 - b g.head) else b) g.head
      (1 - (if (∑ x ∈ g.controls, (b x : ℕ)) ≥ g.threshold + 1 then
        Function.update b g.head (1 - b g.head) else b) g.head)
    else (if (∑ x ∈ g.controls, (b x : ℕ)) ≥ g.threshold + 1 then
        Function.update b g.head (1 - b g.head) else b)) = _
  by_cases hlt : (∑ x ∈ g.controls, (b x : ℕ)) < g.threshold
  · have h1 : ¬g.threshold ≤ ∑ x ∈ g.controls, (b x : ℕ) := by omega
    have h2 : ¬g.threshold + 1 ≤ ∑ x ∈ g.controls, (b x : ℕ) := by omega
    have he : (∑ x ∈ g.controls, (b x : ℕ)) ≠ g.threshold := by omega
    simp [h1, h2, he]
  · by_cases he : (∑ x ∈ g.controls, (b x : ℕ)) = g.threshold
    · have h1 : g.threshold ≤ ∑ x ∈ g.controls, (b x : ℕ) := by omega
      have h2 : ¬g.threshold + 1 ≤ ∑ x ∈ g.controls, (b x : ℕ) := by omega
      simp [h1, h2, he]
    · have h1 : g.threshold ≤ ∑ x ∈ g.controls, (b x : ℕ) := by omega
      have h2 : g.threshold + 1 ≤ ∑ x ∈ g.controls, (b x : ℕ) := by omega
      simp only [h1, h2, he, if_pos, if_false]
      funext x
      by_cases hx : x = g.head
      · subst x; simp
      · simp [hx]

/-- Equation (2), as equality of operators on every computational basis input. -/
theorem equality_unitary_expansion [Fintype J] (g : Threshold J) :
    g.unitary * (nextThreshold g).unitary =
      (fun i j : Basis J => if equalityAct g j = i then (1 : ℂ) else 0) := by
  ext i j
  simp only [Matrix.mul_apply, Threshold.unitary, Matrix.of_apply]
  rw [Finset.sum_eq_single ((nextThreshold g).act j)]
  · rw [if_pos rfl, mul_one, equalityAct_expansion]
  · intro b _ hb
    rw [if_neg (Ne.symm hb), mul_zero]
  · intro hb
    exact (hb (Finset.mem_univ _)).elim
end Paper12
