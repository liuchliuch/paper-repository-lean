import Paper02.EnumeratingDecoder

/-! # Operational base-digit loading of compact candidates

The candidate counter is divided by the base one digit at a time. The running
quotient, position and K output slots are the complete live state.
-/
noncomputable section

namespace Paper02.CandidateLoader

structure State (A : Type*) (K b : ℕ) where
  quotient : Fin (b ^ K + 1)
  position : Fin (K + 1)
  cells : Fin K → A
  deriving Fintype

variable {A : Type*} {K b : ℕ}

def step (hb : 0 < b) (decode : Fin b → A) (s : State A K b) : State A K b :=
  if hj : s.position.val < K then
    { quotient := ⟨s.quotient.val / b,
        lt_of_le_of_lt (Nat.div_le_self _ _) s.quotient.isLt⟩
      position := ⟨s.position.val + 1, by omega⟩
      cells := Function.update s.cells ⟨s.position.val, hj⟩
        (decode ⟨s.quotient.val % b, Nat.mod_lt _ hb⟩) }
  else s

def digits (hb : 0 < b) (decode : Fin b → A) (n : ℕ) : Fin K → A :=
  fun j => decode ⟨(n / b ^ j.val) % b, Nat.mod_lt _ hb⟩

def expected (hb : 0 < b) (decode : Fin b → A) (default : A)
    (n : Fin (b ^ K)) (j : ℕ) (hj : j ≤ K) : State A K b where
  quotient := ⟨n.val / b ^ j, lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)⟩
  position := ⟨j, by omega⟩
  cells := fun i => if i.val < j then digits hb decode n.val i else default

/-- One base-digit transition implements one slot of the closed form. -/
lemma step_expected (hb : 0 < b) (decode : Fin b → A) (default : A)
    (n : Fin (b ^ K)) (j : ℕ) (hj : j < K) :
    step hb decode (expected hb decode default n j hj.le) =
      expected hb decode default n (j + 1) (by omega) := by
  unfold step expected
  simp only [dif_pos hj]
  congr 1
  · apply Fin.ext
    simp only
    rw [Nat.div_div_eq_div_mul, pow_succ]
  · funext i
    by_cases hi : i.val = j
    · have he : i = ⟨j, hj⟩ := Fin.ext (by dsimp only; omega)
      subst i
      simp [digits]
    · have he : i ≠ ⟨j, hj⟩ := fun h => hi (congrArg Fin.val h)
      rw [Function.update_of_ne he]
      have ht : (i.val < j + 1) = (i.val < j) := propext (by omega)
      simp only [ht]

/-- All candidate slots are reached by actual quotient/remainder transitions. -/
theorem loader_reaches (hb : 0 < b) (decode : Fin b → A) (default : A)
    (n : Fin (b ^ K)) (j : ℕ) (hj : j ≤ K) :
    Relation.ReflTransGen (fun x y => step hb decode x = y)
      (expected hb decode default n 0 (by omega))
      (expected hb decode default n j hj) := by
  induction j with
  | zero => exact Relation.ReflTransGen.refl
  | succ j ih =>
    have hj' : j < K := by omega
    exact (ih hj'.le).tail (step_expected hb decode default n j hj')

/-- A loaded code is exactly the arithmetic digit decoding of the counter. -/
theorem loader_correct (hb : 0 < b) (decode : Fin b → A) (default : A)
    (n : Fin (b ^ K)) :
    let finish := expected hb decode default n K (le_refl _)
    Relation.ReflTransGen (fun x y => step hb decode x = y)
      (expected hb decode default n 0 (by omega)) finish ∧
      step hb decode finish = finish ∧ finish.cells = digits hb decode n.val := by
  dsimp only
  refine ⟨loader_reaches hb decode default n K (le_refl _), ?_, ?_⟩
  · simp [step, expected]
  · funext i
    simp [expected, i.isLt]

/-- Exact storage of all running registers, including the loaded code. -/
theorem loader_card [Fintype A] :
    Fintype.card (State A K b) = (b ^ K + 1) * (K + 1) * Fintype.card A ^ K := by
  let e : State A K b ≃ Fin (b ^ K + 1) × Fin (K + 1) × (Fin K → A) :=
    { toFun := fun s => (s.quotient, s.position, s.cells)
      invFun := fun s => ⟨s.1, s.2.1, s.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e]
  simp [Fintype.card_prod, Fintype.card_fun, Nat.mul_assoc]

end Paper02.CandidateLoader
