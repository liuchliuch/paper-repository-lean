import Paper15.ExactChecker

/-! # Compositional rules for kernel-checked certificate compilation -/
namespace Paper15.Exact

def fin3 (n : Nat) : Fin 3 := ⟨n%3, by omega⟩
def fin27 (n : Nat) : Fin 27 := ⟨n%27, by omega⟩

/-- Composing accepted children requires only the local edge check. -/
theorem valid_split (c : Cell) (a i j : Fin 3) (l r : Trace)
    (hij : decide (i ≠ j) = true)
    (hl : valid (child c a i j) l = true) (hr : valid (child c a j i) r = true) :
    valid c (.split a i j l r) = true := by
  simp only [valid, hij, hl, hr, Bool.and_true]

/-- A supplied checkpoint is used only after equality to the computed cell. -/
theorem valid_checkpoint (computed claimed : Cell) (t : Trace)
    (heq : computed = claimed) (ht : valid claimed t = true) :
    valid computed (.checkpoint claimed t) = true := by
  subst claimed
  simp only [valid, decide_true, ht, Bool.and_true]

def AllVerified : List (Nat × Trace) → Prop
  | [] => True
  | p :: ps => verified p = true ∧ AllVerified ps

end Paper15.Exact
