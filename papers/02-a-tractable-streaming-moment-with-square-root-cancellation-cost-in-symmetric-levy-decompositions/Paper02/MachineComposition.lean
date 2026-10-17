import Mathlib.Tactic

/-! An actual finite-register outer search. It runs each candidate's microcode
until completion; only then does it advance the numeric candidate counter. -/

namespace Paper02.MachineComposition

structure State (N : ℕ) (C : Type*) where
  index : Fin (N + 1)
  micro : C
  accepted : Bool
  deriving Fintype

variable {N : ℕ} {C : Type*}

def start (init : Fin N → C) (defaultState : C) (n : ℕ) (hn : n ≤ N) : State N C :=
  ⟨⟨n, by omega⟩, if h : n < N then init ⟨n, h⟩ else defaultState, false⟩

def step (init : Fin N → C) (defaultState : C)
    (microStep : Fin N → C → C) (done accept : C → Bool) (s : State N C) : State N C :=
  if s.accepted then s else
    if h : s.index.val < N then
      if done s.micro then
        if accept s.micro then { s with accepted := true }
        else start init defaultState (s.index.val + 1) (by omega)
      else { s with micro := microStep ⟨s.index.val, h⟩ s.micro }
    else s

abbrev Reaches (init : Fin N → C) (defaultState : C)
    (microStep : Fin N → C → C) (done accept : C → Bool) :=
  Relation.ReflTransGen (fun a b => step init defaultState microStep done accept a = b)

variable (init : Fin N → C) (defaultState : C)
  (microStep : Fin N → C → C) (done accept : C → Bool)
  (fixed : ∀ i x, done x = true → microStep i x = x)

include fixed

/-- Every inner microstep is an outer microstep. An already terminal inner
self-loop needs zero outer steps, so terminal tests are not performed early. -/
theorem lift_micro (i : Fin N) {x y : C}
    (h : Relation.ReflTransGen (fun a b => microStep i a = b) x y) :
    Reaches init defaultState microStep done accept
      ⟨⟨i.val, by omega⟩, x, false⟩ ⟨⟨i.val, by omega⟩, y, false⟩ := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hbc hstep ih =>
    cases hd : done b with
    | false =>
      apply ih.tail
      simp [step, i.isLt, hd, hstep]
    | true =>
      have he : c = b := hstep.symm.trans (fixed i b hd)
      rw [he]
      exact ih

variable (terminal : Fin N → C)
  (runs : ∀ i, Relation.ReflTransGen (fun a b => microStep i a = b) (init i) (terminal i))
  (finished : ∀ i, done (terminal i) = true)

include runs finished

lemma reaches_next (i : Fin N) (hi : accept (terminal i) = false) :
    Reaches init defaultState microStep done accept
      (start init defaultState i.val i.isLt.le)
      (start init defaultState (i.val + 1) (by omega)) := by
  have hr := lift_micro init defaultState microStep done accept fixed i (runs i)
  have hs : start init defaultState i.val i.isLt.le =
      (⟨⟨i.val, by omega⟩, init i, false⟩ : State N C) := by simp [start, i.isLt]
  rw [hs]
  apply hr.tail
  simp [step, i.isLt, finished i, hi]

lemma reaches_accept (i : Fin N) (hi : accept (terminal i) = true) :
    Reaches init defaultState microStep done accept
      (start init defaultState i.val i.isLt.le)
      ⟨⟨i.val, by omega⟩, terminal i, true⟩ := by
  have hr := lift_micro init defaultState microStep done accept fixed i (runs i)
  have hs : start init defaultState i.val i.isLt.le =
      (⟨⟨i.val, by omega⟩, init i, false⟩ : State N C) := by simp [start, i.isLt]
  rw [hs]
  apply hr.tail
  simp [step, i.isLt, finished i, hi]

/-- Rejected candidates are examined in numeric order, with only the current
candidate's microregisters retained. -/
theorem reaches_start (j : ℕ) (hj : j ≤ N)
    (hnone : ∀ i : Fin N, i.val < j → accept (terminal i) = false) :
    Reaches init defaultState microStep done accept
      (start init defaultState 0 (Nat.zero_le N)) (start init defaultState j hj) := by
  induction j with
  | zero => exact Relation.ReflTransGen.refl
  | succ j ih =>
    have hjN : j < N := by omega
    have hr := ih hjN.le (fun i hi => hnone i (by omega))
    have hn := reaches_next init defaultState microStep done accept fixed terminal runs finished
      ⟨j, hjN⟩ (hnone ⟨j, hjN⟩ (by simp))
    exact hr.trans hn

/-- The actual outer machine finds a candidate whenever one exists. -/
theorem search_exists (hex : ∃ i : Fin N, accept (terminal i) = true) :
    ∃ i : Fin N, accept (terminal i) = true ∧
      Reaches init defaultState microStep done accept
        (start init defaultState 0 (Nat.zero_le N))
        ⟨⟨i.val, by omega⟩, terminal i, true⟩ := by
  classical
  let good : Finset (Fin N) := Finset.univ.filter (fun i => accept (terminal i) = true)
  have hgood : good.Nonempty := by
    rcases hex with ⟨i, hi⟩
    exact ⟨i, by simpa [good] using hi⟩
  let i := good.min' hgood
  have hi : accept (terminal i) = true := (Finset.mem_filter.mp (good.min'_mem hgood)).2
  have hbefore : ∀ j : Fin N, j.val < i.val → accept (terminal j) = false := by
    intro j hj
    cases ha : accept (terminal j) with
    | false => rfl
    | true =>
      have hmem : j ∈ good := by simp [good, ha]
      have hle := good.min'_le j hmem
      have hval : i.val ≤ j.val := hle
      omega
  refine ⟨i, hi, ?_⟩
  exact (reaches_start init defaultState microStep done accept fixed terminal runs finished
    i.val i.isLt.le hbefore).trans
      (reaches_accept init defaultState microStep done accept fixed terminal runs finished i hi)

/-- If every candidate is rejected, the actual counter reaches N and halts. -/
theorem search_none (hnone : ∀ i : Fin N, accept (terminal i) = false) :
    Reaches init defaultState microStep done accept
      (start init defaultState 0 (Nat.zero_le N)) (start init defaultState N le_rfl) ∧
    step init defaultState microStep done accept (start init defaultState N le_rfl) =
      start init defaultState N le_rfl := by
  refine ⟨reaches_start init defaultState microStep done accept fixed terminal runs finished
    N le_rfl (fun i _ => hnone i), ?_⟩
  simp [step, start]

omit fixed runs finished

lemma accepted_fixed (s : State N C) (hs : s.accepted = true) :
    step init defaultState microStep done accept s = s := by simp [step, hs]

lemma state_card [Fintype C] : Fintype.card (State N C) = (N + 1) * Fintype.card C * 2 := by
  let e : State N C ≃ Fin (N + 1) × C × Bool :=
    { toFun := fun s => (s.index, s.micro, s.accepted)
      invFun := fun s => ⟨s.1, s.2.1, s.2.2⟩
      left_inv := by intro s; cases s; rfl
      right_inv := by intro s; rcases s with ⟨i, c, a⟩; rfl }
  rw [Fintype.card_congr e]
  simp [Nat.mul_assoc]

/-- The loop's numeric counter and acceptance flag are included in its space. -/
theorem state_bits [Fintype C] (a b : ℕ)
    (hN : N + 1 ≤ 2 ^ a) (hC : Fintype.card C ≤ 2 ^ b) :
    Fintype.card (State N C) ≤ 2 ^ (a + b + 1) := by
  rw [state_card]
  calc
    _ ≤ (2 ^ a * 2 ^ b) * 2 := Nat.mul_le_mul_right 2 (Nat.mul_le_mul hN hC)
    _ = _ := by rw [pow_add, pow_add]; norm_num

end Paper02.MachineComposition
