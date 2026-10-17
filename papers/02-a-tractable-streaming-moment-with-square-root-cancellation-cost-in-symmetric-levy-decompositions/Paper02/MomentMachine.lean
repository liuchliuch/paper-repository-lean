import Paper02.StreamingSpace
import Mathlib.Logic.Relation

/-! # A register machine for checking stored power moments

Every transition has bounded counters, two field accumulators and one flag.
Powers are computed by repeated multiplication; there is no polynomial oracle
or unbounded recursive evaluator in the transition relation.
-/
noncomputable section
open scoped BigOperators

namespace Paper02.MomentMachine

structure State (K q : ℕ) [NeZero q] where
  moment : Fin (2 * K + 1)
  slot : Fin (K + 1)
  exponent : Fin (2 * K + 1)
  power : ZMod q
  accumulator : ZMod q
  good : Bool
  deriving Fintype, DecidableEq

variable {K q : ℕ} [NeZero q]

/-- One multiplication, one accumulation, or one moment comparison. -/
def step (nodes weights : Fin K → ZMod q) (M : Fin (2 * K) → ZMod q)
    (s : State K q) : State K q :=
  if ht : s.moment.val < 2 * K then
    if hj : s.slot.val < K then
      if he : s.exponent.val < s.moment.val then
        { s with exponent := ⟨s.exponent.val + 1, by omega⟩
                 power := s.power * nodes ⟨s.slot.val, hj⟩ }
      else
        { s with slot := ⟨s.slot.val + 1, by omega⟩
                 exponent := 0
                 power := 1
                 accumulator := s.accumulator + weights ⟨s.slot.val, hj⟩ * s.power }
    else
      { moment := ⟨s.moment.val + 1, by omega⟩
        slot := 0
        exponent := 0
        power := 1
        accumulator := 0
        good := s.good && decide (s.accumulator = M ⟨s.moment.val, ht⟩) }
  else s

/-- Only current registers occur in the operational semantics. -/
def Reaches (nodes weights : Fin K → ZMod q) (M : Fin (2 * K) → ZMod q)
    (s t : State K q) : Prop :=
  Relation.ReflTransGen (fun x y => step nodes weights M x = y) s t

def registers (t j e : ℕ) (ht : t ≤ 2 * K) (hj : j ≤ K) (he : e ≤ 2 * K)
    (p a : ZMod q) (g : Bool) : State K q :=
  ⟨⟨t, by omega⟩, ⟨j, by omega⟩, ⟨e, by omega⟩, p, a, g⟩

lemma powers_reach (nodes weights : Fin K → ZMod q) (M : Fin (2 * K) → ZMod q)
    (t j : ℕ) (ht : t < 2 * K) (hj : j < K) (a : ZMod q) (g : Bool)
    (e : ℕ) (he : e ≤ t) :
    Reaches nodes weights M
      (registers t j 0 ht.le hj.le (by omega) 1 a g)
      (registers t j e ht.le hj.le (by omega) (nodes ⟨j, hj⟩ ^ e) a g) := by
  induction e with
  | zero => simpa only [pow_zero] using
      (Relation.ReflTransGen.refl : Reaches nodes weights M
        (registers t j 0 ht.le hj.le (by omega) 1 a g) _) 
  | succ e ih =>
    have hle : e ≤ t := by omega
    apply Relation.ReflTransGen.trans (ih hle)
    apply Relation.ReflTransGen.single
    have hlt : e < t := by omega
    simp [step, registers, ht, hj, hlt, pow_succ]

lemma slot_reach (nodes weights : Fin K → ZMod q) (M : Fin (2 * K) → ZMod q)
    (t j : ℕ) (ht : t < 2 * K) (hj : j < K) (a : ZMod q) (g : Bool) :
    Reaches nodes weights M
      (registers t j 0 ht.le hj.le (by omega) 1 a g)
      (registers t (j + 1) 0 ht.le (by omega) (by omega) 1
        (a + weights ⟨j, hj⟩ * nodes ⟨j, hj⟩ ^ t) g) := by
  apply Relation.ReflTransGen.trans (powers_reach nodes weights M t j ht hj a g t (le_refl _))
  apply Relation.ReflTransGen.single
  simp [step, registers, ht, hj]

def contribution (nodes weights : Fin K → ZMod q) (t j : ℕ) : ZMod q :=
  if h : j < K then weights ⟨j, h⟩ * nodes ⟨j, h⟩ ^ t else 0

def partialSum (nodes weights : Fin K → ZMod q) (t n : ℕ) : ZMod q :=
  ∑ j ∈ Finset.range n, contribution nodes weights t j

lemma slots_reach (nodes weights : Fin K → ZMod q) (M : Fin (2 * K) → ZMod q)
    (t : ℕ) (ht : t < 2 * K) (g : Bool) (n : ℕ) (hn : n ≤ K) :
    Reaches nodes weights M
      (registers t 0 0 ht.le (by omega) (by omega) 1 0 g)
      (registers t n 0 ht.le hn (by omega) 1 (partialSum nodes weights t n) g) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    have hn' : n < K := by omega
    have hs := slot_reach nodes weights M t n ht hn' (partialSum nodes weights t n) g
    have hp : partialSum nodes weights t (n + 1) =
        partialSum nodes weights t n + weights ⟨n, hn'⟩ * nodes ⟨n, hn'⟩ ^ t := by
      simp [partialSum, Finset.sum_range_succ, contribution, hn']
    rw [hp]
    exact (ih hn'.le).trans hs

lemma partialSum_all (nodes weights : Fin K → ZMod q) (t : ℕ) :
    partialSum nodes weights t K = ∑ j, weights j * nodes j ^ t := by
  rw [partialSum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp [contribution, j.isLt]

/-- This is the exact Boolean property computed after the first `n` moments. -/
def goodPrefix (nodes weights : Fin K → ZMod q) (M : Fin (2 * K) → ZMod q)
    (n : ℕ) : Bool :=
  decide (∀ t : Fin (2 * K), t.val < n → (∑ j, weights j * nodes j ^ t.val) = M t)

lemma goodPrefix_zero (nodes weights : Fin K → ZMod q) (M : Fin (2 * K) → ZMod q) :
    goodPrefix nodes weights M 0 = true := by simp [goodPrefix]

lemma goodPrefix_succ (nodes weights : Fin K → ZMod q) (M : Fin (2 * K) → ZMod q)
    (n : ℕ) (hn : n < 2 * K) :
    goodPrefix nodes weights M (n + 1) = (goodPrefix nodes weights M n &&
      decide ((∑ j, weights j * nodes j ^ n) = M ⟨n, hn⟩)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [goodPrefix, Bool.and_eq_true]
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨fun t ht => h t (by omega), h ⟨n, hn⟩ (by simp)⟩
  · rintro ⟨h, he⟩ t ht
    by_cases hn' : t.val < n
    · exact h t hn'
    · have ht' : t = ⟨n, hn⟩ := Fin.ext (by dsimp only; omega)
      simpa [ht'] using he

/-- The complete checker really reaches the moment comparison result through
its bounded register transitions. -/
theorem checker_reaches (nodes weights : Fin K → ZMod q) (M : Fin (2 * K) → ZMod q)
    (n : ℕ) (hn : n ≤ 2 * K) :
    Reaches nodes weights M
      (registers 0 0 0 (by omega) (by omega) (by omega) 1 0 true)
      (registers n 0 0 hn (by omega) (by omega) 1 0 (goodPrefix nodes weights M n)) := by
  induction n with
  | zero => simp only [goodPrefix_zero]; exact Relation.ReflTransGen.refl
  | succ n ih =>
    have hnt : n < 2 * K := by omega
    have hs := slots_reach nodes weights M n hnt (goodPrefix nodes weights M n) K (le_refl _)
    apply Relation.ReflTransGen.trans ((ih hnt.le).trans hs)
    apply Relation.ReflTransGen.single
    simp only [step, registers, dif_pos hnt, lt_self_iff_false, ↓reduceDIte]
    congr 1
    rw [partialSum_all]
    exact (goodPrefix_succ nodes weights M n hnt).symm

/-- At the halting state, acceptance means exactly that every stored moment
matches the compact candidate's moments. -/
theorem checker_correct (nodes weights : Fin K → ZMod q) (M : Fin (2 * K) → ZMod q) :
    let finish := registers (2 * K) 0 0 (le_refl _) (by omega) (by omega) 1 0
      (goodPrefix nodes weights M (2 * K))
    Reaches nodes weights M (registers 0 0 0 (by omega) (by omega) (by omega) 1 0 true) finish ∧
      step nodes weights M finish = finish ∧
      (finish.good = true ↔ ∀ t, (∑ j, weights j * nodes j ^ t.val) = M t) := by
  dsimp only
  refine ⟨checker_reaches nodes weights M _ (le_refl _), ?_, ?_⟩
  · simp [step, registers]
  · simp [registers, goodPrefix]

/-- A state-space bound for the actual checker registers. The code and stored
input moments are counted separately by the caller. -/
theorem checker_space_bound [NeZero q] :
    Fintype.card (State K q) ≤
      2 ^ (2 * WeightEval.registerBits (2 * K + 1) + WeightEval.registerBits (K + 1) +
        2 * WeightEval.registerBits q + 1) := by
  let e : State K q ≃ Fin (2 * K + 1) × Fin (K + 1) × Fin (2 * K + 1) × ZMod q × ZMod q × Bool :=
    { toFun := fun s => (s.moment, s.slot, s.exponent, s.power, s.accumulator, s.good)
      invFun := fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e]
  simp only [Fintype.card_prod, Fintype.card_fin, ZMod.card, Fintype.card_bool]
  have h₁ := (WeightEval.lt_two_pow_registerBits (2 * K + 1)).le
  have h₂ := (WeightEval.lt_two_pow_registerBits (K + 1)).le
  have h₃ := (WeightEval.lt_two_pow_registerBits q).le
  have hm := Nat.mul_le_mul h₁ (Nat.mul_le_mul h₂
    (Nat.mul_le_mul h₁ (Nat.mul_le_mul h₃ (Nat.mul_le_mul h₃ (le_refl 2)))))
  convert hm using 1
  simp only [← pow_succ, ← pow_add]
  congr 1
  omega

end Paper02.MomentMachine
