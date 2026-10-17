import Paper02.CompactCandidates
import Paper02.WeightEval
import Paper02.StreamingSpace

/-! The witness is evaluated by its actual binary scan, once per compact slot.
The program retains only a slot counter, a bounded sum, a clock and scan registers. -/

namespace Paper02.WeightMachine
open CompactCandidates WeightEval Finset

abbrev State (U K : ℕ) :=
  (Fin (K + 1) × Fin (3 * K + 1)) ⊕
    (Fin K × Fin (3 * K + 1) × Fin (U + 2) × ScanState U)

def ready {U K : ℕ} (j : Fin (K + 1)) (total : Fin (3 * K + 1)) : State U K :=
  .inl (j, total)

def scanning {U K : ℕ} (j : Fin K) (total : Fin (3 * K + 1))
    (clock : Fin (U + 2)) (s : ScanState U) : State U K := .inr (j, total, clock, s)

lemma magnitude_bound {U : ℕ} (a : Fin (2 * U + 1)) : (integerValue a).natAbs ≤ U := by
  have hb := integerValue_bounds a
  cases h : integerValue a <;> simp_all <;> omega

def slotWeight {d U : ℕ} (entry : Option (Fin d × Fin (2 * U + 1))) : ℕ :=
  match entry with
  | none => 0
  | some (_, a) => weight (integerValue a)

lemma slotWeight_le {d U : ℕ} (entry : Option (Fin d × Fin (2 * U + 1))) :
    slotWeight entry ≤ 3 := by
  cases entry with
  | none => simp [slotWeight]
  | some entry => exact weight_le_three _

def step {d U K : ℕ} (code : CompactCode d U K) : State U K → State U K
  | .inl (j, total) =>
      if h : j.val < K then
        match code ⟨j.val, h⟩ with
        | none => ready ⟨j.val + 1, by omega⟩ total
        | some (_, a) =>
            if integerValue a = 0 then ready ⟨j.val + 1, by omega⟩ total else
              scanning ⟨j.val, h⟩ total 0 (initialState U (integerValue a).natAbs (magnitude_bound a))
      else ready j total
  | .inr (j, total, clock, s) =>
      if h : clock.val < U + 1 then
        scanning j total ⟨clock.val + 1, by omega⟩ (scanStep s)
      else ready ⟨j.val + 1, by omega⟩
        ⟨min (total.val + if s.parity = 0 then 3 else 1) (3 * K), by
          have := Nat.min_le_right (total.val + if s.parity = 0 then 3 else 1) (3 * K)
          omega⟩

abbrev Reaches {d U K : ℕ} (code : CompactCode d U K) :=
  Relation.ReflTransGen (fun a b => step code a = b)

lemma scanRun_succ (n : ℕ) {U : ℕ} (s : ScanState U) :
    scanRun (n + 1) s = scanStep (scanRun n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa only [scanRun] using ih (scanStep s)

lemma scanning_reaches {d U K : ℕ} (code : CompactCode d U K) (j : Fin K)
    (total : Fin (3 * K + 1)) (s : ScanState U) (n : ℕ) (hn : n ≤ U + 1) :
    Reaches code (scanning j total 0 s)
      (scanning j total ⟨n, by omega⟩ (scanRun n s)) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    have hnt : n < U + 1 := by omega
    apply (ih hnt.le).tail
    simp only [scanning, step, dif_pos hnt, scanRun_succ]

def weightPrefix {d U K : ℕ} (code : CompactCode d U K) (n : ℕ) : ℕ :=
  ∑ j ∈ range n, if h : j < K then slotWeight (code ⟨j, h⟩) else 0

lemma weightPrefix_zero {d U K : ℕ} (code : CompactCode d U K) : weightPrefix code 0 = 0 := by
  simp [weightPrefix]

lemma weightPrefix_succ {d U K : ℕ} (code : CompactCode d U K) (n : ℕ) (hn : n < K) :
    weightPrefix code (n + 1) = weightPrefix code n + slotWeight (code ⟨n, hn⟩) := by
  simp [weightPrefix, Finset.sum_range_succ, hn]

lemma weightPrefix_bound {d U K : ℕ} (code : CompactCode d U K) (n : ℕ) :
    weightPrefix code n ≤ 3 * n := by
  calc
    _ ≤ ∑ _j ∈ range n, 3 := by
      apply sum_le_sum
      intro j _
      split_ifs
      · exact slotWeight_le _
      · omega
    _ = _ := by simp [Nat.mul_comm]

def expected {d U K : ℕ} (code : CompactCode d U K) (n : ℕ) (hn : n ≤ K) : State U K :=
  ready ⟨n, by omega⟩ ⟨weightPrefix code n, by have := weightPrefix_bound code n; omega⟩

lemma single_slot {d U K : ℕ} (code : CompactCode d U K) (n : ℕ) (hn : n < K) :
    Reaches code (expected code n hn.le) (expected code (n + 1) (by omega)) := by
  have hs := weightPrefix_succ code n hn
  have hbound : weightPrefix code n + slotWeight (code ⟨n, hn⟩) ≤ 3 * K := by
    rw [← hs]
    have h := weightPrefix_bound code (n + 1)
    omega
  cases hc : code ⟨n, hn⟩ with
  | none =>
    apply Relation.ReflTransGen.single
    simp [expected, ready, step, hn, hc, hs, slotWeight]
  | some entry =>
    rcases entry with ⟨i, a⟩
    by_cases hk : integerValue a = 0
    · apply Relation.ReflTransGen.single
      simp [expected, ready, step, hn, hc, hk, hs, slotWeight, weight_zero]
    · let scan := initialState U (integerValue a).natAbs (magnitude_bound a)
      let total : Fin (3 * K + 1) := ⟨weightPrefix code n, by have := weightPrefix_bound code n; omega⟩
      have hlaunch : step code (expected code n hn.le) =
          scanning ⟨n, hn⟩ total 0 scan := by
        simp [expected, ready, step, hn, hc, hk, scan, total]
      have hrun := scanning_reaches code ⟨n, hn⟩ total scan (U + 1) le_rfl
      have hp : (scanRun (U + 1) scan).parity =
          parityScan ((integerValue a).natAbs + 1) (integerValue a).natAbs 0 := by
        apply scanRun_parity
        simp [scan, initialState]
        exact magnitude_bound a
      have hw : (if (scanRun (U + 1) scan).parity = 0 then 3 else 1) =
          slotWeight (code ⟨n, hn⟩) := by
        rw [hc, slotWeight, weight, if_neg hk, hp]
      have hfinish : step code
          (scanning ⟨n, hn⟩ total ⟨U + 1, by omega⟩ (scanRun (U + 1) scan)) =
          expected code (n + 1) (by omega) := by
        simp only [scanning, step, lt_self_iff_false, ↓reduceDIte, hw, total,
          Nat.min_eq_left hbound, expected, hs, ready]
      have hl : Reaches code (expected code n hn.le) (scanning ⟨n, hn⟩ total 0 scan) :=
        Relation.ReflTransGen.single hlaunch
      exact hl.trans (hrun.tail hfinish)

theorem machine_reaches {d U K : ℕ} (code : CompactCode d U K) (n : ℕ) (hn : n ≤ K) :
    Reaches code (expected code 0 (Nat.zero_le K)) (expected code n hn) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    have hnt : n < K := by omega
    exact (ih hnt.le).trans (single_slot code n hnt)

lemma weightPrefix_all {d U K : ℕ} (code : CompactCode d U K) :
    weightPrefix code K = ∑ j, slotWeight (code j) := by
  rw [Finset.sum_fin_eq_sum_range]
  rfl

theorem machine_correct {d U K : ℕ} (code : CompactCode d U K) :
    ∃ total : Fin (3 * K + 1),
      Reaches code (ready 0 0) (ready ⟨K, by omega⟩ total) ∧
      step code (ready ⟨K, by omega⟩ total) = ready ⟨K, by omega⟩ total ∧
      total.val = ∑ j, slotWeight (code j) := by
  refine ⟨⟨weightPrefix code K, by have := weightPrefix_bound code K; omega⟩, ?_, ?_, weightPrefix_all code⟩
  · simpa [expected, weightPrefix_zero] using machine_reaches code K le_rfl
  · simp [ready, step]

def initial (U K : ℕ) : State U K := ready 0 0

def done {U K : ℕ} : State U K → Bool
  | .inl (j, _) => decide (j.val = K)
  | .inr _ => false

def result {U K : ℕ} : State U K → ℕ
  | .inl (_, total) => total.val
  | .inr (_, total, _, _) => total.val

lemma result_le {U K : ℕ} (s : State U K) : result s ≤ 3 * K := by
  cases s with
  | inl s => have := s.2.isLt; simp only [result]; omega
  | inr s => have := s.2.1.isLt; simp only [result]; omega

lemma done_fixed {d U K : ℕ} (code : CompactCode d U K) (s : State U K)
    (hs : done s = true) : step code s = s := by
  cases s with
  | inl s =>
    rcases s with ⟨j, total⟩
    have hj : j.val = K := by simpa [done] using hs
    simp [step, ready, hj]
  | inr s => simp [done] at hs

/-- Interface for composing the actual evaluator with a recovered candidate. -/
theorem machine_complete {d U K : ℕ} (code : CompactCode d U K) :
    ∃ finish : State U K, Reaches code (initial U K) finish ∧ done finish = true ∧
      result finish = ∑ j, slotWeight (code j) := by
  obtain ⟨total, hr, _, ht⟩ := machine_correct code
  exact ⟨ready ⟨K, by omega⟩ total, hr, by simp [done, ready], ht⟩

theorem sum_eq_moment {d U K : ℕ} (code : CompactCode d U K)
    (hinj : ∀ (j k : Fin K) (a b : Fin d × Fin (2 * U + 1)),
      code j = some a → code k = some b → a.1 = b.1 → j = k) :
    ((∑ j, slotWeight (code j) : ℕ) : ℝ) = ∑ i, f (candidateValue code i) := by
  rw [moment_slots f f_zero code hinj, Nat.cast_sum]
  apply sum_congr rfl
  intro j _
  cases h : code j with
  | none => simp [slotWeight]
  | some entry => exact weight_cast _

def machineBits (U K : ℕ) : ℕ :=
  registerBits (K + 1) + registerBits (3 * K + 1) + registerBits (U + 2) + evaluatorBits U + 1

theorem machine_fits (U K : ℕ) :
    Fintype.card (State U K) ≤ 2 ^ machineBits U K := by
  have hK := (lt_two_pow_registerBits (K + 1)).le
  have hS := (lt_two_pow_registerBits (3 * K + 1)).le
  have hU := (lt_two_pow_registerBits (U + 2)).le
  have hE := evaluator_space_bound U
  have hK' : K ≤ 2 ^ registerBits (K + 1) := (Nat.le_succ K).trans hK
  have hsmall : (K + 1) * (3 * K + 1) ≤
      2 ^ registerBits (K + 1) * 2 ^ registerBits (3 * K + 1) *
        2 ^ registerBits (U + 2) * 2 ^ evaluatorBits U := by
    have hbase := Nat.mul_le_mul hK hS
    have hu : 1 ≤ 2 ^ registerBits (U + 2) * 2 ^ evaluatorBits U := by
      have hp : 0 < 2 ^ registerBits (U + 2) * 2 ^ evaluatorBits U := by positivity
      omega
    calc
      _ ≤ _ := hbase
      _ = (2 ^ registerBits (K + 1) * 2 ^ registerBits (3 * K + 1)) * 1 := by omega
      _ ≤ (2 ^ registerBits (K + 1) * 2 ^ registerBits (3 * K + 1)) *
          (2 ^ registerBits (U + 2) * 2 ^ evaluatorBits U) := Nat.mul_le_mul_left _ hu
      _ = _ := by ring
  have hlarge := Nat.mul_le_mul hK' (Nat.mul_le_mul hS (Nat.mul_le_mul hU hE))
  simp only [State, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  unfold machineBits
  rw [pow_add, pow_add, pow_add, pow_add]
  norm_num only [pow_one]
  nlinarith [hsmall, hlarge]

end Paper02.WeightMachine
