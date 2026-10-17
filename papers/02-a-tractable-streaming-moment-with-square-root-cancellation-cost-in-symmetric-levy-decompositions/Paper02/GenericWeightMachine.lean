import Paper02.CompactCandidates
import Paper02.WeightEval

/-! An evaluator is precisely the bounded-space hypothesis on the single
weight in Lemma A.2. No moment estimator is assumed by this interface. -/
noncomputable section
namespace Paper02.GenericWeightMachine
open CompactCandidates WeightEval Finset

structure Evaluator (U : ℕ) (w : ℤ → ℕ) where
  Carrier : Type
  finite : Fintype Carrier
  bits : ℕ
  initial : Fin (2 * U + 1) → Carrier
  step : Fin (2 * U + 1) → Carrier → Carrier
  done : Carrier → Bool
  result : Carrier → Fin 4
  fixed : ∀ a s, done s = true → step a s = s
  halts : ∀ a, ∃ finish, Relation.ReflTransGen (fun s t => step a s = t)
    (initial a) finish ∧ done finish = true ∧ (result finish).val = w (integerValue a)
  space : @Fintype.card Carrier finite ≤ 2 ^ bits

abbrev State {U : ℕ} {w : ℤ → ℕ} (ev : Evaluator U w) (K : ℕ) :=
  (Fin (K + 1) × Fin (3 * K + 1)) ⊕ (Fin K × Fin (3 * K + 1) × ev.Carrier)

def ready {U K : ℕ} {w : ℤ → ℕ} {ev : Evaluator U w}
    (j : Fin (K + 1)) (total : Fin (3 * K + 1)) : State ev K := .inl (j, total)

def scanning {U K : ℕ} {w : ℤ → ℕ} {ev : Evaluator U w}
    (j : Fin K) (total : Fin (3 * K + 1)) (s : ev.Carrier) : State ev K := .inr (j, total, s)

def entryWeight {d U : ℕ} (w : ℤ → ℕ) (entry : Option (Fin d × Fin (2 * U + 1))) : ℕ :=
  match entry with | none => 0 | some (_, a) => w (integerValue a)

variable {d U K : ℕ} {w : ℤ → ℕ}

def step (ev : Evaluator U w) (code : CompactCode d U K) : State ev K → State ev K
  | .inl (j, total) =>
      if h : j.val < K then
        match code ⟨j.val, h⟩ with
        | none => ready ⟨j.val + 1, by omega⟩ total
        | some (_, a) => scanning ⟨j.val, h⟩ total (ev.initial a)
      else ready j total
  | .inr (j, total, s) =>
      match code j with
      | none => ready ⟨j.val + 1, by omega⟩ total
      | some (_, a) =>
          if ev.done s then
            ready ⟨j.val + 1, by omega⟩ ⟨min (total.val + (ev.result s).val) (3 * K), by
              have := Nat.min_le_right (total.val + (ev.result s).val) (3 * K); omega⟩
          else scanning j total (ev.step a s)

abbrev Reaches (ev : Evaluator U w) (code : CompactCode d U K) :=
  Relation.ReflTransGen (fun a b => step ev code a = b)

theorem lift_evaluator (ev : Evaluator U w) (code : CompactCode d U K)
    (j : Fin K) (total : Fin (3 * K + 1)) (i : Fin d) (a : Fin (2 * U + 1))
    (hj : code j = some (i, a)) {x y : ev.Carrier}
    (h : Relation.ReflTransGen (fun s t => ev.step a s = t) x y) :
    Reaches ev code (scanning j total x) (scanning j total y) := by
  apply Relation.ReflTransGen.lift' (scanning j total) _ h
  intro s t hst
  cases hd : ev.done s with
  | false =>
    apply Relation.ReflTransGen.single
    simp [step, scanning, hj, hd, hst]
  | true =>
    have he : t = s := hst.symm.trans (ev.fixed a s hd)
    rw [he]

def weightPrefix (code : CompactCode d U K) (n : ℕ) : ℕ :=
  ∑ j ∈ range n, if h : j < K then entryWeight w (code ⟨j, h⟩) else 0

lemma weightPrefix_zero (code : CompactCode d U K) : weightPrefix (w := w) code 0 = 0 := by
  simp [weightPrefix]

lemma weightPrefix_succ (code : CompactCode d U K) (n : ℕ) (hn : n < K) :
    weightPrefix (w := w) code (n + 1) = weightPrefix (w := w) code n + entryWeight w (code ⟨n, hn⟩) := by
  simp [weightPrefix, Finset.sum_range_succ, hn]

lemma weightPrefix_bound (hw : ∀ k, w k ≤ 3) (code : CompactCode d U K) (n : ℕ) :
    weightPrefix (w := w) code n ≤ 3 * n := by
  calc
    _ ≤ ∑ _j ∈ range n, 3 := by
      apply sum_le_sum
      intro j _
      split_ifs with hj
      · cases h : code ⟨j, hj⟩ with
        | none => simp [entryWeight]
        | some entry => exact hw _
      · omega
    _ = _ := by simp [Nat.mul_comm]

def expected (ev : Evaluator U w) (hw : ∀ k, w k ≤ 3)
    (code : CompactCode d U K) (n : ℕ) (hn : n ≤ K) : State ev K :=
  ready ⟨n, by omega⟩ ⟨weightPrefix (w := w) code n, by have := weightPrefix_bound hw code n; omega⟩

lemma single_slot (ev : Evaluator U w) (hw : ∀ k, w k ≤ 3)
    (code : CompactCode d U K) (n : ℕ) (hn : n < K) :
    Reaches ev code (expected ev hw code n hn.le) (expected ev hw code (n + 1) (by omega)) := by
  have hs := weightPrefix_succ (w := w) code n hn
  have hb : weightPrefix (w := w) code n + entryWeight w (code ⟨n, hn⟩) ≤ 3 * K := by
    rw [← hs]
    have h := weightPrefix_bound hw code (n + 1)
    omega
  cases hc : code ⟨n, hn⟩ with
  | none =>
    apply Relation.ReflTransGen.single
    simp [expected, ready, step, hn, hc, hs, entryWeight]
  | some entry =>
    rcases entry with ⟨i, a⟩
    obtain ⟨finish, hr, hd, hv⟩ := ev.halts a
    let total : Fin (3 * K + 1) := ⟨weightPrefix (w := w) code n,
      by have := weightPrefix_bound hw code n; omega⟩
    have hlaunch : step ev code (expected ev hw code n hn.le) =
        scanning ⟨n, hn⟩ total (ev.initial a) := by
      simp [step, expected, ready, hn, hc, total]
    have hl : Reaches ev code (expected ev hw code n hn.le)
        (scanning ⟨n, hn⟩ total (ev.initial a)) := Relation.ReflTransGen.single hlaunch
    have hm := lift_evaluator ev code ⟨n, hn⟩ total i a hc hr
    have hsum : weightPrefix (w := w) code n + (ev.result finish).val ≤ 3 * K := by
      simpa [hc, entryWeight, hv] using hb
    have hsumW : weightPrefix (w := w) code n + w (integerValue a) ≤ 3 * K := by
      simpa [hc, entryWeight] using hb
    have hfinish : step ev code (scanning ⟨n, hn⟩ total finish) =
        expected ev hw code (n + 1) (by omega) := by
      simp [step, scanning, hc, hd, hv, total, Nat.min_eq_left hsumW,
        expected, hs, entryWeight, ready]
    exact hl.trans (hm.tail hfinish)

def initial (ev : Evaluator U w) (K : ℕ) : State ev K := ready 0 0

def done {ev : Evaluator U w} : State ev K → Bool
  | .inl (j, _) => decide (j.val = K)
  | .inr _ => false

def result {ev : Evaluator U w} : State ev K → ℕ
  | .inl (_, total) => total.val
  | .inr (_, total, _) => total.val

lemma result_le (ev : Evaluator U w) (s : State ev K) : result s ≤ 3 * K := by
  cases s with
  | inl s => have := s.2.isLt; simp only [result]; omega
  | inr s => have := s.2.1.isLt; simp only [result]; omega

lemma done_fixed (ev : Evaluator U w) (code : CompactCode d U K) (s : State ev K)
    (hs : done s = true) : step ev code s = s := by
  cases s with
  | inl s => rcases s with ⟨j, total⟩; have hj : j.val = K := by simpa [done] using hs
             simp [step, ready, hj]
  | inr s => simp [done] at hs

theorem machine_complete (ev : Evaluator U w) (hw : ∀ k, w k ≤ 3) (code : CompactCode d U K) :
    ∃ finish : State ev K, Reaches ev code (initial ev K) finish ∧ done finish = true ∧
      result finish = ∑ j, entryWeight w (code j) := by
  have hr (n : ℕ) (hn : n ≤ K) : Reaches ev code
      (expected ev hw code 0 (Nat.zero_le K)) (expected ev hw code n hn) := by
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ n ih => have hnt : n < K := by omega
                   exact (ih hnt.le).trans (single_slot ev hw code n hnt)
  refine ⟨expected ev hw code K le_rfl, ?_, by simp [expected, ready, done], ?_⟩
  · simpa [expected, weightPrefix_zero, initial] using hr K le_rfl
  · change weightPrefix (w := w) code K = _
    rw [Finset.sum_fin_eq_sum_range]
    rfl

theorem sum_eq_moment (hw0 : w 0 = 0) (code : CompactCode d U K)
    (hinj : ∀ (j k : Fin K) (a b : Fin d × Fin (2 * U + 1)),
      code j = some a → code k = some b → a.1 = b.1 → j = k) :
    ((∑ j, entryWeight w (code j) : ℕ) : ℝ) = ∑ i, (w (candidateValue code i) : ℝ) := by
  rw [moment_slots (fun k => (w k : ℝ)) (by simp [hw0]) code hinj, Nat.cast_sum]
  apply sum_congr rfl
  intro j _
  cases h : code j with
  | none => simp [entryWeight]
  | some entry => rfl

def machineBits (ev : Evaluator U w) (K : ℕ) : ℕ :=
  registerBits (K + 1) + registerBits (3 * K + 1) + ev.bits + 1

theorem machine_fits (ev : Evaluator U w) (K : ℕ) :
    @Fintype.card (State ev K) (by letI := ev.finite; exact inferInstance) ≤ 2 ^ machineBits ev K := by
  letI := ev.finite
  have hK := (lt_two_pow_registerBits (K + 1)).le
  have hS := (lt_two_pow_registerBits (3 * K + 1)).le
  have hK' : K ≤ 2 ^ registerBits (K + 1) := (Nat.le_succ K).trans hK
  have hsmall : (K + 1) * (3 * K + 1) ≤
      2 ^ registerBits (K + 1) * 2 ^ registerBits (3 * K + 1) * 2 ^ ev.bits := by
    calc
      _ ≤ _ := Nat.mul_le_mul hK hS
      _ ≤ (2 ^ registerBits (K + 1) * 2 ^ registerBits (3 * K + 1)) * 2 ^ ev.bits := by
        have hp : 1 ≤ 2 ^ ev.bits := Nat.one_le_two_pow
        nlinarith [Nat.mul_le_mul_left (2 ^ registerBits (K + 1) * 2 ^ registerBits (3 * K + 1)) hp]
  have hlarge := Nat.mul_le_mul hK' (Nat.mul_le_mul hS ev.space)
  simp only [State, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  unfold machineBits
  rw [pow_add, pow_add, pow_add]
  norm_num only [pow_one]
  nlinarith [hsmall, hlarge]

end Paper02.GenericWeightMachine
