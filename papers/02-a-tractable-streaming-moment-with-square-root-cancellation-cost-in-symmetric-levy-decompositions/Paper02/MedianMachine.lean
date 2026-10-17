import Paper02.Sampling

/-! # A bounded-register machine computing the amplified sketch's median

The machine scans candidate values from `0` through `V`.  For each candidate
it reads the input array once and counts entries no larger than the candidate.
It halts at the first candidate with at least `b+1` such entries.  Its time is
unrestricted; its auxiliary registers are bounded independently of that time.
-/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Paper02.MedianMachine
open Sampling

def R (b : ℕ) : ℕ := 2 * b + 1

/-- The input array is read-only; these are all mutable registers. -/
structure State (b V : ℕ) where
  candidate : Fin (V + 1)
  cursor : Fin (R b + 1)
  counter : Fin (R b + 1)
  halted : Bool
  deriving DecidableEq, Fintype

@[ext] lemma State.ext {b V : ℕ} {s t : State b V}
    (hc : s.candidate = t.candidate) (hi : s.cursor = t.cursor)
    (hn : s.counter = t.counter) (hh : s.halted = t.halted) : s = t := by
  cases s
  cases t
  simp_all

/-- Initialization uses only zeroed bounded registers. -/
def initial (b V : ℕ) : State b V := ⟨0, 0, 0, false⟩

/-- One executable transition: array access, natural comparison and increment.
The saturated counter makes the transition total even on unreachable states. -/
def step {b V : ℕ} (ys : Fin (R b) → Fin (V + 1)) (s : State b V) : State b V :=
  if s.halted then s
  else if hi : s.cursor.val < R b then
    {s with
      cursor := ⟨s.cursor.val + 1, by omega⟩
      counter := ⟨if ys ⟨s.cursor.val, hi⟩ ≤ s.candidate then
          min (R b) (s.counter.val + 1) else s.counter.val, by
        split_ifs
        · exact Nat.lt_succ_of_le (Nat.min_le_left _ _)
        · exact s.counter.isLt⟩}
  else if b + 1 ≤ s.counter.val then {s with halted := true}
  else if hc : s.candidate.val < V then
    ⟨⟨s.candidate.val + 1, by omega⟩, 0, 0, false⟩
  else {s with halted := true}

/-- Actual reachability by finitely many applications of `step`. -/
def Reaches {b V : ℕ} (ys : Fin (R b) → Fin (V + 1)) (s t : State b V) : Prop :=
  ∃ n : ℕ, (step ys)^[n] s = t

lemma Reaches.refl {b V : ℕ} (ys : Fin (R b) → Fin (V + 1)) (s : State b V) :
    Reaches ys s s := ⟨0, rfl⟩

lemma Reaches.single {b V : ℕ} (ys : Fin (R b) → Fin (V + 1)) (s : State b V) :
    Reaches ys s (step ys s) := ⟨1, rfl⟩

lemma Reaches.trans {b V : ℕ} {ys : Fin (R b) → Fin (V + 1)}
    {s t u : State b V} (hst : Reaches ys s t) (htu : Reaches ys t u) :
    Reaches ys s u := by
  obtain ⟨n, hn⟩ := hst
  obtain ⟨m, hm⟩ := htu
  refine ⟨m + n, ?_⟩
  rw [Function.iterate_add_apply, hn, hm]

/-- The value available at the output port of a halted machine. -/
def output {b V : ℕ} (s : State b V) : Option (Fin (V + 1)) :=
  if s.halted then some s.candidate else none

/-- Count over a prefix of the actual input array. -/
def prefixCount {b V : ℕ} (ys : Fin (R b) → Fin (V + 1))
    (c : Fin (V + 1)) (i : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (R b))).filter (fun j => j.val < i ∧ ys j ≤ c)).card

lemma prefixCount_le {b V : ℕ} (ys : Fin (R b) → Fin (V + 1))
    (c : Fin (V + 1)) (i : ℕ) : prefixCount ys c i ≤ min i (R b) := by
  apply Nat.le_min.mpr
  constructor
  · have hinj : Function.Injective (fun j : Fin (R b) => j.val) := Fin.val_injective
    have hc := Finset.card_le_card_of_injOn (fun j : Fin (R b) => j.val)
      (s := (Finset.univ : Finset (Fin (R b))).filter (fun j => j.val < i ∧ ys j ≤ c))
      (t := Finset.range i) (by intro j hj; exact Finset.mem_range.mpr (Finset.mem_filter.mp hj).2.1)
      (by intro x _ y _ h; exact Fin.ext h)
    simpa [prefixCount] using hc
  · simpa [prefixCount] using Finset.card_filter_le
      (Finset.univ : Finset (Fin (R b))) (fun j => j.val < i ∧ ys j ≤ c)

@[simp] lemma prefixCount_zero {b V : ℕ} (ys : Fin (R b) → Fin (V + 1))
    (c : Fin (V + 1)) : prefixCount ys c 0 = 0 := by simp [prefixCount]

lemma prefixCount_succ {b V i : ℕ} (ys : Fin (R b) → Fin (V + 1))
    (c : Fin (V + 1)) (hi : i < R b) :
    prefixCount ys c (i + 1) = prefixCount ys c i +
      if ys ⟨i, hi⟩ ≤ c then 1 else 0 := by
  classical
  let T := (Finset.univ : Finset (Fin (R b))).filter (fun j => j.val < i ∧ ys j ≤ c)
  by_cases hy : ys ⟨i, hi⟩ ≤ c
  · have he : (Finset.univ : Finset (Fin (R b))).filter
        (fun j => j.val < i + 1 ∧ ys j ≤ c) = insert ⟨i, hi⟩ T := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, T]
      constructor
      · intro hj
        by_cases heq : j.val = i
        · exact Or.inl (Fin.ext heq)
        · exact Or.inr ⟨by omega, hj.2⟩
      · intro hj
        rcases hj with rfl | hj
        · exact ⟨by simpa using Nat.lt_succ_self i, hy⟩
        · exact ⟨by omega, hj.2⟩
    unfold prefixCount
    rw [he, Finset.card_insert_of_notMem]
    · simp [T, hy]
    · simp [T]
  · have he : (Finset.univ : Finset (Fin (R b))).filter
        (fun j => j.val < i + 1 ∧ ys j ≤ c) = T := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, T]
      constructor
      · intro hj
        have hn : j.val ≠ i := by
          intro heq
          have heq' : j = ⟨i, hi⟩ := Fin.ext heq
          subst j
          exact hy hj.2
        exact ⟨by omega, hj.2⟩
      · intro hj
        exact ⟨by omega, hj.2⟩
    simp [prefixCount, he, T, hy]

/-- A fully specified scan configuration; its counter is a derived invariant,
not part of the definition of `step`. -/
def scanning {b V : ℕ} (ys : Fin (R b) → Fin (V + 1)) (c : Fin (V + 1))
    (i : ℕ) (hi : i ≤ R b) : State b V :=
  ⟨c, ⟨i, by omega⟩, ⟨prefixCount ys c i, by
    have hh := (Nat.le_min.mp (prefixCount_le ys c i)).2
    omega⟩, false⟩

lemma scan_step {b V i : ℕ} (ys : Fin (R b) → Fin (V + 1))
    (c : Fin (V + 1)) (hi : i < R b) :
    step ys (scanning ys c i (le_of_lt hi)) =
      scanning ys c (i + 1) (by omega) := by
  have hc := (Nat.le_min.mp (prefixCount_le ys c i)).1
  have hn : prefixCount ys c i + 1 ≤ R b := by omega
  simp only [step, scanning, Bool.false_eq_true, ↓reduceIte, hi]
  apply State.ext <;> simp only
  · rfl
  · rfl
  · apply Fin.ext
    simp only [prefixCount_succ ys c hi]
    split_ifs <;> simp_all [Nat.min_eq_right hn]
  · rfl

lemma scan_reaches {b V : ℕ} (ys : Fin (R b) → Fin (V + 1))
    (c : Fin (V + 1)) (i : ℕ) (hi : i ≤ R b) :
    Reaches ys (scanning ys c 0 (by omega)) (scanning ys c i hi) := by
  induction i with
  | zero => exact Reaches.refl _ _
  | succ i ih =>
    have hi' : i < R b := by omega
    exact (ih (by omega)).trans (by
      have hh := Reaches.single ys (scanning ys c i (by omega))
      rwa [scan_step ys c hi'] at hh)

def countLE {b V : ℕ} (ys : Fin (R b) → Fin (V + 1)) (c : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (R b))).filter (fun i => (ys i).val ≤ c)).card

lemma full_scan_count {b V : ℕ} (ys : Fin (R b) → Fin (V + 1)) (c : Fin (V + 1)) :
    prefixCount ys c (R b) = countLE ys c.val := by
  unfold prefixCount countLE
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change (i.val < R b ∧ (ys i).val ≤ c.val) ↔ (ys i).val ≤ c.val
  exact and_iff_right i.isLt

lemma passing_exists {b V : ℕ} (ys : Fin (R b) → Fin (V + 1)) :
    ∃ c : ℕ, c ≤ V ∧ b + 1 ≤ countLE ys c := by
  refine ⟨V, le_refl V, ?_⟩
  have hh : countLE ys V = R b := by
    have hmem : ∀ i : Fin (R b), (ys i).val ≤ V := fun i => Nat.le_of_lt_succ (ys i).isLt
    simp [countLE, hmem]
  rw [hh]
  unfold R
  omega

/-- The least numerical candidate reaching the desired rank. -/
def firstPassing {b V : ℕ} (ys : Fin (R b) → Fin (V + 1)) : ℕ :=
  Nat.find (passing_exists ys)

lemma firstPassing_spec {b V : ℕ} (ys : Fin (R b) → Fin (V + 1)) :
    firstPassing ys ≤ V ∧ b + 1 ≤ countLE ys (firstPassing ys) :=
  Nat.find_spec (passing_exists ys)

lemma before_first_fails {b V c : ℕ} (ys : Fin (R b) → Fin (V + 1))
    (hc : c < firstPassing ys) : countLE ys c < b + 1 := by
  have hn := Nat.find_min (passing_exists ys) hc
  have hcv : c ≤ V := le_trans (le_of_lt hc) (firstPassing_spec ys).1
  omega

lemma advance_candidate {b V : ℕ} (ys : Fin (R b) → Fin (V + 1))
    (c : Fin (V + 1)) (hc : c.val < V) (hfail : countLE ys c.val < b + 1) :
    step ys (scanning ys c (R b) (le_refl _)) =
      scanning ys ⟨c.val + 1, by omega⟩ 0 (by omega) := by
  simp [step, scanning, full_scan_count, Nat.not_lt, not_le.mpr hfail, hc]

/-- Actual execution reaches the beginning of each candidate scan up to and
including the least passing candidate. -/
lemma candidate_reaches {b V : ℕ} (ys : Fin (R b) → Fin (V + 1))
    (c : ℕ) (hc : c ≤ firstPassing ys) :
    Reaches ys (initial b V)
      (scanning ys ⟨c, by have hh := (firstPassing_spec ys).1; omega⟩ 0 (by omega)) := by
  induction c with
  | zero =>
    have he : initial b V = scanning ys ⟨0, by omega⟩ 0 (by omega) := by
      apply State.ext <;> simp [initial, scanning]
    rw [he]
    exact Reaches.refl _ _
  | succ c ih =>
    have hcf : c < firstPassing ys := by omega
    have hcv : c < V := by have hh := (firstPassing_spec ys).1; omega
    let cFin : Fin (V + 1) := ⟨c, by omega⟩
    have hstart := ih (by omega)
    have hscan := scan_reaches ys cFin (R b) (le_refl _)
    have hnext := Reaches.single ys (scanning ys cFin (R b) (le_refl _))
    rw [advance_candidate ys cFin hcv (before_first_fails ys hcf)] at hnext
    exact hstart.trans (hscan.trans hnext)

/-- Rank characterization of the actual order statistic used in Sampling. -/
lemma median_eq_of_rank {b V : ℕ} (ys : Fin (R b) → Fin (V + 1))
    (c : Fin (V + 1))
    (hle : b + 1 ≤ countLE ys c.val)
    (hlt : ((Finset.univ : Finset (Fin (R b))).filter (fun i => ys i < c)).card ≤ b) :
    Sampling.median b (fun i => ((ys i).val : ℝ)) = (c.val : ℝ) := by
  apply le_antisymm
  · obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hle
    have hfamily : T ∈ (Finset.univ : Finset (Fin (R b))).powersetCard (b + 1) :=
      Finset.mem_powersetCard.mpr ⟨fun i _ => Finset.mem_univ i, hcard⟩
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    unfold Sampling.median
    apply le_trans (Finset.inf'_le _ hfamily)
    unfold Sampling.subsetMaximum
    rw [dif_pos hne]
    apply Finset.sup'_le
    intro i hi
    have hh := (Finset.mem_filter.mp (hT hi)).2
    exact_mod_cast hh
  · unfold Sampling.median
    apply Finset.le_inf'
    intro T hT
    have hcard : T.card = b + 1 := (Finset.mem_powersetCard.mp hT).2
    have hex : ∃ i ∈ T, c ≤ ys i := by
      by_contra hn
      push_neg at hn
      have hsub : T ⊆ (Finset.univ : Finset (Fin (R b))).filter (fun i => ys i < c) := by
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hn i hi⟩
      have hh : T.card ≤ b := (Finset.card_le_card hsub).trans (by simpa using hlt)
      omega
    obtain ⟨i, hi, hci⟩ := hex
    have hne : T.Nonempty := ⟨i, hi⟩
    unfold Sampling.subsetMaximum
    rw [dif_pos hne]
    apply le_trans _ (Finset.le_sup' _ hi)
    exact_mod_cast hci

lemma firstPassing_median {b V : ℕ} (ys : Fin (R b) → Fin (V + 1)) :
    Sampling.median b (fun i => ((ys i).val : ℝ)) = (firstPassing ys : ℝ) := by
  let c : Fin (V + 1) := ⟨firstPassing ys, by have hh := (firstPassing_spec ys).1; omega⟩
  apply median_eq_of_rank ys c (firstPassing_spec ys).2
  by_cases hc : firstPassing ys = 0
  · have he : ((Finset.univ : Finset (Fin (R b))).filter (fun i => ys i < c)) = ∅ := by
      ext i
      simp [c, hc, Fin.lt_def]
    rw [he]
    simp
  · have hf := before_first_fails ys (c := firstPassing ys - 1) (by omega)
    have he : ((Finset.univ : Finset (Fin (R b))).filter (fun i => ys i < c)) =
        (Finset.univ : Finset (Fin (R b))).filter (fun i => (ys i).val ≤ firstPassing ys - 1) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def, c]
      omega
    rw [he]
    exact Nat.le_of_lt_succ hf

/-- The machine halts after a real finite transition sequence and its output
port contains exactly the natural-valued median of the input array. -/
theorem computes_median {b V : ℕ} (ys : Fin (R b) → Fin (V + 1)) :
    ∃ s : State b V, Reaches ys (initial b V) s ∧ s.halted = true ∧
      ∃ y : Fin (V + 1), output s = some y ∧
        (y.val : ℝ) = Sampling.median b (fun i => ((ys i).val : ℝ)) := by
  let c : Fin (V + 1) := ⟨firstPassing ys, by have hh := (firstPassing_spec ys).1; omega⟩
  let t := scanning ys c (R b) (le_refl _)
  let s : State b V := {t with halted := true}
  have hstart := candidate_reaches ys (firstPassing ys) (le_refl _)
  have hscan := scan_reaches ys c (R b) (le_refl _)
  have hhalt : step ys t = s := by
    have hp := (firstPassing_spec ys).2
    simp [step, t, s, scanning, full_scan_count, c, hp]
  refine ⟨s, hstart.trans (hscan.trans ?_), rfl, c, ?_, ?_⟩
  · exact hhalt ▸ Reaches.single ys t
  · rfl
  · exact (firstPassing_median ys).symm

/-- Exact finite bound for all mutable register configurations. -/
theorem state_card (b V : ℕ) :
    Fintype.card (State b V) = 2 * (V + 1) * (R b + 1) ^ 2 := by
  let e : State b V ≃ Fin (V + 1) × Fin (R b + 1) × Fin (R b + 1) × Bool :=
    { toFun s := (s.candidate, s.cursor, s.counter, s.halted)
      invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
      left_inv s := by cases s; rfl
      right_inv t := by rcases t with ⟨a, i, n, h⟩; rfl }
  rw [Fintype.card_congr e]
  simp [Fintype.card_prod]
  ring

/-- Including the read-only array, every complete configuration has this
finite state bound.  Thus the array costs `R log(V+1)` bits and the actual
transition registers cost `O(log R + log(V+1))` bits. -/
theorem total_configuration_card (b V : ℕ) :
    Fintype.card ((Fin (R b) → Fin (V + 1)) × State b V) =
      (V + 1) ^ R b * (2 * (V + 1) * (R b + 1) ^ 2) := by
  rw [Fintype.card_prod, state_card]
  simp [Fintype.card_fun]

end Paper02.MedianMachine
