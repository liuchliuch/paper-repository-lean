import Paper02.Streaming
import Paper02.StreamingSpace

/-! # Operational finite-register processing of one turnstile update

The hash is evaluated one matrix entry at a time. A retained level is updated
one power moment at a time, and its checksum power is obtained by repeated
multiplication. The temporary single-level summary is included in the memory
bound; it is committed to the actual copy buffer after the checksum loop.
-/

noncomputable section
set_option synthInstance.maxSize 1024
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Paper02.UpdateMachine

open SparseRecovery Hashing Streaming StreamingSpace WeightEval

def counterBound (d ℓ K : ℕ) : ℕ := d + ℓ + 2 * K + 2

local instance summaryFintype (K q : ℕ) [NeZero q] : Fintype (Summary K (ZMod q)) := by
  unfold Summary
  infer_instance

local instance copyStateFintype (J K q : ℕ) [NeZero q] : Fintype (CopyState J K q) := by
  unfold CopyState
  infer_instance

structure State (d J ℓ K q : ℕ) [NeZero q] where
  phase : Fin 5
  buffer : CopyState J K q
  hashes : Fin J → ZMod 2
  level : Fin (J + 2)
  counter : Fin (counterBound d ℓ K)
  localSummary : Summary K (ZMod q)
  hashAcc : ZMod 2
  power : ZMod q
  keep : Bool
  deriving Fintype

variable {d J ℓ K q : ℕ} [Fact q.Prime]

def hashRegs (s : CopyState J K q) (h : Fin J → ZMod 2)
    (r c : ℕ) (hr : r ≤ J) (hc : c ≤ ℓ) (a : ZMod 2) : State d J ℓ K q :=
  ⟨0, s, h, ⟨r, by omega⟩, ⟨c, by unfold counterBound; omega⟩, 0, a, 1, false⟩

def levelRegs (s : CopyState J K q) (h : Fin J → ZMod 2)
    (j : ℕ) (hj : j ≤ J + 1) (keep : Bool) : State d J ℓ K q :=
  ⟨1, s, h, ⟨j, by omega⟩, ⟨0, by unfold counterBound; omega⟩, 0, 0, 1, keep⟩

def momentRegs (s : CopyState J K q) (h : Fin J → ZMod 2)
    (j : Fin (J + 1)) (v : Summary K (ZMod q))
    (t : ℕ) (ht : t ≤ 2 * K) (p : ZMod q) : State d J ℓ K q :=
  ⟨2, s, h, ⟨j.val, by omega⟩, ⟨t, by unfold counterBound; omega⟩, v, 0, p, true⟩

def powerRegs (s : CopyState J K q) (h : Fin J → ZMod 2)
    (j : Fin (J + 1)) (v : Summary K (ZMod q))
    (e : ℕ) (he : e ≤ d) (p : ZMod q) : State d J ℓ K q :=
  ⟨3, s, h, ⟨j.val, by omega⟩, ⟨e, by unfold counterBound; omega⟩, v, 0, p, true⟩

def finish (s : CopyState J K q) : State d J ℓ K q :=
  ⟨4, s, 0, 0, ⟨0, by unfold counterBound; omega⟩, 0, 0, 1, false⟩

def initial (s : CopyState J K q) : State d J ℓ K q :=
  hashRegs s 0 0 0 (by omega) (by omega) 0

def nextKeep (h : Fin J → ZMod 2) (j : ℕ) : Bool :=
  if hj : j < J then decide (h ⟨j, hj⟩ = 0) else false

def writeMoment (v : Summary K (ZMod q)) (t : Fin (2 * K))
    (a : ZMod q) : Summary K (ZMod q) := (Function.update v.1 t a, v.2)

/-- Every branch performs a bounded number of field operations and register
reads/writes. No branch evaluates a sum, power, hash, or complete update. -/
def step (seed : CopySeed J ℓ q) (i : Fin d) (δ : ZMod q)
    (s : State d J ℓ K q) : State d J ℓ K q :=
  if s.phase.val = 0 then
    if hr : s.level.val < J then
      if hc : s.counter.val < ℓ then
        hashRegs s.buffer s.hashes s.level.val (s.counter.val + 1) hr.le (by omega)
          (s.hashAcc + (seed.1 ⟨s.level.val, hr⟩).1 ⟨s.counter.val, hc⟩ *
            (if i.val.testBit s.counter.val then 1 else 0))
      else
        hashRegs s.buffer
          (Function.update s.hashes ⟨s.level.val, hr⟩
            (s.hashAcc + (seed.1 ⟨s.level.val, hr⟩).2))
          (s.level.val + 1) 0 (by omega) (by omega) 0
    else levelRegs s.buffer s.hashes 0 (by omega) true
  else if s.phase.val = 1 then
    if hj : s.level.val < J + 1 then
      if s.keep then
        momentRegs s.buffer s.hashes ⟨s.level.val, hj⟩
          (s.buffer ⟨s.level.val, hj⟩) 0 (by omega) 1
      else levelRegs s.buffer s.hashes (s.level.val + 1) (by omega) false
    else finish s.buffer
  else if s.phase.val = 2 then
    if hj : s.level.val < J + 1 then
      if ht : s.counter.val < 2 * K then
        momentRegs s.buffer s.hashes ⟨s.level.val, hj⟩
          (writeMoment s.localSummary ⟨s.counter.val, ht⟩
            (s.localSummary.1 ⟨s.counter.val, ht⟩ + δ * s.power))
          (s.counter.val + 1) (by omega) (s.power * (i.val + 1 : ZMod q))
      else powerRegs s.buffer s.hashes ⟨s.level.val, hj⟩ s.localSummary 0 (by omega) 1
    else finish s.buffer
  else if s.phase.val = 3 then
    if hj : s.level.val < J + 1 then
      if he : s.counter.val < i.val + 1 then
        powerRegs s.buffer s.hashes ⟨s.level.val, hj⟩ s.localSummary
          (s.counter.val + 1) (by have hi := i.isLt; omega)
          (s.power * seed.2 ⟨s.level.val, hj⟩)
      else
        levelRegs (Function.update s.buffer ⟨s.level.val, hj⟩
          (s.localSummary.1, s.localSummary.2 + δ * s.power)) s.hashes
          (s.level.val + 1) (by omega) (nextKeep s.hashes s.level.val)
    else finish s.buffer
  else s

abbrev Reaches (seed : CopySeed J ℓ q) (i : Fin d) (δ : ZMod q) :=
  Relation.ReflTransGen (fun s t : State d J ℓ K q => step seed i δ s = t)

def columnTerm (seed : CopySeed J ℓ q) (i : Fin d) (r : Fin J) (c : ℕ) : ZMod 2 :=
  if hc : c < ℓ then (seed.1 r).1 ⟨c, hc⟩ *
    (if i.val.testBit c then 1 else 0) else 0

def partialRow (seed : CopySeed J ℓ q) (i : Fin d) (r : Fin J) (c : ℕ) : ZMod 2 :=
  ∑ a ∈ Finset.range c, columnTerm seed i r a

lemma columns_reach (seed : CopySeed J ℓ q) (i : Fin d) (δ : ZMod q)
    (s : CopyState J K q) (h : Fin J → ZMod 2) (r : Fin J)
    (c : ℕ) (hc : c ≤ ℓ) :
    Reaches seed i δ (hashRegs s h r.val 0 r.isLt.le (by omega) 0)
      (hashRegs s h r.val c r.isLt.le hc (partialRow seed i r c)) := by
  induction c with
  | zero => exact Relation.ReflTransGen.refl
  | succ c ih =>
    have hc' : c < ℓ := by omega
    apply (ih hc'.le).tail
    simp [step, hashRegs, partialRow, Finset.sum_range_succ, columnTerm, r.isLt, hc']

lemma partialRow_all (seed : CopySeed J ℓ q) (i : Fin d) (r : Fin J) :
    partialRow seed i r ℓ + (seed.1 r).2 =
      Hashing.hash (binaryVector ℓ i.val) seed.1 r := by
  unfold partialRow Hashing.hash rowHash
  rw [← Fin.sum_univ_eq_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  simp [columnTerm, binaryVector, c.isLt]

def partialHashes (seed : CopySeed J ℓ q) (i : Fin d) (n : ℕ) : Fin J → ZMod 2 :=
  fun r => if r.val < n then Hashing.hash (binaryVector ℓ i.val) seed.1 r else 0

lemma partialHashes_succ (seed : CopySeed J ℓ q) (i : Fin d) (r : Fin J) :
    Function.update (partialHashes seed i r.val) r
      (Hashing.hash (binaryVector ℓ i.val) seed.1 r) = partialHashes seed i (r.val + 1) := by
  funext a
  by_cases ha : a = r
  · subst a; simp [partialHashes]
  · have hv : a.val ≠ r.val := fun h => ha (Fin.ext h)
    simp only [Function.update_of_ne ha, partialHashes]
    by_cases hlt : a.val < r.val
    · simp [hlt, show a.val < r.val + 1 by omega]
    · simp [hlt, show ¬ a.val < r.val + 1 by omega]

lemma rows_reach (seed : CopySeed J ℓ q) (i : Fin d) (δ : ZMod q)
    (s : CopyState J K q) (n : ℕ) (hn : n ≤ J) :
    Reaches seed i δ (initial s)
      (hashRegs s (partialHashes seed i n) n 0 hn (by omega) 0) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    have hn' : n < J := by omega
    have hr := (ih hn'.le).trans
      (columns_reach seed i δ s (partialHashes seed i n) ⟨n, hn'⟩ ℓ (le_refl _))
    apply hr.tail
    simp [step, hashRegs, hn', partialRow_all]
    exact partialHashes_succ seed i ⟨n, hn'⟩

theorem hash_reaches (seed : CopySeed J ℓ q) (i : Fin d) (δ : ZMod q)
    (s : CopyState J K q) :
    Reaches seed i δ (initial s)
      (levelRegs s (Hashing.hash (binaryVector ℓ i.val) seed.1) 0 (by omega) true) := by
  have hh : partialHashes seed i J = Hashing.hash (binaryVector ℓ i.val) seed.1 := by
    funext r; simp [partialHashes, r.isLt]
  apply (rows_reach seed i δ s J (le_refl _)).tail
  simp [step, hashRegs, hh]

def partialMoments (i : Fin d) (δ : ZMod q) (v : Summary K (ZMod q))
    (n : ℕ) : Summary K (ZMod q) :=
  (fun t => if t.val < n then v.1 t + δ * (i.val + 1 : ZMod q) ^ t.val else v.1 t, v.2)

@[simp] lemma partialMoments_zero (i : Fin d) (δ : ZMod q) (v : Summary K (ZMod q)) :
    partialMoments i δ v 0 = v := by
  ext t <;> simp [partialMoments]

lemma partialMoments_succ (i : Fin d) (δ : ZMod q) (v : Summary K (ZMod q))
    (t : Fin (2 * K)) :
    writeMoment (partialMoments i δ v t.val) t
      ((partialMoments i δ v t.val).1 t + δ * (i.val + 1 : ZMod q) ^ t.val) =
      partialMoments i δ v (t.val + 1) := by
  apply Prod.ext
  · funext a
    by_cases ha : a = t
    · subst a; simp [writeMoment, partialMoments]
    · have hv : a.val ≠ t.val := fun h => ha (Fin.ext h)
      simp only [writeMoment, partialMoments, Function.update_of_ne ha]
      by_cases hlt : a.val < t.val
      · simp [hlt, show a.val < t.val + 1 by omega]
      · simp [hlt, show ¬ a.val < t.val + 1 by omega]
  · rfl

lemma moments_reach (seed : CopySeed J ℓ q) (i : Fin d) (δ : ZMod q)
    (s : CopyState J K q) (h : Fin J → ZMod 2) (j : Fin (J + 1))
    (v : Summary K (ZMod q)) (n : ℕ) (hn : n ≤ 2 * K) :
    Reaches seed i δ (momentRegs s h j v 0 (by omega) 1)
      (momentRegs s h j (partialMoments i δ v n) n hn ((i.val + 1 : ZMod q) ^ n)) := by
  induction n with
  | zero => simpa using (Relation.ReflTransGen.refl : Reaches seed i δ
      (momentRegs s h j v 0 (by omega) 1) _)
  | succ n ih =>
    have hn' : n < 2 * K := by omega
    apply (ih hn'.le).tail
    simp [step, momentRegs, j.isLt, hn', pow_succ]
    exact partialMoments_succ i δ v ⟨n, hn'⟩

lemma powers_reach (seed : CopySeed J ℓ q) (i : Fin d) (δ : ZMod q)
    (s : CopyState J K q) (h : Fin J → ZMod 2) (j : Fin (J + 1))
    (v : Summary K (ZMod q)) (e : ℕ) (he : e ≤ i.val + 1) :
    Reaches seed i δ (powerRegs s h j v 0 (by omega) 1)
      (powerRegs s h j v e (by have hi := i.isLt; omega) (seed.2 j ^ e)) := by
  induction e with
  | zero => simpa only [pow_zero] using (Relation.ReflTransGen.refl : Reaches seed i δ
      (powerRegs s h j v 0 (by omega) 1) _)
  | succ e ih =>
    have he' : e < i.val + 1 := by omega
    apply (ih he'.le).tail
    simp [step, powerRegs, j.isLt, he', pow_succ]

lemma one_level_reach (seed : CopySeed J ℓ q) (i : Fin d) (δ : ZMod q)
    (s : CopyState J K q) (h : Fin J → ZMod 2) (j : Fin (J + 1)) :
    Reaches seed i δ (levelRegs s h j.val j.isLt.le true)
      (levelRegs (Function.update s j (updateSummary K (seed.2 j) (s j) i δ)) h
        (j.val + 1) (by omega) (nextKeep h j.val)) := by
  have start : step seed i δ (levelRegs s h j.val j.isLt.le true) =
      momentRegs s h j (s j) 0 (by omega) 1 := by
    simp [step, levelRegs, j.isLt]
  have middle : step seed i δ
      (momentRegs s h j (partialMoments i δ (s j) (2 * K)) (2 * K) (le_refl _)
        ((i.val + 1 : ZMod q) ^ (2 * K))) =
      powerRegs s h j (partialMoments i δ (s j) (2 * K)) 0 (by omega) 1 := by
    simp [step, momentRegs, j.isLt]
  have hr : Reaches seed i δ (levelRegs s h j.val j.isLt.le true)
      (powerRegs s h j (partialMoments i δ (s j) (2 * K)) 0 (by omega) 1) :=
    ((show Reaches seed i δ (levelRegs s h j.val j.isLt.le true)
      (momentRegs s h j (s j) 0 (by omega) 1) from Relation.ReflTransGen.single start).trans
      (moments_reach seed i δ s h j (s j) (2 * K) (le_refl _))).tail middle
  apply (hr.trans (powers_reach seed i δ s h j _ (i.val + 1) (le_refl _))).tail
  have hu : ((partialMoments i δ (s j) (2 * K)).1,
      (partialMoments i δ (s j) (2 * K)).2 + δ * seed.2 j ^ (i.val + 1)) =
      updateSummary K (seed.2 j) (s j) i δ := by
    apply Prod.ext
    · funext t
      simp [partialMoments, updateSummary, t.isLt]
    · rfl
  simp [step, powerRegs, j.isLt, hu]

def prefixKeep (h : Fin J → ZMod 2) (n : ℕ) : Bool :=
  if n ≤ J then decide (PrefixZero n h) else false

@[simp] lemma prefixKeep_zero (h : Fin J → ZMod 2) : prefixKeep h 0 = true := by
  simp [prefixKeep, PrefixZero]

lemma prefixKeep_succ (h : Fin J → ZMod 2) (j : ℕ) (hj : j ≤ J) :
    prefixKeep h (j + 1) = if prefixKeep h j then nextKeep h j else false := by
  by_cases hj' : j < J
  · have hp : PrefixZero (j + 1) h ↔ PrefixZero j h ∧ h ⟨j, hj'⟩ = 0 := by
      constructor
      · intro hz
        exact ⟨fun r hr => hz r (by omega), hz ⟨j, hj'⟩ (by simp)⟩
      · rintro ⟨hz, hjz⟩ r hr
        by_cases he : r.val = j
        · have hre : r = ⟨j, hj'⟩ := Fin.ext he
          simpa only [hre] using hjz
        · exact hz r (by omega)
    simp only [prefixKeep, hj, if_pos, show j + 1 ≤ J by omega, nextKeep, dif_pos hj']
    by_cases hpj : PrefixZero j h <;> simp [hp, hpj]
  · have he : j = J := by omega
    subst j
    simp [prefixKeep, nextKeep]

/-- The semantic update with an already reduced input increment. -/
def fieldUpdate (seed : CopySeed J ℓ q) (i : Fin d) (δ : ZMod q)
    (s : CopyState J K q) : CopyState J K q :=
  fun j => if PrefixZero j.val (Hashing.hash (binaryVector ℓ i.val) seed.1) then
    updateSummary K (seed.2 j) (s j) i δ else s j

def partialBuffer (seed : CopySeed J ℓ q) (i : Fin d) (δ : ZMod q)
    (s : CopyState J K q) (n : ℕ) : CopyState J K q :=
  fun j => if j.val < n then fieldUpdate seed i δ s j else s j

lemma partialBuffer_succ (seed : CopySeed J ℓ q) (i : Fin d) (δ : ZMod q)
    (s : CopyState J K q) (j : Fin (J + 1)) :
    Function.update (partialBuffer seed i δ s j.val) j (fieldUpdate seed i δ s j) =
      partialBuffer seed i δ s (j.val + 1) := by
  funext a
  by_cases ha : a = j
  · subst a; simp [partialBuffer]
  · have hv : a.val ≠ j.val := fun h => ha (Fin.ext h)
    simp only [Function.update_of_ne ha, partialBuffer]
    by_cases hlt : a.val < j.val
    · simp [hlt, show a.val < j.val + 1 by omega]
    · simp [hlt, show ¬ a.val < j.val + 1 by omega]

theorem levels_reach (seed : CopySeed J ℓ q) (i : Fin d) (δ : ZMod q)
    (s : CopyState J K q) (n : ℕ) (hn : n ≤ J + 1) :
    let h := Hashing.hash (binaryVector ℓ i.val) seed.1
    Reaches seed i δ (levelRegs s h 0 (by omega) true)
      (levelRegs (partialBuffer seed i δ s n) h n hn (prefixKeep h n)) := by
  dsimp only
  let h := Hashing.hash (binaryVector ℓ i.val) seed.1
  change Reaches seed i δ (levelRegs s h 0 (by omega) true)
    (levelRegs (partialBuffer seed i δ s n) h n hn (prefixKeep h n))
  induction n with
  | zero => simpa [partialBuffer] using (Relation.ReflTransGen.refl : Reaches seed i δ
      (levelRegs s h 0 (by omega) true) _)
  | succ n ih =>
    have hn' : n < J + 1 := by omega
    have hread : partialBuffer seed i δ s n ⟨n, hn'⟩ = s ⟨n, hn'⟩ := by
      simp [partialBuffer]
    have hp : prefixKeep h (n + 1) = if prefixKeep h n then nextKeep h n else false :=
      prefixKeep_succ h n (by omega)
    by_cases hk : PrefixZero n h
    · have hkeep : prefixKeep h n = true := by simp [prefixKeep, show n ≤ J by omega, hk]
      have hr := one_level_reach seed i δ (partialBuffer seed i δ s n) h ⟨n, hn'⟩
      have hwrite : Function.update (partialBuffer seed i δ s n) ⟨n, hn'⟩
          (updateSummary K (seed.2 ⟨n, hn'⟩) (partialBuffer seed i δ s n ⟨n, hn'⟩) i δ) =
          partialBuffer seed i δ s (n + 1) := by
        rw [hread]
        have hj : fieldUpdate seed i δ s ⟨n, hn'⟩ =
            updateSummary K (seed.2 ⟨n, hn'⟩) (s ⟨n, hn'⟩) i δ := by
          change (if PrefixZero n h then _ else _) = _
          rw [if_pos hk]
        rw [← hj]
        exact partialBuffer_succ seed i δ s ⟨n, hn'⟩
      have prior := ih hn'.le
      rw [hkeep] at prior
      simpa only [hp, hkeep, hwrite, Bool.true_eq, ite_true] using prior.trans hr
    · have hkeep : prefixKeep h n = false := by simp [prefixKeep, show n ≤ J by omega, hk]
      have hstay : partialBuffer seed i δ s (n + 1) = partialBuffer seed i δ s n := by
        rw [← partialBuffer_succ seed i δ s ⟨n, hn'⟩]
        have hj : fieldUpdate seed i δ s ⟨n, hn'⟩ = s ⟨n, hn'⟩ := by
          change (if PrefixZero n h then _ else _) = _
          rw [if_neg hk]
        rw [hj, ← hread, Function.update_eq_self]
      apply (ih hn'.le).tail
      simp [step, levelRegs, hkeep, hn', hp, hstay]

/-- Actual bounded-register execution of the semantic field update. -/
theorem machine_correct (seed : CopySeed J ℓ q) (i : Fin d) (δ : ZMod q)
    (s : CopyState J K q) :
    Reaches seed i δ (initial s) (finish (fieldUpdate seed i δ s)) ∧
      step seed i δ (finish (fieldUpdate seed i δ s)) = finish (fieldUpdate seed i δ s) := by
  have hbuf : partialBuffer seed i δ s (J + 1) = fieldUpdate seed i δ s := by
    funext j; simp [partialBuffer, j.isLt]
  refine ⟨?_, ?_⟩
  · apply ((hash_reaches seed i δ s).trans (levels_reach seed i δ s (J + 1) (le_refl _))).tail
    simp [step, levelRegs, hbuf]
  · simp [step, finish]

/-- The operational machine computes exactly the public streaming transition. -/
theorem machine_update (seed : CopySeed J ℓ q) (i : Fin d) (Δ : ℤ)
    (s : CopyState J K q) :
    Reaches seed i (Δ : ZMod q) (initial s) (finish (Streaming.update K seed s (i, Δ))) ∧
      step seed i (Δ : ZMod q) (finish (Streaming.update K seed s (i, Δ))) =
        finish (Streaming.update K seed s (i, Δ)) :=
  machine_correct seed i (Δ : ZMod q) s

/-- Every live register, including the temporary current-level summary. Since
`registerBits n = Nat.log 2 n + 1`, the dimension enters logarithmically. -/
def machineBits (d J ℓ K q : ℕ) : ℕ :=
  registerBits 5 + ((J + 1) * ((2 * K + 1) * registerBits q) +
    (J * registerBits 2 + (registerBits (J + 2) +
    (registerBits (counterBound d ℓ K) + ((2 * K + 1) * registerBits q +
    (registerBits 2 + (registerBits q + 1)))))))

theorem machine_fits : FitsBits (State d J ℓ K q) (machineBits d J ℓ K q) := by
  let e : State d J ℓ K q ≃
      Fin 5 × CopyState J K q × (Fin J → ZMod 2) × Fin (J + 2) ×
      Fin (counterBound d ℓ K) × Summary K (ZMod q) × ZMod 2 × ZMod q × Bool :=
    { toFun := fun s => (s.phase, s.buffer, s.hashes, s.level, s.counter,
        s.localSummary, s.hashAcc, s.power, s.keep)
      invFun := fun s => ⟨s.1, s.2.1, s.2.2.1, s.2.2.2.1, s.2.2.2.2.1,
        s.2.2.2.2.2.1, s.2.2.2.2.2.2.1, s.2.2.2.2.2.2.2.1, s.2.2.2.2.2.2.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hb : FitsBits Bool 1 := by norm_num [FitsBits]
  have hh := prod_fits (fin_fits 5)
    (prod_fits (array_fits (J + 1) (summary_fits K q))
      (prod_fits (array_fits J (field_fits 2))
        (prod_fits (fin_fits (J + 2))
          (prod_fits (fin_fits (counterBound d ℓ K))
            (prod_fits (summary_fits K q)
              (prod_fits (field_fits 2) (prod_fits (field_fits q) hb)))))))
  unfold FitsBits at *
  rw [Fintype.card_congr e]
  exact hh

def seedBits (J ℓ q : ℕ) : ℕ := J * (ℓ + 1) + (J + 1) * registerBits q

lemma seed_fits : FitsBits (CopySeed J ℓ q) (seedBits J ℓ q) := by
  have hh : FitsBits (Hashing.Seed J ℓ) (J * (ℓ + 1)) := by
    rw [FitsBits, Hashing.card_seed]
  exact prod_fits hh (array_fits (J + 1) (field_fits q))

/-- Count the stored random seed, reduced increment and index as well as all
online update registers. This bound is independent of stream length and of
the bit length or magnitude of intermediate frequencies. -/
theorem machine_with_input_fits :
    FitsBits (CopySeed J ℓ q × Fin d × ZMod q × State d J ℓ K q)
      (seedBits J ℓ q + (registerBits d + (registerBits q + machineBits d J ℓ K q))) :=
  prod_fits seed_fits (prod_fits (fin_fits d) (prod_fits (field_fits q) machine_fits))

end Paper02.UpdateMachine
