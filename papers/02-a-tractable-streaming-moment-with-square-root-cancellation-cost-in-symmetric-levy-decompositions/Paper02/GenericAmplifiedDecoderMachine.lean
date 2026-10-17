import Paper02.GenericCopyDecoderMachine
import Paper02.AmplifiedDecoderMachine
import Paper02.MedianMachine

/-! # Sequential decoding of all copies and the actual median program -/
set_option synthInstance.maxSize 1024
noncomputable section

namespace Paper02.GenericAmplifiedDecoderMachine

open Streaming GenericWeightMachine
variable {w : ℤ → ℕ}
local instance evaluatorFintype {U : ℕ} (ev : Evaluator U w) : Fintype ev.Carrier := ev.finite
abbrev R (b : ℕ) := MedianMachine.R b
abbrev V (J K : ℕ) := GenericCopyDecoderMachine.outputBound J K
abbrev Buffer (b J K : ℕ) := Fin (R b) → Fin (V J K + 1)

inductive State (d U b J K q : ℕ) (ev : Evaluator U w) [NeZero q] where
  | collect : Fin (R b + 1) → Buffer b J K → GenericCopyDecoderMachine.State d U J K q ev → State d U b J K q ev
  | median : Buffer b J K → MedianMachine.State b (V J K) → State d U b J K q ev
  | halt : Fin (V J K + 1) → State d U b J K q ev
  deriving Fintype

variable {d U b J ℓ K q : ℕ} [Fact q.Prime] (ev : Evaluator U w)

def step (seeds : Fin (R b) → CopySeed J ℓ q) (states : Fin (R b) → CopyState J K q) :
    State d U b J K q ev → State d U b J K q ev
  | .collect i buffer c =>
      if hi : i.val < R b then
        if GenericCopyDecoderMachine.done ev c then
          let buffer' := Function.update buffer ⟨i.val, hi⟩ (GenericCopyDecoderMachine.result ev c)
          if hn : i.val + 1 < R b then
            .collect ⟨i.val + 1, by omega⟩ buffer' (GenericCopyDecoderMachine.initial ev (states ⟨i.val + 1, hn⟩))
          else .median buffer' (MedianMachine.initial b (V J K))
        else .collect i buffer (GenericCopyDecoderMachine.step ev (seeds ⟨i.val, hi⟩) (states ⟨i.val, hi⟩) c)
      else .median buffer (MedianMachine.initial b (V J K))
  | .median buffer m => if m.halted then .halt m.candidate else .median buffer (MedianMachine.step buffer m)
  | .halt out => .halt out

def initial (states : Fin (R b) → CopyState J K q) : State d U b J K q ev :=
  .collect 0 (fun _ => 0) (GenericCopyDecoderMachine.initial ev (states ⟨0, by unfold R MedianMachine.R; omega⟩))

def Reaches (seeds : Fin (R b) → CopySeed J ℓ q) (states : Fin (R b) → CopyState J K q)
    (s t : State d U b J K q ev) : Prop :=
  Relation.ReflTransGen (fun x y => step ev seeds states x = y) s t

def bufferPrefix (ys : Buffer b J K) (n : ℕ) : Buffer b J K := fun i => if i.val < n then ys i else 0

lemma prefix_update (ys : Buffer b J K) (i : Fin (R b)) :
    Function.update (bufferPrefix ys i.val) i (ys i) = bufferPrefix ys (i.val + 1) := by
  funext k
  by_cases hki : k = i
  · subst k; simp [bufferPrefix]
  · rw [Function.update_of_ne hki]
    have he : (k.val < i.val + 1) = (k.val < i.val) := propext (by
      have hne : k.val ≠ i.val := fun h => hki (Fin.ext h)
      omega)
    simp only [bufferPrefix, he]

def expected (states : Fin (R b) → CopyState J K q) (ys : Buffer b J K)
    (n : ℕ) (hn : n ≤ R b) : State d U b J K q ev :=
  if h : n < R b then
    .collect ⟨n, by omega⟩ (bufferPrefix ys n) (GenericCopyDecoderMachine.initial ev (states ⟨n, h⟩))
  else .median ys (MedianMachine.initial b (V J K))

lemma lift_copy (seeds : Fin (R b) → CopySeed J ℓ q) (states : Fin (R b) → CopyState J K q)
    (i : Fin (R b)) (buffer : Buffer b J K) {s t : GenericCopyDecoderMachine.State d U J K q ev}
    (h : GenericCopyDecoderMachine.Reaches ev (d := d) (U := U) (seeds i) (states i) s t) :
    Reaches ev (d := d) (U := U) seeds states (.collect ⟨i.val, by omega⟩ buffer s) (.collect ⟨i.val, by omega⟩ buffer t) := by
  apply Relation.ReflTransGen.lift' (fun c => State.collect ⟨i.val, by omega⟩ buffer c) _ h
  intro a c hac
  by_cases hd : GenericCopyDecoderMachine.done ev a = true
  · have he : a = c := hac.symm.trans (GenericCopyDecoderMachine.done_fixed ev (seeds i) (states i) a hd) |>.symm
    rw [← he]
  · exact Relation.ReflTransGen.single (by
      simpa only [step, dif_pos i.isLt, hd, ↓reduceIte] using congrArg (fun c => State.collect ⟨i.val, by omega⟩ buffer c) hac)

lemma collect_reaches (seeds : Fin (R b) → CopySeed J ℓ q) (states : Fin (R b) → CopyState J K q)
    (ys : Buffer b J K)
    (runs : ∀ i, GenericCopyDecoderMachine.Reaches ev (d := d) (U := U) (seeds i) (states i)
      (GenericCopyDecoderMachine.initial ev (d := d) (U := U) (states i)) (.halt (ys i)))
    (n : ℕ) (hn : n ≤ R b) :
    Reaches ev (d := d) (U := U) seeds states (initial ev (d := d) (U := U) states) (expected ev (d := d) (U := U) states ys n hn) := by
  induction n with
  | zero =>
    have hr : 0 < R b := by unfold R MedianMachine.R; omega
    simpa only [expected, dif_pos hr, bufferPrefix, Nat.not_lt_zero, if_false, initial] using
      (Relation.ReflTransGen.refl : Reaches ev (d := d) (U := U) seeds states (initial ev (d := d) (U := U) states) _)
  | succ n ih =>
    have hnt : n < R b := by omega
    let i : Fin (R b) := ⟨n, hnt⟩
    have hh := lift_copy ev seeds states i (bufferPrefix ys n) (runs i)
    have hp := (ih hnt.le).trans (by simpa only [expected, dif_pos hnt] using hh)
    apply hp.tail
    dsimp only [i]
    simp only [step, dif_pos hnt, GenericCopyDecoderMachine.done, ↓reduceIte, GenericCopyDecoderMachine.result]
    rw [show Function.update (bufferPrefix ys n) ⟨n, hnt⟩ (ys i) = bufferPrefix ys (n + 1) from prefix_update ys i]
    unfold expected
    split_ifs with hnext
    · rfl
    · have hnR : n + 1 = R b := by omega
      have hbuf : bufferPrefix ys (n + 1) = ys := by funext j; simp [bufferPrefix, hnR, j.isLt]
      rw [hbuf]

lemma lift_median (seeds : Fin (R b) → CopySeed J ℓ q) (states : Fin (R b) → CopyState J K q)
    (ys : Buffer b J K) {s t : MedianMachine.State b (V J K)} (h : MedianMachine.Reaches ys s t) :
    Reaches ev (d := d) (U := U) seeds states (.median ys s) (.median ys t) := by
  obtain ⟨n, hn⟩ := h
  have iter : ∀ n : ℕ, Relation.ReflTransGen (fun a c => MedianMachine.step ys a = c) s ((MedianMachine.step ys)^[n] s) := by
    intro n
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ n ih =>
      apply ih.tail
      exact (Function.iterate_succ_apply' _ _ _).symm
  apply Relation.ReflTransGen.lift' (State.median ys) _ (hn ▸ iter n)
  intro a c hac
  by_cases ha : a.halted = true
  · have he : a = c := by simpa only [MedianMachine.step, ha, ↓reduceIte] using hac
    rw [← he]
  · exact Relation.ReflTransGen.single (by simpa only [step, ha, ↓reduceIte] using congrArg (State.median ys) hac)

/-- Actual sequential copy decoding, output buffering and median execution. -/
theorem machine_correct (hdq : d < q) (hUq : 2 * U < q)
    (hw0 : w 0 = 0) (hw3 : ∀ k, w k ≤ 3)
    (seeds : Fin (R b) → CopySeed J ℓ q) (states : Fin (R b) → CopyState J K q) :
    ∃ out : Fin (V J K + 1), Reaches ev (d := d) (U := U) seeds states (initial ev (d := d) (U := U) states) (.halt out) ∧
      (out.val : ℝ) = Sampling.median b (fun i => Streaming.output (d := d) (fun k => (w k : ℝ)) U K (seeds i) (states i)) := by
  have copy (i : Fin (R b)) := GenericCopyDecoderMachine.machine_correct ev hdq hUq hw0 hw3 (seeds i) (states i)
  let ys : Buffer b J K := fun i => Classical.choose (copy i)
  have runs (i : Fin (R b)) := (Classical.choose_spec (copy i)).1
  have specs (i : Fin (R b)) := (Classical.choose_spec (copy i)).2
  have hc := collect_reaches ev seeds states ys runs (R b) (le_refl _)
  have hcollect : Reaches ev (d := d) (U := U) seeds states (initial ev (d := d) (U := U) states) (.median ys (MedianMachine.initial b (V J K))) := by
    simpa only [expected, lt_self_iff_false, ↓reduceDIte] using hc
  obtain ⟨finish, hmedian, hhalt, out, hout, hspec⟩ := MedianMachine.computes_median ys
  have hm := lift_median ev (d := d) (U := U) seeds states ys hmedian
  refine ⟨out, (hcollect.trans hm).tail ?_, ?_⟩
  · have ho : finish.candidate = out := by simpa [MedianMachine.output, hhalt] using hout
    simp [step, hhalt, ho]
  · rw [hspec]
    congr 1
    funext i
    exact specs i


def done : State d U b J K q ev → Bool
  | .halt _ => true
  | _ => false

def result : State d U b J K q ev → Fin (V J K + 1)
  | .halt out => out
  | _ => 0


open AmplifiedDecoderMachine (terminal_unique)

/-- Failure refers to an actual halting execution of the program. Determinism
makes this exactly the event used in the finite-seed probability proof. -/
def FailureEvent (seeds : Fin (R b) → CopySeed J ℓ q)
    (states : Fin (R b) → CopyState J K q) (F ε : ℝ) : Prop :=
  ∃ out : Fin (V J K + 1), Reaches ev (d := d) (U := U) seeds states
    (initial ev (d := d) (U := U) states) (.halt out) ∧ ε * F < |(out.val : ℝ) - F|

lemma failureEvent_iff (hdq : d < q) (hUq : 2 * U < q)
    (hw0 : w 0 = 0) (hw3 : ∀ k, w k ≤ 3)
    (seeds : Fin (R b) → CopySeed J ℓ q) (states : Fin (R b) → CopyState J K q) (F ε : ℝ) :
    FailureEvent ev (d := d) (U := U) seeds states F ε ↔ ε * F <
      |Sampling.median b (fun i => Streaming.output (d := d) (fun k => (w k : ℝ)) U K (seeds i) (states i)) - F| := by
  obtain ⟨out, hr, hs⟩ := machine_correct ev hdq hUq hw0 hw3 seeds states
  constructor
  · rintro ⟨other, ho, hbad⟩
    have he : (.halt other : State d U b J K q ev) = .halt out :=
      terminal_unique (step ev seeds states) ho hr rfl rfl
    have hy : other = out := State.halt.inj he
    simpa only [hy, hs] using hbad
  · intro hbad
    exact ⟨out, hr, by simpa only [hs] using hbad⟩

/-- The full probability theorem now concerns actual program executions,
including sparse recovery, all decoding work, the supplied weight evaluation and median. -/
theorem bounded_weights_stream_failure
    (hw0 : w 0 = 0) (hw1 : ∀ k, k ≠ 0 → 1 ≤ w k) (hw3 : ∀ k, w k ≤ 3)
    (hdℓ : d ≤ 2 ^ ℓ) (hdJ : d ≤ 2 ^ J) (hdq : d < q)
    (hUq : 2 * U < q) (hK : 2 ≤ K)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hKbig : 65536 / ε ^ 2 ≤ (K : ℝ))
    (hqbig : (J + 1 : ℕ) * ((d : ℝ) / q) ≤ 1 / 64)
    (b : ℕ) (hR : 8 * Real.log (1 / δ) ≤ (2 * b + 1 : ℕ))
    (stream : List (SparseRecovery.Update d))
    (hv : ∀ i, -(U : ℤ) ≤ SparseRecovery.finalVector stream i ∧ SparseRecovery.finalVector stream i ≤ U) :
    ((Sampling.FiniteLaw.uniform (CopySeed J ℓ q)).iid (Fin (R b))).prob
      {seeds | FailureEvent ev (d := d) (U := U) seeds
        (fun i => run K (seeds i) stream) (moment (fun k => (w k : ℝ)) (SparseRecovery.finalVector stream)) ε} ≤ δ := by
  have he : {seeds : Fin (R b) → CopySeed J ℓ q | FailureEvent ev (d := d) (U := U) seeds
      (fun i => run K (seeds i) stream) (moment (fun k => (w k : ℝ)) (SparseRecovery.finalVector stream)) ε} =
      {seeds | ε * moment (fun k => (w k : ℝ)) (SparseRecovery.finalVector stream) <
        |Sampling.median b (fun i => output (d := d) (fun k => (w k : ℝ)) U K (seeds i) (run K (seeds i) stream)) -
          moment (fun k => (w k : ℝ)) (SparseRecovery.finalVector stream)|} := by
    ext seeds
    exact failureEvent_iff ev hdq hUq hw0 hw3 seeds _ _ _
  rw [he]
  exact Streaming.bounded_weights_amplified (fun k => (w k : ℝ))
    (by simp [hw0]) (fun k hk => by dsimp; exact_mod_cast hw1 k hk)
    (fun k => by dsimp; exact_mod_cast hw3 k) hdℓ hdJ hdq hUq hK hε hε1 hδ hKbig hqbig b hR stream hv

open StreamingSpace WeightEval

def medianBits (b V : ℕ) : ℕ := registerBits (V + 1) + 2 * registerBits (R b + 1) + 1

def bufferBits (b J K : ℕ) : ℕ := R b * registerBits (V J K + 1)

def machineBits (d U b J K q : ℕ) : ℕ :=
  (registerBits (R b + 1) + bufferBits b J K + GenericCopyDecoderMachine.machineBits ev d U J K q) +
    (bufferBits b J K + medianBits b (V J K)) + registerBits (V J K + 1) + 2

lemma median_fits (b V : ℕ) : FitsBits (MedianMachine.State b V) (medianBits b V) := by
  unfold FitsBits
  rw [MedianMachine.state_card]
  have hv := (lt_two_pow_registerBits (V + 1)).le
  have hr := (lt_two_pow_registerBits (R b + 1)).le
  have hh := Nat.mul_le_mul (Nat.mul_le_mul (le_refl 2) hv) (Nat.pow_le_pow_left hr 2)
  apply hh.trans_eq
  unfold medianBits
  rw [← pow_mul]
  rw [show registerBits (R b + 1) * 2 = 2 * registerBits (R b + 1) by omega]
  rw [pow_add, pow_add]
  norm_num
  ring

/-- The output array, copy index, reused decoder registers, and median counters
all occur in this exact machine's finite configuration bound. -/
theorem machine_fits : FitsBits (State d U b J K q ev) (machineBits ev d U b J K q) := by
  let e : State d U b J K q ev ≃
      (Fin (R b + 1) × Buffer b J K × GenericCopyDecoderMachine.State d U J K q ev) ⊕
      (Buffer b J K × MedianMachine.State b (V J K)) ⊕ Fin (V J K + 1) :=
    { toFun := fun s => match s with
        | .collect i buf c => .inl (i, buf, c)
        | .median buf m => .inr (.inl (buf, m))
        | .halt y => .inr (.inr y)
      invFun := fun s => match s with
        | .inl ibc => .collect ibc.1 ibc.2.1 ibc.2.2
        | .inr (.inl bm) => .median bm.1 bm.2
        | .inr (.inr y) => .halt y
      left_inv := by intro s; cases s <;> rfl
      right_inv := by intro s; rcases s with ibc | bm | y <;> rfl }
  have hb : FitsBits (Buffer b J K) (bufferBits b J K) := array_fits (R b) (fin_fits (V J K + 1))
  have hc := prod_fits (fin_fits (R b + 1))
    (prod_fits hb (GenericCopyDecoderMachine.machine_fits ev (d := d) (U := U) (J := J) (K := K) (q := q)))
  have hm := prod_fits hb (median_fits b (V J K))
  have hh := CandidateChecker.sum_fits hc (CandidateChecker.sum_fits hm (fin_fits (V J K + 1)))
  unfold FitsBits at *
  rw [Fintype.card_congr e]
  apply hh.trans_eq
  congr 1
  unfold machineBits
  omega

def configurationBits (d U b J ℓ K q : ℕ) : ℕ :=
  R b * onlineBits J ℓ K q + machineBits ev d U b J K q

/-- Includes every seed, every online field accumulator, all output storage,
and all mutable registers in the actual sequential generic decoding program. -/
theorem configuration_fits : FitsBits
    ((Fin (R b) → (CopySeed J ℓ q × CopyState J K q)) × State d U b J K q ev)
    (configurationBits ev d U b J ℓ K q) := by
  let e : (CopySeed J ℓ q × CopyState J K q) ≃ OnlineState J ℓ K q := Equiv.prodAssoc _ _ _
  have ho : FitsBits (CopySeed J ℓ q × CopyState J K q) (onlineBits J ℓ K q) := by
    unfold FitsBits
    rw [Fintype.card_congr e]
    exact online_fits J ℓ K q
  exact prod_fits (array_fits (R b) ho) (machine_fits ev)

/-- A supplied evaluator adds only its own work register; all other registers
are shared with the concrete witness construction. -/
theorem machineBits_le_witness : machineBits ev d U b J K q ≤
    AmplifiedDecoderMachine.machineBits d U b J K q + ev.bits := by
  simp only [machineBits, AmplifiedDecoderMachine.machineBits,
    GenericCopyDecoderMachine.machineBits, CopyDecoderMachine.machineBits,
    GenericWeightMachine.machineBits, WeightMachine.machineBits,
    bufferBits, AmplifiedDecoderMachine.bufferBits, medianBits,
    AmplifiedDecoderMachine.medianBits, V, GenericCopyDecoderMachine.outputBound,
    AmplifiedDecoderMachine.V, CopyDecoderMachine.outputBound, R, AmplifiedDecoderMachine.R]
  omega

theorem configurationBits_le_witness : configurationBits ev d U b J ℓ K q ≤
    AmplifiedDecoderMachine.configurationBits d U b J ℓ K q + ev.bits := by
  unfold configurationBits AmplifiedDecoderMachine.configurationBits
  simp only [R, AmplifiedDecoderMachine.R]
  have h := machineBits_le_witness (d := d) (U := U) (b := b) (J := J) (K := K) (q := q) ev
  omega

end Paper02.GenericAmplifiedDecoderMachine
