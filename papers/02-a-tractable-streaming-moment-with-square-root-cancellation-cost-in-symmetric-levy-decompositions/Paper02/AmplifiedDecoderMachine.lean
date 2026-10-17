import Paper02.CopyDecoderMachine
import Paper02.MedianMachine

/-! # Sequential decoding of all copies and the actual median program -/
set_option synthInstance.maxSize 1024
noncomputable section

namespace Paper02.AmplifiedDecoderMachine

open Streaming
abbrev R (b : ℕ) := MedianMachine.R b
abbrev V (J K : ℕ) := CopyDecoderMachine.outputBound J K
abbrev Buffer (b J K : ℕ) := Fin (R b) → Fin (V J K + 1)

inductive State (d U b J K q : ℕ) [NeZero q] where
  | collect : Fin (R b + 1) → Buffer b J K → CopyDecoderMachine.State d U J K q → State d U b J K q
  | median : Buffer b J K → MedianMachine.State b (V J K) → State d U b J K q
  | halt : Fin (V J K + 1) → State d U b J K q
  deriving Fintype

variable {d U b J ℓ K q : ℕ} [Fact q.Prime]

def step (seeds : Fin (R b) → CopySeed J ℓ q) (states : Fin (R b) → CopyState J K q) :
    State d U b J K q → State d U b J K q
  | .collect i buffer c =>
      if hi : i.val < R b then
        if CopyDecoderMachine.done c then
          let buffer' := Function.update buffer ⟨i.val, hi⟩ (CopyDecoderMachine.result c)
          if hn : i.val + 1 < R b then
            .collect ⟨i.val + 1, by omega⟩ buffer' (CopyDecoderMachine.initial (states ⟨i.val + 1, hn⟩))
          else .median buffer' (MedianMachine.initial b (V J K))
        else .collect i buffer (CopyDecoderMachine.step (seeds ⟨i.val, hi⟩) (states ⟨i.val, hi⟩) c)
      else .median buffer (MedianMachine.initial b (V J K))
  | .median buffer m => if m.halted then .halt m.candidate else .median buffer (MedianMachine.step buffer m)
  | .halt out => .halt out

def initial (states : Fin (R b) → CopyState J K q) : State d U b J K q :=
  .collect 0 (fun _ => 0) (CopyDecoderMachine.initial (states ⟨0, by unfold R MedianMachine.R; omega⟩))

def Reaches (seeds : Fin (R b) → CopySeed J ℓ q) (states : Fin (R b) → CopyState J K q)
    (s t : State d U b J K q) : Prop :=
  Relation.ReflTransGen (fun x y => step seeds states x = y) s t

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
    (n : ℕ) (hn : n ≤ R b) : State d U b J K q :=
  if h : n < R b then
    .collect ⟨n, by omega⟩ (bufferPrefix ys n) (CopyDecoderMachine.initial (states ⟨n, h⟩))
  else .median ys (MedianMachine.initial b (V J K))

lemma lift_copy (seeds : Fin (R b) → CopySeed J ℓ q) (states : Fin (R b) → CopyState J K q)
    (i : Fin (R b)) (buffer : Buffer b J K) {s t : CopyDecoderMachine.State d U J K q}
    (h : CopyDecoderMachine.Reaches (d := d) (U := U) (seeds i) (states i) s t) :
    Reaches (d := d) (U := U) seeds states (.collect ⟨i.val, by omega⟩ buffer s) (.collect ⟨i.val, by omega⟩ buffer t) := by
  apply Relation.ReflTransGen.lift' (fun c => State.collect ⟨i.val, by omega⟩ buffer c) _ h
  intro a c hac
  by_cases hd : CopyDecoderMachine.done a = true
  · have he : a = c := hac.symm.trans (CopyDecoderMachine.done_fixed (seeds i) (states i) a hd) |>.symm
    rw [← he]
  · exact Relation.ReflTransGen.single (by
      simpa only [step, dif_pos i.isLt, hd, ↓reduceIte] using congrArg (fun c => State.collect ⟨i.val, by omega⟩ buffer c) hac)

lemma collect_reaches (seeds : Fin (R b) → CopySeed J ℓ q) (states : Fin (R b) → CopyState J K q)
    (ys : Buffer b J K)
    (runs : ∀ i, CopyDecoderMachine.Reaches (d := d) (U := U) (seeds i) (states i)
      (CopyDecoderMachine.initial (d := d) (U := U) (states i)) (.halt (ys i)))
    (n : ℕ) (hn : n ≤ R b) :
    Reaches (d := d) (U := U) seeds states (initial (d := d) (U := U) states) (expected (d := d) (U := U) states ys n hn) := by
  induction n with
  | zero =>
    have hr : 0 < R b := by unfold R MedianMachine.R; omega
    simpa only [expected, dif_pos hr, bufferPrefix, Nat.not_lt_zero, if_false, initial] using
      (Relation.ReflTransGen.refl : Reaches (d := d) (U := U) seeds states (initial (d := d) (U := U) states) _)
  | succ n ih =>
    have hnt : n < R b := by omega
    let i : Fin (R b) := ⟨n, hnt⟩
    have hh := lift_copy seeds states i (bufferPrefix ys n) (runs i)
    have hp := (ih hnt.le).trans (by simpa only [expected, dif_pos hnt] using hh)
    apply hp.tail
    dsimp only [i]
    simp only [step, dif_pos hnt, CopyDecoderMachine.done, ↓reduceIte, CopyDecoderMachine.result]
    rw [show Function.update (bufferPrefix ys n) ⟨n, hnt⟩ (ys i) = bufferPrefix ys (n + 1) from prefix_update ys i]
    unfold expected
    split_ifs with hnext
    · rfl
    · have hnR : n + 1 = R b := by omega
      have hbuf : bufferPrefix ys (n + 1) = ys := by funext j; simp [bufferPrefix, hnR, j.isLt]
      rw [hbuf]

lemma lift_median (seeds : Fin (R b) → CopySeed J ℓ q) (states : Fin (R b) → CopyState J K q)
    (ys : Buffer b J K) {s t : MedianMachine.State b (V J K)} (h : MedianMachine.Reaches ys s t) :
    Reaches (d := d) (U := U) seeds states (.median ys s) (.median ys t) := by
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
    (seeds : Fin (R b) → CopySeed J ℓ q) (states : Fin (R b) → CopyState J K q) :
    ∃ out : Fin (V J K + 1), Reaches (d := d) (U := U) seeds states (initial (d := d) (U := U) states) (.halt out) ∧
      (out.val : ℝ) = Sampling.median b (fun i => Streaming.output (d := d) f U K (seeds i) (states i)) := by
  have copy (i : Fin (R b)) := CopyDecoderMachine.machine_correct hdq hUq (seeds i) (states i)
  let ys : Buffer b J K := fun i => Classical.choose (copy i)
  have runs (i : Fin (R b)) := (Classical.choose_spec (copy i)).1
  have specs (i : Fin (R b)) := (Classical.choose_spec (copy i)).2
  have hc := collect_reaches seeds states ys runs (R b) (le_refl _)
  have hcollect : Reaches (d := d) (U := U) seeds states (initial (d := d) (U := U) states) (.median ys (MedianMachine.initial b (V J K))) := by
    simpa only [expected, lt_self_iff_false, ↓reduceDIte] using hc
  obtain ⟨finish, hmedian, hhalt, out, hout, hspec⟩ := MedianMachine.computes_median ys
  have hm := lift_median (d := d) (U := U) seeds states ys hmedian
  refine ⟨out, (hcollect.trans hm).tail ?_, ?_⟩
  · have ho : finish.candidate = out := by simpa [MedianMachine.output, hhalt] using hout
    simp [step, hhalt, ho]
  · rw [hspec]
    congr 1
    funext i
    exact specs i



def done : State d U b J K q → Bool
  | .halt _ => true
  | _ => false

def result : State d U b J K q → Fin (V J K + 1)
  | .halt out => out
  | _ => 0

lemma reaches_iterate {A : Type*} (f : A → A) {s t : A}
    (h : Relation.ReflTransGen (fun a c => f a = c) s t) : ∃ n, f^[n] s = t := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | @tail a c h hac ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    rw [Function.iterate_succ_apply', hn]
    exact hac

lemma fixed_iterate {A : Type*} (f : A → A) (s : A) (hs : f s = s) (n : ℕ) : f^[n] s = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, hs]

lemma terminal_unique {A : Type*} (f : A → A) {s a c : A}
    (ha : Relation.ReflTransGen (fun x y => f x = y) s a)
    (hc : Relation.ReflTransGen (fun x y => f x = y) s c)
    (hfa : f a = a) (hfc : f c = c) : a = c := by
  obtain ⟨n, hn⟩ := reaches_iterate f ha
  obtain ⟨m, hm⟩ := reaches_iterate f hc
  have compare : ∀ {n m : ℕ} {a c : A}, f^[n] s = a → f^[m] s = c →
      f a = a → n ≤ m → a = c := by
    intro n m a c hn hm hfa hnm
    have he : m = (m - n) + n := by omega
    rw [he, Function.iterate_add_apply, hn, fixed_iterate f a hfa] at hm
    exact hm
  rcases Nat.le_total n m with h | h
  · exact compare hn hm hfa h
  · exact (compare hm hn hfc h).symm

/-- Failure refers to an actual halting execution of the program. Determinism
makes this exactly the event used in the finite-seed probability proof. -/
def FailureEvent (seeds : Fin (R b) → CopySeed J ℓ q)
    (states : Fin (R b) → CopyState J K q) (F ε : ℝ) : Prop :=
  ∃ out : Fin (V J K + 1), Reaches (d := d) (U := U) seeds states
    (initial (d := d) (U := U) states) (.halt out) ∧ ε * F < |(out.val : ℝ) - F|

lemma failureEvent_iff (hdq : d < q) (hUq : 2 * U < q)
    (seeds : Fin (R b) → CopySeed J ℓ q) (states : Fin (R b) → CopyState J K q) (F ε : ℝ) :
    FailureEvent (d := d) (U := U) seeds states F ε ↔ ε * F <
      |Sampling.median b (fun i => Streaming.output (d := d) f U K (seeds i) (states i)) - F| := by
  obtain ⟨out, hr, hs⟩ := machine_correct hdq hUq seeds states
  constructor
  · rintro ⟨other, ho, hbad⟩
    have he : (.halt other : State d U b J K q) = .halt out :=
      terminal_unique (step seeds states) ho hr rfl rfl
    have hy : other = out := State.halt.inj he
    simpa only [hy, hs] using hbad
  · intro hbad
    exact ⟨out, hr, by simpa only [hs] using hbad⟩

/-- The full probability theorem now concerns actual program executions,
including sparse recovery, all decoding work, direct f evaluation and median. -/
theorem witness_stream_failure {d J ℓ q U K : ℕ} [Fact q.Prime]
    (hdℓ : d ≤ 2 ^ ℓ) (hdJ : d ≤ 2 ^ J) (hdq : d < q)
    (hUq : 2 * U < q) (hK : 2 ≤ K)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hKbig : 65536 / ε ^ 2 ≤ (K : ℝ))
    (hqbig : (J + 1 : ℕ) * ((d : ℝ) / q) ≤ 1 / 64)
    (b : ℕ) (hR : 8 * Real.log (1 / δ) ≤ (2 * b + 1 : ℕ))
    (stream : List (SparseRecovery.Update d))
    (hv : ∀ i, -(U : ℤ) ≤ SparseRecovery.finalVector stream i ∧ SparseRecovery.finalVector stream i ≤ U) :
    ((Sampling.FiniteLaw.uniform (CopySeed J ℓ q)).iid (Fin (R b))).prob
      {seeds | FailureEvent (d := d) (U := U) seeds
        (fun i => run K (seeds i) stream) (moment f (SparseRecovery.finalVector stream)) ε} ≤ δ := by
  have he : {seeds : Fin (R b) → CopySeed J ℓ q | FailureEvent (d := d) (U := U) seeds
      (fun i => run K (seeds i) stream) (moment f (SparseRecovery.finalVector stream)) ε} =
      {seeds | ε * moment f (SparseRecovery.finalVector stream) <
        |Sampling.median b (fun i => output (d := d) f U K (seeds i) (run K (seeds i) stream)) -
          moment f (SparseRecovery.finalVector stream)|} := by
    ext seeds
    exact failureEvent_iff hdq hUq seeds _ _ _
  rw [he]
  exact Streaming.witness_stream_estimate hdℓ hdJ hdq hUq hK hε hε1 hδ hKbig hqbig b hR stream hv

open StreamingSpace WeightEval

def medianBits (b V : ℕ) : ℕ := registerBits (V + 1) + 2 * registerBits (R b + 1) + 1

def bufferBits (b J K : ℕ) : ℕ := R b * registerBits (V J K + 1)

def machineBits (d U b J K q : ℕ) : ℕ :=
  (registerBits (R b + 1) + bufferBits b J K + CopyDecoderMachine.machineBits d U J K q) +
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
theorem machine_fits : FitsBits (State d U b J K q) (machineBits d U b J K q) := by
  let e : State d U b J K q ≃
      (Fin (R b + 1) × Buffer b J K × CopyDecoderMachine.State d U J K q) ⊕
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
    (prod_fits hb (CopyDecoderMachine.machine_fits (d := d) (U := U) (J := J) (K := K) (q := q)))
  have hm := prod_fits hb (median_fits b (V J K))
  have hh := CandidateChecker.sum_fits hc (CandidateChecker.sum_fits hm (fin_fits (V J K + 1)))
  unfold FitsBits at *
  rw [Fintype.card_congr e]
  apply hh.trans_eq
  congr 1
  unfold machineBits
  omega

def configurationBits (d U b J ℓ K q : ℕ) : ℕ :=
  R b * onlineBits J ℓ K q + machineBits d U b J K q

/-- Includes every seed, every online field accumulator, all output storage,
and all mutable registers in the actual sequential decoding program. -/
theorem configuration_fits {d U b J ℓ K q : ℕ} [Fact q.Prime] : FitsBits
    ((Fin (R b) → (CopySeed J ℓ q × CopyState J K q)) × State d U b J K q)
    (configurationBits d U b J ℓ K q) := by
  let e : (CopySeed J ℓ q × CopyState J K q) ≃ OnlineState J ℓ K q := Equiv.prodAssoc _ _ _
  have ho : FitsBits (CopySeed J ℓ q × CopyState J K q) (onlineBits J ℓ K q) := by
    unfold FitsBits
    rw [Fintype.card_congr e]
    exact online_fits J ℓ K q
  exact prod_fits (array_fits (R b) ho) machine_fits

end Paper02.AmplifiedDecoderMachine
