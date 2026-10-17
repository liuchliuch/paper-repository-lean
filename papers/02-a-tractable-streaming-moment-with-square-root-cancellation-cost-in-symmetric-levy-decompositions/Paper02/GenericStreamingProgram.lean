import Paper02.BitSpaceModel
import Paper02.ReplicatedUpdateMachine
import Paper02.GenericAmplifiedDecoderMachine
import Paper02.StreamingProgram

/-! # The actual program in the paper's bit-space model -/
set_option synthInstance.maxSize 1024
noncomputable section

namespace Paper02.GenericStreamingProgram

open Streaming SparseRecovery BitSpaceModel StreamingSpace WeightEval GenericWeightMachine
variable {w : ℤ → ℕ}
local instance evaluatorFintype {U : ℕ} (ev : Evaluator U w) : Fintype ev.Carrier := ev.finite

variable {d U b J ℓ K q : ℕ} [Fact q.Prime] (ev : Evaluator U w)

abbrev R (b : ℕ) := GenericAmplifiedDecoderMachine.R b

/-- Every implementation field below is an already verified finite-register
program. No accuracy, space or moment conclusion is placed in this structure. -/
def program (d U b J ℓ K q : ℕ) (ev : Evaluator U w) [Fact q.Prime] : Program d q (GenericAmplifiedDecoderMachine.V J K) where
  Seed := Fin (R b) → CopySeed J ℓ q
  seedFinite := inferInstance
  seedNonempty := inferInstance
  Online := Fin (R b) → CopyState J K q
  onlineFinite := inferInstance
  UpdateWork := ReplicatedUpdateMachine.State d (R b) J ℓ K q
  updateFinite := inferInstance
  DecodeWork := GenericAmplifiedDecoderMachine.State d U b J K q ev
  decodeFinite := inferInstance
  initial _ := 0
  next seeds states i δ := fun r => UpdateMachine.fieldUpdate (seeds r) i δ (states r)
  updateInit _ states _ _ := ReplicatedUpdateMachine.initial (by unfold R GenericAmplifiedDecoderMachine.R MedianMachine.R; omega) states
  updateStep := ReplicatedUpdateMachine.step
  updateDone s := decide (s.index.val = R b)
  updateResult s := s.buffers
  decodeInit _ states := GenericAmplifiedDecoderMachine.initial ev states
  decodeStep := GenericAmplifiedDecoderMachine.step ev
  decodeDone := GenericAmplifiedDecoderMachine.done ev
  decodeResult := GenericAmplifiedDecoderMachine.result ev

theorem update_refines : UpdateRefines (program d U b J ℓ K q ev) := by
  intro seeds states i δ
  obtain ⟨finish, hr, hi, hresult⟩ := ReplicatedUpdateMachine.machine_correct
    (by unfold R GenericAmplifiedDecoderMachine.R MedianMachine.R; omega) seeds i δ states
  exact ⟨finish, hr, by simpa [program] using hi, hresult⟩

theorem decode_total (hdq : d < q) (hUq : 2 * U < q)
    (hw0 : w 0 = 0) (hw3 : ∀ k, w k ≤ 3) : DecodeTotal (program d U b J ℓ K q ev) := by
  intro seeds states
  obtain ⟨out, hr, _⟩ := GenericAmplifiedDecoderMachine.machine_correct ev hdq hUq hw0 hw3 seeds states
  exact ⟨.halt out, hr, rfl⟩

lemma run_eq (seeds : (program d U b J ℓ K q ev).Seed) (stream : List (Update d))
    (r : Fin (R b)) :
    BitSpaceModel.run (program d U b J ℓ K q ev) seeds stream r = Streaming.run K (seeds r) stream := by
  have aux : ∀ (xs : List (Update d)) (states : Fin (R b) → CopyState J K q),
      (xs.foldl (fun s u => fun a => UpdateMachine.fieldUpdate (seeds a) u.1 (u.2 : ZMod q) (s a)) states) r =
        xs.foldl (Streaming.update K (seeds r)) (states r) := by
    intro xs
    induction xs with
    | nil => intro states; rfl
    | cons u us ih =>
      intro states
      simp only [List.foldl_cons]
      exact ih _
  exact aux stream 0

lemma failure_iff (seeds : (program d U b J ℓ K q ev).Seed) (stream : List (Update d)) (F ε : ℝ) :
    Failure (program d U b J ℓ K q ev) seeds stream F ε ↔
      GenericAmplifiedDecoderMachine.FailureEvent ev (d := d) (U := U) seeds
        (fun i => Streaming.run K (seeds i) stream) F ε := by
  have hrun : BitSpaceModel.run (program d U b J ℓ K q ev) seeds stream =
      (fun i => Streaming.run K (seeds i) stream) := funext (run_eq ev seeds stream)
  unfold Failure
  rw [hrun]
  constructor
  · rintro ⟨finish, hr, hd, hb⟩
    cases finish with
    | collect i buf c => simp [program, GenericAmplifiedDecoderMachine.done] at hd
    | median buf m => simp [program, GenericAmplifiedDecoderMachine.done] at hd
    | halt out => exact ⟨out, hr, hb⟩
  · rintro ⟨out, hr, hb⟩
    exact ⟨.halt out, hr, rfl, hb⟩

/-- Accuracy is now a property of the actual program in the model. -/
theorem success
    (hw0 : w 0 = 0) (hw1 : ∀ k, k ≠ 0 → 1 ≤ w k) (hw3 : ∀ k, w k ≤ 3)
    (hdℓ : d ≤ 2 ^ ℓ) (hdJ : d ≤ 2 ^ J) (hdq : d < q)
    (hUq : 2 * U < q) (hK : 2 ≤ K)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hKbig : 65536 / ε ^ 2 ≤ (K : ℝ))
    (hqbig : (J + 1 : ℕ) * ((d : ℝ) / q) ≤ 1 / 64)
    (hR : 8 * Real.log (1 / δ) ≤ (2 * b + 1 : ℕ))
    (stream : List (Update d))
    (hv : ∀ i, -(U : ℤ) ≤ finalVector stream i ∧ finalVector stream i ≤ U) :
    (Sampling.FiniteLaw.uniform (program d U b J ℓ K q ev).Seed).prob
      {seeds | Failure (program d U b J ℓ K q ev) seeds stream (moment (fun k => (w k : ℝ)) (finalVector stream)) ε} ≤ δ := by
  change (Sampling.FiniteLaw.uniform (Fin (R b) → CopySeed J ℓ q)).prob _ ≤ δ
  have hm := (Sampling.FiniteLaw.uniform (Fin (R b) → CopySeed J ℓ q)).prob_mono
    (show {seeds | Failure (program d U b J ℓ K q ev) seeds stream
      (moment (fun k => (w k : ℝ)) (finalVector stream)) ε} ⊆
      {seeds | GenericAmplifiedDecoderMachine.FailureEvent ev (d := d) (U := U) seeds
        (fun i => Streaming.run K (seeds i) stream)
        (moment (fun k => (w k : ℝ)) (finalVector stream)) ε} from
      fun seeds h => (failure_iff ev seeds stream _ _).mp h)
  apply hm.trans
  rw [← iid_uniform_eq (CopySeed J ℓ q) (Fin (R b))]
  exact GenericAmplifiedDecoderMachine.bounded_weights_stream_failure ev hw0 hw1 hw3 hdℓ hdJ hdq hUq hK hε hε1 hδ hKbig hqbig b hR stream hv

def programBits (d U b J ℓ K q : ℕ) : ℕ :=
  GenericAmplifiedDecoderMachine.configurationBits ev d U b J ℓ K q +
    ReplicatedUpdateMachine.machineBits d (R b) J ℓ K q + registerBits q + 3 +
    registerBits (d + 1) + registerBits q

/-- Charges all random seeds, online memory, binary input reduction, actual
replicated update work, and all actual decoding phases. -/
theorem fits : Fits (program d U b J ℓ K q ev) (programBits ev d U b J ℓ K q) := by
  have ho : FitsBits ((Fin (R b) → CopySeed J ℓ q) × (Fin (R b) → CopyState J K q))
      (R b * onlineBits J ℓ K q) := by
    let e : ((Fin (R b) → CopySeed J ℓ q) × (Fin (R b) → CopyState J K q)) ≃
        (Fin (R b) → (CopySeed J ℓ q × CopyState J K q)) :=
      { toFun := fun s r => (s.1 r, s.2 r)
        invFun := fun s => (fun r => (s r).1, fun r => (s r).2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    let a : (CopySeed J ℓ q × CopyState J K q) ≃ OnlineState J ℓ K q := Equiv.prodAssoc _ _ _
    have hc : FitsBits (CopySeed J ℓ q × CopyState J K q) (onlineBits J ℓ K q) := by
      unfold FitsBits
      rw [Fintype.card_congr a]
      exact online_fits J ℓ K q
    unfold FitsBits
    rw [Fintype.card_congr e]
    exact array_fits (R b) hc
  have hw := CandidateChecker.sum_fits (update_reader_fits q)
    (CandidateChecker.sum_fits (ReplicatedUpdateMachine.machine_fits (d := d) (R := R b) (J := J) (ℓ := ℓ) (K := K) (q := q))
      (GenericAmplifiedDecoderMachine.machine_fits ev (d := d) (U := U) (b := b) (J := J) (K := K) (q := q)))
  have hh := prod_fits ho hw
  have e : ((Fin (R b) → CopySeed J ℓ q) × (Fin (R b) → CopyState J K q)) ×
      ((Bool × ZMod q) ⊕ ReplicatedUpdateMachine.State d (R b) J ℓ K q ⊕ GenericAmplifiedDecoderMachine.State d U b J K q ev) ≃
    (program d U b J ℓ K q ev).Seed × (program d U b J ℓ K q ev).Online ×
      ((Bool × ZMod q) ⊕ (program d U b J ℓ K q ev).UpdateWork ⊕ (program d U b J ℓ K q ev).DecodeWork) :=
    Equiv.prodAssoc _ _ _
  have hinput := prod_fits (fin_fits (d + 1)) (prod_fits (field_fits q) hh)
  let e' := Equiv.prodCongr (Equiv.refl (Fin (d + 1)))
    (Equiv.prodCongr (Equiv.refl (ZMod q)) e)
  unfold Fits FitsBits at *
  rw [← Fintype.card_congr e']
  apply hinput.trans_eq
  congr 1
  unfold programBits GenericAmplifiedDecoderMachine.configurationBits
  simp only [R, GenericAmplifiedDecoderMachine.R]
  omega

/-- Only the supplied evaluator's work register is additional to the concrete
witness program, since all sampling and update microcode is identical. -/
theorem programBits_le_witness : programBits ev d U b J ℓ K q ≤
    StreamingProgram.programBits d U b J ℓ K q + ev.bits := by
  have h := GenericAmplifiedDecoderMachine.configurationBits_le_witness
    (d := d) (U := U) (b := b) (J := J) (ℓ := ℓ) (K := K) (q := q) ev
  unfold programBits StreamingProgram.programBits
  simp only [R, StreamingProgram.R, GenericAmplifiedDecoderMachine.R,
    AmplifiedDecoderMachine.R] at *
  omega

end Paper02.GenericStreamingProgram
