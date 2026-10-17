import Paper02.BitSpaceModel
import Paper02.ReplicatedUpdateMachine

/-! # The actual program in the paper's bit-space model -/
set_option synthInstance.maxSize 1024
noncomputable section

namespace Paper02.StreamingProgram

open Streaming SparseRecovery BitSpaceModel StreamingSpace WeightEval

variable {d U b J ℓ K q : ℕ} [Fact q.Prime]

abbrev R (b : ℕ) := AmplifiedDecoderMachine.R b

/-- Every implementation field below is an already verified finite-register
program. No accuracy, space or moment conclusion is placed in this structure. -/
def program (d U b J ℓ K q : ℕ) [Fact q.Prime] : Program d q (AmplifiedDecoderMachine.V J K) where
  Seed := Fin (R b) → CopySeed J ℓ q
  seedFinite := inferInstance
  seedNonempty := inferInstance
  Online := Fin (R b) → CopyState J K q
  onlineFinite := inferInstance
  UpdateWork := ReplicatedUpdateMachine.State d (R b) J ℓ K q
  updateFinite := inferInstance
  DecodeWork := AmplifiedDecoderMachine.State d U b J K q
  decodeFinite := inferInstance
  initial _ := 0
  next seeds states i δ := fun r => UpdateMachine.fieldUpdate (seeds r) i δ (states r)
  updateInit _ states _ _ := ReplicatedUpdateMachine.initial (by unfold R AmplifiedDecoderMachine.R MedianMachine.R; omega) states
  updateStep := ReplicatedUpdateMachine.step
  updateDone s := decide (s.index.val = R b)
  updateResult s := s.buffers
  decodeInit _ states := AmplifiedDecoderMachine.initial states
  decodeStep := AmplifiedDecoderMachine.step
  decodeDone := AmplifiedDecoderMachine.done
  decodeResult := AmplifiedDecoderMachine.result

theorem update_refines : UpdateRefines (program d U b J ℓ K q) := by
  intro seeds states i δ
  obtain ⟨finish, hr, hi, hresult⟩ := ReplicatedUpdateMachine.machine_correct
    (by unfold R AmplifiedDecoderMachine.R MedianMachine.R; omega) seeds i δ states
  exact ⟨finish, hr, by simpa [program] using hi, hresult⟩

theorem decode_total (hdq : d < q) (hUq : 2 * U < q) : DecodeTotal (program d U b J ℓ K q) := by
  intro seeds states
  obtain ⟨out, hr, _⟩ := AmplifiedDecoderMachine.machine_correct hdq hUq seeds states
  exact ⟨.halt out, hr, rfl⟩

lemma run_eq (seeds : (program d U b J ℓ K q).Seed) (stream : List (Update d))
    (r : Fin (R b)) :
    BitSpaceModel.run (program d U b J ℓ K q) seeds stream r = Streaming.run K (seeds r) stream := by
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

lemma failure_iff (seeds : (program d U b J ℓ K q).Seed) (stream : List (Update d)) (F ε : ℝ) :
    Failure (program d U b J ℓ K q) seeds stream F ε ↔
      AmplifiedDecoderMachine.FailureEvent (d := d) (U := U) seeds
        (fun i => Streaming.run K (seeds i) stream) F ε := by
  have hrun : BitSpaceModel.run (program d U b J ℓ K q) seeds stream =
      (fun i => Streaming.run K (seeds i) stream) := funext (run_eq seeds stream)
  unfold Failure
  rw [hrun]
  constructor
  · rintro ⟨finish, hr, hd, hb⟩
    cases finish with
    | collect i buf c => simp [program, AmplifiedDecoderMachine.done] at hd
    | median buf m => simp [program, AmplifiedDecoderMachine.done] at hd
    | halt out => exact ⟨out, hr, hb⟩
  · rintro ⟨out, hr, hb⟩
    exact ⟨.halt out, hr, rfl, hb⟩

/-- Accuracy is now a property of the actual program in the model. -/
theorem success
    (hdℓ : d ≤ 2 ^ ℓ) (hdJ : d ≤ 2 ^ J) (hdq : d < q)
    (hUq : 2 * U < q) (hK : 2 ≤ K)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hKbig : 65536 / ε ^ 2 ≤ (K : ℝ))
    (hqbig : (J + 1 : ℕ) * ((d : ℝ) / q) ≤ 1 / 64)
    (hR : 8 * Real.log (1 / δ) ≤ (2 * b + 1 : ℕ))
    (stream : List (Update d))
    (hv : ∀ i, -(U : ℤ) ≤ finalVector stream i ∧ finalVector stream i ≤ U) :
    (Sampling.FiniteLaw.uniform (program d U b J ℓ K q).Seed).prob
      {seeds | Failure (program d U b J ℓ K q) seeds stream (moment f (finalVector stream)) ε} ≤ δ := by
  change (Sampling.FiniteLaw.uniform (Fin (R b) → CopySeed J ℓ q)).prob _ ≤ δ
  have hm := (Sampling.FiniteLaw.uniform (Fin (R b) → CopySeed J ℓ q)).prob_mono
    (show {seeds | Failure (program d U b J ℓ K q) seeds stream
      (moment f (finalVector stream)) ε} ⊆
      {seeds | AmplifiedDecoderMachine.FailureEvent (d := d) (U := U) seeds
        (fun i => Streaming.run K (seeds i) stream) (moment f (finalVector stream)) ε} from
      fun seeds h => (failure_iff seeds stream _ _).mp h)
  apply hm.trans
  rw [← iid_uniform_eq (CopySeed J ℓ q) (Fin (R b))]
  exact AmplifiedDecoderMachine.witness_stream_failure hdℓ hdJ hdq hUq hK hε hε1 hδ hKbig hqbig b hR stream hv

def programBits (d U b J ℓ K q : ℕ) : ℕ :=
  AmplifiedDecoderMachine.configurationBits d U b J ℓ K q +
    ReplicatedUpdateMachine.machineBits d (R b) J ℓ K q + registerBits q + 3 +
    registerBits (d + 1) + registerBits q

/-- Charges all random seeds, online memory, binary input reduction, actual
replicated update work, and all actual decoding phases. -/
theorem fits : Fits (program d U b J ℓ K q) (programBits d U b J ℓ K q) := by
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
      (AmplifiedDecoderMachine.machine_fits (d := d) (U := U) (b := b) (J := J) (K := K) (q := q)))
  have hh := prod_fits ho hw
  have e : ((Fin (R b) → CopySeed J ℓ q) × (Fin (R b) → CopyState J K q)) ×
      ((Bool × ZMod q) ⊕ ReplicatedUpdateMachine.State d (R b) J ℓ K q ⊕ AmplifiedDecoderMachine.State d U b J K q) ≃
    (program d U b J ℓ K q).Seed × (program d U b J ℓ K q).Online ×
      ((Bool × ZMod q) ⊕ (program d U b J ℓ K q).UpdateWork ⊕ (program d U b J ℓ K q).DecodeWork) :=
    Equiv.prodAssoc _ _ _
  have hinput := prod_fits (fin_fits (d + 1)) (prod_fits (field_fits q) hh)
  let e' := Equiv.prodCongr (Equiv.refl (Fin (d + 1)))
    (Equiv.prodCongr (Equiv.refl (ZMod q)) e)
  unfold Fits FitsBits at *
  rw [← Fintype.card_congr e']
  apply hinput.trans_eq
  congr 1
  unfold programBits AmplifiedDecoderMachine.configurationBits
  simp only [R, AmplifiedDecoderMachine.R]
  omega

end Paper02.StreamingProgram
