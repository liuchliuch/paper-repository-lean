import Paper02.AmplifiedDecoderMachine
import Paper02.StreamingParameters
import Paper02.StreamingProgram

/-! # A single polynomial bound for the actual finite program configurations -/
set_option maxHeartbeats 1000000
noncomputable section

namespace Paper02.StreamingComplexity
open WeightEval StreamingSpace

lemma registerBits_le (n : ℕ) : registerBits n ≤ n + 1 := by
  unfold registerBits
  exact Nat.add_le_add_right (Nat.log_le_self _ _) 1

lemma double_frequency_bits (U : ℕ) :
    registerBits (2 * U + 1) ≤ registerBits (U + 1) + 2 := by
  have h := (registerBits_mono (show 2 * U + 1 ≤ 2 * (U + 1) by omega)).trans
    (registerBits_mul_le 2 (U + 1))
  have ht : registerBits 2 = 2 := by norm_num [registerBits]
  rw [ht] at h
  omega

/-- A coarse fourth-degree bound with fixed absolute constants. Every term is
an actual register count already connected to execution in the machine modules. -/
theorem configurationBits_polynomial (d U b J ℓ K q : ℕ)
    (hJ : J ≤ registerBits (d + 1)) (hℓ : ℓ ≤ registerBits (d + 1))
    (hQ : registerBits q ≤ 8 + 2 * registerBits (d + 1) + registerBits (U + 1)) :
    AmplifiedDecoderMachine.configurationBits d U b J ℓ K q ≤
      1024 * (K + AmplifiedDecoderMachine.R b + registerBits (d + 1) + registerBits (U + 1) + 10) ^ 4 := by
  let T := K + AmplifiedDecoderMachine.R b + registerBits (d + 1) + registerBits (U + 1) + 10
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hT10 : 10 ≤ T := by dsimp [T]; omega
  have hTT : T ≤ T ^ 2 := by have h := Nat.mul_le_mul_left T hT; nlinarith
  have hK : K ≤ T := by dsimp [T]; omega
  have hR : AmplifiedDecoderMachine.R b ≤ T := by dsimp [T]; omega
  have hD : registerBits (d + 1) ≤ T := by dsimp [T]; omega
  have hU : registerBits (U + 1) ≤ T := by dsimp [T]; omega
  have hj : J ≤ T := hJ.trans hD
  have hl : ℓ ≤ T := hℓ.trans hD
  have hq : registerBits q ≤ 3 * T := by dsimp [T]; omega
  have hk1 : registerBits (K + 1) ≤ T := by have h := registerBits_le (K + 1); dsimp [T]; omega
  have hk2 : registerBits (2 * K + 1) ≤ 2 * T := by have h := registerBits_le (2 * K + 1); dsimp [T]; omega
  have hk3 : registerBits (3 * K + 1) ≤ 3 * T := by have h := registerBits_le (3 * K + 1); dsimp [T]; omega
  have hkk : registerBits (K * K + 1) ≤ 2 * T ^ 2 := by
    have h := registerBits_le (K * K + 1)
    have hp := Nat.pow_le_pow_left hK 2
    nlinarith only [h, hp, hT10]
  have hj1 : registerBits (J + 1) ≤ T := by have h := registerBits_le (J + 1); dsimp [T]; omega
  have hj2 : registerBits (J + 2) ≤ T := by have h := registerBits_le (J + 2); dsimp [T]; omega
  have hr1 : registerBits (AmplifiedDecoderMachine.R b + 1) ≤ T := by
    have h := registerBits_le (AmplifiedDecoderMachine.R b + 1); dsimp [T]; omega
  have hu2 : registerBits (U + 2) ≤ T := by
    have h := (registerBits_mono (show U + 2 ≤ 2 * (U + 1) by omega)).trans (registerBits_mul_le 2 (U + 1))
    have ht : registerBits 2 = 2 := by norm_num [registerBits]
    rw [ht] at h
    dsimp [T]; omega
  have heval : evaluatorBits U ≤ 2 * T := by
    have h := evaluatorBits_polylog U
    dsimp [T]; omega
  have hV : registerBits (AmplifiedDecoderMachine.V J K + 1) ≤ 3 * T := by
    have h := accumulator_bits K J
    change registerBits (AmplifiedDecoderMachine.V J K + 1) ≤ J + registerBits (K + 1) + 3 at h
    dsimp [T] at *
    omega
  have hcode : CandidateChecker.codeBits d U K ≤ T ^ 2 := by
    unfold CandidateChecker.codeBits
    have hsum : registerBits (d + 1) + registerBits (2 * U + 1) + 1 ≤ T := by
      have h := double_frequency_bits U
      dsimp [T]; omega
    exact (Nat.mul_le_mul hK hsum).trans_eq (by ring)
  have hchecker : CandidateChecker.checkerBits d U K q ≤ 26 * T ^ 2 := by
    unfold CandidateChecker.checkerBits CandidateChecker.loaderBits CandidateChecker.boolBits CandidateChecker.momentBits
    nlinarith only [hcode, hk1, hk2, hkk, hq, hTT, hT]
  have hcheck : RecoveryMachine.checksumBits d K q ≤ 8 * T := by
    unfold RecoveryMachine.checksumBits
    omega
  have hrecovery : RecoveryMachine.machineBits d U K q ≤ 42 * T ^ 2 := by
    unfold RecoveryMachine.machineBits
    nlinarith only [hcode, hchecker, hcheck, hTT, hT]
  have hweight : WeightMachine.machineBits U K ≤ 8 * T := by
    unfold WeightMachine.machineBits
    omega
  have hcopy : CopyDecoderMachine.machineBits d U J K q ≤ 59 * T ^ 2 := by
    unfold CopyDecoderMachine.machineBits
    nlinarith only [hj1, hj2, hcode, hrecovery, hweight, hV, hTT, hT]
  have hbuffer : AmplifiedDecoderMachine.bufferBits b J K ≤ 3 * T ^ 2 := by
    unfold AmplifiedDecoderMachine.bufferBits
    exact (Nat.mul_le_mul hR hV).trans_eq (by ring)
  have hmedian : AmplifiedDecoderMachine.medianBits b (AmplifiedDecoderMachine.V J K) ≤ 6 * T := by
    unfold AmplifiedDecoderMachine.medianBits
    omega
  have hdecode : AmplifiedDecoderMachine.machineBits d U b J K q ≤ 77 * T ^ 2 := by
    unfold AmplifiedDecoderMachine.machineBits
    nlinarith only [hcopy, hbuffer, hmedian, hV, hr1, hTT, hT]
  have honline : onlineBits J ℓ K q ≤ 26 * T ^ 3 := by
    unfold onlineBits
    have h1 : J * (ℓ + 1) ≤ 2 * T ^ 2 := by
      have h := Nat.mul_le_mul hj (show ℓ + 1 ≤ 2 * T by omega)
      nlinarith
    have h2 : (J + 1) * (2 * K + 2) * registerBits q ≤ 24 * T ^ 3 := by
      have h := Nat.mul_le_mul (Nat.mul_le_mul (show J + 1 ≤ 2 * T by omega)
        (show 2 * K + 2 ≤ 4 * T by omega)) hq
      nlinarith
    nlinarith
  have htotal := Nat.mul_le_mul hR honline
  have hpow : T ^ 2 ≤ T ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  unfold AmplifiedDecoderMachine.configurationBits
  change _ ≤ 1024 * T ^ 4
  nlinarith only [htotal, hdecode, hpow]

/-- The complete operational program also charges the replicated update buffer,
the update microcode registers, and the signed binary increment reader. -/
theorem programBits_polynomial (d U b J ℓ K q : ℕ)
    (hJ : J ≤ registerBits (d + 1)) (hℓ : ℓ ≤ registerBits (d + 1))
    (hQ : registerBits q ≤ 8 + 2 * registerBits (d + 1) + registerBits (U + 1)) :
    StreamingProgram.programBits d U b J ℓ K q ≤
      4096 * (K + AmplifiedDecoderMachine.R b + registerBits (d + 1) + registerBits (U + 1) + 10) ^ 4 := by
  let T := K + AmplifiedDecoderMachine.R b + registerBits (d + 1) + registerBits (U + 1) + 10
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hT10 : 10 ≤ T := by dsimp [T]; omega
  have hK : K ≤ T := by dsimp [T]; omega
  have hR : AmplifiedDecoderMachine.R b ≤ T := by dsimp [T]; omega
  have hD : registerBits (d + 1) ≤ T := by dsimp [T]; omega
  have hj : J ≤ T := hJ.trans hD
  have hl : ℓ ≤ T := hℓ.trans hD
  have hq : registerBits q ≤ 3 * T := by dsimp [T]; omega
  have hr : registerBits (AmplifiedDecoderMachine.R b + 1) ≤ T := by
    have h := registerBits_le (AmplifiedDecoderMachine.R b + 1)
    dsimp [T]; omega
  have hj2 : registerBits (J + 2) ≤ T := by
    have h := registerBits_le (J + 2)
    dsimp [T]; omega
  have hcounter : registerBits (UpdateMachine.counterBound d ℓ K) ≤ 4 * T := by
    have hc : UpdateMachine.counterBound d ℓ K ≤ d + 2 * K + ℓ + 3 := by
      unfold UpdateMachine.counterBound; omega
    have hh := (registerBits_mono hc).trans (scan_counter_bits d ℓ K)
    dsimp [T]; omega
  have hfield : (2 * K + 1) * registerBits q ≤ 9 * T ^ 2 := by
    have hh := Nat.mul_le_mul (show 2 * K + 1 ≤ 3 * T by omega) hq
    nlinarith only [hh]
  have hbuffer : (J + 1) * ((2 * K + 1) * registerBits q) ≤ 18 * T ^ 3 := by
    have hh := Nat.mul_le_mul (show J + 1 ≤ 2 * T by omega) hfield
    nlinarith only [hh]
  have hTT : T ≤ T ^ 2 := by nlinarith only [Nat.mul_le_mul_left T hT]
  have h23 : T ^ 2 ≤ T ^ 3 := Nat.pow_le_pow_right hT (by omega)
  have h34 : T ^ 3 ≤ T ^ 4 := Nat.pow_le_pow_right hT (by omega)
  have hupdate : UpdateMachine.machineBits d J ℓ K q ≤ 50 * T ^ 3 := by
    unfold UpdateMachine.machineBits
    have ht2 : registerBits 2 = 2 := by norm_num [registerBits]
    have ht5 : registerBits 5 = 3 := by norm_num [registerBits]
    rw [ht2, ht5]
    nlinarith only [hbuffer, hfield, hcounter, hj2, hq, hj, hTT, h23, hT]
  have hrepbuffer : AmplifiedDecoderMachine.R b *
      ((J + 1) * (2 * K + 1) * registerBits q) ≤ 18 * T ^ 4 := by
    have hh := Nat.mul_le_mul hR hbuffer
    nlinarith only [hh]
  have hrep : ReplicatedUpdateMachine.machineBits d (AmplifiedDecoderMachine.R b) J ℓ K q ≤ 70 * T ^ 4 := by
    unfold ReplicatedUpdateMachine.machineBits
    nlinarith only [hr, hrepbuffer, hupdate, h34, h23, hTT]
  have hconf := configurationBits_polynomial d U b J ℓ K q hJ hℓ hQ
  change AmplifiedDecoderMachine.configurationBits d U b J ℓ K q ≤ 1024 * T ^ 4 at hconf
  unfold StreamingProgram.programBits StreamingProgram.R
  change _ ≤ 4096 * T ^ 4
  nlinarith only [hconf, hrep, hq, hD, hT, hTT, h23, h34]

end Paper02.StreamingComplexity
