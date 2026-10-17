import Paper02.RecoveryMachine

/-! Workspace of the actual sparse-recovery enumerator. The program may take
exponential time, but its live registers meet the source's quadratic space
bound. No Gaussian-elimination runtime theorem is assumed. -/
noncomputable section
namespace Paper02.SparseRecoverySpace
open WeightEval StreamingSpace

lemma actual_decoder_bits (d U K q : ℕ) (hdq : d < q) (hUq : 2 * U < q) :
    RecoveryMachine.machineBits d U K q ≤
      100 * (K + 1) ^ 2 * registerBits q := by
  let T := (K + 1) ^ 2 * registerBits q
  have hq1 : 1 ≤ registerBits q := by unfold registerBits; omega
  have hk1 : 1 ≤ (K + 1) ^ 2 := by
    have hp : 0 < (K + 1) ^ 2 := by positivity
    omega
  have hK : K ≤ (K + 1) ^ 2 := by nlinarith
  have hT1 : 1 ≤ T := by
    simpa only [T, Nat.one_mul] using Nat.mul_le_mul hk1 hq1
  have hTq : registerBits q ≤ T := by
    simpa only [T, Nat.one_mul] using (Nat.mul_le_mul_right (registerBits q) hk1)
  have hTk : (K + 1) ^ 2 ≤ T := by
    simpa only [T, Nat.mul_one] using (Nat.mul_le_mul_left ((K + 1) ^ 2) hq1)
  have hd : registerBits (d + 1) ≤ registerBits q := registerBits_mono (by omega)
  have hU : registerBits (2 * U + 1) ≤ registerBits q := registerBits_mono (by omega)
  have hcode : CandidateChecker.codeBits d U K ≤ 3 * T := by
    unfold CandidateChecker.codeBits
    have hs : registerBits (d + 1) + registerBits (2 * U + 1) + 1 ≤ 3 * registerBits q := by omega
    have hm := Nat.mul_le_mul_left K hs
    have hn := Nat.mul_le_mul_right (registerBits q) hK
    dsimp [T] at *
    nlinarith
  have hr1 : registerBits (K + 1) ≤ 2 * T := by
    have h : registerBits (K + 1) ≤ K + 2 := by
      unfold registerBits
      exact Nat.add_le_add_right (Nat.log_le_self _ _) 1
    nlinarith
  have hr2 : registerBits (2 * K + 1) ≤ 2 * T := by
    have h : registerBits (2 * K + 1) ≤ 2 * K + 2 := by
      unfold registerBits
      exact Nat.add_le_add_right (Nat.log_le_self _ _) 1
    nlinarith
  have hrs : registerBits (K * K + 1) ≤ 2 * T := by
    have h : registerBits (K * K + 1) ≤ K * K + 2 := by
      unfold registerBits
      exact Nat.add_le_add_right (Nat.log_le_self _ _) 1
    nlinarith
  unfold RecoveryMachine.machineBits RecoveryMachine.checksumBits
    CandidateChecker.checkerBits CandidateChecker.loaderBits
    CandidateChecker.boolBits CandidateChecker.momentBits
  rw [show 100 * (K + 1) ^ 2 * registerBits q = 100 * T by dsimp [T]; ring]
  omega

/-- Every configuration of the actual halting sparse-recovery program fits
within O((K+1)² log q) bits; its correctness is RecoveryMachine.machine_correct. -/
theorem actual_decoder_fits {d U K q : ℕ} [Fact q.Prime]
    (hdq : d < q) (hUq : 2 * U < q) :
    FitsBits (RecoveryMachine.State d U K q)
      (100 * (K + 1) ^ 2 * registerBits q) := by
  exact (RecoveryMachine.machine_fits (d := d) (U := U) (K := K) (q := q)).trans
    (Nat.pow_le_pow_right (by decide) (actual_decoder_bits d U K q hdq hUq))

/-- In the source range K≥1 this is the exact O(K² log q) workspace order. -/
theorem actual_decoder_quadratic {d U K q : ℕ} [Fact q.Prime]
    (hK : 1 ≤ K) (hdq : d < q) (hUq : 2 * U < q) :
    FitsBits (RecoveryMachine.State d U K q) (400 * K ^ 2 * registerBits q) := by
  have hs : (K + 1) ^ 2 ≤ 4 * K ^ 2 := by nlinarith
  have hb : 100 * (K + 1) ^ 2 * registerBits q ≤ 400 * K ^ 2 * registerBits q := by
    calc
      _ ≤ 100 * (4 * K ^ 2) * registerBits q :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 100 hs)
      _ = _ := by ring
  exact (actual_decoder_fits hdq hUq).trans (Nat.pow_le_pow_right (by decide) hb)

/-- Includes the checksum seed and stored linear summary as well as every
mutable register of the actual decoder. -/
theorem summary_and_decoder_quadratic {d U K q : ℕ} [Fact q.Prime]
    (hK : 1 ≤ K) (hdq : d < q) (hUq : 2 * U < q) :
    FitsBits (ZMod q × SparseRecovery.Summary K (ZMod q) × RecoveryMachine.State d U K q)
      (512 * K ^ 2 * registerBits q) := by
  have hh := prod_fits (field_fits q)
    (prod_fits (summary_fits K q) (actual_decoder_quadratic hK hdq hUq))
  have hc : 1 + (2 * K + 1) + 400 * K ^ 2 ≤ 512 * K ^ 2 := by nlinarith
  have hb : registerBits q + ((2 * K + 1) * registerBits q + 400 * K ^ 2 * registerBits q) ≤
      512 * K ^ 2 * registerBits q := by
    convert Nat.mul_le_mul_right (registerBits q) hc using 1 <;> ring
  exact hh.trans (Nat.pow_le_pow_right (by decide) hb)

end Paper02.SparseRecoverySpace
