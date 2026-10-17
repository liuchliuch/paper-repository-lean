import Paper20.Certs.CheckedRec.Chunk00
import Paper20.Certs.CheckedRec.Chunk01
import Paper20.Certs.CheckedRec.Chunk02
import Paper20.Certs.CheckedRec.Chunk03
import Paper20.Certs.CheckedRec.Chunk04
import Paper20.Certs.CheckedRec.Chunk05
import Paper20.Certs.CheckedRec.Chunk06
import Paper20.Certs.CheckedRec.Chunk07
import Paper20.Certs.CheckedRec.Chunk08
import Paper20.Certs.CheckedRec.Chunk09
import Paper20.Certs.CheckedRec.Chunk10
import Paper20.Certs.CheckedRec.Chunk11
import Paper20.Certs.CheckedRec.Chunk12
import Paper20.Certs.CheckedRec.Chunk13
import Paper20.Certs.CheckedRec.Chunk14
import Paper20.Certs.CheckedRec.Chunk15
import Paper20.Certs.CheckedRec.Chunk16
import Paper20.Certs.CheckedRec.Chunk17
import Paper20.Certs.CheckedRec.Chunk18
import Paper20.Certs.CheckedRec.Chunk19
import Paper20.Certs.CheckedRec.Chunk20
import Paper20.Certs.CheckedRec.Chunk21
import Paper20.Certs.CheckedRec.Chunk22
import Paper20.Certs.CheckedRec.Chunk23
import Paper20.Certs.CheckedRec.Chunk24
import Paper20.Certs.CheckedRec.Chunk25
import Paper20.Certs.CheckedRec.Chunk26
import Paper20.Certs.CheckedRec.Chunk27
import Paper20.Certs.CheckedRec.Chunk28

namespace Paper20.Cert.Checked43
open Paper20.CheckedRecurrence Paper20.Semantics

/-- Every equation of (25) was checked by the Lean kernel. -/
theorem check_all (h : ℕ) (hh : h ≤ 903) : checkRow 903 f43List integers h = true := by
  by_cases h0 : h < 32
  · exact checkRows_sound verified_00 (by omega) h0
  by_cases h1 : h < 64
  · exact checkRows_sound verified_01 (by omega) h1
  by_cases h2 : h < 96
  · exact checkRows_sound verified_02 (by omega) h2
  by_cases h3 : h < 128
  · exact checkRows_sound verified_03 (by omega) h3
  by_cases h4 : h < 160
  · exact checkRows_sound verified_04 (by omega) h4
  by_cases h5 : h < 192
  · exact checkRows_sound verified_05 (by omega) h5
  by_cases h6 : h < 224
  · exact checkRows_sound verified_06 (by omega) h6
  by_cases h7 : h < 256
  · exact checkRows_sound verified_07 (by omega) h7
  by_cases h8 : h < 288
  · exact checkRows_sound verified_08 (by omega) h8
  by_cases h9 : h < 320
  · exact checkRows_sound verified_09 (by omega) h9
  by_cases h10 : h < 352
  · exact checkRows_sound verified_10 (by omega) h10
  by_cases h11 : h < 384
  · exact checkRows_sound verified_11 (by omega) h11
  by_cases h12 : h < 416
  · exact checkRows_sound verified_12 (by omega) h12
  by_cases h13 : h < 448
  · exact checkRows_sound verified_13 (by omega) h13
  by_cases h14 : h < 480
  · exact checkRows_sound verified_14 (by omega) h14
  by_cases h15 : h < 512
  · exact checkRows_sound verified_15 (by omega) h15
  by_cases h16 : h < 544
  · exact checkRows_sound verified_16 (by omega) h16
  by_cases h17 : h < 576
  · exact checkRows_sound verified_17 (by omega) h17
  by_cases h18 : h < 608
  · exact checkRows_sound verified_18 (by omega) h18
  by_cases h19 : h < 640
  · exact checkRows_sound verified_19 (by omega) h19
  by_cases h20 : h < 672
  · exact checkRows_sound verified_20 (by omega) h20
  by_cases h21 : h < 704
  · exact checkRows_sound verified_21 (by omega) h21
  by_cases h22 : h < 736
  · exact checkRows_sound verified_22 (by omega) h22
  by_cases h23 : h < 768
  · exact checkRows_sound verified_23 (by omega) h23
  by_cases h24 : h < 800
  · exact checkRows_sound verified_24 (by omega) h24
  by_cases h25 : h < 832
  · exact checkRows_sound verified_25 (by omega) h25
  by_cases h26 : h < 864
  · exact checkRows_sound verified_26 (by omega) h26
  by_cases h27 : h < 896
  · exact checkRows_sound verified_27 (by omega) h27
  exact checkRows_sound verified_28 (by omega) (by omega)

/-- The complete 904-entry certificate solves the actual signed-binomial
recurrence, rather than a system with unrelated literal weights. -/
theorem certificate_recurrence : recurrence25 903
    (fun ℓ => f43List.getD ℓ 0) (fun h => integers.getD h 0) := by
  intro h hh
  exact checkRow_sound integers_length hh (check_all h hh)

/-- Unconditional connection of the certificate to canonical extraction. -/
theorem certificate_eq_extracted : ∀ h, h ≤ 903 →
    integers.getD h 0 = extracted 903 (fun ℓ => f43List.getD ℓ 0) h :=
  recurrence25_unique certificate_recurrence (extracted_recurrence _ _)

/-- All lower-half coefficients of the defining expansion (24). -/
theorem certificate_low_expansion : ∀ ℓ, ℓ ≤ 903 →
    f43List.getD ℓ 0 = expansionCoeff 903 (fun h => integers.getD h 0) ℓ :=
  (recurrence25_iff_low _ _ _).mp certificate_recurrence

end Paper20.Cert.Checked43
