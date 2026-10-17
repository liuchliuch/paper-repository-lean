import Paper22.Basic
import Paper22.Programs
import Paper22.Divergences
import Paper22.Tensor
import Paper22.RateExtension
import Paper22.ReliabilityPositivity
import Paper22.TensorLowerBound
import Paper22.DivergenceExtended
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Instances.EReal.Lemmas
import Paper22.OneShot
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Reliability exponents and Theorem 2

Defines the message-count sequence `M_n(R) = ⌈2^{nR}⌉`, the non-signaling and
activated non-signaling reliability exponents `E_NS(R)`, `E_ANS(R)` as limits of
`-(1/n) · log2 ε`, and states Theorem 2:

  for full-rank `W` and `0 < R < C(W)`, `E_NS(R) = E_ANS(R) = E_sp(R)`.

External inputs used only inside Theorem 2 (cited results, not proved here):
* `ExternalMetaConverseLimit` — the meta-converse exponent of
  Oufkir–Tomamichel–Berta [4, Thm. 4.1 and Eq. (34)]: (paper (23)).
* `ExternalActivationIdentity` — the one-bit activation identity of [3, 4]:
  `ε_NS(2m, V⊗I₂) = ε_MC(m, V)` (paper (26)).

The paper's own argument (sandwich from Theorem 1, sequence extension (24),
positivity of errors) is proved from the concrete cq coding programs.
-/

open scoped MatrixOrder ComplexOrder
open Matrix

noncomputable section

namespace Paper22

variable {n d : ℕ}

/-! ## Message counts -/

/-- Message count `M_n(R) = ⌈2^{nR}⌉` (paper: `M_n(R) = ⌈2^{nR}⌉`). -/
def msgCount (R : ℝ) (n : ℕ) : ℕ := ⌈((2 : ℝ) ^ ((n : ℝ) * R))⌉₊

lemma msgCount_pos {R : ℝ} (hR : 0 < R) {n : ℕ} (hn : 0 < n) :
    0 < msgCount R n := by
  unfold msgCount
  refine Nat.ceil_pos.mpr ?_
  positivity

lemma msgCount_one {R : ℝ} : msgCount R 1 = ⌈((2 : ℝ) ^ R)⌉₊ := by
  simp [msgCount]

/-- Normalized log of the message count: `(1/n) · log2 (msgCount R n) → R`. -/
lemma msgCount_log_asymptotic {R : ℝ} (hR : 0 < R) :
    Filter.Tendsto (fun n : ℕ => (1 / (n : ℝ)) * log2 (msgCount R n : ℝ))
      Filter.atTop (nhds R) := by
  have hbase (n : ℕ) : 1 ≤ (2 : ℝ) ^ ((n : ℝ) * R) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg n) hR.le)
  have hlog (n : ℕ) : log2 ((2 : ℝ) ^ ((n : ℝ) * R)) = (n : ℝ) * R := by
    rw [log2_rpow (by norm_num)]
    simp [log2]
  have hinv : Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ)) Filter.atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inverse_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using tendsto_const_nhds.add hinv)
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have h := log2_le_log2 (by positivity : 0 < (2 : ℝ) ^ ((n : ℝ) * R))
      (Nat.le_ceil ((2 : ℝ) ^ ((n : ℝ) * R)))
    rw [hlog] at h
    calc R = (1 / (n : ℝ)) * ((n : ℝ) * R) := by field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_left h (by positivity)
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have hceil : (msgCount R n : ℝ) ≤ 2 * (2 : ℝ) ^ ((n : ℝ) * R) := by
      have hc := (Nat.ceil_lt_add_one (show 0 ≤ (2 : ℝ) ^ ((n : ℝ) * R) by positivity)).le
      dsimp [msgCount]
      linarith [hbase n]
    have hcpos : (0 : ℝ) < msgCount R n := by exact_mod_cast msgCount_pos hR hn
    have h := log2_le_log2 hcpos hceil
    rw [log2_mul (by norm_num) (by positivity), hlog] at h
    have htwo : log2 2 = 1 := Real.logb_self_eq_one (by norm_num)
    rw [htwo] at h
    calc (1 / (n : ℝ)) * log2 (msgCount R n : ℝ)
        ≤ (1 / (n : ℝ)) * (1 + (n : ℝ) * R) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = R + (n : ℝ)⁻¹ := by field_simp; ring

lemma msgCount_ge_one (R : ℝ) (k : ℕ) : 1 ≤ msgCount R k := by
  apply Nat.one_le_ceil_iff.mpr
  positivity

lemma msgCount_ge_two {R : ℝ} (hR : 0 < R) {k : ℕ} (hk : 0 < k) :
    2 ≤ msgCount R k := by
  change 1 + 1 ≤ ⌈(2 : ℝ) ^ ((k : ℝ) * R)⌉₊
  apply Nat.add_one_le_ceil_iff.mpr
  simpa only [Nat.cast_one] using Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (mul_pos (Nat.cast_pos.mpr hk) hR)

lemma msgCount_tendsto_atTop {R : ℝ} (hR : 0 < R) :
    Filter.Tendsto (fun k => (msgCount R k : ℝ)) Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono (fun k => Nat.le_ceil _)
  have ht : Filter.Tendsto (fun k : ℕ => (k : ℝ) * R * Real.log 2)
      Filter.atTop Filter.atTop :=
    (Filter.Tendsto.atTop_mul_const hR tendsto_natCast_atTop_atTop).atTop_mul_const
      (Real.log_pos (by norm_num))
  simpa only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm (Real.log 2)]
    using Real.tendsto_exp_atTop.comp ht

lemma msgCount_add_log_asymptotic {R : ℝ} (hR : 0 < R) (c : ℕ) :
    Filter.Tendsto (fun k : ℕ => (1 / (k : ℝ)) * log2 ((msgCount R k + c : ℕ) : ℝ))
      Filter.atTop (nhds R) := by
  have hi : Filter.Tendsto (fun k : ℕ => (1 / (k : ℝ)) * log2 ((c : ℝ) + 1))
      Filter.atTop (nhds 0) := by
    simpa using (tendsto_inverse_atTop_nhds_zero_nat.mul_const (log2 ((c : ℝ) + 1)))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (msgCount_log_asymptotic hR)
    (by simpa using (msgCount_log_asymptotic hR).add hi)
  · exact Filter.Eventually.of_forall fun k => mul_le_mul_of_nonneg_left
      (log2_le_log2 (by exact_mod_cast (msgCount_ge_one R k).trans_lt' Nat.zero_lt_one)
        (by exact_mod_cast Nat.le_add_right (msgCount R k) c)) (by positivity)
  · filter_upwards [Filter.eventually_gt_atTop 0] with k hk
    have hm : (1 : ℝ) ≤ msgCount R k := by exact_mod_cast msgCount_ge_one R k
    have hbound : ((msgCount R k + c : ℕ) : ℝ) ≤ ((c : ℝ) + 1) * msgCount R k := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) c]
    have hlog := log2_le_log2 (by exact_mod_cast (show 0 < msgCount R k + c by have := msgCount_ge_one R k; omega)) hbound
    rw [log2_mul (by positivity) (by positivity)] at hlog
    calc _ ≤ (1 / (k : ℝ)) * (log2 ((c : ℝ) + 1) + log2 (msgCount R k : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = _ := by ring

/-- The half-message sequence used to transfer the activation identity. -/
def halfMsgCount (R : ℝ) (k : ℕ) : ℕ := max 1 (msgCount R k / 2)

lemma halfMsgCount_ge_one (R : ℝ) (k : ℕ) : 1 ≤ halfMsgCount R k := le_max_left _ _

lemma halfMsgCount_bounds (R : ℝ) (k : ℕ) :
    (halfMsgCount R k : ℝ) ≤ msgCount R k ∧
      (msgCount R k : ℝ) ≤ 4 * halfMsgCount R k := by
  have hm := msgCount_ge_one R k
  have hq := Nat.div_le_self (msgCount R k) 2
  have hmax : max 1 (msgCount R k / 2) ≤ msgCount R k := max_le hm hq
  have hdiv : msgCount R k < (msgCount R k / 2 + 1) * 2 := by omega
  have h1 := halfMsgCount_ge_one R k
  have h2 : msgCount R k / 2 ≤ halfMsgCount R k := le_max_right _ _
  constructor
  · exact_mod_cast hmax
  · have hdiv' : (msgCount R k : ℝ) < ((msgCount R k / 2 : ℕ) + 1) * 2 := by exact_mod_cast hdiv
    have h1' : (1 : ℝ) ≤ halfMsgCount R k := by exact_mod_cast h1
    have h2' : ((msgCount R k / 2 : ℕ) : ℝ) ≤ halfMsgCount R k := by exact_mod_cast h2
    nlinarith

lemma halfMsgCount_log_asymptotic {R : ℝ} (hR : 0 < R) :
    Filter.Tendsto (fun k : ℕ => (1 / (k : ℝ)) * log2 (halfMsgCount R k : ℝ))
      Filter.atTop (nhds R) := by
  have hi : Filter.Tendsto (fun k : ℕ => (1 / (k : ℝ)) * log2 4)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_inverse_atTop_nhds_zero_nat.mul_const (log2 4)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using (msgCount_log_asymptotic hR).sub hi)
    (msgCount_log_asymptotic hR)
  · exact Filter.Eventually.of_forall fun k => by
      have hm : (0 : ℝ) < msgCount R k := by exact_mod_cast (msgCount_ge_one R k).trans_lt' Nat.zero_lt_one
      have hh : (0 : ℝ) < halfMsgCount R k := by exact_mod_cast (halfMsgCount_ge_one R k).trans_lt' Nat.zero_lt_one
      have hlog := log2_le_log2 hm (halfMsgCount_bounds R k).2
      rw [log2_mul (by norm_num) hh.ne'] at hlog
      have hm := mul_le_mul_of_nonneg_left hlog (show (0 : ℝ) ≤ 1 / (k : ℝ) by positivity)
      simp only [one_div] at *
      nlinarith
  · exact Filter.Eventually.of_forall fun k => mul_le_mul_of_nonneg_left
      (log2_le_log2 (by exact_mod_cast (halfMsgCount_ge_one R k).trans_lt' Nat.zero_lt_one)
        (halfMsgCount_bounds R k).1) (by positivity)

/-- The literal floor in (27) has normalized message rate `R`. -/
lemma msgCount_floor_half_log_asymptotic {R : ℝ} (hR : 0 < R) :
    Filter.Tendsto (fun k : ℕ => (1 / (k : ℝ)) * log2 ((msgCount R k / 2 : ℕ) : ℝ))
      Filter.atTop (nhds R) := by
  apply (halfMsgCount_log_asymptotic hR).congr'
  filter_upwards [(msgCount_tendsto_atTop hR).eventually (Filter.eventually_ge_atTop 2)] with k hk
  have hm : 2 ≤ msgCount R k := by exact_mod_cast hk
  have heq : halfMsgCount R k = msgCount R k / 2 := by dsimp [halfMsgCount]; omega
  rw [heq]

/-- The literal ceiling in (27) has normalized message rate `R`. -/
lemma msgCount_ceil_half_log_asymptotic {R : ℝ} (hR : 0 < R) :
    Filter.Tendsto (fun k : ℕ => (1 / (k : ℝ)) * log2 (((msgCount R k + 1) / 2 : ℕ) : ℝ))
      Filter.atTop (nhds R) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (msgCount_floor_half_log_asymptotic hR) (msgCount_log_asymptotic hR)
  · filter_upwards [(msgCount_tendsto_atTop hR).eventually (Filter.eventually_ge_atTop 2)] with k hk
    have hm : 2 ≤ msgCount R k := by exact_mod_cast hk
    have hpos : (0 : ℝ) < (msgCount R k / 2 : ℕ) := by
      exact_mod_cast (show 0 < msgCount R k / 2 by omega)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply log2_le_log2 hpos
    exact_mod_cast (show msgCount R k / 2 ≤ (msgCount R k + 1) / 2 by omega)
  · exact Filter.Eventually.of_forall fun k => by
      have hm := msgCount_ge_one R k
      have hpos : (0 : ℝ) < ((msgCount R k + 1) / 2 : ℕ) := by
        exact_mod_cast (show 0 < (msgCount R k + 1) / 2 by omega)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply log2_le_log2 hpos
      exact_mod_cast (show (msgCount R k + 1) / 2 ≤ msgCount R k by omega)

/-! ## Finite-blocklength exponents -/

/-- Finite-blocklength non-signaling error exponent at blocklength `k`:
`-(1/k) · log2 ε_NS(M_k(R), W^{⊗k})`. The extended-real definition below
implements the zero-error convention and agrees eventually at positive rates. -/
def nsErrorExp (V : CQChannel n d) (R : ℝ) (k : ℕ) : ℝ :=
  -(1 / (k : ℝ)) * log2 (epsNS (tensorPowerFamily V k) (msgCount R k))

/-- Finite-blocklength activated non-signaling error exponent:
`-(1/k) · log2 ε_NS(M_k(R), W^{⊗k} ⊗ I₂)`. -/
def ansErrorExp (V : CQChannel n d) (R : ℝ) (k : ℕ) : ℝ :=
  -(1 / (k : ℝ)) * log2 (epsNS (activatedTensorPowerFamily V k) (msgCount R k))

/-- `E_NS(R)` is the limit of `nsErrorExp`, when it exists. -/
def eNSExists (V : CQChannel n d) (R : ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto (nsErrorExp V R) Filter.atTop (nhds L)

/-- `E_ANS(R)` is the limit of `ansErrorExp`, when it exists. -/
def eANSExists (V : CQChannel n d) (R : ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto (ansErrorExp V R) Filter.atTop (nhds L)

/-! ## External inputs (cited, used only in Theorem 2) -/

/-- **External input (23)** — meta-converse exponent of
Oufkir–Tomamichel–Berta [4, Thm. 4.1 and Eq. (34)].

For every finite cq channel `W` and every `0 < r < C(W)`,
`lim_{n} -(1/n) · log2 ε_MC(2^{nr}, W^{⊗n}) = E_sp(r)`.

This is a cited external result, not proved in this development. -/
structure ExternalMetaConverseLimit : Prop where
  /-- The meta-converse exponent equals the sphere-packing function. -/
  limit_eq : ∀ {n d : ℕ} (W : CQChannel n d) (_hW : W.FullRank) {r : ℝ}
    (_hr : 0 < r) (_hrC : r < holevoCapacity W),
    Filter.Tendsto
      (fun k : ℕ => -(1 / (k : ℝ)) * log2 (epsMC (tensorPowerFamily W k) ((2 : ℝ) ^ ((k : ℝ) * r))))
      Filter.atTop (nhds (spherePacking W r))

/-- **External input (26)** — one-bit activation identity of [3, 4, Eq. (32)].

For every integer `m ≥ 1` and every finite cq channel `V`,
`ε_NS(2m, V ⊗ I₂) = ε_MC(m, V)`.

This structure is retained for the original transfer proof. Its field is now
proved internally by Paper22.activation_identity and supplied by
Paper22.activationIdentity_proved; it is not a remaining external dependency. -/
structure ExternalActivationIdentity : Prop where
  /-- Activated non-signaling error equals the meta-converse error at half the messages. -/
  activation : ∀ {n d : ℕ} (V : CQChannel n d) (m : ℕ) (_hm : 1 ≤ m),
    epsNS (activationFamily V) (2 * m) = epsMC V m

/-- The exact floor/ceiling sandwich (27), with `(L + 1) / 2` the
integer ceiling of `L / 2`. -/
theorem activation_floor_ceil_bounds (ext : ExternalActivationIdentity)
    {n d : ℕ} (V : CQChannel n d) (L : ℕ) (hL : 2 ≤ L) :
    epsMC V ((L / 2 : ℕ) : ℝ) ≤ epsNS (activationFamily V) L ∧
      epsNS (activationFamily V) L ≤ epsMC V (((L + 1) / 2 : ℕ) : ℝ) := by
  have hfloor : 1 ≤ L / 2 := by omega
  have hceil : 1 ≤ (L + 1) / 2 := by omega
  constructor
  · rw [← ext.activation V (L / 2) hfloor]
    exact epsNS_mono _ (by omega) (by omega)
  · rw [← ext.activation V ((L + 1) / 2) hceil]
    exact epsNS_mono _ (by omega) (by omega)

/-- Equation (27) with literal real floor and ceiling notation. -/
theorem activation_floor_ceil_bounds_source (ext : ExternalActivationIdentity)
    {n d : ℕ} (V : CQChannel n d) (L : ℕ) (hL : 2 ≤ L) :
    epsMC V (⌊(L : ℝ) / 2⌋₊ : ℝ) ≤ epsNS (activationFamily V) L ∧
      epsNS (activationFamily V) L ≤ epsMC V (⌈(L : ℝ) / 2⌉₊ : ℝ) := by
  simpa only [floor_half_natCast, ceil_half_natCast] using
    activation_floor_ceil_bounds ext V L hL

/-! ## Sequence extension (24) -/

/-- **Sequence extension (24), meta-converse side.**
If `L_k ≥ 1` and `(1/k) · log2 L_k → r ∈ (0, C(W))`, then
`-(1/k) · log2 ε_MC(L_k, W^{⊗k}) → E_sp(r)`.

Proved from the external meta-converse limit (23), monotonicity of `ε_MC`,
and continuity of `E_sp`; the write-up is the paper's S3.p4 argument. -/
theorem metaConverse_sequence_extension
    (ext : ExternalMetaConverseLimit)
    {n d : ℕ} [NeZero n] [NeZero d] (W : CQChannel n d) (hW : W.FullRank)
    {r : ℝ} (hr : 0 < r) (hrC : r < holevoCapacity W)
    (L : ℕ → ℝ) (hL1 : ∀ k, 1 ≤ L k)
    (hLim : Filter.Tendsto (fun k : ℕ => (1 / (k : ℝ)) * log2 (L k)) Filter.atTop (nhds r)) :
    Filter.Tendsto
      (fun k : ℕ => -(1 / (k : ℝ)) * log2 (epsMC (tensorPowerFamily W k) (L k)))
      Filter.atTop (nhds (spherePacking W r)) := by
  apply rate_sequence_extension
    (fun k L => -(1 / (k : ℝ)) * log2 (epsMC (tensorPowerFamily W k) L))
    (spherePacking W) hr hrC
  · intro k a ha b hb hab
    exact mul_le_mul_of_nonpos_left
      (log2_le_log2 (epsMC_pos_fullRank _ (tensorPowerFamily_fullRank W hW k) ha)
        (epsMC_mono _ ha.le hab)) (neg_nonpos.mpr (by positivity))
  · intro s hs hsC
    exact ext.limit_eq W hW hs hsC
  · exact (spherePacking_continuousOn W hW).continuousAt (isOpen_Ioi.mem_nhds hr)
  · exact hL1
  · exact hLim

/-- **Sequence extension (24), non-signaling side.**
Same statement for `ε_NS`, using Theorem 1's sandwich. -/
theorem ns_sequence_extension
    (ext : ExternalMetaConverseLimit)
    {n d : ℕ} [NeZero n] [NeZero d] (W : CQChannel n d) (hW : W.FullRank)
    {r : ℝ} (hr : 0 < r) (hrC : r < holevoCapacity W) :
    eNSExists W r (spherePacking W r) := by
  have hl := metaConverse_sequence_extension ext W hW hr hrC
    (fun k => (msgCount r k : ℝ)) (fun k => by dsimp; exact_mod_cast msgCount_ge_one r k)
    (msgCount_log_asymptotic hr)
  have hu := metaConverse_sequence_extension ext W hW hr hrC
    (fun k => ((msgCount r k + 6 : ℕ) : ℝ))
    (fun k => by dsimp; exact_mod_cast (msgCount_ge_one r k).trans (Nat.le_add_right _ 6))
    (msgCount_add_log_asymptotic hr 6)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hu hl
  · filter_upwards [Filter.eventually_gt_atTop 0] with k hk
    have hm := msgCount_ge_two hr hk
    have hm' : (1 : ℝ) < msgCount r k := by exact_mod_cast (show 1 < msgCount r k by omega)
    have hp := epsMC_pos_fullRank _ (tensorPowerFamily_fullRank W hW k) hm'
    have hb := theorem_one_shot (tensorPowerFamily W k) (msgCount r k) hm
    have hnsp := hp.trans_le hb.1
    exact mul_le_mul_of_nonpos_left (log2_le_log2 hnsp (by simpa using hb.2)) (neg_nonpos.mpr (by positivity))
  · filter_upwards [Filter.eventually_gt_atTop 0] with k hk
    have hm := msgCount_ge_two hr hk
    have hm' : (1 : ℝ) < msgCount r k := by exact_mod_cast (show 1 < msgCount r k by omega)
    have hp := epsMC_pos_fullRank _ (tensorPowerFamily_fullRank W hW k) hm'
    exact mul_le_mul_of_nonpos_left (log2_le_log2 hp
      (theorem_one_shot (tensorPowerFamily W k) (msgCount r k) hm).1) (neg_nonpos.mpr (by positivity))

/-- The source's quantitative full-rank block error bound, using the original
channel's common spectral lower bound at every tensor length. -/
theorem epsMC_tensor_lower_bound_of_spectral
    {n d : ℕ} [NeZero n] (W : CQChannel n d) {lam : ℝ}
    (hlam : ∀ x i, lam ≤ (W.density x).isHermitian.eigenvalues i)
    (hlam0 : 0 < lam) (k : ℕ) {L : ℝ} (hL : 1 < L) :
    ((d : ℝ) * lam) ^ k * (1 - 1 / L) ≤ epsMC (tensorPowerFamily W k) L := by
  exact tensorPowerFamily_epsMC_lower_bound W hlam0
    (fun x => spectral_scalar_lower_bound (W.density x).isHermitian (hlam x)) k hL

/-- **Positivity of errors.** For `L > 1` the meta-converse error of a full-rank
block channel is strictly positive (paper S3.p3):
`ε_MC(L, W^{⊗k}) ≥ (d·λ)^k · (1 - 1/L) > 0`. -/
theorem epsMC_pos_of_fullRank
    {n d : ℕ} [NeZero n] [NeZero d] (W : CQChannel n d) (hW : W.FullRank)
    {lam : ℝ} (hlam : ∀ x i, lam ≤ (W.density x).isHermitian.eigenvalues i) (hlam0 : 0 < lam)
    (k : ℕ) {L : ℝ} (hL : 1 < L) :
    0 < epsMC (tensorPowerFamily W k) L := by
  apply lt_of_lt_of_le _ (epsMC_tensor_lower_bound_of_spectral W hlam hlam0 k hL)
  have hd : (0 : ℝ) < d := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hdiv : 1 / L < 1 := (div_lt_one (by linarith : 0 < L)).mpr hL
  exact mul_pos (pow_pos (mul_pos hd hlam0) k) (sub_pos.mpr hdiv)

/-! ## Theorem 2 -/

/-- **Theorem 2 (Reliability without activation).**

Let `W` be a finite cq channel whose output states are full rank.
For every `0 < R < C(W)`, the limits in the definitions of `E_NS(R)` and
`E_ANS(R)` exist and satisfy `E_NS(R) = E_ANS(R) = E_sp(R)`.

The proof is the paper's S3 argument:
1. (21)–(22) give finiteness and continuity of `E_sp` on `(0, ∞)`.
2. External input (23) identifies the meta-converse exponent with `E_sp`.
3. Sequence extension (24) passes from `2^{nr}` to `M_n(R) = ⌈2^{nR}⌉`.
4. Theorem 1's sandwich `ε_MC(M) ≤ ε_NS(M) ≤ ε_MC(M+6)` transfers the limit.
5. External input (26) plus monotonicity transfers it to the activated model.

Only (23) and (26) are external; everything else is the paper's own argument. -/
theorem theorem_2_reliability
    (extMeta : ExternalMetaConverseLimit) (extAct : ExternalActivationIdentity)
    {n d : ℕ} (W : CQChannel n d) (hW : W.FullRank)
    {R : ℝ} (hR0 : 0 < R) (hRC : R < holevoCapacity W) :
    eNSExists W R (spherePacking W R) ∧
      eANSExists W R (spherePacking W R) := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    have hc := holevoCapacity_zero_input W
    linarith
  letI : NeZero n := ⟨hn⟩
  have hd : d ≠ 0 := by
    intro hd
    subst d
    have htrace := (W.density (⟨0, Nat.pos_of_ne_zero hn⟩ : Fin n)).trace_one
    simpa [Matrix.trace] using htrace
  letI : NeZero d := ⟨hd⟩
  refine ⟨ns_sequence_extension extMeta W hW hR0 hRC, ?_⟩
  have hl := metaConverse_sequence_extension extMeta W hW hR0 hRC
    (fun k => (msgCount R k : ℝ)) (fun k => by dsimp; exact_mod_cast msgCount_ge_one R k)
    (msgCount_log_asymptotic hR0)
  have hu := metaConverse_sequence_extension extMeta W hW hR0 hRC
    (fun k => (halfMsgCount R k : ℝ)) (fun k => by dsimp; exact_mod_cast halfMsgCount_ge_one R k)
    (halfMsgCount_log_asymptotic hR0)
  have hevent : ∀ᶠ k : ℕ in Filter.atTop, 4 ≤ msgCount R k := by
    filter_upwards [(msgCount_tendsto_atTop hR0).eventually (Filter.eventually_ge_atTop 4)] with k hk
    exact_mod_cast hk
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hu
  · filter_upwards [hevent] with k hk
    have hM1 : 1 ≤ msgCount R k := by omega
    have hH1 := halfMsgCount_ge_one R k
    have hHM : 2 * halfMsgCount R k ≤ msgCount R k := by
      dsimp [halfMsgCount]
      omega
    have hMpos : (1 : ℝ) < msgCount R k := by exact_mod_cast (show 1 < msgCount R k by omega)
    have hHpos : (1 : ℝ) < halfMsgCount R k := by
      dsimp [halfMsgCount]
      exact_mod_cast (show 1 < max 1 (msgCount R k / 2) by omega)
    have hlo : epsMC (tensorPowerFamily W k) (halfMsgCount R k) ≤
        epsNS (activatedTensorPowerFamily W k) (msgCount R k) := by
      rw [← extAct.activation (tensorPowerFamily W k) (halfMsgCount R k) hH1]
      exact epsNS_mono _ (by omega) hHM
    have hhi : epsNS (activatedTensorPowerFamily W k) (msgCount R k) ≤
        epsMC (tensorPowerFamily W k) (msgCount R k) := by
      rw [← extAct.activation (tensorPowerFamily W k) (msgCount R k) hM1]
      exact epsNS_mono _ hM1 (by omega)
    have hp := (epsMC_pos_fullRank _ (tensorPowerFamily_fullRank W hW k) hHpos).trans_le hlo
    exact mul_le_mul_of_nonpos_left (log2_le_log2 hp hhi) (neg_nonpos.mpr (by positivity))
  · filter_upwards [hevent] with k hk
    have hH1 := halfMsgCount_ge_one R k
    have hHM : 2 * halfMsgCount R k ≤ msgCount R k := by
      dsimp [halfMsgCount]
      omega
    have hHpos : (1 : ℝ) < halfMsgCount R k := by
      dsimp [halfMsgCount]
      exact_mod_cast (show 1 < max 1 (msgCount R k / 2) by omega)
    have hlo : epsMC (tensorPowerFamily W k) (halfMsgCount R k) ≤
        epsNS (activatedTensorPowerFamily W k) (msgCount R k) := by
      rw [← extAct.activation (tensorPowerFamily W k) (halfMsgCount R k) hH1]
      exact epsNS_mono _ (by omega) hHM
    exact mul_le_mul_of_nonpos_left (log2_le_log2
      (epsMC_pos_fullRank _ (tensorPowerFamily_fullRank W hW k) hHpos) hlo) (neg_nonpos.mpr (by positivity))

/-- Extended-real exponent, implementing `-log₂ 0 = +∞`. -/
def nsErrorExpEReal (V : CQChannel n d) (R : ℝ) (k : ℕ) : EReal :=
  if epsNS (tensorPowerFamily V k) (msgCount R k) = 0 then ⊤
  else (nsErrorExp V R k : EReal)

/-- Extended-real activated exponent, implementing `-log₂ 0 = +∞`. -/
def ansErrorExpEReal (V : CQChannel n d) (R : ℝ) (k : ℕ) : EReal :=
  if epsNS (activatedTensorPowerFamily V k) (msgCount R k) = 0 then ⊤
  else (ansErrorExp V R k : EReal)

theorem nsErrorExpEReal_eventually_eq [NeZero n] [NeZero d]
    (W : CQChannel n d) (hW : W.FullRank) {R : ℝ} (hR : 0 < R) :
    ∀ᶠ k : ℕ in Filter.atTop, nsErrorExpEReal W R k = (nsErrorExp W R k : EReal) := by
  filter_upwards [Filter.eventually_gt_atTop 0] with k hk
  have hm := msgCount_ge_two hR hk
  have hm' : (1 : ℝ) < msgCount R k := by exact_mod_cast (show 1 < msgCount R k by omega)
  have hp := (epsMC_pos_fullRank _ (tensorPowerFamily_fullRank W hW k) hm').trans_le
    (theorem_one_shot (tensorPowerFamily W k) (msgCount R k) hm).1
  simp [nsErrorExpEReal, hp.ne']

theorem ansErrorExpEReal_eventually_eq [NeZero n] [NeZero d]
    (ext : ExternalActivationIdentity) (W : CQChannel n d) (hW : W.FullRank)
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ k : ℕ in Filter.atTop, ansErrorExpEReal W R k = (ansErrorExp W R k : EReal) := by
  filter_upwards [(msgCount_tendsto_atTop hR).eventually (Filter.eventually_ge_atTop 4)] with k hk
  have hm : 4 ≤ msgCount R k := by exact_mod_cast hk
  have hfloor : (1 : ℝ) < (msgCount R k / 2 : ℕ) := by exact_mod_cast (show 1 < msgCount R k / 2 by omega)
  have hp := (epsMC_pos_fullRank _ (tensorPowerFamily_fullRank W hW k) hfloor).trans_le
    (activation_floor_ceil_bounds ext (tensorPowerFamily W k) (msgCount R k) (by omega)).1
  simp [ansErrorExpEReal, activatedTensorPowerFamily, hp.ne']

/-- Theorem 2 also holds with the source's extended-real zero-error convention. -/
theorem theorem_2_reliability_ereal
    (extMeta : ExternalMetaConverseLimit) (extAct : ExternalActivationIdentity)
    (W : CQChannel n d) (hW : W.FullRank) {R : ℝ} (hR : 0 < R) (hRC : R < holevoCapacity W) :
    Filter.Tendsto (nsErrorExpEReal W R) Filter.atTop (nhds (spherePacking W R : EReal)) ∧
    Filter.Tendsto (ansErrorExpEReal W R) Filter.atTop (nhds (spherePacking W R : EReal)) := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    have hc := holevoCapacity_zero_input W
    linarith
  letI : NeZero n := ⟨hn⟩
  have hd : d ≠ 0 := by
    intro hd
    subst d
    have htrace := (W.density (⟨0, Nat.pos_of_ne_zero hn⟩ : Fin n)).trace_one
    simpa [Matrix.trace] using htrace
  letI : NeZero d := ⟨hd⟩
  have hreal := theorem_2_reliability extMeta extAct W hW hR hRC
  constructor
  · exact (EReal.tendsto_coe.mpr hreal.1).congr' (Filter.EventuallyEq.symm (nsErrorExpEReal_eventually_eq W hW hR))
  · exact (EReal.tendsto_coe.mpr hreal.2).congr' (Filter.EventuallyEq.symm (ansErrorExpEReal_eventually_eq extAct W hW hR))

/-- Theorem 2 stated using both of the source's extended-real definitions. -/
theorem theorem_2_reliability_source
    (extMeta : ExternalMetaConverseLimit) (extAct : ExternalActivationIdentity)
    (W : CQChannel n d) (hW : W.FullRank) {R : ℝ} (hR : 0 < R) (hRC : R < holevoCapacity W) :
    Filter.Tendsto (nsErrorExpEReal W R) Filter.atTop (nhds (spherePackingExtended W R)) ∧
    Filter.Tendsto (ansErrorExpEReal W R) Filter.atTop (nhds (spherePackingExtended W R)) := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    have hc := holevoCapacity_zero_input W
    linarith
  letI : NeZero n := ⟨hn⟩
  have hd : d ≠ 0 := by
    intro hd
    subst d
    have htrace := (W.density (⟨0, Nat.pos_of_ne_zero hn⟩ : Fin n)).trace_one
    simpa [Matrix.trace] using htrace
  letI : NeZero d := ⟨hd⟩
  rw [spherePackingExtended_eq_coe W hW hR.le]
  exact theorem_2_reliability_ereal extMeta extAct W hW hR hRC

end Paper22

end
