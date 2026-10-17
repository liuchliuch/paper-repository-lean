import Paper22.Programs

/-! # The substitution Sₓ = qₓ Tₓ as an exact SDP reformulation

Zero probability coordinates are handled explicitly; no invertibility hypothesis
is imposed on the probability vector or the matrix effects.
-/

open scoped MatrixOrder ComplexOrder
open Matrix
noncomputable section
namespace Paper22
variable {n d : ℕ}

/-- Semidefinite constraints for the relaxed program in the variables (q,S). -/
def MCSDPFeasible (L : ℝ) (q : Fin n → ℝ)
    (S : Fin n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ x, 0 ≤ q x) ∧ (∑ x, q x = 1) ∧
    (∀ x, 0 ≤ S x ∧ S x ≤ q x • 1) ∧
    (∑ x, S x) ≤ (1 / L : ℝ) • 1

/-- Semidefinite constraints for the exactly normalized program. -/
def NSSDPFeasible (M : ℕ) (q : Fin n → ℝ)
    (S : Fin n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ x, 0 ≤ q x) ∧ (∑ x, q x = 1) ∧
    (∀ x, 0 ≤ S x ∧ S x ≤ q x • 1) ∧
    (∑ x, S x) = (1 / M : ℝ) • 1

/-- The affine error objective in the SDP variables. -/
def sdpObjective (V : CQChannel n d)
    (S : Fin n → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  1 - ∑ x, (V.states x * S x).trace.re

/-- Multiplying effects by nonnegative weights gives the SDP intervals. -/
theorem weighted_effect_interval {q : ℝ} {T : Matrix (Fin d) (Fin d) ℂ}
    (hq : 0 ≤ q) (hT : IsEffect T) :
    0 ≤ q • T ∧ q • T ≤ q • 1 :=
  ⟨(hT.posSemidef.smul hq).nonneg, matrix_smul_mono hq hT.le_one⟩

/-- The inverse substitution chooses the zero effect at zero probability. -/
def sdpDecoder (q : Fin n → ℝ) (S : Fin n → Matrix (Fin d) (Fin d) ℂ)
    (x : Fin n) : Matrix (Fin d) (Fin d) ℂ :=
  if q x = 0 then 0 else (q x)⁻¹ • S x

/-- The inverse substitution reconstructs effects and exactly recovers S. -/
theorem sdpDecoder_spec {q : Fin n → ℝ}
    {S : Fin n → Matrix (Fin d) (Fin d) ℂ}
    (hq : ∀ x, 0 ≤ q x) (hS : ∀ x, 0 ≤ S x ∧ S x ≤ q x • 1) :
    (∀ x, IsEffect (sdpDecoder q S x)) ∧
      ∀ x, q x • sdpDecoder q S x = S x := by
  have hx (x : Fin n) : IsEffect (sdpDecoder q S x) ∧
      q x • sdpDecoder q S x = S x := by
    by_cases hqx : q x = 0
    · have hSz : S x = 0 := le_antisymm (by simpa [hqx] using (hS x).2) (hS x).1
      simp [sdpDecoder, hqx, hSz, IsEffect.zero]
    · have hqi : 0 ≤ (q x)⁻¹ := inv_nonneg.mpr (hq x)
      have hTi : (q x)⁻¹ • S x ≤ (1 : Matrix (Fin d) (Fin d) ℂ) := by
        have hi := matrix_smul_mono hqi (hS x).2
        simpa only [smul_smul, inv_mul_cancel₀ hqx, one_smul] using hi
      simp only [sdpDecoder, if_neg hqx]
      refine ⟨⟨((hS x).1.posSemidef.smul hqi).nonneg, hTi⟩, ?_⟩
      rw [smul_smul, mul_inv_cancel₀ hqx, one_smul]
  exact ⟨fun x => (hx x).1, fun x => (hx x).2⟩

/-- The substitution preserves the actual coding objective. -/
theorem programObjective_eq_sdp (V : CQChannel n d) {q : Fin n → ℝ}
    (hq : ∑ x, q x = 1) (T : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    programObjective V.states q T = sdpObjective V (fun x => q x • T x) := by
  unfold programObjective sdpObjective
  simp_rw [mul_sub, mul_one, trace_sub, Complex.sub_re,
    (V.isDensity _).trace_one, Complex.one_re, mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, hq]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.mul_smul, trace_smul, Complex.smul_re, smul_eq_mul]

/-- Forward substitution for the relaxed feasible set. -/
theorem MCFEasable.toSDP {L : ℝ} {q : Fin n → ℝ}
    {T : Fin n → Matrix (Fin d) (Fin d) ℂ} (h : MCFEasable L q T) :
    MCSDPFeasible L q (fun x => q x • T x) :=
  ⟨h.1, h.2.1, fun x => weighted_effect_interval (h.1 x) (h.2.2.1 x), h.2.2.2⟩

/-- Forward substitution for the exactly normalized feasible set. -/
theorem NSFeasible.toSDP {M : ℕ} {q : Fin n → ℝ}
    {T : Fin n → Matrix (Fin d) (Fin d) ℂ} (h : NSFeasible M q T) :
    NSSDPFeasible M q (fun x => q x • T x) :=
  ⟨h.1, h.2.1, fun x => weighted_effect_interval (h.1 x) (h.2.2.1 x), h.2.2.2⟩

/-- Every relaxed SDP feasible pair lifts to a genuine family of matrix effects. -/
theorem MCSDPFeasible.toEffects {L : ℝ} {q : Fin n → ℝ}
    {S : Fin n → Matrix (Fin d) (Fin d) ℂ} (h : MCSDPFeasible L q S) :
    MCFEasable L q (sdpDecoder q S) ∧
      ∀ x, q x • sdpDecoder q S x = S x := by
  obtain ⟨hT, hrec⟩ := sdpDecoder_spec h.1 h.2.2.1
  refine ⟨⟨h.1, h.2.1, hT, ?_⟩, hrec⟩
  simpa only [hrec] using h.2.2.2

/-- Every exactly normalized SDP feasible pair lifts to matrix effects. -/
theorem NSSDPFeasible.toEffects {M : ℕ} {q : Fin n → ℝ}
    {S : Fin n → Matrix (Fin d) (Fin d) ℂ} (h : NSSDPFeasible M q S) :
    NSFeasible M q (sdpDecoder q S) ∧
      ∀ x, q x • sdpDecoder q S x = S x := by
  obtain ⟨hT, hrec⟩ := sdpDecoder_spec h.1 h.2.2.1
  refine ⟨⟨h.1, h.2.1, hT, ?_⟩, hrec⟩
  simpa only [hrec] using h.2.2.2

/-- Equality of all achievable objective values for the relaxed formulations. -/
theorem mc_objective_values_eq_sdp (V : CQChannel n d) (L : ℝ) :
    {e | ∃ q T, MCFEasable L q T ∧ e = programObjective V.states q T} =
      {e | ∃ q S, MCSDPFeasible L q S ∧ e = sdpObjective V S} := by
  ext e
  constructor
  · rintro ⟨q, T, h, rfl⟩
    exact ⟨q, fun x => q x • T x, h.toSDP, programObjective_eq_sdp V h.2.1 T⟩
  · rintro ⟨q, S, h, rfl⟩
    obtain ⟨hT, hrec⟩ := h.toEffects
    refine ⟨q, sdpDecoder q S, hT, ?_⟩
    rw [programObjective_eq_sdp V h.2.1, show (fun x => q x • sdpDecoder q S x) = S
      from funext hrec]

/-- Equality of all achievable objective values for the exact formulations. -/
theorem ns_objective_values_eq_sdp (V : CQChannel n d) (M : ℕ) :
    {e | ∃ q T, NSFeasible M q T ∧ e = programObjective V.states q T} =
      {e | ∃ q S, NSSDPFeasible M q S ∧ e = sdpObjective V S} := by
  ext e
  constructor
  · rintro ⟨q, T, h, rfl⟩
    exact ⟨q, fun x => q x • T x, h.toSDP, programObjective_eq_sdp V h.2.1 T⟩
  · rintro ⟨q, S, h, rfl⟩
    obtain ⟨hT, hrec⟩ := h.toEffects
    refine ⟨q, sdpDecoder q S, hT, ?_⟩
    rw [programObjective_eq_sdp V h.2.1, show (fun x => q x • sdpDecoder q S x) = S
      from funext hrec]

/-- Exact SDP formula for ε_MC, also valid on the empty input alphabet. -/
theorem epsMC_eq_sdp (V : CQChannel n d) (L : ℝ) :
    epsMC V L = sInf {e | ∃ q S, MCSDPFeasible L q S ∧ e = sdpObjective V S} := by
  rw [epsMC, mc_objective_values_eq_sdp]

/-- Exact SDP formula for ε_NS. -/
theorem epsNS_eq_sdp (V : CQChannel n d) (M : ℕ) :
    epsNS V M = sInf {e | ∃ q S, NSSDPFeasible M q S ∧ e = sdpObjective V S} := by
  rw [epsNS, ns_objective_values_eq_sdp]

end Paper22
end
