import Paper29.HuberProcesses
import Paper29.EventTools

noncomputable section
open scoped BigOperators
namespace Paper29.ProcessTools

def trueShifted {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z : Fin n → ℝ) (h : Fin d → ℝ) : ℝ := ∑ i, huber (z i + (A.mulVec h) i)

/-- Exact cancellation of the shared baseline on both sides of the sampling error. -/
theorem centered_error_eq {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z π : Fin n → ℝ) (S : ℝ) (ν : Fin m → Fin n) (h : Ball A S) :
    Sampling.importanceAverage π ν (fun i => affineClass A z S i h) -
      (∑ i, affineClass A z S i h) =
      (Sampling.sampledShifted π ν A z h - Sampling.sampledShifted π ν A z 0) -
        (trueShifted A z h - trueShifted A z 0) := by
  simp only [affineClass, Sampling.importanceAverage, Sampling.sampledShifted,
    Sampling.sampledHuber, trueShifted, Matrix.mulVec_zero, Pi.zero_apply, add_zero,
    sub_div, Finset.sum_sub_distrib]

theorem trueShifted_le {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z : Fin n → ℝ) {S : ℝ} (h : Ball A S) :
    trueShifted A z h ≤ 2 * (∑ i, huber (z i)) + 2 * S := by
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    huber_add_le (z i) ((A.mulVec h) i))
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hh
  have hp : (∑ i, huber ((A.mulVec h) i)) ≤ S := h.property
  exact hh.trans (by linarith only [hp])

theorem centered_error_bdd {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) {S : ℝ} (hS : 0 ≤ S)
    (ν : Fin m → Fin n) :
    BddAbove (Set.range (fun h : Ball A S =>
      |Sampling.importanceAverage π ν (fun i => affineClass A z S i h) -
        (∑ i, affineClass A z S i h)|)) := by
  refine ⟨shiftedEnvelope A z π S ν + Sampling.sampledShifted π ν A z 0 +
    3 * (∑ i, huber (z i)) + 2 * S, ?_⟩
  rintro v ⟨h, rfl⟩
  dsimp only
  rw [centered_error_eq]
  have ha := le_supremum _ (sampledShifted_bdd A z π hπ hS ν) h
  change Sampling.sampledShifted π ν A z h ≤ shiftedEnvelope A z π S ν at ha
  have ha0 := Sampling.sampledHuber_nonneg π ν (fun i => z i + (A.mulVec h) i) hπ
  change 0 ≤ Sampling.sampledShifted π ν A z h at ha0
  have hb0 := Sampling.sampledHuber_nonneg π ν z hπ
  have hbEq : Sampling.sampledShifted π ν A z 0 = Sampling.sampledHuber π ν z := by
    simp [Sampling.sampledShifted, Matrix.mulVec_zero]
  rw [← hbEq] at hb0
  have hc0 : 0 ≤ trueShifted A z h := Finset.sum_nonneg (fun i _ => huber_nonneg _)
  have hd0 : 0 ≤ ∑ i, huber (z i) := Finset.sum_nonneg (fun i _ => huber_nonneg _)
  have hc := trueShifted_le A z h
  have hdEq : trueShifted A z 0 = ∑ i, huber (z i) := by simp [trueShifted, Matrix.mulVec_zero]
  rw [hdEq]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem centered_error_nonneg {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) {S : ℝ} (hS : 0 ≤ S)
    (ν : Fin m → Fin n) : 0 ≤ errorSup π (affineClass A z S) ν := by
  letI : Nonempty (Ball A S) := ⟨zeroBall A hS⟩
  exact supremum_nonneg _ (centered_error_bdd A z π hπ hS ν) (fun _ => abs_nonneg _)

/-- The event is the original uniform centered increment statement, on actual
vectors rather than a supplied objective-preservation certificate. -/
def CenteredTransferEvent {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z π : Fin n → ℝ) (S a : ℝ) (ν : Fin m → Fin n) : Prop :=
  ∀ h : Fin d → ℝ, unshifted A h ≤ S →
    |(Sampling.sampledShifted π ν A z h - Sampling.sampledShifted π ν A z 0) -
      (trueShifted A z h - trueShifted A z 0)| ≤ a

theorem centered_event_iff {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (z π : Fin n → ℝ) (hπ : ∀ i, 0 ≤ π i) {S : ℝ} (hS : 0 ≤ S)
    (a : ℝ) (ν : Fin m → Fin n) :
    CenteredTransferEvent A z π S a ν ↔ errorSup π (affineClass A z S) ν ≤ a := by
  letI : Nonempty (Ball A S) := ⟨zeroBall A hS⟩
  constructor
  · intro he
    apply supremum_le
    intro h
    rw [centered_error_eq]
    exact he h h.property
  · intro he h hh
    have hx := le_supremum _ (centered_error_bdd A z π hπ hS ν) (⟨h, hh⟩ : Ball A S)
    rw [centered_error_eq] at hx
    exact hx.trans he

end Paper29.ProcessTools
