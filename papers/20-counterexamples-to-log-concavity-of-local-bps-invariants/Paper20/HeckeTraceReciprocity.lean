import Paper20.HeckeBarInverse

namespace Paper20.HeckeBar
open Polynomial Matrix Paper20.HeckeTraceAlgebra Paper20.HeckeMatrices
open Paper20.HeckeWalkExpansion Paper20.HeckeFullTwistTrace Paper20.HalfTwistMatrix
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

lemma reversePositions_eq_one (r : ℕ) (p : State r) :
    reversePositions p=1 ↔ p=Fin.revPerm := by
  constructor
  · intro h
    have he := congrArg (@reversePositions r) h
    simpa only [reversePositions,one_mul,mul_assoc,longest_square,mul_one] using he
  · intro h
    rw [h,reversePositions,longest_square]

lemma J_transpose (r : ℕ) : (J r).transpose=J r := by
  apply Matrix.ext
  intro s t
  have he : s=reversePositions t ↔ t=reversePositions s := by
    constructor
    · intro h; rw [h,reversePositions_twice]
    · intro h; rw [h,reversePositions_twice]
  simp only [J,Matrix.transpose_apply,he]

lemma J_delta_one (r : ℕ) : (J r).mulVec (delta (1 : State r))=delta Fin.revPerm := by
  rw [J_mulVec]
  funext s
  simp only [delta,reversePositions_eq_one]
  split_ifs <;> rfl

lemma conjugateBar_identity_entry (r : ℕ) (A : Mat r) :
    conjugateBar r A 1 1=(A Fin.revPerm Fin.revPerm).comp (-X) := by
  change (J r*bar r A*J r) 1 1=_
  rw [sandwich_entry (J r) (bar r A) 1 Fin.revPerm (J_transpose r) (J_delta_one r)]
  rfl

lemma closedPolynomial_comp_neg (r k : ℕ) :
    (closedHeckePolynomial r k).comp (-X)=closedHeckePolynomial r k := by
  rw [closedHeckePolynomial_eq_comp,comp_assoc,pow_comp,X_comp]
  simp only [neg_sq]

lemma longest_entry_power (r k : ℕ) (hr : 1 ≤ r) :
    (fullTwist r^k) Fin.revPerm Fin.revPerm=(fullTwist r^(k+1)) 1 1 := by
  exact (square_power_identity_entry (halfTwist r) 1 Fin.revPerm
    (halfTwist_transpose r) (halfTwist_delta r hr) k).symm

/-- Exact reciprocity of the genuine canonical trace: the negative kth
full-twist power has the same trace as the positive (k+1)st power. This is
proved by explicit polynomial inverses, longest-state conjugation and the
actual even walk polynomial. -/
theorem inverse_fullTwist_trace (r k : ℕ) (hr : 1 ≤ r) :
    trace r ((conjugateBar r (fullTwist r))^k)=closedHeckePolynomial r k := by
  rw [← map_pow]
  change conjugateBar r (fullTwist r^k) 1 1=_
  rw [conjugateBar_identity_entry,longest_entry_power r k hr,
    fullTwist_identity_entry r k hr,closedPolynomial_comp_neg]

theorem fullTwist_trace_reciprocity (r k : ℕ) (hr : 1 ≤ r) :
    trace r ((conjugateBar r (fullTwist r))^k)=trace r (fullTwist r^(k+1)) := by
  rw [inverse_fullTwist_trace r k hr,trace_fullTwist r k hr]

end
end Paper20.HeckeBar
