import Paper20.HilbertCertificate
set_option maxHeartbeats 0
set_option maxRecDepth 200000
namespace Paper20.Cert.Hilbert43
open Paper20.HilbertCertificate Paper20.Semantics

def row : List ℤ := [1, -43, 903, -12341, 123410, -962598, 6096454, -32224114, 145008513, -563921995, 1917334783, -5752004349, 15338678264, -36576848168, 78378960360, -151532656696, 265182149218, -421171648758, 608359048206, -800472431850, 960566918220, -1052049481860, 1052049481860, -960566918220, 800472431850, -608359048206, 421171648758, -265182149218, 151532656696, -78378960360, 36576848168, -15338678264, 5752004349, -1917334783, 563921995, -145008513, 32224114, -6096454, 962598, -123410, 12341, -903, 43, -1]

theorem row_correct : row = binomialRow 43 := by decide

def H : List ℤ := h43List.map Int.ofNat

/-- All 904 finite-difference equations, independently checked by the kernel. -/
theorem checked : (List.range 904).all (fun ℓ =>
    residualWithRow row H ℓ == f43List.getD ℓ 0) = true := by decide

/-- The certified `F` is the actual lower-half residual of the certified `H`. -/
theorem residual_eq (ℓ : ℕ) (hℓ : ℓ ≤ 903) :
    hilbertResidual 43 (fun i => H.getD i 0) ℓ = f43List.getD ℓ 0 := by
  have hc := (List.all_eq_true.mp checked) ℓ (List.mem_range.mpr (by omega))
  simp only [beq_iff_eq] at hc
  rw [row_correct, residualWithRow_correct] at hc
  exact hc

end Paper20.Cert.Hilbert43
