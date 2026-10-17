import P31.Results
import P31.HilbertDiagnostics

/-! Actual algorithmic consequences for alternate vector targets and (7.9). -/
noncomputable section
namespace P31
open QueryProgram Schedule
variable {ι : Type*} [Fintype ι]

theorem vector_weaker_target {p κ C L R ε s : ℝ}
    (hp : 2 ≤ p) (hκ : 1 < κ) (hκhi : κ ≤ 2) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hε : 0 < ε) (hqs : dualExponent p ≤ s)
    (hClarkson : ScalarWeightedClarkson p) (engine : ExternalComplementaryComposite ι p κ C)
    (initial : ι → ℝ) (f : (ι → ℝ) → ℝ) (grad : (ι → ℝ) → ι → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasFDerivAt f (coordinateFunctional (grad x)) x)
    (hh : ∀ x y, lpNorm (dualExponent p) (grad x-grad y) ≤ L*lpNorm p (x-y)^(κ-1))
    (xstar : ι → ℝ) (hstar : ∀ y, f xstar ≤ f y) (hr : lpNorm p (initial-xstar) ≤ R) :
    let P := vectorGradientMethod p κ L R ε initial hp hκ hκhi engine
    lpNorm s (grad (P.run grad).value) ≤ ε ∧
    ((P.run grad).calls : ℝ) ≤ queryConstant C (vectorBiasCoefficient p) p κ *
      (1+(L*R^(κ-1)/ε)^beta p κ) := by
  have h := vectorGradientMethod_guarantee hp hκ hκhi hC hL hR hε hClarkson engine
    initial f grad hf hg hh xstar hstar hr
  exact ⟨(lpNorm_antitone_exponent (dualExponent_pos (by linarith)) hqs _).trans h.1, h.2⟩

/-- The hypothesis used by the diagnostic module is supplied by the actual
main algorithm. No continuation accuracy estimate is an external input. -/
theorem smooth_accuracy_family {d : ℕ} {p C L R : ℝ}
    (hp : 2 ≤ p) (hC : 0 ≤ C) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hClarkson : ScalarWeightedClarkson p) (engine : ExternalComplementaryComposite (Fin d) p 2 C)
    (initial : Fin d → ℝ) (f : (Fin d → ℝ) → ℝ) (grad : (Fin d → ℝ) → Fin d → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasFDerivAt f (coordinateFunctional (grad x)) x)
    (hh : ∀ x y, lpNorm (dualExponent p) (grad x-grad y) ≤ L*lpNorm p (x-y))
    (xstar : Fin d → ℝ) (hstar : ∀ y, f xstar ≤ f y) (hr : lpNorm p (initial-xstar) ≤ R) :
    ∀ ε : ℝ, 0 < ε → HilbertDiagnostics.AccuracyCertificate
      (vectorGradientMethod p 2 L R ε initial hp (by norm_num) (by norm_num) engine)
      f grad (dualExponent p) (queryConstant C (vectorBiasCoefficient p) p 2) (L*R) (beta p 2) ε := by
  intro ε hε
  have hh' : ∀ x y, lpNorm (dualExponent p) (grad x-grad y) ≤ L*lpNorm p (x-y)^((2:ℝ)-1) := by
    simpa only [show (2:ℝ)-1=1 by norm_num, Real.rpow_one] using hh
  have h := vectorGradientMethod_guarantee hp (by norm_num : (1:ℝ)<2) (by norm_num) hC hL hR
    hε hClarkson engine initial f grad hf hg hh' xstar hstar hr
  refine ⟨_, rfl, ?_, h.1⟩
  simpa only [show (2:ℝ)-1=1 by norm_num, Real.rpow_one] using h.2

/-- Full finite-dimensional diagnostic, with the continuation half discharged
by the main actual query program and only the Euclidean theorem supplied. -/
theorem smooth_finite_dimension_envelope {d : ℕ} (hd : 0 < d) {p C C_H L R : ℝ}
    (hp : 2 ≤ p) (hC : 0 ≤ C) (hCH : 0 ≤ C_H) (hL : 0 < L) (hR : 0 < R)
    (hClarkson : ScalarWeightedClarkson p) (engine : ExternalComplementaryComposite (Fin d) p 2 C)
    (H : HilbertDiagnostics.EuclideanRateInput C_H)
    (initial : Fin d → ℝ) (f : (Fin d → ℝ) → ℝ) (grad : (Fin d → ℝ) → Fin d → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ x, HasFDerivAt f (coordinateFunctional (grad x)) x)
    (hh : ∀ x y, lpNorm (dualExponent p) (grad x-grad y) ≤ L*lpNorm p (x-y))
    (xstar : Fin d → ℝ) (hstar : ∀ y, f xstar ≤ f y) (hr : lpNorm p (initial-xstar) ≤ R)
    (N : ℕ) (hN : 0 < N) (hlarge : 2*queryConstant C (vectorBiasCoefficient p) p 2 ≤ (N:ℝ)) :
    ∃ P : HilbertDiagnostics.Program d, HilbertDiagnostics.Certificate P f grad (dualExponent p) N
      (max C_H ((2*queryConstant C (vectorBiasCoefficient p) p 2)^((p+2)/p))*L*R*
        min (HilbertDiagnostics.hilbertFactor d p N) (HilbertDiagnostics.continuationFactor p N)) := by
  have hK := queryConstant_pos hC (vectorBiasCoefficient_pos p) hp (by norm_num : (1:ℝ)<2)
  exact ⟨_, HilbertDiagnostics.finite_dimension_envelope_from_accuracy hd hp hCH hK hL hR H
    f grad initial xstar hf hg hstar hh hr _
    (smooth_accuracy_family hp hC hL.le hR.le hClarkson engine initial f grad hf hg hh xstar hstar hr)
    N hN hlarge⟩

end P31
