import P31.SchattenUpperBound
import P31.DiagonalLowerBound

/-! Remark 5.3 for the actual matrix query program, including its cost. -/
noncomputable section
open scoped Matrix.Norms.Elementwise
namespace P31.Schatten
open QueryProgram Schedule
variable {m n : ℕ}

/-- Every weaker Schatten gradient target has the same executed query bound. -/
theorem matrix_weaker_target {p κ C L R ε s : ℝ}
    (S : SpectralInput m n) (hp : 2 ≤ p) (hκ : 1 < κ) (hκhi : κ ≤ 2) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hε : 0 < ε) (hqs : dualExponent p ≤ s)
    (engine : ExternalMatrixComposite S p κ C)
    (initial : Mat m n) (f : Mat m n → ℝ) (grad : Mat m n → Mat m n)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ X, HasFDerivAt f (traceFunctional (grad X)) X)
    (hh : ∀ X Y, S.snorm (dualExponent p) (grad X-grad Y) ≤ L*S.snorm p (X-Y)^(κ-1))
    (xstar : Mat m n) (hstar : ∀ Y, f xstar ≤ f Y) (hr : S.snorm p (initial-xstar) ≤ R) :
    let P := matrixGradientMethod S p κ L R ε initial hp hκ hκhi engine
    S.snorm s (grad (P.run grad).value) ≤ ε ∧
    ((P.run grad).calls : ℝ) ≤ queryConstant C (matrixBiasCoefficient p) p κ *
      (1+(L*R^(κ-1)/ε)^beta p κ) := by
  have h := matrixGradientMethod_guarantee S hp hκ hκhi hC hL hR hε engine
    initial f grad hf hg hh xstar hstar hr
  exact ⟨S.weaker_target_certificate (dualExponent_pos (by linarith)) hqs _ h.1, h.2⟩

/-- For a stronger target, the exact dimensional loss enters the accuracy
given to the actual method and hence its executed query count. -/
theorem matrix_stronger_target {p κ C L R ε s : ℝ}
    (S : SpectralInput m n) (hk : 0 < min m n)
    (hp : 2 ≤ p) (hκ : 1 < κ) (hκhi : κ ≤ 2) (hC : 0 ≤ C)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (hε : 0 < ε) (hs : 0 < s) (hsq : s ≤ dualExponent p)
    (engine : ExternalMatrixComposite S p κ C)
    (initial : Mat m n) (f : Mat m n → ℝ) (grad : Mat m n → Mat m n)
    (hf : ConvexOn ℝ Set.univ f) (hg : ∀ X, HasFDerivAt f (traceFunctional (grad X)) X)
    (hh : ∀ X Y, S.snorm (dualExponent p) (grad X-grad Y) ≤ L*S.snorm p (X-Y)^(κ-1))
    (xstar : Mat m n) (hstar : ∀ Y, f xstar ≤ f Y) (hr : S.snorm p (initial-xstar) ≤ R) :
    let factor := ((min m n : ℕ) : ℝ)^(1/s-1/dualExponent p)
    let P := matrixGradientMethod S p κ L R (ε/factor) initial hp hκ hκhi engine
    S.snorm s (grad (P.run grad).value) ≤ ε ∧
    ((P.run grad).calls : ℝ) ≤ queryConstant C (matrixBiasCoefficient p) p κ *
      (1+(L*R^(κ-1)*factor/ε)^beta p κ) := by
  dsimp only
  have hfactor : 0 < ((min m n : ℕ) : ℝ)^(1/s-1/dualExponent p) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hk) _
  have h := matrixGradientMethod_guarantee S hp hκ hκhi hC hL hR (div_pos hε hfactor)
    engine initial f grad hf hg hh xstar hstar hr
  refine ⟨S.stronger_target_certificate hs hsq hk _ h.1, ?_⟩
  convert h.2 using 1
  congr 3
  field_simp

end P31.Schatten
