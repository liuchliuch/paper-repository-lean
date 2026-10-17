import Paper20.Counterexample36Transfer
import Paper20.RulingPolynomial
import Paper20.Certs.RContent36.All

/-! Final exports consume the full actual kernel-checked finite root.
No finite-computation premise remains in these theorem types. -/
namespace Paper20.Counterexample36
open Polynomial Paper20.ExternalInput Paper20.Relative
noncomputable section

theorem theorem1_2 (mathas : MathasInputs) : ∀ k : ℕ, 10 ≤ k →
    (bpsCoeff 36 k 21)^2 < bpsCoeff 36 k 20*bpsCoeff 36 k 22 ∧
      (∀ h ≤ deg 36 k, 0 < bpsCoeff 36 k h) :=
  Counterexample36Transfer.theorem1_2 Cert.RContent36.Tree.root_correct mathas

theorem geometric_theorem1_2 (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (k : ℕ) (hk : 10 ≤ k) :
    (geometricBPS data 36 k 21)^2 <
      geometricBPS data 36 k 20*geometricBPS data 36 k 22 ∧
      (∀ h ≤ deg 36 k, 0 < geometricBPS data 36 k h) :=
  Counterexample36Transfer.geometric_theorem1_2 Cert.RContent36.Tree.root_correct data geo mathas k hk

theorem returns20 (mathas : MathasInputs) :
    (P20Objects.transpositionReturns 36 20:ℚ)=(Uniform36.T20:ℚ) :=
  Counterexample36Transfer.returns20 Cert.RContent36.Tree.root_correct mathas

theorem returns21 (mathas : MathasInputs) :
    (P20Objects.transpositionReturns 36 21:ℚ)=(Uniform36.T21:ℚ) :=
  Counterexample36Transfer.returns21 Cert.RContent36.Tree.root_correct mathas

theorem returns22 (mathas : MathasInputs) :
    (P20Objects.transpositionReturns 36 22:ℚ)=(Uniform36.T22:ℚ) :=
  Counterexample36Transfer.returns22 Cert.RContent36.Tree.root_correct mathas

theorem actual_return_ratio (mathas : MathasInputs) :
    (99993:ℚ)/100000 <
      (44*43*(P20Objects.transpositionReturns 36 21:ℚ)^2)/
        (42*41*(P20Objects.transpositionReturns 36 20:ℚ)*
          (P20Objects.transpositionReturns 36 22:ℚ)) ∧
      (44*43*(P20Objects.transpositionReturns 36 21:ℚ)^2)/
        (42*41*(P20Objects.transpositionReturns 36 20:ℚ)*
          (P20Objects.transpositionReturns 36 22:ℚ)) < (99994:ℚ)/100000 :=
  Counterexample36Transfer.actual_return_ratio Cert.RContent36.Tree.root_correct mathas

theorem actual_return_obstruction (mathas : MathasInputs) :
    (44:ℚ)*43*(P20Objects.transpositionReturns 36 21:ℚ)^2 <
      42*41*(P20Objects.transpositionReturns 36 20:ℚ)*
        (P20Objects.transpositionReturns 36 22:ℚ) :=
  Counterexample36Transfer.actual_return_obstruction Cert.RContent36.Tree.root_correct mathas

theorem ruling_theorem1_2 (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (k : ℕ) (hk : 10 ≤ k) (P : ℤ[X])
    (hP : IsNormalizedRulingPolynomial data 36 k P) :
    (P.coeff 21)^2 < P.coeff 20*P.coeff 22 ∧ (∀ h ≤ deg 36 k, 0 < P.coeff h) :=
  ExternalInput.ruling_theorem1_2_of_root Cert.RContent36.Tree.root_correct
    data geo mathas k hk P hP

end
end Paper20.Counterexample36
