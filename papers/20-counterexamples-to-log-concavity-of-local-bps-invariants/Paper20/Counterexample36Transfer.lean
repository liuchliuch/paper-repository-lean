import Paper20.RelativeCounterexamples

/-! Internal transfer proofs, separated from the still-running finite root.
The final Counterexample36 module discharges this exact own finite premise. -/
namespace Paper20.Counterexample36Transfer
open Paper20.ExternalInput Paper20.Relative
noncomputable section

theorem theorem1_2 (hs : Paper20.RContent36.Correct Paper20.RContent36.root Paper20.Cert.RContent36.Tree.rootState) (mathas : MathasInputs) : ∀ k : ℕ, 10 ≤ k →
    (bpsCoeff 36 k 21)^2 < bpsCoeff 36 k 20*bpsCoeff 36 k 22 ∧
      (∀ h ≤ deg 36 k, 0 < bpsCoeff 36 k h) :=
  theorem1_2_of_root mathas hs

theorem geometric_theorem1_2 (hs : Paper20.RContent36.Correct Paper20.RContent36.root Paper20.Cert.RContent36.Tree.rootState) (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (k : ℕ) (hk : 10 ≤ k) :
    (geometricBPS data 36 k 21)^2 <
      geometricBPS data 36 k 20*geometricBPS data 36 k 22 ∧
      (∀ h ≤ deg 36 k, 0 < geometricBPS data 36 k h) := by
  have hd : 22 ≤ deg 36 k := by
    change 22 ≤ k*Nat.choose 36 2
    rw [show Nat.choose 36 2=630 by decide]
    omega
  rw [geometricBPS_eq_program data geo mathas 36 k 21 (by decide) (by omega) (by omega),
    geometricBPS_eq_program data geo mathas 36 k 20 (by decide) (by omega) (by omega),
    geometricBPS_eq_program data geo mathas 36 k 22 (by decide) (by omega) hd]
  obtain ⟨hi,hpos⟩ := theorem1_2 hs mathas k hk
  constructor
  · exact_mod_cast hi
  · intro h hh
    rw [geometricBPS_eq_program data geo mathas 36 k h (by decide) (by omega) hh]
    exact_mod_cast hpos h hh

theorem returns20 (hs : Paper20.RContent36.Correct Paper20.RContent36.root Paper20.Cert.RContent36.Tree.rootState) (mathas : MathasInputs) :
    (P20Objects.transpositionReturns 36 20:ℚ)=(Uniform36.T20:ℚ) :=
  returns20_of_root mathas hs

theorem returns21 (hs : Paper20.RContent36.Correct Paper20.RContent36.root Paper20.Cert.RContent36.Tree.rootState) (mathas : MathasInputs) :
    (P20Objects.transpositionReturns 36 21:ℚ)=(Uniform36.T21:ℚ) :=
  returns21_of_root mathas hs

theorem returns22 (hs : Paper20.RContent36.Correct Paper20.RContent36.root Paper20.Cert.RContent36.Tree.rootState) (mathas : MathasInputs) :
    (P20Objects.transpositionReturns 36 22:ℚ)=(Uniform36.T22:ℚ) :=
  returns22_of_root mathas hs

theorem actual_return_ratio (hs : Paper20.RContent36.Correct Paper20.RContent36.root Paper20.Cert.RContent36.Tree.rootState) (mathas : MathasInputs) :
    (99993:ℚ)/100000 <
      (44*43*(P20Objects.transpositionReturns 36 21:ℚ)^2)/
        (42*41*(P20Objects.transpositionReturns 36 20:ℚ)*
          (P20Objects.transpositionReturns 36 22:ℚ)) ∧
      (44*43*(P20Objects.transpositionReturns 36 21:ℚ)^2)/
        (42*41*(P20Objects.transpositionReturns 36 20:ℚ)*
          (P20Objects.transpositionReturns 36 22:ℚ)) < (99994:ℚ)/100000 := by
  rw [returns20 hs mathas,returns21 hs mathas,returns22 hs mathas]
  exact Uniform36.thm26

theorem actual_return_obstruction (hs : Paper20.RContent36.Correct Paper20.RContent36.root Paper20.Cert.RContent36.Tree.rootState) (mathas : MathasInputs) :
    (44:ℚ)*43*(P20Objects.transpositionReturns 36 21:ℚ)^2 <
      42*41*(P20Objects.transpositionReturns 36 20:ℚ)*
        (P20Objects.transpositionReturns 36 22:ℚ) := by
  rw [returns20 hs mathas,returns21 hs mathas,returns22 hs mathas]
  exact_mod_cast Uniform36.eq23_fails

end
end Paper20.Counterexample36Transfer
