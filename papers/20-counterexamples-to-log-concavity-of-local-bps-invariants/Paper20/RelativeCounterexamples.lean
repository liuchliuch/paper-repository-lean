import Paper20.GeometricInput
import Paper20.ContentQ36Bridge
import Paper20.Counterexample43
import Paper20.Appendix

namespace Paper20.Relative
open Paper20.ExternalInput
noncomputable section
set_option maxHeartbeats 5000000

/-- Internal transfer of the certified same-Q inequality to the original
actual BPS implementation. The finite root premise is discharged by the
complete partition certificate in the final counterexample module. -/
theorem theorem1_2_of_root (mathas : MathasInputs)
    (hs : Paper20.RContent36.Correct Paper20.RContent36.root
      Paper20.Cert.RContent36.Tree.rootState) (k : ℕ) (hk : 10 ≤ k) :
    (bpsCoeff 36 k 21)^2 < bpsCoeff 36 k 20*bpsCoeff 36 k 22 ∧
      (∀ h ≤ deg 36 k, 0 < bpsCoeff 36 k h) := by
  have hd : 22 ≤ deg 36 k := by
    change 22 ≤ k*Nat.choose 36 2
    rw [show Nat.choose 36 2=630 by decide]
    omega
  constructor
  · have he := ContentQ36Bridge.constructed_Q_inequality hs k hk
    rw [← bps_Q mathas 36 k 21 (by decide) (by omega),
      ← bps_Q mathas 36 k 20 (by decide) (by omega),
      ← bps_Q mathas 36 k 22 (by decide) hd] at he
    exact_mod_cast he
  · intro h hh
    have hb := (bps_bounds mathas 36 k h (by decide) hh).1
    omega

/-- The numerical ordinary-point theorem reaches the geometric BPS
invariants defined from the supplied Euler characteristics. -/
theorem geometric_theorem1_1 (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) :
    geometricBPS data 43 1 23=46743830419465000460525749853426296821511513919267 ∧
    geometricBPS data 43 1 24=4478706954001198396797888969114794682889954544660295 ∧
    geometricBPS data 43 1 25=429147501803199891064835526788080765663004079176388506 ∧
    20000*(geometricBPS data 43 1 24)^2 <
      19999*geometricBPS data 43 1 23*geometricBPS data 43 1 25 ∧
    (∀ h ≤ 903, 0 < geometricBPS data 43 1 h) := by
  have he (h : ℕ) (hh : h ≤ 903) :
      geometricBPS data 43 1 h=(bpsCoeff 43 1 h:ℤ) :=
    geometricBPS_eq_program data geo mathas 43 1 h (by decide) (by decide) hh
  rw [he 23 (by decide),he 24 (by decide),he 25 (by decide)]
  obtain ⟨h23,h24,h25,hi,hpos⟩ := Counterexample43.theorem1_1
  refine ⟨by exact_mod_cast h23,by exact_mod_cast h24,by exact_mod_cast h25,
    by exact_mod_cast hi,?_⟩
  intro h hh
  rw [he h hh]
  exact_mod_cast hpos h hh

theorem geometric_bounds (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k h : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hh : h ≤ deg r k) :
    1 ≤ geometricBPS data r k h ∧
      geometricBPS data r k h ≤ (Nat.choose (2*deg r k) (2*h):ℤ) ∧
      geometricBPS data r k 0=1 ∧ geometricBPS data r k (deg r k)=1 := by
  rw [geometricBPS_eq_program data geo mathas r k h hr hk hh,
    geometricBPS_eq_program data geo mathas r k 0 hr hk (Nat.zero_le _),
    geometricBPS_eq_program data geo mathas r k (deg r k) hr hk le_rfl]
  exact_mod_cast bps_bounds mathas r k h hr hh

theorem geometric_Q (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k h : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hh : h ≤ deg r k) :
    (geometricBPS data r k h:ℚ)=peval (Qcoeff r h) ((k:ℚ)*(k+1)) := by
  rw [geometricBPS_eq_program data geo mathas r k h hr hk hh,Int.cast_natCast]
  exact bps_Q mathas r k h hr hh

lemma returns_of_leading (mathas : MathasInputs) (r h : ℕ) (hr : 2 ≤ r) (T : ℤ)
    (he : (listPolynomial (Qcoeff r h)).coeff h=(T:ℚ)/((2*h).factorial:ℚ)) :
    (P20Objects.transpositionReturns r h:ℚ)=(T:ℚ) := by
  have ht := Q_top_returns mathas r h hr
  rw [← coeff_listPolynomial,he] at ht
  have hm := congrArg (fun x : ℚ => x*((2*h).factorial:ℚ)) ht
  dsimp only at hm
  have hf : ((2*h).factorial:ℚ)≠0 := by positivity
  rw [div_mul_cancel₀ _ hf,div_mul_cancel₀ _ hf] at hm
  exact hm.symm

/-- The displayed T20,T21,T22 are actual return cardinalities once the
same-Q finite root has been checked; they are not independently defined
spectral substitutes for those cardinalities. -/
theorem returns20_of_root (mathas : MathasInputs)
    (hs : Paper20.RContent36.Correct Paper20.RContent36.root
      Paper20.Cert.RContent36.Tree.rootState) :
    (P20Objects.transpositionReturns 36 20:ℚ)=(Uniform36.T20:ℚ) := by
  apply returns_of_leading mathas 36 20 (by decide) Uniform36.T20
  rw [ContentQ36Bridge.Q20_of_root hs]
  exact Uniform36.leading20

theorem returns21_of_root (mathas : MathasInputs)
    (hs : Paper20.RContent36.Correct Paper20.RContent36.root
      Paper20.Cert.RContent36.Tree.rootState) :
    (P20Objects.transpositionReturns 36 21:ℚ)=(Uniform36.T21:ℚ) := by
  apply returns_of_leading mathas 36 21 (by decide) Uniform36.T21
  rw [ContentQ36Bridge.Q21_of_root hs]
  exact Uniform36.leading21

theorem returns22_of_root (mathas : MathasInputs)
    (hs : Paper20.RContent36.Correct Paper20.RContent36.root
      Paper20.Cert.RContent36.Tree.rootState) :
    (P20Objects.transpositionReturns 36 22:ℚ)=(Uniform36.T22:ℚ) := by
  apply returns_of_leading mathas 36 22 (by decide) Uniform36.T22
  rw [ContentQ36Bridge.Q22_of_root hs]
  exact Uniform36.leading22

end
end Paper20.Relative
