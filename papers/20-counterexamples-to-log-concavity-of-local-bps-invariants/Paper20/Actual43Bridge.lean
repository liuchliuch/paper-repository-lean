import Paper20.Elimination
import Paper20.Ordinary43Bridge
import Paper20.FastHilbertProof

/-! The verified generic last step for Theorem 1.1: actual Hilbert input
coefficients determine the actual implemented BPS sequence via the proved
elimination program. The complete partition-sum certificate supplies the
remaining Hilbert equality in Counterexample43; no BPS coefficient conclusion
is assumed by this bridge. -/
namespace Paper20.Actual43Bridge
open Paper20.Semantics Paper20.Elimination
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

variable (hH : (hilbertArray 43 1).toList = Cert.h43List)

lemma degree : deg 43 1 = 903 := by decide

include hH

lemma hilbert_coeff (ℓ : ℕ) :
    (hilbertArray 43 1).getD ℓ 0 = Cert.h43List.getD ℓ 0 := by
  have he := congrArg (fun l : List ℕ => l.getD ℓ 0)
    hH
  simpa only [FastHilbert.getD_toList] using he

omit hH in
lemma h43_int_coeff (ℓ : ℕ) :
    Cert.Hilbert43.H.getD ℓ 0 = (Cert.h43List.getD ℓ 0 : ℤ) := by
  unfold Cert.Hilbert43.H
  simp only [List.getD_eq_getD_getElem?, List.getElem?_map]
  cases he : Cert.h43List[ℓ]? <;> simp

/-- Actual Hilbert-program residual, identified with the verified F43 data. -/
theorem residual_coeff (ℓ : ℕ) (hℓ : ℓ ≤ 903) :
    (fArray 43 1).getD ℓ 0 = Cert.f43List.getD ℓ 0 := by
  rw [Paper20.ArraySemantics.fArray_correct 43 1 ℓ (by rwa [degree])]
  calc
    _ = hilbertResidual 43 (fun i => Cert.Hilbert43.H.getD i 0) ℓ := by
      unfold hilbertResidual
      apply Finset.sum_congr rfl
      intro i hi
      simp only [hilbert_coeff hH, h43_int_coeff]
    _ = _ := Cert.Hilbert43.residual_eq ℓ hℓ

/-- The actual implemented integer coefficients solve the certified recurrence. -/
theorem actual_recurrence : recurrence25 903
    (fun ℓ => Cert.f43List.getD ℓ 0)
    (fun h => (bpsFromF (fArray 43 1)).getD h 0) := by
  have hr := bpsFromHilbert_recurrence 43 1
  rw [degree] at hr
  intro h hh
  have he := hr h hh
  dsimp only at he
  rw [residual_coeff hH (903-h) (by omega)] at he
  exact he

/-- The full actual BPS sequence agrees with the 904-entry certificate. -/
theorem coefficient (h : ℕ) (hh : h ≤ 903) : bpsCoeff 43 1 h = Ordinary43.n_h h := by
  rw [bpsCoeff_eq_toNat 43 1 h (by rwa [degree])]
  have he := recurrence25_unique (actual_recurrence hH) Cert.Checked43.certificate_recurrence h hh
  rw [he, Ordinary43Bridge.integers_get]
  exact Int.toNat_natCast _

/-- Full computational Theorem 1.1, with the actual BPS coefficient function. -/
theorem theorem1_1 :
    bpsCoeff 43 1 23 = 46743830419465000460525749853426296821511513919267 ∧
    bpsCoeff 43 1 24 = 4478706954001198396797888969114794682889954544660295 ∧
    bpsCoeff 43 1 25 = 429147501803199891064835526788080765663004079176388506 ∧
    20000*(bpsCoeff 43 1 24)^2 < 19999*bpsCoeff 43 1 23*bpsCoeff 43 1 25 ∧
    (∀ h ≤ 903, 0 < bpsCoeff 43 1 h) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [coefficient hH 23 (by decide)]; exact Ordinary43.n_h_23
  · rw [coefficient hH 24 (by decide)]; exact Ordinary43.n_h_24
  · rw [coefficient hH 25 (by decide)]; exact Ordinary43.n_h_25
  · rw [coefficient hH 24 (by decide), coefficient hH 23 (by decide), coefficient hH 25 (by decide)]
    exact Ordinary43.thm11_ineq
  · intro h hh
    rw [coefficient hH h hh]
    exact Ordinary43.n_h_pos h (by omega)

end Paper20.Actual43Bridge
