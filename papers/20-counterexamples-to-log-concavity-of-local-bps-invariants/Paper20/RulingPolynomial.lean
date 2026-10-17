import Paper20.Counterexample36Transfer
import Paper20.GeometricNode

namespace Paper20.ExternalInput
open Polynomial Finset Paper20.HilbertAtZero Paper20.HilbertSeriesProof Paper20.Semantics
open Paper20.QuantumSeriesCoordinates
noncomputable section
set_option maxHeartbeats 5000000

lemma bpsPolynomial_coeff (d : ℕ) (n : ℕ → ℤ) (i : ℕ) :
    (bpsPolynomial d n).coeff i=if i ≤ d then n i else 0 := by
  classical
  simp only [bpsPolynomial,C_mul_X_pow_eq_monomial,finset_sum_coeff,coeff_monomial]
  by_cases hi : i ≤ d
  · rw [if_pos hi,Finset.sum_eq_single i]
    · simp
    · intro j hj hji; simp [hji,Ne.symm hji]
    · intro hn; exact False.elim (hn (Finset.mem_range.mpr (by omega)))
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j hj
    have hn : j≠i := by have := Finset.mem_range.mp hj; omega
    simp [hn]

lemma bpsPolynomial_of_coeff (p : ℤ[X]) : bpsPolynomial p.natDegree p.coeff=p :=
  p.as_sum_range_C_mul_X_pow.symm

/-- Faithfulness of w=(t-t^-1)² at the original Hilbert origin. The
proof uses the already proved original BPS triangular independence. -/
theorem origin_eval_eq_zero (p : ℤ[X])
    (he : p.eval₂ (Int.castRingHom SeriesField) ((HilbertAtZero.v-HilbertAtZero.v⁻¹)^2)=0) :
    p=0 := by
  have hmap : qMap (rationalBPS p.natDegree p.coeff)=qMap 0 := by
    rw [qMap_rationalBPS,bpsPolynomial_of_coeff,he,mul_zero,map_zero]
  have hr := qMap_injective hmap
  have hz : bpsSeries p.natDegree p.coeff=0 := by
    apply PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective
    simpa only [rationalBPS,map_zero] using hr
  have hh : hilbertSeries (fun _ => (0:ℤ))=0 := by
    ext i
    simp only [hilbertSeries,PowerSeries.coeff_mk,map_zero]
  have hn : localBPSExpansion 0 p.natDegree (fun _ => 0) p.coeff := by
    apply (localBPSExpansion_iff_series ..).2
    rw [pow_zero,one_mul,hh,hz]
  have hzero : localBPSExpansion 0 p.natDegree (fun _ => 0) (fun _ => 0) := by
    apply (localBPSExpansion_iff_series ..).2
    rw [pow_zero,one_mul,hh]
    simp [bpsSeries]
  ext i
  rw [coeff_zero]
  by_cases hi : i ≤ p.natDegree
  · exact localBPSExpansion_unique hn hzero i hi
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem origin_eval_injective : Function.Injective (fun p : ℤ[X] =>
    p.eval₂ (Int.castRingHom SeriesField) ((HilbertAtZero.v-HilbertAtZero.v⁻¹)^2)) := by
  intro p q he
  dsimp only at he
  apply sub_eq_zero.mp
  apply origin_eval_eq_zero
  rw [eval₂_sub,he,sub_self]

/-- Equation(8) determines a UNIQUE normalized ruling polynomial, not
merely a value at an unspecified scalar. -/
theorem normalized_ruling_unique (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (P : ℤ[X]) (hP : IsNormalizedRulingPolynomial data r k P) :
    P=geometricBPSPolynomial data r k :=
  origin_eval_injective (hP.trans (geometric_normalized_ruling data geo mathas r k hr hk).symm)

theorem normalized_ruling_exists (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    ∃! P : ℤ[X], IsNormalizedRulingPolynomial data r k P := by
  refine ⟨geometricBPSPolynomial data r k,
    geometric_normalized_ruling data geo mathas r k hr hk,?_⟩
  intro P hP
  exact normalized_ruling_unique data geo mathas r k hr hk P hP

theorem normalized_ruling_coeff (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (P : ℤ[X]) (hP : IsNormalizedRulingPolynomial data r k P)
    (h : ℕ) (hh : h ≤ deg r k) : P.coeff h=geometricBPS data r k h := by
  rw [normalized_ruling_unique data geo mathas r k hr hk P hP,
    geometricBPSPolynomial,bpsPolynomial_coeff,if_pos hh]

theorem ruling_theorem1_1 (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (P : ℤ[X]) (hP : IsNormalizedRulingPolynomial data 43 1 P) :
    P.coeff 23=46743830419465000460525749853426296821511513919267 ∧
    P.coeff 24=4478706954001198396797888969114794682889954544660295 ∧
    P.coeff 25=429147501803199891064835526788080765663004079176388506 ∧
    20000*(P.coeff 24)^2 < 19999*P.coeff 23*P.coeff 25 ∧
    (∀ h ≤ 903, 0 < P.coeff h) := by
  have he (h : ℕ) (hh : h ≤ 903) : P.coeff h=geometricBPS data 43 1 h :=
    normalized_ruling_coeff data geo mathas 43 1 (by decide) (by decide) P hP h hh
  rw [he 23 (by decide),he 24 (by decide),he 25 (by decide)]
  obtain ⟨h23,h24,h25,hi,hpos⟩ := Relative.geometric_theorem1_1 data geo mathas
  refine ⟨h23,h24,h25,hi,?_⟩
  intro h hh
  rw [he h hh]
  exact hpos h hh

theorem ruling_theorem1_2_of_root
    (hs : Paper20.RContent36.Correct Paper20.RContent36.root Paper20.Cert.RContent36.Tree.rootState)
    (data : GeometricData) (geo : GeometricInputs data) (mathas : MathasInputs)
    (k : ℕ) (hk : 10 ≤ k) (P : ℤ[X]) (hP : IsNormalizedRulingPolynomial data 36 k P) :
    (P.coeff 21)^2 < P.coeff 20*P.coeff 22 ∧ (∀ h ≤ deg 36 k, 0 < P.coeff h) := by
  have hd : 22 ≤ deg 36 k := by
    change 22 ≤ k*Nat.choose 36 2
    rw [show Nat.choose 36 2=630 by decide]
    omega
  have he (h : ℕ) (hh : h ≤ deg 36 k) : P.coeff h=geometricBPS data 36 k h :=
    normalized_ruling_coeff data geo mathas 36 k (by decide) (by omega) P hP h hh
  rw [he 21 (by omega),he 20 (by omega),he 22 hd]
  obtain ⟨hi,hpos⟩ := Counterexample36Transfer.geometric_theorem1_2 hs data geo mathas k hk
  refine ⟨hi,?_⟩
  intro h hh
  rw [he h hh]
  exact hpos h hh

end
end Paper20.ExternalInput
