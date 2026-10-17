import Verification.RelativeTransfer
import Paper20.Certs.RContent36.All

/-! Final exact contracts. These thin wrappers discharge the own finite
root using root_correct. Root verification and this final elaboration are
verification_deferred_by_user; no full validation is claimed. -/
namespace P20Relative
open Polynomial Paper20 Paper20.ExternalInput

theorem thm_1_1 :
    bpsCoeff 43 1 23=46743830419465000460525749853426296821511513919267 ∧
    bpsCoeff 43 1 24=4478706954001198396797888969114794682889954544660295 ∧
    bpsCoeff 43 1 25=429147501803199891064835526788080765663004079176388506 ∧
    20000*(bpsCoeff 43 1 24)^2 < 19999*bpsCoeff 43 1 23*bpsCoeff 43 1 25 ∧
    (∀ h ≤ 903, 0 < bpsCoeff 43 1 h) :=
  P20RelativeTransfer.thm_1_1

theorem thm_1_2 (mathas : MathasInputs) : ∀ k : ℕ, 10 ≤ k →
    (bpsCoeff 36 k 21)^2 < bpsCoeff 36 k 20*bpsCoeff 36 k 22 ∧
      (∀ h ≤ deg 36 k, 0 < bpsCoeff 36 k h) :=
  P20RelativeTransfer.thm_1_2 Paper20.Cert.RContent36.Tree.root_correct mathas

theorem lemma_2_2 (mathas : MathasInputs) (r k h : ℕ) (hr : 2 ≤ r)
    (hk : 1 ≤ k) (hh : h ≤ deg r k) :
    1 ≤ bpsCoeff r k h ∧ bpsCoeff r k h ≤ Nat.choose (2*deg r k) (2*h) ∧
      bpsCoeff r k 0=1 ∧ bpsCoeff r k (deg r k)=1 :=
  P20RelativeTransfer.lemma_2_2 mathas r k h hr hk hh

theorem prop_3_1 (mathas : MathasInputs) (r h : ℕ) (hr : 2 ≤ r) :
    (∀ i, h < i → cget (Qcoeff r h) i=0) ∧
    (∀ k, 1 ≤ k → h ≤ deg r k →
      (bpsCoeff r k h:ℚ)=peval (Qcoeff r h) ((k:ℚ)*(k+1))) ∧
    peval (Qcoeff r h) 0=if h=0 then 1 else 0 :=
  P20RelativeTransfer.prop_3_1 mathas r h hr

theorem prop_3_2_spectral (r h : ℕ) :
    cget (Qcoeff r h) h=transpositionMoment r h/((2*h).factorial:ℚ) :=
  P20RelativeTransfer.prop_3_2_spectral r h

theorem prop_3_2 (mathas : MathasInputs) (r h : ℕ) (hr : 2 ≤ r) :
    cget (Qcoeff r h) h=(P20Objects.transpositionReturns r h:ℚ)/
      ((2*h).factorial:ℚ) :=
  P20RelativeTransfer.prop_3_2 mathas r h hr

theorem eq_22 (mathas : MathasInputs) (r h : ℕ) (hr : 2 ≤ r) :
    transpositionMoment r h=(P20Objects.transpositionReturns r h:ℚ) :=
  P20RelativeTransfer.eq_22 mathas r h hr

theorem prop_2_3 (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    (geometricBPSPolynomial data r k).comp (Polynomial.X^2)=
      HeckeTraceAlgebra.canonicalTrace r (HeckeTraceAlgebra.omega r^(k+1)) :=
  P20RelativeTransfer.prop_2_3 data geo mathas r k hr hk

theorem prop_2_4 (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    geometricHilbert data r k=HilbertSeriesProof.partitionHilbertSeries r k :=
  P20RelativeTransfer.prop_2_4 data geo mathas r k hr hk

theorem original_geometric_definition (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    Semantics.localBPSExpansion r (deg r k) (data.euler r k)
      (fun h => (BraidWalk.walkCount r k h:ℤ)) :=
  P20RelativeTransfer.original_geometric_definition data geo mathas r k hr hk

theorem geometric_program (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k h : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hh : h ≤ deg r k) : geometricBPS data r k h=(bpsCoeff r k h:ℤ) :=
  P20RelativeTransfer.geometric_program data geo mathas r k h hr hk hh

theorem geometric_thm_1_1 (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) :
    geometricBPS data 43 1 23=46743830419465000460525749853426296821511513919267 ∧
    geometricBPS data 43 1 24=4478706954001198396797888969114794682889954544660295 ∧
    geometricBPS data 43 1 25=429147501803199891064835526788080765663004079176388506 ∧
    20000*(geometricBPS data 43 1 24)^2 <
      19999*geometricBPS data 43 1 23*geometricBPS data 43 1 25 ∧
    (∀ h ≤ 903, 0 < geometricBPS data 43 1 h) :=
  P20RelativeTransfer.geometric_thm_1_1 data geo mathas

theorem geometric_thm_1_2 (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (k : ℕ) (hk : 10 ≤ k) :
    (geometricBPS data 36 k 21)^2 <
      geometricBPS data 36 k 20*geometricBPS data 36 k 22 ∧
      (∀ h ≤ deg 36 k, 0 < geometricBPS data 36 k h) :=
  P20RelativeTransfer.geometric_thm_1_2 Paper20.Cert.RContent36.Tree.root_correct data geo mathas k hk

theorem geometric_prop_3_1 (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k h : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hh : h ≤ deg r k) :
    (geometricBPS data r k h:ℚ)=peval (Qcoeff r h) ((k:ℚ)*(k+1)) :=
  P20RelativeTransfer.geometric_prop_3_1 data geo mathas r k h hr hk hh

theorem normalized_ruling (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    (geometricBPSPolynomial data r k).eval₂ (Int.castRingHom QuantumSeriesCoordinates.SeriesField)
      ((HilbertAtZero.v-HilbertAtZero.v⁻¹)^2)=
        (HilbertAtZero.v-HilbertAtZero.v⁻¹)^r*data.ruling r k :=
  P20RelativeTransfer.normalized_ruling data geo mathas r k hr hk

theorem eq_23 (mathas : MathasInputs) (r h : ℕ) (hr : 2 ≤ r) (hh : 1 ≤ h)
    (he : ∀ᶠ u : ℚ in Filter.atTop,
      peval (Qcoeff r (h-1)) u*peval (Qcoeff r (h+1)) u ≤ peval (Qcoeff r h) u^2) :
    ((2*h+2:ℕ):ℚ)*((2*h+1:ℕ):ℚ)*(P20Objects.transpositionReturns r h:ℚ)^2 ≥
      ((2*h:ℕ):ℚ)*((2*h-1:ℕ):ℚ)*(P20Objects.transpositionReturns r (h-1):ℚ)*
        (P20Objects.transpositionReturns r (h+1):ℚ) :=
  P20RelativeTransfer.eq_23 mathas r h hr hh he

theorem eq_26 (mathas : MathasInputs) :
    (99993:ℚ)/100000 <
      (44*43*(P20Objects.transpositionReturns 36 21:ℚ)^2)/
        (42*41*(P20Objects.transpositionReturns 36 20:ℚ)*
          (P20Objects.transpositionReturns 36 22:ℚ)) ∧
      (44*43*(P20Objects.transpositionReturns 36 21:ℚ)^2)/
        (42*41*(P20Objects.transpositionReturns 36 20:ℚ)*
          (P20Objects.transpositionReturns 36 22:ℚ)) < (99994:ℚ)/100000 :=
  P20RelativeTransfer.eq_26 Paper20.Cert.RContent36.Tree.root_correct mathas

theorem remark_2_1_node (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) :
    geometricBPSPolynomial data 2 1=1+Polynomial.X ∧
      data.lowestHOMFLY 2 1=(HilbertAtZero.v-HilbertAtZero.v⁻¹)+
        (HilbertAtZero.v-HilbertAtZero.v⁻¹)⁻¹ :=
  P20RelativeTransfer.remark_2_1_node data geo mathas

theorem remark_2_1_sign {L I K : Type*} [Field K] (S : SkeinParity.System L I)
    (a z : K)
    (unique : ∀ P Q : L → K, SkeinParity.Law S a z P → SkeinParity.Law S a z Q → P=Q)
    (P Q : L → K) (hP : SkeinParity.Law S a z P) (hQ : SkeinParity.Law S a (-z) Q) :
    P=(fun l => SkeinParity.componentSign S l*Q l) :=
  P20RelativeTransfer.remark_2_1_sign S a z unique P Q hP hQ

theorem ruling_polynomial_unique (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (P : ℤ[X]) (hP : IsNormalizedRulingPolynomial data r k P) :
    P=geometricBPSPolynomial data r k :=
  P20RelativeTransfer.ruling_polynomial_unique data geo mathas r k hr hk P hP

theorem ruling_thm_1_1 (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (P : ℤ[X]) (hP : IsNormalizedRulingPolynomial data 43 1 P) :
    P.coeff 23=46743830419465000460525749853426296821511513919267 ∧
    P.coeff 24=4478706954001198396797888969114794682889954544660295 ∧
    P.coeff 25=429147501803199891064835526788080765663004079176388506 ∧
    20000*(P.coeff 24)^2 < 19999*P.coeff 23*P.coeff 25 ∧
    (∀ h ≤ 903, 0 < P.coeff h) :=
  P20RelativeTransfer.ruling_thm_1_1 data geo mathas P hP

theorem ruling_thm_1_2 (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (k : ℕ) (hk : 10 ≤ k) (P : ℤ[X])
    (hP : IsNormalizedRulingPolynomial data 36 k P) :
    (P.coeff 21)^2 < P.coeff 20*P.coeff 22 ∧ (∀ h ≤ deg 36 k, 0 < P.coeff h) :=
  P20RelativeTransfer.ruling_thm_1_2 Paper20.Cert.RContent36.Tree.root_correct data geo mathas k hk P hP

end P20Relative
