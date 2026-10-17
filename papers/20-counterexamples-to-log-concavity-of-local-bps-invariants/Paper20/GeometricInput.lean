import Paper20.RelativeConsequences
import Paper20.HOMFLYInput

/-!
Explicit external geometric data and the THREE original published
identities.  The actual schemes, Euler characteristic, HOMFLY invariant,
and Legendrian ruling construction are outside this formalization.  Their
values are supplied as named data, with precisely stated identities.
No field asserts equation (8), a BPS equality, the partition Hilbert sum,
or any result newly proved in this paper.
-/
namespace Paper20.ExternalInput
open Polynomial Paper20.QuantumSeriesCoordinates Paper20.HilbertAtZero
open Paper20.HeckeWalkExpansion Paper20.HilbertSeriesProof
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

/-- Values of external invariants for C_(r,k): y^r=x^(rk), its algebraic
link, and the rainbow closure of Delta^(2k). Their geometric construction
is explicitly not claimed to have been formalized. -/
structure GeometricData where
  euler : ℕ → ℕ → ℕ → ℤ
  ruling : ℕ → ℕ → SeriesField
  homfly : HOMFLYData

def geometricHilbert (data : GeometricData) (r k : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk (fun ℓ => (data.euler r k ℓ:ℚ))

def milnorExponent (r k : ℕ) : ℤ := 2*(deg r k:ℤ)+1-(r:ℤ)

/-- The lowest coefficient is the actual a-Laurent coefficient of the
supplied full HOMFLY invariant, with no opaque extraction postulate. -/
def GeometricData.lowestHOMFLY (data : GeometricData) (r k : ℕ) : SeriesField :=
  (data.homfly.positive (data.homfly.familyLink r k)).coeff (milnorExponent r k)

def GeometricData.oppositeLowestHOMFLY (data : GeometricData) (r k : ℕ) : SeriesField :=
  (data.homfly.opposite (data.homfly.familyLink r k)).coeff (milnorExponent r k)

/-- Original normalized ruling meaning: P(w), w=z², represents z^r R(z).
This definition contains neither a BPS coefficient nor a walk polynomial. -/
def IsNormalizedRulingPolynomial (data : GeometricData) (r k : ℕ) (P : ℤ[X]) : Prop :=
  P.eval₂ (Int.castRingHom SeriesField) ((HilbertAtZero.v-HilbertAtZero.v⁻¹)^2)=
    (HilbertAtZero.v-HilbertAtZero.v⁻¹)^r*data.ruling r k

/-- Maulik/Oblomkov--Shende at lowest a degree, Rutherford, and the
Su--Xie--Yu walk/ruling formula, specialized only to the explicit curve
family and braid. The sign and exponent normalization is retained. -/
structure GeometricInputs (data : GeometricData) : Prop where
  homfly : HOMFLYInputs data.homfly
  hilbert_homfly_original : ∀ r k, 2 ≤ r → 1 ≤ k →
    data.oppositeLowestHOMFLY r k=
      HilbertAtZero.v^(-milnorExponent r k)*(1-HilbertAtZero.v^2)*
        qMap (geometricHilbert data r k)
  rutherford : ∀ r k, 2 ≤ r → 1 ≤ k →
    data.lowestHOMFLY r k=(HilbertAtZero.v-HilbertAtZero.v⁻¹)*data.ruling r k
  walk_ruling : ∀ r k, 2 ≤ r → 1 ≤ k →
    data.ruling r k=(HilbertAtZero.v-HilbertAtZero.v⁻¹)^(-(r:ℤ))*
      (closedHeckePolynomial r k).eval₂ (Int.castRingHom SeriesField)
        (HilbertAtZero.v-HilbertAtZero.v⁻¹)

/-- The corrected sign in(7) is DERIVED from the original opposite-z
Hilbert--HOMFLY input and the proved skein sign conversion. -/
theorem GeometricInputs.hilbert_homfly {data : GeometricData}
    (input : GeometricInputs data) (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    data.lowestHOMFLY r k=(-1:SeriesField)^(r-1)*
      HilbertAtZero.v^(-milnorExponent r k)*(1-HilbertAtZero.v^2)*
        qMap (geometricHilbert data r k) := by
  have he := homfly_coefficient_sign data.homfly input.homfly r k hr hk
    (milnorExponent r k)
  change data.lowestHOMFLY r k=(-1:SeriesField)^(r-1)*
    data.oppositeLowestHOMFLY r k at he
  rw [he,input.hilbert_homfly_original r k hr hk]
  ring

lemma origin_difference_ne_zero : HilbertAtZero.v-HilbertAtZero.v⁻¹≠0 := by
  intro he
  have hp : HilbertAtZero.v^(2:ℤ)=HilbertAtZero.v^(0:ℤ) := by
    have hh := sub_eq_zero.mp he
    simp only [zpow_ofNat,pow_zero]
    calc
      HilbertAtZero.v^2=HilbertAtZero.v*HilbertAtZero.v := pow_two _
      _=HilbertAtZero.v*HilbertAtZero.v⁻¹ := congrArg (HilbertAtZero.v*·) hh
      _=1 := mul_inv_cancel₀ HilbertAtZero.v_ne_zero
  have hn := Paper20.Seminormal.hilbert_origin_parameter_injective hp
  omega

lemma homflyZ_ne_zero : homflyZ≠0 := HahnSeries.C_ne_zero origin_difference_ne_zero

/-- The sign in (7) and the Milnor shift produce the original BPS
normalization. This algebra is a proved step, not an external input. -/
lemma geometric_normalization {K : Type*} [Field K] (r d : ℕ) (hr : 1 ≤ r)
    (v : K) (hv : v≠0) :
    (v-v⁻¹)^(r-1)*(-1:K)^(r-1)*v^(-(2*(d:ℤ)+1-(r:ℤ)))*(1-v^2)=
      v^(-(2*(d:ℤ)))*(1-v^2)^r := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r≠0)
  have he : -(2*(d:ℤ)+1-((n+1:ℕ):ℤ))=(n:ℤ)-(2*(d:ℤ)) := by omega
  rw [he]
  simp only [Nat.succ_sub_one,zpow_sub₀ hv,zpow_natCast,zpow_neg]
  have hb : 1-v^2=(-1:K)*v*(v-v⁻¹) := by field_simp <;> ring
  rw [hb,pow_succ,mul_pow,mul_pow]
  ring

/-- Equation (8), before BPS coefficient extraction, derived from all
three original external identities and the proved sign normalization. -/
theorem geometric_quantum (data : GeometricData) (input : GeometricInputs data)
    (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    HilbertAtZero.v^(-(2*(deg r k:ℤ)))*(1-HilbertAtZero.v^2)^r*
      qMap (geometricHilbert data r k)=
        (closedHeckePolynomial r k).eval₂ (Int.castRingHom SeriesField)
          (HilbertAtZero.v-HilbertAtZero.v⁻¹) := by
  have he := (input.hilbert_homfly r k hr hk).symm.trans (input.rutherford r k hr hk)
  rw [input.walk_ruling r k hr hk] at he
  have hm := congrArg (fun x : SeriesField =>
    (HilbertAtZero.v-HilbertAtZero.v⁻¹)^(r-1)*x) he
  dsimp only at hm
  have hleft := geometric_normalization r (deg r k) (by omega)
    HilbertAtZero.v HilbertAtZero.v_ne_zero
  unfold milnorExponent at hm
  rw [← mul_assoc,← mul_assoc,← mul_assoc,hleft] at hm
  have hz : (HilbertAtZero.v-HilbertAtZero.v⁻¹)^(r-1)*
      (HilbertAtZero.v-HilbertAtZero.v⁻¹)*
      (HilbertAtZero.v-HilbertAtZero.v⁻¹)^(-(r:ℤ))=1 := by
    rw [← pow_succ,show r-1+1=r by omega,← zpow_natCast,
      ← zpow_add₀ origin_difference_ne_zero,add_neg_cancel,zpow_zero]
  rw [← mul_assoc,← mul_assoc,hz,one_mul] at hm
  exact hm

/-- The actual partition Hilbert series equals the supplied geometric
Euler series. No partition formula or BPS equality is a premise. -/
theorem geometric_hilbert_eq (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    geometricHilbert data r k=partitionHilbertSeries r k := by
  apply qMap_injective
  have hn : HilbertAtZero.v^(-(2*(deg r k:ℤ)))*(1-HilbertAtZero.v^2)^r≠0 := by
    apply mul_ne_zero (zpow_ne_zero _ HilbertAtZero.v_ne_zero)
    apply pow_ne_zero
    intro he
    have hp : HilbertAtZero.v^(2:ℤ)=HilbertAtZero.v^(0:ℤ) := by
      simpa only [zpow_ofNat,pow_zero] using (sub_eq_zero.mp he).symm
    have hh := Paper20.Seminormal.hilbert_origin_parameter_injective hp
    omega
  apply mul_left_cancel₀ hn
  rw [geometric_quantum data geo r k hr hk,hilbert_evaluation]
  have hc := character_origin mathas r k hr
  rw [HilbertHeckeBridge.CharacterFormulaAt,
    HeckeTraceAlgebra.canonicalTrace_omega r k (by omega)] at hc
  rw [← hc]
  symm
  simpa only [mul_assoc] using
    (rationalHilbertSeries_quantum r k HilbertAtZero.v HilbertAtZero.v_ne_zero
      origin_difference_ne_zero)

/-- The original local BPS expansion for the supplied geometric Euler
series, with actual nonnegative walk coefficients. -/
theorem geometric_bps_expansion (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    (1-PowerSeries.X)^r*geometricHilbert data r k=
      rationalBPS (deg r k) (fun h => (Paper20.BraidWalk.walkCount r k h:ℤ)) := by
  rw [geometric_hilbert_eq data geo mathas r k hr hk]
  exact HilbertHeckeBridge.original_expansion_of_character r k (by omega)
    (character_origin mathas r k hr)

lemma geometricHilbert_map (data : GeometricData) (r k : ℕ) :
    geometricHilbert data r k=PowerSeries.map (Int.castRingHom ℚ)
      (Paper20.Semantics.hilbertSeries (data.euler r k)) := by
  ext ℓ
  simp only [geometricHilbert,Paper20.Semantics.hilbertSeries,
    PowerSeries.coeff_mk,PowerSeries.coeff_map]
  rfl

/-- The integer coefficient form of the ORIGINAL local BPS definition,
for the supplied Euler characteristics of the punctual Hilbert schemes. -/
theorem geometric_local_expansion (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    Paper20.Semantics.localBPSExpansion r (deg r k) (data.euler r k)
      (fun h => (Paper20.BraidWalk.walkCount r k h:ℤ)) := by
  apply (Paper20.Semantics.localBPSExpansion_iff_series ..).2
  apply PowerSeries.map_injective (Int.castRingHom ℚ) Int.cast_injective
  simpa only [map_mul,map_pow,map_sub,map_one,PowerSeries.map_X,
    ← geometricHilbert_map,HilbertSeriesProof.rationalBPS] using
      geometric_bps_expansion data geo mathas r k hr hk

/-- Canonical signed BPS extraction from the external GEOMETRIC Euler
data, using precisely the original genus expansion and its proved inverse. -/
def geometricBPS (data : GeometricData) (r k h : ℕ) : ℤ :=
  Paper20.Semantics.extracted (deg r k)
    (Paper20.Semantics.hilbertResidual r (data.euler r k)) h

theorem geometricBPS_eq_walk (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k h : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hh : h ≤ deg r k) :
    geometricBPS data r k h=(Paper20.BraidWalk.walkCount r k h:ℤ) :=
  (Paper20.Semantics.localBPSExpansion_eq_extracted
    (geometric_local_expansion data geo mathas r k hr hk) h hh).symm

/-- Semantic identification with the actual executable extraction. It is
derived from the original three external identities, not supplied as an input. -/
theorem geometricBPS_eq_program (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k h : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hh : h ≤ deg r k) : geometricBPS data r k h=(bpsCoeff r k h:ℤ) := by
  rw [geometricBPS_eq_walk data geo mathas r k h hr hk hh,
    Relative.bps_walk mathas r k h hr hh]

def geometricBPSPolynomial (data : GeometricData) (r k : ℕ) : ℤ[X] :=
  HilbertAtZero.bpsPolynomial (deg r k) (geometricBPS data r k)

theorem geometricBPSPolynomial_eq_walk (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    geometricBPSPolynomial data r k=walkBPSPolynomial r k := by
  unfold geometricBPSPolynomial HilbertAtZero.bpsPolynomial walkBPSPolynomial
  apply Finset.sum_congr rfl
  intro h hh
  rw [geometricBPS_eq_walk data geo mathas r k h hr hk
    (by have := Finset.mem_range.mp hh; omega),C_mul_X_pow_eq_monomial]

/-- Original Proposition 2.3 as a polynomial identity, after w=z²,
for the BPS polynomial obtained from the supplied geometric Euler data. -/
theorem geometric_trace (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    (geometricBPSPolynomial data r k).comp (X^2)=
      HeckeTraceAlgebra.canonicalTrace r (HeckeTraceAlgebra.omega r^(k+1)) := by
  rw [geometricBPSPolynomial_eq_walk data geo mathas r k hr hk,
    HeckeTraceAlgebra.canonicalTrace_omega_even_variable r k (by omega)]

/-- The normalized ruling identity (8), with the actual original BPS
polynomial and supplied geometric ruling value. -/
theorem geometric_normalized_ruling (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    (geometricBPSPolynomial data r k).eval₂ (Int.castRingHom SeriesField)
      ((HilbertAtZero.v-HilbertAtZero.v⁻¹)^2)=
        (HilbertAtZero.v-HilbertAtZero.v⁻¹)^r*data.ruling r k := by
  rw [geo.walk_ruling r k hr hk,← mul_assoc,
    ← zpow_natCast (HilbertAtZero.v-HilbertAtZero.v⁻¹) r,
    ← zpow_add₀ origin_difference_ne_zero,add_neg_cancel,zpow_zero,one_mul,
    closedHeckePolynomial_eq_comp,eval₂_comp,eval₂_pow,eval₂_X,
    geometricBPSPolynomial_eq_walk data geo mathas r k hr hk]

/-- Every coefficient retained by the actual Hilbert-array program is
the corresponding supplied punctual-Hilbert Euler characteristic. -/
theorem geometricEuler_array (data : GeometricData) (geo : GeometricInputs data)
    (mathas : MathasInputs) (r k ℓ : ℕ) (hr : 2 ≤ r) (hk : 1 ≤ k)
    (hℓ : ℓ ≤ deg r k) : data.euler r k ℓ=((hilbertArray r k).getD ℓ 0:ℤ) := by
  have he := congrArg (PowerSeries.coeff ℓ) (geometric_hilbert_eq data geo mathas r k hr hk)
  rw [← hilbertArray_coeff r k ℓ hℓ] at he
  simp only [geometricHilbert,PowerSeries.coeff_mk] at he
  exact_mod_cast he

end
end Paper20.ExternalInput
