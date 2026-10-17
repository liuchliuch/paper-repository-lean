import P31.NormTargets
import P31.NormComparison
import P31.Path
import P31.Terminal
import P31.PowerProx
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp

/-!
# Schatten geometry on actual rectangular real matrices

`SpectralInput` explicitly records the presently unavailable spectral-library
inputs: compact SVD, Schatten norm laws, the Clarkson--McCarthy midpoint
inequality [McCarthy 1967; Ball--Carlen--Lieb 1994], and the unnormalized
spectral derivative and its convex supporting inequality.  It does not
postulate the paper's normalized atom, its Jensen modulus, or any optimization
or query-complexity conclusion.  The normalization and the resulting bounds
below are proved from these inputs.
-/

noncomputable section
open scoped BigOperators
open scoped Matrix.Norms.Elementwise

namespace P31.Schatten

abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

def tracePair {m n : ℕ} (G X : Mat m n) : ℝ := ∑ i, ∑ j, G i j * X i j

def traceFunctional {m n : ℕ} (G : Mat m n) : Mat m n →L[ℝ] ℝ :=
  ∑ i, ∑ j, (G i j) •
    ((ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : Mat m n →L[ℝ] (Fin n → ℝ)))

@[simp] theorem traceFunctional_apply {m n : ℕ} (G X : Mat m n) :
    traceFunctional G X = tracePair G X := by
  simp [traceFunctional, tracePair, ContinuousLinearMap.proj_apply]
  rfl

/-- The pairing is the actual rectangular trace pairing in the manuscript. -/
theorem tracePair_eq_trace {m n : ℕ} (G X : Mat m n) :
    tracePair G X = Matrix.trace (G.transpose * X) := by
  simp only [tracePair, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_comm

def spectralNorm {m n : ℕ} (singular : Mat m n → Fin (min m n) → ℝ)
    (r : ℝ) (X : Mat m n) : ℝ := lpNorm r (singular X)

def rawAtom {m n : ℕ} (singular : Mat m n → Fin (min m n) → ℝ)
    (p : ℝ) (C X : Mat m n) : ℝ := (1 / p) * spectralNorm singular p (X - C) ^ p

/-- Exact external spectral facts, all on actual matrices.  The compact SVD
certificate pins `singular` to genuine nonnegative singular values, rather
than an unrelated norm oracle.  The last norm comparison only relates the
Schatten norm to the existing finite-dimensional matrix topology. -/
structure SpectralInput (m n : ℕ) where
  singular : Mat m n → Fin (min m n) → ℝ
  singular_nonneg : ∀ X i, 0 ≤ singular X i
  singular_sorted : ∀ X, Antitone (singular X)
  powerGradient : ℝ → Mat m n → Mat m n
  compact_svd : ∀ p, 2 ≤ p → ∀ X,
    ∃ U : Matrix (Fin m) (Fin (min m n)) ℝ,
    ∃ V : Matrix (Fin n) (Fin (min m n)) ℝ,
      U.transpose * U = 1 ∧ V.transpose * V = 1 ∧
      X = U * Matrix.diagonal (singular X) * V.transpose ∧
      powerGradient p X = U * Matrix.diagonal (fun i => singular X i ^ (p - 1)) * V.transpose
  norm_zero : ∀ r, 0 < r → spectralNorm singular r 0 = 0
  norm_eq_zero : ∀ r, 1 ≤ r → ∀ X, spectralNorm singular r X = 0 ↔ X = 0
  norm_smul : ∀ r, 1 ≤ r → ∀ a X,
    spectralNorm singular r (a • X) = |a| * spectralNorm singular r X
  norm_triangle : ∀ r, 1 ≤ r → ∀ X Y,
    spectralNorm singular r (X + Y) ≤ spectralNorm singular r X + spectralNorm singular r Y
  norm_continuous : ∀ r, 1 ≤ r → Continuous (spectralNorm singular r)
  midpoint : ∀ p, 2 ≤ p → ∀ C X Y,
    rawAtom singular p C ((1 / 2 : ℝ) • (X + Y)) +
        (1 / p) * spectralNorm singular p ((1 / 2 : ℝ) • (X - Y)) ^ p ≤
      (rawAtom singular p C X + rawAtom singular p C Y) / 2
  raw_support : ∀ p, 2 ≤ p → ∀ C X Y,
    rawAtom singular p C X + tracePair (powerGradient p (X - C)) (Y - X) ≤
      rawAtom singular p C Y
  raw_derivative : ∀ p, 2 ≤ p → ∀ C X,
    HasFDerivAt (rawAtom singular p C) (traceFunctional (powerGradient p (X - C))) X
  gradient_norm : ∀ p, 2 ≤ p → ∀ X,
    spectralNorm singular (dualExponent p) (powerGradient p X) =
      spectralNorm singular p X ^ (p - 1)
  trace_holder : ∀ p, 1 < p → ∀ G X,
    |tracePair G X| ≤ spectralNorm singular (dualExponent p) G * spectralNorm singular p X
  norm_comparison : ∀ p, 1 ≤ p → ∃ K : ℝ, 0 < K ∧
    ∀ X, ‖X‖ ≤ K * spectralNorm singular p X

namespace SpectralInput

variable {m n : ℕ} (S : SpectralInput m n)

abbrev snorm (r : ℝ) (X : Mat m n) : ℝ := spectralNorm S.singular r X
abbrev psi (p : ℝ) (C X : Mat m n) : ℝ := rawAtom S.singular p C X

lemma snorm_nonneg (r : ℝ) (X : Mat m n) : 0 ≤ S.snorm r X := lpNorm_nonneg _ _

lemma snorm_smul {p : ℝ} (hp : 1 ≤ p) (a : ℝ) (X : Mat m n) :
    S.snorm p (a • X) = |a| * S.snorm p X := S.norm_smul p hp a X

lemma snorm_neg {p : ℝ} (hp : 1 ≤ p) (X : Mat m n) : S.snorm p (-X) = S.snorm p X := by
  simpa using S.norm_smul p hp (-1) X

lemma snorm_sub_rev {p : ℝ} (hp : 1 ≤ p) (X Y : Mat m n) :
    S.snorm p (X - Y) = S.snorm p (Y - X) := by
  rw [← neg_sub X Y, S.snorm_neg hp]

def atomScale (p : ℝ) : ℝ := (2 : ℝ) ^ (2 * p - 3)
def atom (p : ℝ) (C X : Mat m n) : ℝ := atomScale p * S.psi p C X
def atomGradient (p : ℝ) (C X : Mat m n) : Mat m n :=
  atomScale p • S.powerGradient p (X - C)

lemma atomScale_pos (p : ℝ) : 0 < atomScale p := Real.rpow_pos_of_pos (by norm_num) _

/-- Equation (5.5), derived from precisely the midpoint and support inputs. -/
theorem raw_bregman_lower {p : ℝ} (hp : 2 ≤ p) (C X Y : Mat m n) :
    (2 : ℝ) ^ (1 - p) / p * S.snorm p (Y - X) ^ p ≤
      S.psi p C Y - S.psi p C X - tracePair (S.powerGradient p (X - C)) (Y - X) := by
  have hp1 : 1 ≤ p := by linarith
  have hMid := S.midpoint p hp C X Y
  have hSupport := S.raw_support p hp C X ((1 / 2 : ℝ) • (X + Y))
  have hlin : tracePair (S.powerGradient p (X - C))
      ((1 / 2 : ℝ) • (X + Y) - X) =
        (1 / 2 : ℝ) * tracePair (S.powerGradient p (X - C)) (Y - X) := by
    have hm : (1 / 2 : ℝ) • (X + Y) - X = (1 / 2 : ℝ) • (Y - X) := by module
    rw [hm, ← traceFunctional_apply, map_smul, traceFunctional_apply]
    rfl
  rw [hlin] at hSupport
  have hNorm : S.snorm p ((1 / 2 : ℝ) • (X - Y)) ^ p =
      (2 : ℝ) ^ (-p) * S.snorm p (Y - X) ^ p := by
    rw [S.snorm_smul hp1, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      Real.mul_rpow (by norm_num) (S.snorm_nonneg _ _), S.snorm_sub_rev hp1]
    congr 1
    rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  change S.psi p C ((1 / 2 : ℝ) • (X + Y)) +
    (1 / p) * S.snorm p ((1 / 2 : ℝ) • (X - Y)) ^ p ≤ _ at hMid
  rw [hNorm] at hMid
  have hCoeff : (2 : ℝ) ^ (1 - p) / p = 2 * ((1 / p) * (2 : ℝ) ^ (-p)) := by
    rw [show 1 - p = 1 + (-p) by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
    ring
  rw [hCoeff]
  linarith

/-- The scalar theta lower bound used to pass from Bregman growth to the
paper's Jensen convention. -/
theorem theta_power_lower {p θ : ℝ} (hp : 2 ≤ p) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (2 : ℝ) ^ (2 - p) ≤ θ ^ (p - 1) + (1 - θ) ^ (p - 1) := by
  have hcv : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ (p - 1)) :=
    convexOn_rpow (by linarith)
  have hc : ((1 / 2 : ℝ) • θ + (1 / 2 : ℝ) • (1 - θ)) ^ (p - 1) ≤
      (1 / 2 : ℝ) * θ ^ (p - 1) + (1 / 2 : ℝ) * (1 - θ) ^ (p - 1) :=
    hcv.2 hθ0 (sub_nonneg.mpr hθ1) (by norm_num) (by norm_num) (by norm_num)
  have hhalf : (1 / 2 : ℝ) ^ (p - 1) = (2 : ℝ) ^ (1 - p) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) by norm_num,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hmid : (1 / 2 : ℝ) • θ + (1 / 2 : ℝ) • (1 - θ) = (1 / 2 : ℝ) := by
    simp only [smul_eq_mul]
    ring
  rw [hmid, hhalf] at hc
  have htwo : (2 : ℝ) ^ (2 - p) = 2 * (2 : ℝ) ^ (1 - p) := by
    rw [show 2 - p = 1 + (1 - p) by ring, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  rw [htwo]
  simpa only [smul_eq_mul] using (by linarith : 2 * (2 : ℝ) ^ (1 - p) ≤ θ ^ (p - 1) + (1 - θ) ^ (p - 1))

def Jensen (p μ : ℝ) (F : Mat m n → ℝ) : Prop :=
  ∀ X Y (θ : ℝ), 0 ≤ θ → θ ≤ 1 →
    F ((1 - θ) • X + θ • Y) ≤ (1 - θ) * F X + θ * F Y -
      μ / p * θ * (1 - θ) * S.snorm p (X - Y) ^ p

/-- The exact normalized Jensen modulus asserted in Section 5.3. -/
theorem atom_jensen {p : ℝ} (hp : 2 ≤ p) (C : Mat m n) :
    S.Jensen p 1 (S.atom p C) := by
  intro X Y θ hθ0 hθ1
  let Z := (1 - θ) • X + θ • Y
  let G := S.powerGradient p (Z - C)
  let d := S.snorm p (X - Y) ^ p
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hX := S.raw_bregman_lower hp C Z X
  have hY := S.raw_bregman_lower hp C Z Y
  have hXZ : X - Z = θ • (X - Y) := by dsimp [Z]; module
  have hYZ : Y - Z = (1 - θ) • (Y - X) := by dsimp [Z]; module
  have hNormX : S.snorm p (X - Z) ^ p = θ ^ p * d := by
    rw [hXZ, S.snorm_smul hp1, abs_of_nonneg hθ0,
      Real.mul_rpow hθ0 (S.snorm_nonneg _ _)]
  have hNormY : S.snorm p (Y - Z) ^ p = (1 - θ) ^ p * d := by
    rw [hYZ, S.snorm_smul hp1, abs_of_nonneg (sub_nonneg.mpr hθ1),
      Real.mul_rpow (sub_nonneg.mpr hθ1) (S.snorm_nonneg _ _), S.snorm_sub_rev hp1 Y X]
  rw [hNormX] at hX
  rw [hNormY] at hY
  have hCancel : (1 - θ) * tracePair G (X - Z) + θ * tracePair G (Y - Z) = 0 := by
    rw [← traceFunctional_apply, ← traceFunctional_apply]
    change (1 - θ) • traceFunctional G (X - Z) + θ • traceFunctional G (Y - Z) = 0
    rw [← map_smul, ← map_smul, ← map_add]
    have he : (1 - θ) • (X - Z) + θ • (Y - Z) = 0 := by dsimp [Z]; module
    rw [he, map_zero]
  have hWeighted := add_le_add (mul_le_mul_of_nonneg_left hX (sub_nonneg.mpr hθ1))
    (mul_le_mul_of_nonneg_left hY hθ0)
  change (1 - θ) * _ + θ * _ ≤ _ at hWeighted
  have hpowθ : θ ^ p = θ * θ ^ (p - 1) := by
    calc
      θ ^ p = θ ^ (1 + (p - 1)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add' hθ0 (by linarith : 1 + (p - 1) ≠ 0), Real.rpow_one]
  have hpowθ' : (1 - θ) ^ p = (1 - θ) * (1 - θ) ^ (p - 1) := by
    calc
      (1 - θ) ^ p = (1 - θ) ^ (1 + (p - 1)) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add' (sub_nonneg.mpr hθ1) (by linarith : 1 + (p - 1) ≠ 0), Real.rpow_one]
  have hBase : (2 : ℝ) ^ (1 - p) / p * θ * (1 - θ) *
      (θ ^ (p - 1) + (1 - θ) ^ (p - 1)) * d ≤
      (1 - θ) * S.psi p C X + θ * S.psi p C Y - S.psi p C Z := by
    rw [hpowθ, hpowθ'] at hWeighted
    dsimp [G] at hCancel
    nlinarith [hCancel]
  have hd : 0 ≤ d := Real.rpow_nonneg (S.snorm_nonneg _ _) _
  have hCoeff : 0 ≤ (2 : ℝ) ^ (1 - p) / p * θ * (1 - θ) * d :=
    mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg
      (Real.rpow_nonneg (by norm_num) _) hp0.le) hθ0) (sub_nonneg.mpr hθ1)) hd
  have hTheta := mul_le_mul_of_nonneg_left (theta_power_lower hp hθ0 hθ1) hCoeff
  have hSmall : (2 : ℝ) ^ (3 - 2 * p) / p * θ * (1 - θ) * d ≤
      (1 - θ) * S.psi p C X + θ * S.psi p C Y - S.psi p C Z := by
    have hmul : (2 : ℝ) ^ (1 - p) * (2 : ℝ) ^ (2 - p) = (2 : ℝ) ^ (3 - 2 * p) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    calc
      _ = ((2 : ℝ) ^ (1 - p) / p * θ * (1 - θ) * d) * (2 : ℝ) ^ (2 - p) := by rw [← hmul]; ring
      _ ≤ ((2 : ℝ) ^ (1 - p) / p * θ * (1 - θ) * d) *
          (θ ^ (p - 1) + (1 - θ) ^ (p - 1)) := hTheta
      _ = _ := by ring
      _ ≤ _ := hBase
  have hScale := mul_le_mul_of_nonneg_left hSmall (atomScale_pos p).le
  have hUnit : atomScale p * (2 : ℝ) ^ (3 - 2 * p) = 1 := by
    unfold atomScale
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp
  change S.atom p C Z ≤ _
  dsimp [atom]
  have hNormalize : atomScale p * ((2 : ℝ) ^ (3 - 2 * p) / p * θ * (1 - θ) * d) =
      1 / p * θ * (1 - θ) * d := by
    calc
      _ = (atomScale p * (2 : ℝ) ^ (3 - 2 * p)) / p * θ * (1 - θ) * d := by ring
      _ = _ := by rw [hUnit]
  rw [hNormalize] at hScale
  nlinarith

lemma atom_eq_radial (p : ℝ) (C X : Mat m n) :
    S.atom p C X = atomScale p / p * S.snorm p (X - C) ^ p := by
  unfold atom psi rawAtom
  ring

lemma atom_nonneg {p : ℝ} (hp : 0 < p) (C X : Mat m n) : 0 ≤ S.atom p C X := by
  rw [S.atom_eq_radial]
  exact mul_nonneg (div_nonneg (atomScale_pos p).le hp.le)
    (Real.rpow_nonneg (S.snorm_nonneg _ _) _)

/-- Radial sublevels, the hypothesis actually used by minimizer transport. -/
theorem atom_sublevel_iff {p : ℝ} (hp : 0 < p) (C X Y : Mat m n) :
    S.atom p C X ≤ S.atom p C Y ↔ S.snorm p (X - C) ≤ S.snorm p (Y - C) := by
  rw [S.atom_eq_radial, S.atom_eq_radial]
  exact (mul_le_mul_iff_right₀ (div_pos (atomScale_pos p) hp)).trans
    (Real.rpow_le_rpow_iff (S.snorm_nonneg _ _) (S.snorm_nonneg _ _) hp)

/-- The two prox inequalities in Section 5.3. -/
theorem atom_prox_bounds {p : ℝ} (hp : 2 ≤ p) (C X : Mat m n) :
    (1 / p) * S.snorm p (X - C) ^ p ≤ S.atom p C X ∧
      S.atom p C X ≤ atomScale p / p * S.snorm p (X - C) ^ p := by
  rw [S.atom_eq_radial]
  have hscale : 1 ≤ atomScale p := Real.one_le_rpow (by norm_num) (by linarith)
  have hp0 : 0 < p := by linarith
  constructor
  · apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (S.snorm_nonneg _ _) _)
    exact div_le_div_of_nonneg_right hscale hp0.le
  · exact le_rfl

lemma traceFunctional_smul (a : ℝ) (G : Mat m n) :
    traceFunctional (a • G) = a • traceFunctional G := by
  ext X
  simp [tracePair, Finset.mul_sum, mul_assoc]

theorem atom_hasFDerivAt {p : ℝ} (hp : 2 ≤ p) (C X : Mat m n) :
    HasFDerivAt (S.atom p C) (traceFunctional (S.atomGradient p C X)) X := by
  rw [atomGradient, traceFunctional_smul]
  exact (S.raw_derivative p hp C X).const_mul (atomScale p)

/-- Equation (5.6), with the exact normalized gradient and genuine singular
value dual norm, including matrices with repeated or zero singular values. -/
theorem atom_gradient_norm {p : ℝ} (hp : 2 ≤ p) (C X : Mat m n) :
    S.snorm (dualExponent p) (S.atomGradient p C X) =
      atomScale p * S.snorm p (X - C) ^ (p - 1) := by
  have hq : 1 ≤ dualExponent p := by
    unfold dualExponent
    apply (le_div_iff₀ (by linarith : 0 < p - 1)).2
    linarith
  rw [atomGradient, S.snorm_smul hq, abs_of_pos (atomScale_pos p)]
  exact congrArg (fun z => atomScale p * z) (S.gradient_norm p hp (X - C))

theorem atom_continuous {p : ℝ} (hp : 2 ≤ p) (C : Mat m n) : Continuous (S.atom p C) := by
  unfold atom psi rawAtom
  apply continuous_const.mul
  apply continuous_const.mul
  exact (Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp
    ((S.norm_continuous p (by linarith)).comp (continuous_id.sub continuous_const))

/-- Remark 5.3, the dimension-free conversion to every weaker Schatten norm,
proved on the actual singular values rather than assumed spectrally. -/
theorem target_norm_mono {q s : ℝ} (hq : 0 < q) (hqs : q ≤ s) (G : Mat m n) :
    S.snorm s G ≤ S.snorm q G :=
  lpNorm_antitone_exponent hq hqs (S.singular G)

theorem weaker_target_certificate {q s ε : ℝ} (hq : 0 < q) (hqs : q ≤ s)
    (G : Mat m n) (hG : S.snorm q G ≤ ε) : S.snorm s G ≤ ε :=
  (S.target_norm_mono hq hqs G).trans hG

/-- The dimensional conversion in Remark 5.3 is the finite-vector inequality
applied to the genuine singular-value list. -/
theorem stronger_target_norm {q s : ℝ} (hs : 0 < s) (hsq : s ≤ q) (G : Mat m n) :
    S.snorm s G ≤ ((min m n : ℕ) : ℝ) ^ (1 / s - 1 / q) * S.snorm q G := by
  simpa only [Fintype.card_fin] using lpNorm_dimension_comparison hs hsq (S.singular G)

theorem stronger_target_certificate {q s ε : ℝ} (hs : 0 < s) (hsq : s ≤ q)
    (hk : 0 < min m n) (G : Mat m n)
    (hG : S.snorm q G ≤ ε / ((min m n : ℕ) : ℝ) ^ (1 / s - 1 / q)) :
    S.snorm s G ≤ ε := by
  have hd : 0 < ((min m n : ℕ) : ℝ) ^ (1 / s - 1 / q) :=
    Real.rpow_pos_of_pos (Nat.cast_pos.mpr hk) _
  calc
    S.snorm s G ≤ ((min m n : ℕ) : ℝ) ^ (1 / s - 1 / q) * S.snorm q G := S.stronger_target_norm hs hsq G
    _ ≤ ((min m n : ℕ) : ℝ) ^ (1 / s - 1 / q) *
        (ε / ((min m n : ℕ) : ℝ) ^ (1 / s - 1 / q)) := mul_le_mul_of_nonneg_left hG hd.le
    _ = ε := mul_div_cancel₀ _ hd.ne'

/-- The norm laws in the spectral input install the genuine Schatten norm
on the actual matrix additive group when a generic normed theorem is used.
This is a local construction, not a replacement of the default topology. -/
def schattenCore (p : ℝ) (hp : 1 ≤ p) :
    letI : Norm (Mat m n) := ⟨S.snorm p⟩
    NormedSpace.Core ℝ (Mat m n) := by
  letI : Norm (Mat m n) := ⟨S.snorm p⟩
  exact {
    norm_nonneg := S.snorm_nonneg p
    norm_smul := fun a X => by simpa only [Real.norm_eq_abs] using S.snorm_smul hp a X
    norm_triangle := S.norm_triangle p hp
    norm_eq_zero_iff := S.norm_eq_zero p hp }

def schattenGroup (p : ℝ) (hp : 1 ≤ p) : NormedAddCommGroup (Mat m n) :=
  letI : Norm (Mat m n) := ⟨S.snorm p⟩
  NormedAddCommGroup.ofCore (S.schattenCore p hp)

def schattenSpace (p : ℝ) (hp : 1 ≤ p) :
    letI : SeminormedAddCommGroup (Mat m n) := (S.schattenGroup p hp).toSeminormedAddCommGroup
    NormedSpace ℝ (Mat m n) := by
  letI : SeminormedAddCommGroup (Mat m n) := (S.schattenGroup p hp).toSeminormedAddCommGroup
  exact NormedSpace.ofCore (S.schattenCore p hp)

theorem path_bound {p : ℝ} (hp : 1 ≤ p)
    (x exactMin : ℕ → Mat m n) (R : ℝ) (N : ℕ) (hR : 0 ≤ R)
    (hTransport : ∀ s, 1 ≤ s → s ≤ N →
      S.snorm p (exactMin s - x (s - 1)) ≤ R / 2 ^ (s - 1))
    (hContract : ∀ s, 1 ≤ s → s ≤ N →
      S.snorm p (x s - exactMin s) ≤ R / 2 ^ s)
    (i : ℕ) (hi : 1 ≤ i) (hiN : i ≤ N) :
    S.snorm p (exactMin N - x (i - 1)) ≤ 3 * (R / 2 ^ (i - 1)) := by
  letI : SeminormedAddCommGroup (Mat m n) := (S.schattenGroup p hp).toSeminormedAddCommGroup
  exact P31.geometric_path_bound_two x exactMin R N hR hTransport hContract i hi hiN

theorem minimizer_transport {p α : ℝ} (hp : 0 < p) (hα : 0 < α)
    (F : Mat m n → ℝ) (center oldMin newMin : Mat m n)
    (hold : ∀ Y, F oldMin ≤ F Y)
    (hnew : ∀ Y, F newMin + α * S.atom p center newMin ≤ F Y + α * S.atom p center Y) :
    S.snorm p (newMin - center) ≤ S.snorm p (oldMin - center) := by
  have h₁ := hold newMin
  have h₂ := hnew oldMin
  have ha : S.atom p center newMin ≤ S.atom p center oldMin := by nlinarith
  exact (S.atom_sublevel_iff hp center newMin oldMin).mp ha

/-- Growth at a genuine minimizer is derived from Jensen uniform convexity. -/
theorem jensen_min_growth {p μ : ℝ} (hp : 1 ≤ p) {F : Mat m n → ℝ}
    (hJ : S.Jensen p μ F) {z : Mat m n} (hz : ∀ X, F z ≤ F X) (Y : Mat m n) :
    μ / p * S.snorm p (Y - z) ^ p ≤ F Y - F z := by
  let K := μ / p * S.snorm p (Y - z) ^ p
  let gap := F Y - F z
  change K ≤ gap
  have hgap : 0 ≤ gap := sub_nonneg.mpr (hz Y)
  by_cases hK : K ≤ 0
  · exact hK.trans hgap
  have hKpos : 0 < K := lt_of_not_ge hK
  by_contra hfail
  have hsmall : gap < K := lt_of_not_ge hfail
  let θ := (K - gap) / (2 * K)
  have hden : 0 < 2 * K := mul_pos (by norm_num) hKpos
  have hθpos : 0 < θ := div_pos (sub_pos.mpr hsmall) hden
  have hθlt : θ < 1 := (div_lt_one hden).mpr (by linarith)
  have hθeq : (2 * K) * θ = K - gap := by
    dsimp [θ]
    exact mul_div_cancel₀ _ (ne_of_gt hden)
  have hprod : 0 < θ * (K * (1 - θ) - gap) := by nlinarith
  have hj := hJ z Y θ hθpos.le hθlt.le
  rw [S.snorm_sub_rev hp z Y] at hj
  have hm := hz ((1 - θ) • z + θ • Y)
  dsimp [K, gap] at hprod
  nlinarith

theorem jensen_stage_contraction {p μ δ : ℝ} (hp : 1 ≤ p) (hμ : 0 < μ) (hδ : 0 ≤ δ)
    {F : Mat m n → ℝ} (hJ : S.Jensen p μ F) {z : Mat m n}
    (hz : ∀ X, F z ≤ F X) (Y : Mat m n)
    (hgap : F Y - F z ≤ μ / p * δ ^ p) : S.snorm p (Y - z) ≤ δ := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpower := (mul_le_mul_iff_right₀ (div_pos hμ hp0)).mp
    ((S.jensen_min_growth hp hJ hz Y).trans hgap)
  exact (Real.rpow_le_rpow_iff (S.snorm_nonneg _ _) hδ hp0).mp hpower

theorem jensen_weighted_sum {ι : Type*} (s : Finset ι) (p : ℝ)
    (F : ι → Mat m n → ℝ) (μ w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hJ : ∀ i ∈ s, S.Jensen p (μ i) (F i)) :
    S.Jensen p (∑ i ∈ s, w i * μ i) (fun X => ∑ i ∈ s, w i * F i X) := by
  intro X Y θ hθ0 hθ1
  have hs := Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_left (hJ i hi X Y θ hθ0 hθ1) (hw i hi)
  convert hs using 1
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_div,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem jensen_add_convex {p μ : ℝ} {f H : Mat m n → ℝ}
    (hf : ConvexOn ℝ Set.univ f) (hH : S.Jensen p μ H) :
    S.Jensen p μ (fun X => f X + H X) := by
  intro X Y θ hθ0 hθ1
  have hc := hf.2 (Set.mem_univ X) (Set.mem_univ Y)
    (sub_nonneg.mpr hθ1) hθ0 (show (1 - θ) + θ = 1 by ring)
  have hh := hH X Y θ hθ0 hθ1
  simp only [smul_eq_mul] at hc
  dsimp only
  linarith

lemma traceFunctional_injective : Function.Injective (@traceFunctional m n) := by
  intro G H h
  ext i j
  have hh := congrArg (fun l : Mat m n →L[ℝ] ℝ => l (Matrix.single i j 1)) h
  simpa [tracePair, Matrix.single, ite_and] using hh

lemma traceFunctional_neg (G : Mat m n) : traceFunctional (-G) = -traceFunctional G := by
  ext X
  simp [tracePair, Finset.sum_neg_distrib]

lemma traceFunctional_sum {ι : Type*} (s : Finset ι) (G : ι → Mat m n) :
    traceFunctional (∑ i ∈ s, G i) = ∑ i ∈ s, traceFunctional (G i) := by
  ext X
  simp only [traceFunctional_apply, ContinuousLinearMap.sum_apply, tracePair, Matrix.sum_apply,
    Finset.sum_mul]
  calc
    (∑ i, ∑ j, ∑ k ∈ s, G k i j * X i j) =
        ∑ i, ∑ k ∈ s, ∑ j, G k i j * X i j := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem accumulated_stationarity {ι : Type*} {p : ℝ} (hp : 2 ≤ p)
    (s : Finset ι) (f : Mat m n → ℝ) (α : ι → ℝ) (C : ι → Mat m n)
    (z grad : Mat m n) (hf : HasFDerivAt f (traceFunctional grad) z)
    (hmin : ∀ Y, f z + ∑ i ∈ s, α i * S.atom p (C i) z ≤
      f Y + ∑ i ∈ s, α i * S.atom p (C i) Y) :
    grad = -(∑ i ∈ s, α i • S.atomGradient p (C i) z) := by
  apply traceFunctional_injective
  rw [traceFunctional_neg, traceFunctional_sum]
  simp_rw [traceFunctional_smul]
  exact P31.accumulated_stationarity s f (fun i => S.atom p (C i)) α z
    (traceFunctional grad) (fun i => traceFunctional (S.atomGradient p (C i) z))
    hf (fun i _ => S.atom_hasFDerivAt hp (C i) z) hmin

lemma snorm_sum_le {ι : Type*} {p : ℝ} (hp : 1 ≤ p) (s : Finset ι) (X : ι → Mat m n) :
    S.snorm p (∑ i ∈ s, X i) ≤ ∑ i ∈ s, S.snorm p (X i) := by
  letI : SeminormedAddCommGroup (Mat m n) := (S.schattenGroup p hp).toSeminormedAddCommGroup
  exact norm_sum_le s X

theorem accumulated_gradient_bound {ι : Type*} {p : ℝ} (hp : 2 ≤ p)
    (s : Finset ι) (f : Mat m n → ℝ) (α : ι → ℝ) (C : ι → Mat m n)
    (z grad : Mat m n) (hf : HasFDerivAt f (traceFunctional grad) z)
    (hα : ∀ i ∈ s, 0 ≤ α i)
    (hmin : ∀ Y, f z + ∑ i ∈ s, α i * S.atom p (C i) z ≤
      f Y + ∑ i ∈ s, α i * S.atom p (C i) Y) :
    S.snorm (dualExponent p) grad ≤
      atomScale p * ∑ i ∈ s, α i * S.snorm p (z - C i) ^ (p - 1) := by
  have hq : 1 ≤ dualExponent p := by
    unfold dualExponent
    apply (le_div_iff₀ (by linarith : 0 < p - 1)).2
    linarith
  rw [S.accumulated_stationarity hp s f α C z grad hf hmin, S.snorm_neg hq]
  calc
    _ ≤ ∑ i ∈ s, S.snorm (dualExponent p) (α i • S.atomGradient p (C i) z) :=
      S.snorm_sum_le hq s _
    _ = atomScale p * ∑ i ∈ s, α i * S.snorm p (z - C i) ^ (p - 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [S.snorm_smul hq, abs_of_nonneg (hα i hi), S.atom_gradient_norm hp]
      ring

theorem holder_terminal_transfer {p t L δ ε : ℝ} (hp : 2 ≤ p)
    (grad : Mat m n → Mat m n) (X Z : Mat m n)
    (hL : 0 ≤ L) (ht : 0 ≤ t)
    (hh : ∀ U V, S.snorm (dualExponent p) (grad U - grad V) ≤
      L * S.snorm p (U - V) ^ t)
    (hd : S.snorm p (X - Z) ≤ δ) (hbias : S.snorm (dualExponent p) (grad Z) ≤ ε / 2)
    (hscale : L * δ ^ t ≤ ε / 2) : S.snorm (dualExponent p) (grad X) ≤ ε := by
  have hq : 1 ≤ dualExponent p := by
    unfold dualExponent
    apply (le_div_iff₀ (by linarith : 0 < p - 1)).2
    linarith
  have htransfer : S.snorm (dualExponent p) (grad X - grad Z) ≤ ε / 2 :=
    (hh X Z).trans ((mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (S.snorm_nonneg _ _) hd ht) hL).trans hscale)
  have htriangle := S.norm_triangle (dualExponent p) hq (grad X - grad Z) (grad Z)
  rw [sub_add_cancel] at htriangle
  linarith

def objective (p : ℝ) (f : Mat m n → ℝ) (α : ℕ → ℝ) (x : ℕ → Mat m n)
    (s : ℕ) (Y : Mat m n) : ℝ := f Y + ∑ k ∈ Finset.range s, α (k + 1) * S.atom p (x k) Y

def modulus (α : ℕ → ℝ) (s : ℕ) : ℝ := ∑ k ∈ Finset.range s, α (k + 1)

lemma objective_succ (p : ℝ) (f : Mat m n → ℝ) (α : ℕ → ℝ) (x : ℕ → Mat m n)
    (s : ℕ) (Y : Mat m n) :
    S.objective p f α x (s + 1) Y = S.objective p f α x s Y + α (s + 1) * S.atom p (x s) Y := by
  simp only [objective, Finset.sum_range_succ]
  ring

theorem objective_jensen {p : ℝ} (hp : 2 ≤ p) (f : Mat m n → ℝ)
    (α : ℕ → ℝ) (x : ℕ → Mat m n) (s : ℕ)
    (hf : ConvexOn ℝ Set.univ f) (hα : ∀ k < s, 0 ≤ α (k + 1)) :
    S.Jensen p (modulus α s) (S.objective p f α x s) := by
  apply S.jensen_add_convex hf
  simpa only [mul_one] using S.jensen_weighted_sum (Finset.range s) p
    (fun k => S.atom p (x k)) (fun _ => 1) (fun k => α (k + 1))
    (fun k hk => hα k (Finset.mem_range.mp hk)) (fun k _ => S.atom_jensen hp (x k))

lemma modulus_pos {α : ℕ → ℝ} {s : ℕ} (hs : 1 ≤ s)
    (hα : ∀ k, 1 ≤ k → k ≤ s → 0 < α k) : 0 < modulus α s := by
  have hfirst : α 1 ≤ modulus α s :=
    Finset.single_le_sum (fun k hk => (hα (k + 1) (by omega) (by simpa using Finset.mem_range.mp hk)).le)
      (show 0 ∈ Finset.range s by simp; omega)
  exact (hα 1 le_rfl hs).trans_le hfirst

/-- The matrix version of Lemma 4.1 for the actual accumulated objectives.
The stage gap is only required after its warm-start condition has been
established, so the proof follows the algorithm's induction without assuming
validity of all solver calls in advance. -/
theorem stagewise_transport_contraction {p : ℝ} (hp : 2 ≤ p)
    (f : Mat m n → ℝ) (α δ : ℕ → ℝ) (x z : ℕ → Mat m n) (N : ℕ)
    (hf : ConvexOn ℝ Set.univ f)
    (hα : ∀ s, 1 ≤ s → s ≤ N → 0 < α s)
    (hδ : ∀ s, s ≤ N → 0 ≤ δ s)
    (hInitial : S.snorm p (x 0 - z 0) ≤ δ 0)
    (hMin : ∀ s, s ≤ N → ∀ Y, S.objective p f α x s (z s) ≤ S.objective p f α x s Y)
    (hGap : ∀ s, 1 ≤ s → s ≤ N →
      S.snorm p (z s - x (s - 1)) ≤ δ (s - 1) →
      S.objective p f α x s (x s) - S.objective p f α x s (z s) ≤ modulus α s / p * δ s ^ p) :
    ∀ s, 1 ≤ s → s ≤ N →
      S.snorm p (z s - x (s - 1)) ≤ δ (s - 1) ∧ S.snorm p (x s - z s) ≤ δ s := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hTransport (s : ℕ) (hs : 1 ≤ s) (hsN : s ≤ N) :
      S.snorm p (z s - x (s - 1)) ≤ S.snorm p (z (s - 1) - x (s - 1)) := by
    apply S.minimizer_transport hp0 (hα s hs hsN) (S.objective p f α x (s - 1))
      (x (s - 1)) (z (s - 1)) (z s) (hMin (s - 1) (by omega))
    intro Y
    have h := hMin s hsN Y
    have hind : s - 1 + 1 = s := by omega
    rw [← hind, S.objective_succ, S.objective_succ] at h
    simpa only [hind] using h
  have hComputed : ∀ s, s ≤ N → S.snorm p (x s - z s) ≤ δ s := by
    intro s
    induction s with
    | zero => intro _; exact hInitial
    | succ s ih =>
      intro hsN
      have hprev := ih (by omega)
      have hT : S.snorm p (z (s + 1) - x s) ≤ δ s := by
        have ht := hTransport (s + 1) (by omega) hsN
        simp only [Nat.add_sub_cancel] at ht
        exact ht.trans (by simpa only [S.snorm_sub_rev hp1] using hprev)
      apply S.jensen_stage_contraction hp1 (modulus_pos (by omega)
        (fun k hk hk' => hα k hk (by omega))) (hδ _ hsN)
        (S.objective_jensen hp f α x (s + 1) hf
          (fun k hk => (hα (k + 1) (by omega) (by omega)).le)) (hMin _ hsN)
      exact hGap (s + 1) (by omega) hsN (by simpa using hT)
  intro s hs hsN
  constructor
  · exact (hTransport s hs hsN).trans (by simpa only [S.snorm_sub_rev hp1] using hComputed (s - 1) (by omega))
  · exact hComputed s hsN

/-- The complete matrix accuracy step of Corollary 1.4.  The premises are
true stage minimizers and objective-only CC gap certificates, with the actual
source accumulated spectral atoms.  Transport, contraction, historical path,
stationarity and Hölder transfer are all derived here.  Scalar schedule
calibration is isolated in `hBiasBudget` and `hTerminalScale`. -/
theorem outer_accuracy {p t L R ε : ℝ} (hp : 2 ≤ p)
    (f : Mat m n → ℝ) (grad : Mat m n → Mat m n)
    (α : ℕ → ℝ) (x z : ℕ → Mat m n) (N : ℕ) (hN : 1 ≤ N)
    (hR : 0 ≤ R) (hL : 0 ≤ L) (ht : 0 ≤ t)
    (hf : ConvexOn ℝ Set.univ f)
    (hDerivative : ∀ X, HasFDerivAt f (traceFunctional (grad X)) X)
    (hHolder : ∀ X Y, S.snorm (dualExponent p) (grad X - grad Y) ≤ L * S.snorm p (X - Y) ^ t)
    (hα : ∀ s, 1 ≤ s → s ≤ N → 0 < α s)
    (hInitial : S.snorm p (x 0 - z 0) ≤ R)
    (hMin : ∀ s, s ≤ N → ∀ Y, S.objective p f α x s (z s) ≤ S.objective p f α x s Y)
    (hGap : ∀ s, 1 ≤ s → s ≤ N → S.snorm p (z s - x (s - 1)) ≤ R / 2 ^ (s - 1) →
      S.objective p f α x s (x s) - S.objective p f α x s (z s) ≤
        modulus α s / p * (R / 2 ^ s) ^ p)
    (hBiasBudget : atomScale p * ∑ k ∈ Finset.range N,
      α (k + 1) * (3 * (R / 2 ^ k)) ^ (p - 1) ≤ ε / 2)
    (hTerminalScale : L * (R / 2 ^ N) ^ t ≤ ε / 2) :
    S.snorm (dualExponent p) (grad (x N)) ≤ ε := by
  have hp1 : 1 ≤ p := by linarith
  have hStages := S.stagewise_transport_contraction hp f α (fun s => R / 2 ^ s) x z N hf hα
    (fun s _ => div_nonneg hR (pow_nonneg (by norm_num) _))
    (by simpa using hInitial) hMin hGap
  have hPath (k : ℕ) (hk : k < N) : S.snorm p (z N - x k) ≤ 3 * (R / 2 ^ k) := by
    simpa only [Nat.add_sub_cancel] using S.path_bound hp1 x z R N hR
      (fun s hs hsN => (hStages s hs hsN).1) (fun s hs hsN => (hStages s hs hsN).2)
      (k + 1) (by omega) (by omega)
  have hgrad := S.accumulated_gradient_bound hp (Finset.range N) f (fun k => α (k + 1)) x
    (z N) (grad (z N)) (hDerivative (z N))
    (fun k hk => (hα (k + 1) (by omega) (by simpa using Finset.mem_range.mp hk)).le) (hMin N le_rfl)
  have hBias : S.snorm (dualExponent p) (grad (z N)) ≤ ε / 2 := by
    apply hgrad.trans
    apply le_trans _ hBiasBudget
    apply mul_le_mul_of_nonneg_left _ (atomScale_pos p).le
    apply Finset.sum_le_sum
    intro k hk
    apply mul_le_mul_of_nonneg_left _ (hα (k + 1) (by omega) (by simpa using Finset.mem_range.mp hk)).le
    exact Real.rpow_le_rpow (S.snorm_nonneg _ _) (hPath k (Finset.mem_range.mp hk)) (by linarith)
  exact S.holder_terminal_transfer hp grad (x N) (z N) hL ht hHolder
    (hStages N hN le_rfl).2 hBias hTerminalScale

def comparisonConstant (p : ℝ) (hp : 1 ≤ p) : ℝ := Classical.choose (S.norm_comparison p hp)

lemma comparisonConstant_pos (p : ℝ) (hp : 1 ≤ p) : 0 < S.comparisonConstant p hp :=
  (Classical.choose_spec (S.norm_comparison p hp)).1

lemma comparisonConstant_bound (p : ℝ) (hp : 1 ≤ p) (X : Mat m n) :
    ‖X‖ ≤ S.comparisonConstant p hp * S.snorm p X :=
  (Classical.choose_spec (S.norm_comparison p hp)).2 X

lemma radial_atom_jensen {p : ℝ} (hp : 2 ≤ p) (C : Mat m n) :
    RadialPowerJensen (S.snorm p) p 1 (radialPowerAtom (S.snorm p) p (atomScale p) C) := by
  have hfun : radialPowerAtom (S.snorm p) p (atomScale p) C = S.atom p C := by
    funext X
    exact (S.atom_eq_radial p C X).symm
  rw [hfun]
  exact S.atom_jensen hp C

/-- Equation (5.7) has exactly one minimizer, even for empty history.  Its
coercivity and strict Jensen modulus are proved by the generic power-prox
theorem from the displayed radial objective, not assumed as new inputs. -/
theorem composite_existsUnique {ι : Type*} {p : ℝ} (hp : 2 ≤ p)
    (s : Finset ι) (w : ι → ℝ) (C : ι → Mat m n) (hw : ∀ i ∈ s, 0 ≤ w i)
    (center G : Mat m n) (A ξ : ℝ) (hA : 0 ≤ A) (hξ : 0 < ξ) :
    ∃! Z : Mat m n, ∀ X,
      tracePair G Z + A * (∑ i ∈ s, w i * S.atom p (C i) Z) + ξ * S.atom p center Z ≤
        tracePair G X + A * (∑ i ∈ s, w i * S.atom p (C i) X) + ξ * S.atom p center X := by
  have hp1 : 1 ≤ p := by linarith
  have h := radialComposite_existsUnique_minimizer (S.snorm p) (S.norm_continuous p hp1)
    (S.snorm_nonneg p) (S.norm_eq_zero p hp1) (S.comparisonConstant p hp1)
    (S.comparisonConstant_pos p hp1) (S.comparisonConstant_bound p hp1) hp (atomScale_pos p)
    (S.radial_atom_jensen hp) s w C hw center (traceFunctional G) A ξ hA hξ
  simpa only [traceFunctional_apply, radialPowerAtom, ← S.atom_eq_radial] using h

/-- A deterministic single-valued exact map of the known matrix prox data.
The legal branch is chosen from the proved unique minimum of (5.7). -/
def compositeProx {ι : Type*} {p : ℝ} (hp : 2 ≤ p)
    (s : Finset ι) (w : ι → ℝ) (C : ι → Mat m n) (hw : ∀ i ∈ s, 0 ≤ w i)
    (center G : Mat m n) (A ξ : ℝ) : Mat m n :=
  radialCompositeProx (S.snorm p) (S.norm_continuous p (by linarith)) (S.snorm_nonneg p)
    (S.norm_eq_zero p (by linarith)) (S.comparisonConstant p (by linarith))
    (S.comparisonConstant_pos p (by linarith)) (S.comparisonConstant_bound p (by linarith))
    hp (atomScale_pos p) (S.radial_atom_jensen hp) s w C hw center (traceFunctional G) A ξ

theorem compositeProx_minimizes {ι : Type*} {p : ℝ} (hp : 2 ≤ p)
    (s : Finset ι) (w : ι → ℝ) (C : ι → Mat m n) (hw : ∀ i ∈ s, 0 ≤ w i)
    (center G : Mat m n) (A ξ : ℝ) (hA : 0 ≤ A) (hξ : 0 < ξ) :
    let Z := S.compositeProx hp s w C hw center G A ξ
    ∀ X, tracePair G Z + A * (∑ i ∈ s, w i * S.atom p (C i) Z) + ξ * S.atom p center Z ≤
      tracePair G X + A * (∑ i ∈ s, w i * S.atom p (C i) X) + ξ * S.atom p center X := by
  have hp1 : 1 ≤ p := by linarith
  have h := radialCompositeProx_minimizes (S.snorm p) (S.norm_continuous p hp1)
    (S.snorm_nonneg p) (S.norm_eq_zero p hp1) (S.comparisonConstant p hp1)
    (S.comparisonConstant_pos p hp1) (S.comparisonConstant_bound p hp1) hp (atomScale_pos p)
    (S.radial_atom_jensen hp) s w C hw center (traceFunctional G) A ξ hA hξ
  simpa only [compositeProx, traceFunctional_apply, radialPowerAtom, ← S.atom_eq_radial] using h

theorem objective_continuous {p : ℝ} (hp : 2 ≤ p) (f : Mat m n → ℝ)
    (hf : Continuous f) (α : ℕ → ℝ) (x : ℕ → Mat m n) (s : ℕ) :
    Continuous (S.objective p f α x s) :=
  hf.add (continuous_finset_sum _ (fun k _ => continuous_const.mul (S.atom_continuous hp (x k))))

/-- Every actual stage objective has an attained unique minimizer.  The
first positive atom supplies a coercive power lower bound, and the derived
Jensen modulus supplies uniqueness. -/
theorem objective_existsUnique {p : ℝ} (hp : 2 ≤ p)
    (f : Mat m n → ℝ) (hfcont : Continuous f) (hf : ConvexOn ℝ Set.univ f)
    (xstar : Mat m n) (hstar : ∀ X, f xstar ≤ f X)
    (α : ℕ → ℝ) (x : ℕ → Mat m n) (s : ℕ) (hs : 1 ≤ s)
    (hα : ∀ k, 1 ≤ k → k ≤ s → 0 < α k) :
    ∃! Z : Mat m n, ∀ X, S.objective p f α x s Z ≤ S.objective p f α x s X := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hF := S.objective_continuous hp f hfcont α x s
  have hLower (X : Mat m n) : f xstar + (α 1 * (atomScale p / p)) * S.snorm p (X - x 0) ^ p -
      0 * S.snorm p (X - x 0) ≤ S.objective p f α x s X := by
    have hsum : α 1 * S.atom p (x 0) X ≤
        ∑ k ∈ Finset.range s, α (k + 1) * S.atom p (x k) X :=
      Finset.single_le_sum
        (fun k hk => mul_nonneg (hα (k + 1) (by omega) (by simpa using Finset.mem_range.mp hk)).le
          (S.atom_nonneg hp0 (x k) X)) (show 0 ∈ Finset.range s by simp; omega)
    rw [S.atom_eq_radial] at hsum
    have hmin := hstar X
    dsimp [objective]
    nlinarith
  obtain ⟨Z, hZ⟩ := radial_power_lower_exists_min (S.snorm_nonneg p) hp
    (mul_pos (hα 1 le_rfl hs) (div_pos (atomScale_pos p) hp0)) (by norm_num)
    (S.comparisonConstant_pos p hp1).le (S.comparisonConstant_bound p hp1) hF (x 0) hLower
  refine ⟨Z, hZ, ?_⟩
  intro Y hY
  exact radialPowerJensen_unique_minimizer (S.snorm_nonneg p) (S.norm_eq_zero p hp1) hp0
    (modulus_pos hs hα) (S.objective_jensen hp f α x s hf
      (fun k hk => (hα (k + 1) (by omega) (by omega)).le)) hZ hY

theorem powerGradient_two (X : Mat m n) : S.powerGradient 2 X = X := by
  obtain ⟨U, V, _, _, hX, hG⟩ := S.compact_svd 2 (by norm_num) X
  norm_num [Real.rpow_one] at hG
  exact hG.trans hX.symm

theorem atomGradient_two (C X : Mat m n) : S.atomGradient 2 C X = (2 : ℝ) • (X - C) := by
  rw [atomGradient, S.powerGradient_two]
  norm_num [atomScale]

/-- At the Hilbert endpoint every finite spectral history compresses to one
weighted center, with the factor `G/2` caused by this paper's normalization. -/
theorem quadratic_weighted_minimizer {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (C : ι → Mat m n) (G Z : Mat m n) (hW : 0 < ∑ i ∈ s, w i)
    (hMin : ∀ X, tracePair G Z + ∑ i ∈ s, w i * S.atom 2 (C i) Z ≤
      tracePair G X + ∑ i ∈ s, w i * S.atom 2 (C i) X) :
    Z = (∑ i ∈ s, w i)⁻¹ • ((∑ i ∈ s, w i • C i) - (1 / 2 : ℝ) • G) := by
  have hd : HasFDerivAt (fun X => tracePair G X) (traceFunctional G) Z := by
    have hfun : (fun X => tracePair G X) = traceFunctional G := by
      funext X
      exact (traceFunctional_apply G X).symm
    rw [hfun]
    exact (traceFunctional G).hasFDerivAt
  have hStat := S.accumulated_stationarity (by norm_num : (2 : ℝ) ≤ 2) s
    (fun X => tracePair G X) w C Z G hd hMin
  simp_rw [S.atomGradient_two] at hStat
  ext i j
  have hcoord := congrArg (fun M : Mat m n => M i j) hStat
  simp only [Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at hcoord
  have hsum : (∑ k ∈ s, w k * (2 * (Z i j - C k i j))) =
      2 * ((∑ k ∈ s, w k) * Z i j - ∑ k ∈ s, w k * C k i j) := by
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hsum] at hcoord
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.sum_apply, smul_eq_mul]
  apply (eq_inv_mul_iff_mul_eq₀ hW.ne').2
  linarith

/-- The literal closed form after (5.7), for the deterministic matrix prox. -/
theorem compositeProx_two_eq {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (C : ι → Mat m n) (hw : ∀ i ∈ s, 0 ≤ w i)
    (center G : Mat m n) (A ξ : ℝ) (hA : 0 ≤ A) (hξ : 0 < ξ) :
    S.compositeProx (by norm_num : (2 : ℝ) ≤ 2) s w C hw center G A ξ =
      (A * (∑ i ∈ s, w i) + ξ)⁻¹ •
        (A • (∑ i ∈ s, w i • C i) + ξ • center - (1 / 2 : ℝ) • G) := by
  classical
  let w' : Option s → ℝ := radialCompositeWeights s w A ξ
  let C' : Option s → Mat m n := radialCompositeCenters s C center
  let Z := S.compositeProx (by norm_num : (2 : ℝ) ≤ 2) s w C hw center G A ξ
  have hsum (X : Mat m n) : (∑ i : Option s, w' i * S.atom 2 (C' i) X) =
      A * (∑ i ∈ s, w i * S.atom 2 (C i) X) + ξ * S.atom 2 center X := by
    simpa only [w', C', radialPowerAtom, ← S.atom_eq_radial] using
      radialComposite_sum_eq s w C center (S.snorm 2) 2 (atomScale 2) A ξ X
  have hWsum : (∑ i : Option s, w' i) = A * (∑ i ∈ s, w i) + ξ := by
    simp only [w', univ_option, Finset.sum_insertNone, radialCompositeWeights,
      Option.elim_none, Option.elim_some]
    have hs : (∑ i : s, A * w i) = A * (∑ i ∈ s, w i) := by
      calc
        _ = ∑ i ∈ s, A * w i := Finset.sum_coe_sort s _
        _ = _ := (Finset.mul_sum _ _ _).symm
    rw [hs, add_comm]
  have hCenters : (∑ i : Option s, w' i • C' i) =
      A • (∑ i ∈ s, w i • C i) + ξ • center := by
    simp only [w', C', univ_option, Finset.sum_insertNone, radialCompositeWeights,
      radialCompositeCenters, Option.elim_none, Option.elim_some]
    have hs : (∑ i : s, (A * w i) • C i) = A • (∑ i ∈ s, w i • C i) := by
      calc
        _ = ∑ i ∈ s, (A * w i) • C i := Finset.sum_coe_sort s _
        _ = _ := by simp only [Finset.smul_sum, smul_smul]
    rw [hs, add_comm]
  have hWpos : 0 < ∑ i : Option s, w' i := by
    rw [hWsum]
    exact add_pos_of_nonneg_of_pos (mul_nonneg hA (Finset.sum_nonneg hw)) hξ
  have hMin : ∀ X, tracePair G Z + ∑ i : Option s, w' i * S.atom 2 (C' i) Z ≤
      tracePair G X + ∑ i : Option s, w' i * S.atom 2 (C' i) X := by
    intro X
    rw [hsum, hsum]
    have h := S.compositeProx_minimizes (by norm_num : (2 : ℝ) ≤ 2) s w C hw center G A ξ hA hξ X
    dsimp [Z]
    linarith
  have hZ := S.quadratic_weighted_minimizer (Finset.univ : Finset (Option s)) w' C' G Z hWpos hMin
  rw [hWsum, hCenters] at hZ
  exact hZ

end SpectralInput

end P31.Schatten
