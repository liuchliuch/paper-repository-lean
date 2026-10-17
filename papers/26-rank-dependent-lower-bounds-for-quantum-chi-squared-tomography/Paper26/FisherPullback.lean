import Paper26.AlignedFisherBudget
import Paper26.PositiveLossBridge
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Unitary transport and real Euclidean contraction of the one-copy budget

The transformed POVM has the actual effects `W† E W`. The score functional
is the actual Born directional trace composed with the inverse real matrix
coordinate map. Its dual norm and every contracted score are proved internally.
The result does not assert a graph tangent formula or an adaptive chain rule.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory Paper26.QuantumModel Paper26.ContinuousPOVM

namespace Paper26.FisherPullback

open AlignedFisherBudget

section UnitaryPOVM
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

def conjugatedEffect (W : Matrix.unitaryGroup ι ℂ) (E : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (W : Matrix ι ι ℂ)ᴴ * E * (W : Matrix ι ι ℂ)

theorem conjugatedEffect_posSemidef (W : Matrix.unitaryGroup ι ℂ)
    (E : Matrix ι ι ℂ) (hE : E.PosSemidef) : (conjugatedEffect W E).PosSemidef :=
  hE.conjTranspose_mul_mul_same _

variable (M : DominatedPOVM ι Ω) (W : Matrix.unitaryGroup ι ℂ)

theorem conjugated_entry_measurable (i j : ι) :
    Measurable (fun y => conjugatedEffect W (M.effect y) i j) := by
  simp only [conjugatedEffect, Matrix.mul_apply]
  exact Finset.measurable_sum Finset.univ fun k _ =>
    (Finset.measurable_sum Finset.univ fun l _ =>
      (M.entry_measurable l k).const_mul ((W : Matrix ι ι ℂ)ᴴ i l)).mul_const _

theorem conjugated_entry_integrable (i j : ι) :
    Integrable (fun y => conjugatedEffect W (M.effect y) i j) M.reference := by
  simp only [conjugatedEffect, Matrix.mul_apply]
  exact integrable_finset_sum Finset.univ fun k _ =>
    (integrable_finset_sum Finset.univ fun l _ =>
      (M.entry_integrable l k).const_mul ((W : Matrix ι ι ℂ)ᴴ i l)).mul_const _

theorem conjugated_entry_total (i j : ι) :
    ∫ y, conjugatedEffect W (M.effect y) i j ∂M.reference = (1 : Matrix ι ι ℂ) i j := by
  simp only [conjugatedEffect, Matrix.mul_apply]
  rw [integral_finset_sum Finset.univ (fun k _ =>
    (integrable_finset_sum Finset.univ (fun l _ =>
      (M.entry_integrable l k).const_mul ((W : Matrix ι ι ℂ)ᴴ i l))).mul_const _)]
  simp_rw [integral_mul_const, integral_finset_sum Finset.univ (fun l _ =>
    (M.entry_integrable l _).const_mul ((W : Matrix ι ι ℂ)ᴴ i l)), integral_const_mul, M.total]
  have hW := congrFun (congrFun W.property.1 i) j
  simpa only [Matrix.mul_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using hW

/-- Genuine dominated POVM in arbitrary ambient unitary coordinates. -/
def unitaryPOVM : DominatedPOVM ι Ω where
  reference := M.reference
  reference_finite := M.reference_finite
  effect y := conjugatedEffect W (M.effect y)
  entry_measurable := conjugated_entry_measurable M W
  positive_ae := M.positive_ae.mono fun y hy => conjugatedEffect_posSemidef W (M.effect y) hy
  entry_integrable := conjugated_entry_integrable M W
  total := conjugated_entry_total M W

@[simp] theorem unitaryPOVM_reference : (unitaryPOVM M W).reference = M.reference := rfl
@[simp] theorem unitaryPOVM_effect (y : Ω) :
    (unitaryPOVM M W).effect y = conjugatedEffect W (M.effect y) := rfl

/-- Trace transport identifies the actual rotated tangent likelihood. -/
theorem conjugatedEffect_trace (E D : Matrix ι ι ℂ) :
    Matrix.trace (D * conjugatedEffect W E) =
      Matrix.trace (((W : Matrix ι ι ℂ) * D * (W : Matrix ι ι ℂ)ᴴ) * E) := by
  simp only [conjugatedEffect, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (W : Matrix ι ι ℂ)]
  simp only [Matrix.mul_assoc]

theorem unitaryPOVM_born (ρ : Density ι) (y : Ω) :
    (unitaryPOVM M W).born ρ y =
      M.born (PositiveLossBridge.conjugateDensity W ρ) y := by
  exact congrArg Complex.re (conjugatedEffect_trace W (M.effect y) ρ.matrix)

end UnitaryPOVM

section EuclideanScores
variable (r s : ℕ)

abbrev ParameterSpace := EuclideanSpace ℝ (Fin (2 * r * s))
abbrev EffectMatrix := Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ

theorem tangent_add (K L : Matrix (Fin s) (Fin r) ℂ) : tangent (K + L) = tangent K + tangent L := by
  simp only [tangent, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, smul_add]
  abel

theorem tangent_real_smul (a : ℝ) (K : Matrix (Fin s) (Fin r) ℂ) :
    tangent (a • K) = a • tangent K := by
  simp only [tangent, Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul,
    Matrix.smul_mul, ← smul_add]
  exact smul_comm _ _ _

theorem directionalDerivative_add (E : EffectMatrix r s) (K L : Matrix (Fin s) (Fin r) ℂ) :
    directionalDerivative E (K + L) = directionalDerivative E K + directionalDerivative E L := by
  rw [directionalDerivative, tangent_add, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
  rfl

theorem directionalDerivative_real_smul (E : EffectMatrix r s) (a : ℝ)
    (K : Matrix (Fin s) (Fin r) ℂ) :
    directionalDerivative E (a • K) = a * directionalDerivative E K := by
  rw [directionalDerivative, tangent_real_smul, Matrix.smul_mul, Matrix.trace_smul]
  simp only [directionalDerivative, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]

/-- Actual real-linear Born derivative in the existing Euclidean matrix coordinates. -/
def scoreLinear (E : EffectMatrix r s) : ParameterSpace r s →ₗ[ℝ] ℝ where
  toFun v := directionalDerivative E ((MatrixCoordinates.coordinates r s).symm v)
  map_add' v w := by rw [map_add, directionalDerivative_add]
  map_smul' a v := by rw [map_smul, directionalDerivative_real_smul]; rfl

def score (E : EffectMatrix r s) : ParameterSpace r s →L[ℝ] ℝ :=
  (scoreLinear r s E).toContinuousLinearMap

@[simp] theorem score_apply (E : EffectMatrix r s) (v : ParameterSpace r s) :
    score r s E v = directionalDerivative E ((MatrixCoordinates.coordinates r s).symm v) := rfl

/-- The actual coordinate gradient, represented by the Riesz isometry. -/
def gradient (E : EffectMatrix r s) : ParameterSpace r s :=
  (InnerProductSpace.toDual ℝ (ParameterSpace r s)).symm (score r s E)

theorem gradient_represents (E : EffectMatrix r s) (v : ParameterSpace r s) :
    inner ℝ (gradient r s E) v = score r s E v :=
  InnerProductSpace.toDual_symm_apply

theorem dual_norm_sq_eq_sum {n : ℕ}
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    ‖L‖ ^ 2 = ∑ k, (L (EuclideanSpace.single k 1)) ^ 2 := by
  let g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm L
  have hg : ‖g‖ = ‖L‖ := (InnerProductSpace.toDual ℝ _).symm.norm_map L
  have hb (k : Fin n) : g k = L (EuclideanSpace.single k 1) := by
    simpa only [EuclideanSpace.inner_single_right, conj_trivial, one_mul] using
      (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin n))
        (x := EuclideanSpace.single k 1) (y := L))
  rw [← hg, EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, hb]

theorem coordinates_symm_single (i : Fin s) (j : Fin r) (c : Fin 2) :
    (MatrixCoordinates.coordinates r s).symm
      (EuclideanSpace.single (MatrixCoordinates.indexEquiv r s (i, j, c)) 1) = direction i j c := by
  ext a b
  fin_cases c <;>
    simp [MatrixCoordinates.coordinates_symm_entry, EuclideanSpace.single_apply,
      direction, Matrix.single, (MatrixCoordinates.indexEquiv r s).injective.eq_iff,
      eq_comm, and_comm] <;> split_ifs <;> simp

theorem score_basis (E : EffectMatrix r s) (i : Fin s) (j : Fin r) (c : Fin 2) :
    score r s E (EuclideanSpace.single (MatrixCoordinates.indexEquiv r s (i, j, c)) 1) =
      coordinateDerivative E i j c := by
  rw [score_apply, coordinates_symm_single]
  rfl

theorem score_norm_sq (E : EffectMatrix r s) : ‖score r s E‖ ^ 2 = derivativeNormSq E := by
  rw [dual_norm_sq_eq_sum]
  have h := Fintype.sum_equiv (MatrixCoordinates.indexEquiv r s)
    (fun k => (coordinateDerivative E k.1 k.2.1 k.2.2) ^ 2)
    (fun k => (score r s E (EuclideanSpace.single k 1)) ^ 2)
    (fun k => by rcases k with ⟨i, j, c⟩; dsimp only; rw [score_basis])
  rw [← h]
  simp only [derivativeNormSq, Fintype.sum_prod_type]

/-- Composition by a genuine real Euclidean contraction cannot increase
this actual directional-score dual norm. -/
theorem score_comp_norm_le (E : EffectMatrix r s)
    (T : ParameterSpace r s →L[ℝ] ParameterSpace r s) (hT : ‖T‖ ≤ 1) :
    ‖(score r s E).comp T‖ ≤ ‖score r s E‖ := by
  exact ((score r s E).opNorm_comp_le T).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hT (norm_nonneg (score r s E)))

/-- The contracted per-effect Fisher contribution is defined by the
actual pulled-back directional-score functional. -/
def contractedFisher (E : EffectMatrix r s)
    (T : ParameterSpace r s →L[ℝ] ParameterSpace r s) : ℝ :=
  if probability E = 0 then 0 else ‖(score r s E).comp T‖ ^ 2 / probability E

theorem contractedFisher_nonneg (E : EffectMatrix r s) (hE : E.PosSemidef)
    (T : ParameterSpace r s →L[ℝ] ParameterSpace r s) : 0 ≤ contractedFisher r s E T := by
  unfold contractedFisher
  split_ifs
  · exact le_rfl
  · exact div_nonneg (sq_nonneg _) (probability_nonneg E hE)

theorem contractedFisher_le (E : EffectMatrix r s) (hE : E.PosSemidef)
    (T : ParameterSpace r s →L[ℝ] ParameterSpace r s) (hT : ‖T‖ ≤ 1) :
    contractedFisher r s E T ≤ perEffectFisher E := by
  unfold contractedFisher perEffectFisher
  split_ifs
  · exact le_rfl
  · rw [← score_norm_sq r s E]
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg _) (score_comp_norm_le r s E T hT) 2)
      (probability_nonneg E hE)

theorem gradient_coordinate (E : EffectMatrix r s) (i : Fin s) (j : Fin r) (c : Fin 2) :
    gradient r s E (MatrixCoordinates.indexEquiv r s (i, j, c)) =
      coordinateDerivative E i j c := by
  have h := gradient_represents r s E
    (EuclideanSpace.single (MatrixCoordinates.indexEquiv r s (i, j, c)) 1)
  simpa only [EuclideanSpace.inner_single_right, conj_trivial, one_mul, score_basis] using h

/-- The contracted score norm is exactly the sum of squared actual Born
trace derivatives in the contracted coordinate directions. -/
theorem contracted_norm_sq (E : EffectMatrix r s)
    (T : ParameterSpace r s →L[ℝ] ParameterSpace r s) :
    ‖(score r s E).comp T‖ ^ 2 = ∑ k,
      (directionalDerivative E ((MatrixCoordinates.coordinates r s).symm
        (T (EuclideanSpace.single k 1)))) ^ 2 := by
  rw [dual_norm_sq_eq_sum]
  rfl

/-- Zero Born probability forces the entire actual score functional to
vanish; the contraction therefore has no hidden zero-probability derivative. -/
theorem score_zero_of_probability_zero [NeZero r] (E : EffectMatrix r s)
    (hE : E.PosSemidef) (hp : probability E = 0) : score r s E = 0 := by
  apply norm_eq_zero.1
  apply sq_eq_zero_iff.1
  rw [score_norm_sq]
  exact probability_zero_derivative_zero E hE hp

end EuclideanScores

section ArbitraryOutcomes
variable {Ω : Type*} [MeasurableSpace Ω]
variable (r s : ℕ) (M : DominatedPOVM (Fin r ⊕ Fin s) Ω)
variable (T : ParameterSpace r s →L[ℝ] ParameterSpace r s)

theorem measurable_contractedFisher :
    Measurable (fun y => contractedFisher r s (M.effect y) T) := by
  have hn : Measurable (fun y => ‖(score r s (M.effect y)).comp T‖ ^ 2) := by
    simp_rw [contracted_norm_sq]
    exact Finset.measurable_sum Finset.univ fun k _ =>
      (AlignedFisherBudget.measurable_directionalDerivative M
        ((MatrixCoordinates.coordinates r s).symm
          (T (EuclideanSpace.single k 1)))).pow_const 2
  exact Measurable.ite
    (measurableSet_eq_fun (AlignedFisherBudget.measurable_probability M) measurable_const)
    measurable_const (hn.div (AlignedFisherBudget.measurable_probability M))

theorem integrable_contractedFisher [NeZero r] (hT : ‖T‖ ≤ 1) :
    Integrable (fun y => contractedFisher r s (M.effect y) T) M.reference := by
  apply (AlignedFisherBudget.integrable_perEffectFisher M).mono'
    (measurable_contractedFisher r s M T).aestronglyMeasurable
  filter_upwards [M.positive_ae] with y hy
  rw [Real.norm_eq_abs, abs_of_nonneg (contractedFisher_nonneg r s (M.effect y) hy T)]
  exact contractedFisher_le r s (M.effect y) hy T hT

/-- The arbitrary-outcome one-copy budget survives every genuine real
Euclidean contraction of the actual directional-score functional. -/
theorem contracted_fisher_budget [NeZero r] (hT : ‖T‖ ≤ 1) :
    ∫ y, contractedFisher r s (M.effect y) T ∂M.reference ≤ 4 * (s : ℝ) / (r : ℝ) := by
  calc
    _ ≤ ∫ y, perEffectFisher (M.effect y) ∂M.reference :=
      integral_mono_ae (integrable_contractedFisher r s M T hT)
        (AlignedFisherBudget.integrable_perEffectFisher M)
        (M.positive_ae.mono fun y hy => contractedFisher_le r s (M.effect y) hy T hT)
    _ ≤ _ := by simpa only [Fintype.card_fin] using AlignedFisherBudget.aligned_fisher_budget M

/-- Actual ambient-unitary and coordinate-contraction transport, on
arbitrary outcome spaces. No graph tangent identification is assumed. -/
theorem unitary_contracted_fisher_budget [NeZero r]
    (W : Matrix.unitaryGroup (Fin r ⊕ Fin s) ℂ) (hT : ‖T‖ ≤ 1) :
    ∫ y, contractedFisher r s (conjugatedEffect W (M.effect y)) T ∂M.reference ≤
      4 * (s : ℝ) / (r : ℝ) :=
  contracted_fisher_budget r s (unitaryPOVM M W) T hT

/-- The transported directional likelihood is the derivative of the
actual conjugated density tangent, with no scalar score supplied as input. -/
theorem transported_directionalDerivative
    (W : Matrix.unitaryGroup (Fin r ⊕ Fin s) ℂ)
    (E : EffectMatrix r s) (v : ParameterSpace r s) :
    score r s (conjugatedEffect W E) (T v) =
      (Matrix.trace (((W : EffectMatrix r s) *
        tangent ((MatrixCoordinates.coordinates r s).symm (T v)) *
        (W : EffectMatrix r s)ᴴ) * E)).re := by
  rw [score_apply]
  exact congrArg Complex.re (conjugatedEffect_trace W E _)

/-- A genuine derivative statement along the actual ambient-unitary
transported affine tangent path. This is a tangent calculation only, without
asserting a derivative formula for the nonlinear graph-family map. -/
theorem hasDerivAt_transported_born [NeZero r]
    (W : Matrix.unitaryGroup (Fin r ⊕ Fin s) ℂ)
    (E : EffectMatrix r s) (v : ParameterSpace r s) (t : ℝ) :
    HasDerivAt (fun u : ℝ =>
      (Matrix.trace (((W : EffectMatrix r s) *
        ((GraphFamily.density (0 : Matrix (Fin s) (Fin r) ℂ)).matrix +
          u • tangent ((MatrixCoordinates.coordinates r s).symm (T v))) *
        (W : EffectMatrix r s)ᴴ) * E)).re)
      (score r s (conjugatedEffect W E) (T v)) t := by
  have heq : (fun u : ℝ =>
      (Matrix.trace (((W : EffectMatrix r s) *
        ((GraphFamily.density (0 : Matrix (Fin s) (Fin r) ℂ)).matrix +
          u • tangent ((MatrixCoordinates.coordinates r s).symm (T v))) *
        (W : EffectMatrix r s)ᴴ) * E)).re) =
      (fun u : ℝ => (Matrix.trace
        (((GraphFamily.density (0 : Matrix (Fin s) (Fin r) ℂ)).matrix +
          u • tangent ((MatrixCoordinates.coordinates r s).symm (T v))) *
          conjugatedEffect W E)).re) := by
    funext u
    exact (congrArg Complex.re (conjugatedEffect_trace W E _)).symm
  rw [heq, score_apply]
  exact AlignedFisherBudget.hasDerivAt_born_tangent _ _ _

end ArbitraryOutcomes

end Paper26.FisherPullback
