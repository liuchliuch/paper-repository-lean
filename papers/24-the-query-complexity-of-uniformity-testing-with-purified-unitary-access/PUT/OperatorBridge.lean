import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Genuine Hilbert space block reduction for Lemma 1

This module uses bounded operators on the Hilbert direct sum `WithLp 2 (E × F)` and the
actual adjoints of preparation isometries. No numerical variable is identified
with an operator norm by definition. The identity and bound below are the
operator statement (9) of the paper, before the Fourier coefficient estimates.
-/

noncomputable section

open scoped InnerProduct

namespace PUT.OperatorBridge

section Blocks

variable {E₀ E₁ F₀ F₁ : Type*}
variable [NormedAddCommGroup E₀] [NormedSpace ℂ E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
  [NormedAddCommGroup F₀] [NormedSpace ℂ F₀]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]

/-- A bounded operator matrix on Hilbert direct sums, with their genuine
Euclidean product norm, rather than the default supremum product norm. -/
def block (A : E₁ →L[ℂ] E₀) (B : F₁ →L[ℂ] E₀)
    (C : E₁ →L[ℂ] F₀) (D : F₁ →L[ℂ] F₀) :
    WithLp 2 (E₁ × F₁) →L[ℂ] WithLp 2 (E₀ × F₀) :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ E₀ F₀).symm.toContinuousLinearMap ∘L
    ((A.coprod B).prod (C.coprod D)) ∘L
    (WithLp.prodContinuousLinearEquiv 2 ℂ E₁ F₁).toContinuousLinearMap

@[simp] theorem block_apply (A : E₁ →L[ℂ] E₀) (B : F₁ →L[ℂ] E₀)
    (C : E₁ →L[ℂ] F₀) (D : F₁ →L[ℂ] F₀) (x : WithLp 2 (E₁ × F₁)) :
    block A B C D x = WithLp.toLp 2 (A x.fst + B x.snd, C x.fst + D x.snd) := rfl

omit [NormedSpace ℂ E₀] [NormedSpace ℂ F₀] in
/-- Triangle inequality for the true Hilbert direct sum. -/
theorem norm_toLp_pair_le (x : E₀) (y : F₀) :
    ‖WithLp.toLp 2 (x, y)‖ ≤ ‖x‖ + ‖y‖ := by
  have h := norm_add_le (WithLp.toLp 2 (x, (0 : F₀)))
    (WithLp.toLp 2 ((0 : E₀), y))
  simpa [← WithLp.toLp_add] using h

/-- Each of the four actual blocks contributes at most its operator norm. -/
theorem norm_block_le (A : E₁ →L[ℂ] E₀) (B : F₁ →L[ℂ] E₀)
    (C : E₁ →L[ℂ] F₀) (D : F₁ →L[ℂ] F₀) :
    ‖block A B C D‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ + ‖D‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  calc
    ‖block A B C D x‖
        ≤ ‖A x.fst + B x.snd‖ + ‖C x.fst + D x.snd‖ :=
      norm_toLp_pair_le _ _
    _ ≤ (‖A x.fst‖ + ‖B x.snd‖) + (‖C x.fst‖ + ‖D x.snd‖) :=
      add_le_add (norm_add_le _ _) (norm_add_le _ _)
    _ ≤ (‖A‖ * ‖x‖ + ‖B‖ * ‖x‖) + (‖C‖ * ‖x‖ + ‖D‖ * ‖x‖) := by
      exact add_le_add
        (add_le_add ((A.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (WithLp.norm_fst_le E₁ x) (norm_nonneg _)))
          ((B.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (WithLp.norm_snd_le E₁ x) (norm_nonneg _))))
        (add_le_add ((C.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (WithLp.norm_fst_le E₁ x) (norm_nonneg _)))
          ((D.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (WithLp.norm_snd_le E₁ x) (norm_nonneg _))))
    _ = (‖A‖ + ‖B‖ + ‖C‖ + ‖D‖) * ‖x‖ := by ring

end Blocks

section Reflection

variable {E₀ E₁ F₀ F₁ : Type*}
variable [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
  [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]

/-- The preparation/erasure block form of the reflection (3). -/
def reflectionBlock {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : E →L[ℂ] F) : WithLp 2 (E × F) →L[ℂ] WithLp 2 (E × F) :=
  block 0 V.adjoint V (V ∘L V.adjoint - ContinuousLinearMap.id ℂ F)

/-- An isometric preparation is cancelled by its actual Hilbert adjoint. -/
theorem adjoint_preparation_apply {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : E →ₗᵢ[ℂ] F) (x : E) :
    V.toContinuousLinearMap.adjoint (V x) = x := by
  have h := V.toContinuousLinearMap.norm_map_iff_adjoint_comp_self.mp V.norm_map
  exact DFunLike.congr_fun h x

/-- The full block operator really is an involution for an isometric
preparation, including on arbitrary vectors orthogonal to the prepared range. -/
theorem reflectionBlock_sq {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : E →ₗᵢ[ℂ] F) :
    reflectionBlock V.toContinuousLinearMap ∘L reflectionBlock V.toContinuousLinearMap =
      ContinuousLinearMap.id ℂ (WithLp 2 (E × F)) := by
  ext x
  apply WithLp.ofLp_injective
  ext <;> simp [reflectionBlock, block_apply, map_add, map_sub,
    adjoint_preparation_apply]

/-- The reflection block is self-adjoint on the Hilbert direct sum. -/
theorem reflectionBlock_inner {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : E →L[ℂ] F) (x y : WithLp 2 (E × F)) :
    inner ℂ (reflectionBlock V x) y = inner ℂ x (reflectionBlock V y) := by
  simp only [reflectionBlock, block_apply, WithLp.prod_inner_apply,
    WithLp.ofLp_toLp, WithLp.ofLp_fst, WithLp.ofLp_snd,
    ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, zero_add, inner_add_left, inner_sub_left,
    inner_add_right, inner_sub_right]
  rw [V.adjoint_inner_left, ← V.adjoint_inner_right,
    ← V.adjoint_inner_right, V.adjoint_inner_left]
  abel

/-- The adjoint of the full reflection, including the unused output
subspace, equals the reflection itself. -/
theorem reflectionBlock_adjoint {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : E →L[ℂ] F) : (reflectionBlock V).adjoint = reflectionBlock V := by
  ext x
  apply ext_inner_left ℂ
  intro y
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact reflectionBlock_inner V y x

/-- A preparation isometry yields a norm-preserving full reflection. -/
theorem reflectionBlock_norm_map {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (V : E →ₗᵢ[ℂ] F) (x : WithLp 2 (E × F)) :
    ‖reflectionBlock V.toContinuousLinearMap x‖ = ‖x‖ := by
  apply (reflectionBlock V.toContinuousLinearMap).norm_map_iff_adjoint_comp_self.mpr
    (by rw [reflectionBlock_adjoint, reflectionBlock_sq]; rfl)

/-- The adversary acts on the bottom and output parts by the corresponding
operators `Γ` and `Γ ⊗ I_H`. The latter is an actual bounded operator input. -/
def liftedAdversary (Γ : E₁ →L[ℂ] E₀) (ΓH : F₁ →L[ℂ] F₀) :
    WithLp 2 (E₁ × F₁) →L[ℂ] WithLp 2 (E₀ × F₀) :=
  block Γ 0 0 ΓH

/-- Creation and erasure query differences, using actual adjoints. -/
def dplus (Γ : E₁ →L[ℂ] E₀) (ΓH : F₁ →L[ℂ] F₀)
    (V₀ : E₀ →L[ℂ] F₀) (V₁ : E₁ →L[ℂ] F₁) : E₁ →L[ℂ] F₀ :=
  ΓH ∘L V₁ - V₀ ∘L Γ

def dminus (Γ : E₁ →L[ℂ] E₀) (ΓH : F₁ →L[ℂ] F₀)
    (V₀ : E₀ →L[ℂ] F₀) (V₁ : E₁ →L[ℂ] F₁) : F₁ →L[ℂ] E₀ :=
  Γ ∘L V₁.adjoint - V₀.adjoint ∘L ΓH

/-- The exact lower-right cancellation used in equation (9). -/
theorem query_difference_eq_block (Γ : E₁ →L[ℂ] E₀) (ΓH : F₁ →L[ℂ] F₀)
    (V₀ : E₀ →L[ℂ] F₀) (V₁ : E₁ →L[ℂ] F₁) :
    liftedAdversary Γ ΓH ∘L reflectionBlock V₁
        - reflectionBlock V₀ ∘L liftedAdversary Γ ΓH =
      block 0 (dminus Γ ΓH V₀ V₁) (dplus Γ ΓH V₀ V₁)
        (dplus Γ ΓH V₀ V₁ ∘L V₁.adjoint + V₀ ∘L dminus Γ ΓH V₀ V₁) := by
  ext x
  apply WithLp.ofLp_injective
  ext <;> simp [liftedAdversary, reflectionBlock, dplus, dminus, block_apply,
    map_add, map_sub] <;> abel

/-- Equation (9) as an actual operator-norm statement on arbitrary Hilbert
spaces. The hypotheses are preparation isometries, not a presumed query bound. -/
theorem full_query_norm_le (Γ : E₁ →L[ℂ] E₀) (ΓH : F₁ →L[ℂ] F₀)
    (V₀ : E₀ →ₗᵢ[ℂ] F₀) (V₁ : E₁ →ₗᵢ[ℂ] F₁) :
    ‖liftedAdversary Γ ΓH ∘L reflectionBlock V₁.toContinuousLinearMap
        - reflectionBlock V₀.toContinuousLinearMap ∘L liftedAdversary Γ ΓH‖ ≤
      2 * (‖dplus Γ ΓH V₀.toContinuousLinearMap V₁.toContinuousLinearMap‖
        + ‖dminus Γ ΓH V₀.toContinuousLinearMap V₁.toContinuousLinearMap‖) := by
  let Dp := dplus Γ ΓH V₀.toContinuousLinearMap V₁.toContinuousLinearMap
  let Dm := dminus Γ ΓH V₀.toContinuousLinearMap V₁.toContinuousLinearMap
  have h₀ : ‖V₀.toContinuousLinearMap‖ ≤ 1 := V₀.norm_toContinuousLinearMap_le
  have h₁ : ‖V₁.toContinuousLinearMap.adjoint‖ ≤ 1 := by
    simpa only [LinearIsometryEquiv.norm_map] using V₁.norm_toContinuousLinearMap_le
  have hbottom : ‖Dp ∘L V₁.toContinuousLinearMap.adjoint
      + V₀.toContinuousLinearMap ∘L Dm‖ ≤ ‖Dp‖ + ‖Dm‖ := by
    calc
      _ ≤ ‖Dp ∘L V₁.toContinuousLinearMap.adjoint‖
          + ‖V₀.toContinuousLinearMap ∘L Dm‖ := norm_add_le _ _
      _ ≤ ‖Dp‖ * ‖V₁.toContinuousLinearMap.adjoint‖
          + ‖V₀.toContinuousLinearMap‖ * ‖Dm‖ :=
        add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
          (ContinuousLinearMap.opNorm_comp_le _ _)
      _ ≤ ‖Dp‖ * 1 + 1 * ‖Dm‖ :=
        add_le_add (mul_le_mul_of_nonneg_left h₁ (norm_nonneg _))
          (mul_le_mul_of_nonneg_right h₀ (norm_nonneg _))
      _ = ‖Dp‖ + ‖Dm‖ := by ring
  rw [query_difference_eq_block]
  have h := norm_block_le (0 : E₁ →L[ℂ] E₀) Dm Dp
    (Dp ∘L V₁.toContinuousLinearMap.adjoint + V₀.toContinuousLinearMap ∘L Dm)
  simp only [norm_zero, zero_add] at h
  change _ ≤ 2 * (‖Dp‖ + ‖Dm‖)
  linarith

end Reflection

section ResidualGram

variable {ι H : Type*} [Fintype ι] [DecidableEq ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Actual finite synthesis operator for residual vectors in a Hilbert space. -/
def radialSynthesis (r : ι → H) : EuclideanSpace ℂ ι →L[ℂ] H :=
  ∑ i, (EuclideanSpace.proj i).smulRight (r i)

omit [DecidableEq ι] [CompleteSpace H] in
@[simp] theorem radialSynthesis_apply (r : ι → H) (x : EuclideanSpace ℂ ι) :
    radialSynthesis r x = ∑ i, x i • r i := by
  simp [radialSynthesis]

/-- Actual analysis operator `h ↦ (⟪rᵢ,h⟫)ᵢ`, obtained from the Hilbert
adjoint rather than postulated real quantities. -/
def radialAnalysis (r : ι → H) : H →L[ℂ] EuclideanSpace ℂ ι :=
  (radialSynthesis r).adjoint

@[simp] theorem radialAnalysis_apply (r : ι → H) (h : H) (i : ι) :
    radialAnalysis r h i = inner ℂ (r i) h := by
  classical
  have ht : radialSynthesis r (EuclideanSpace.single i 1) = r i := by simp
  calc
    radialAnalysis r h i =
        inner ℂ (EuclideanSpace.single i 1) (radialAnalysis r h) := by
      simp [EuclideanSpace.inner_single_left]
    _ = inner ℂ (radialSynthesis r (EuclideanSpace.single i 1)) h :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    _ = inner ℂ (r i) h := by rw [ht]

/-- Exact Gram identity (16), now expressed as equality of actual bounded
operators. This holds for complex Hilbert residual vectors and complex
Euclidean coefficients. -/
theorem radial_gram_operator (r : ι → H) (b : EuclideanSpace ℂ ι) (s : ℝ)
    (hgram : ∀ i j, inner ℂ (r i) (r j) =
      ((if i = j then 1 else 0) - b i * star (b j)) / (s : ℂ)) :
    radialAnalysis r ∘L radialSynthesis r =
      (s⁻¹ : ℂ) • (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ ι)
        - (innerSL ℂ b).smulRight b) := by
  classical
  ext x i
  simp only [ContinuousLinearMap.comp_apply, radialAnalysis_apply, radialSynthesis_apply,
    inner_sum, inner_smul_right, hgram, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply, PiLp.smul_apply,
    PiLp.sub_apply, PiLp.inner_apply, RCLike.inner_apply', smul_eq_mul]
  have hdelta : (∑ j : ι, x j * (if i = j then (1 : ℂ) else 0)) = x i := by
    simp [mul_ite]
  simp_rw [← mul_div_assoc, ← Finset.sum_div, mul_sub, Finset.sum_sub_distrib]
  rw [hdelta]
  have hprod : (∑ j : ι, x j * (b i * star (b j))) =
      b i * ∑ j : ι, star (b j) * x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hprod]
  push_cast
  simp only [starRingEnd_apply]
  ring

/-- The residual Gram identity gives the genuine norm bound for the finite
synthesis operator; its adjoint is the radial analysis map in (17). -/
theorem norm_radialSynthesis_le_of_gram (r : ι → H) (b : EuclideanSpace ℂ ι) (s : ℝ)
    (hs : 0 < s)
    (hgram : ∀ i j, inner ℂ (r i) (r j) =
      ((if i = j then 1 else 0) - b i * star (b j)) / (s : ℂ)) :
    ‖radialSynthesis r‖ ≤ 1 / Real.sqrt s := by
  have hsq : (1 / Real.sqrt s) ^ 2 = s⁻¹ := by
    rw [div_pow, one_pow, Real.sq_sqrt hs.le]
    exact one_div s
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  have hid := radial_gram_operator r b s hgram
  have hpoint := DFunLike.congr_fun hid x
  have hnorm : ‖radialSynthesis r x‖ ^ 2 =
      s⁻¹ * (‖x‖ ^ 2 - ‖inner ℂ b x‖ ^ 2) := by
    rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
    change (inner ℂ x ((radialAnalysis r ∘L radialSynthesis r) x)).re = _
    rw [hpoint]
    have hprod : inner ℂ b x * inner ℂ x b = (‖inner ℂ b x‖ : ℂ) ^ 2 := by
      rw [← inner_conj_symm x b]
      exact Complex.mul_conj' _
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
      innerSL_apply, inner_smul_right, inner_sub_right,
      inner_self_eq_norm_sq_to_K, hprod]
    simp [← Complex.ofReal_pow]
  have hle : ‖radialSynthesis r x‖ ^ 2 ≤ ((1 / Real.sqrt s) * ‖x‖) ^ 2 := by
    rw [mul_pow, hsq, hnorm]
    have hpos : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
    nlinarith [sq_nonneg ‖inner ℂ b x‖]
  exact le_of_sq_le_sq hle (by positivity)

/-- Equation (16) controls the entire radial analysis operator, on every input
of its Hilbert space, rather than just on real coefficient vectors. -/
theorem norm_radialAnalysis_le_of_gram (r : ι → H) (b : EuclideanSpace ℂ ι) (s : ℝ)
    (hs : 0 < s)
    (hgram : ∀ i j, inner ℂ (r i) (r j) =
      ((if i = j then 1 else 0) - b i * star (b j)) / (s : ℂ)) :
    ‖radialAnalysis r‖ ≤ 1 / Real.sqrt s := by
  simpa only [radialAnalysis, LinearIsometryEquiv.norm_map] using
    norm_radialSynthesis_le_of_gram r b s hs hgram

end ResidualGram

end PUT.OperatorBridge
