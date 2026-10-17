import Paper18.Fusion.ComplexDimensions
import Paper18.Results.Integrality
import Paper18.Category.PivotalDimensionFusion

/-!
# Dimension bounds towards the ENO pseudounitary theorem

These bounds are consequences of the actual categorical dimension character
after applying `PivotalStructure.pivotalData`. They do not assert the ENO
global-dimension equality or positive-pivotal existence as an assumption or
a construction field.
-/

noncomputable section
open Classical
open scoped BigOperators ComplexConjugate Matrix

universe u
namespace Paper18.PivotalData

variable {ι : Type u} [Fintype ι] {B : FusionBasis ι} (J : PivotalData B)

/-- A complex dimension character is bounded pointwise by the genuine FP
dimension, by a maximal coordinate ratio and the triangle inequality. -/
theorem norm_jdim_le_fpdim (x : ι) : ‖J.jdim x‖ ≤ B.fpdim x := by
  letI : Nonempty ι := ⟨B.one⟩
  obtain ⟨i, hi⟩ : ∃ i : ι, ∀ j, ‖J.jdim j‖ / B.fpdim j ≤ ‖J.jdim i‖ / B.fpdim i :=
    Finite.exists_max _
  let R := ‖J.jdim i‖ / B.fpdim i
  have hR (j : ι) : ‖J.jdim j‖ ≤ R * B.fpdim j :=
    (div_le_iff₀ (B.fpdim_pos j)).mp (hi j)
  have he : R * B.fpdim i = ‖J.jdim i‖ :=
    div_mul_cancel₀ _ (ne_of_gt (B.fpdim_pos i))
  have hb : ‖J.jdim x‖ * ‖J.jdim i‖ ≤ B.fpdim x * ‖J.jdim i‖ := by
    calc
      _ = ‖J.jdim x * J.jdim i‖ := (norm_mul _ _).symm
      _ = ‖∑ j, (B.N x i j : ℂ) * J.jdim j‖ := by rw [J.jdim_tensor]
      _ ≤ ∑ j, ‖(B.N x i j : ℂ) * J.jdim j‖ := norm_sum_le _ _
      _ = ∑ j, (B.N x i j : ℝ) * ‖J.jdim j‖ := by simp only [norm_mul, Complex.norm_natCast]
      _ ≤ ∑ j, (B.N x i j : ℝ) * (R * B.fpdim j) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hR j) (Nat.cast_nonneg _))
      _ = R * ∑ j, (B.N x i j : ℝ) * B.fpdim j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = B.fpdim x * ‖J.jdim i‖ := by rw [B.fpdim_mul, ← he]; ring
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr (J.jdim_ne_zero i))).mp hb

theorem normSq_jdim_le_fpdim_sq (x : ι) :
    Complex.normSq (J.jdim x) ≤ B.fpdim x ^ 2 := by
  rw [← Complex.sq_norm]
  exact pow_le_pow_left₀ (norm_nonneg _) (J.norm_jdim_le_fpdim x) 2

theorem globalDimension_re_le_totalFPdim : J.globalDimension.re ≤ B.totalFPdim := by
  change Complex.reAddGroupHom (∑ i, J.ndim i) ≤ _
  rw [map_sum]
  exact Finset.sum_le_sum (fun i _ => by
    rw [J.ndim_eq_normSq]
    exact J.normSq_jdim_le_fpdim_sq i)

/-- Equality of the actual global dimension and total FP dimension forces
equality in every pointwise dimension bound. -/
theorem norm_jdim_eq_fpdim_of_global_eq (hD : J.globalDimension.re = B.totalFPdim) (x : ι) :
    ‖J.jdim x‖ = B.fpdim x := by
  have hs : (∑ i, Complex.normSq (J.jdim i)) = ∑ i, B.fpdim i ^ 2 := by
    simpa only [globalDimension, FusionBasis.totalFPdim, Complex.re_sum,
      J.ndim_eq_normSq, Complex.ofReal_re] using hD
  have he := (Finset.sum_eq_sum_iff_of_le
    (fun i (_ : i ∈ Finset.univ) => J.normSq_jdim_le_fpdim_sq i)).mp hs x (Finset.mem_univ x)
  rw [← Complex.sq_norm] at he
  nlinarith [norm_nonneg (J.jdim x), B.fpdim_pos x]

/-- Every categorical simple dimension is an algebraic integer, proved
from its actual integer fusion matrix and characteristic polynomial. -/
theorem jdim_isIntegral (x : ι) : IsIntegral ℤ (J.jdim x) := by
  let L : Matrix ι ι ℤ := fun i j => B.N x i j
  let Lc : Matrix ι ι ℂ := L.map (Int.castRingHom ℂ)
  have hker : (Matrix.scalar ι (J.jdim x) - Lc) *ᵥ J.jdim = 0 := by
    ext i
    simp only [Matrix.sub_mulVec, Matrix.scalar_apply, Matrix.mulVec_diagonal, Pi.sub_apply,
      Pi.zero_apply]
    change J.jdim x * J.jdim i - ∑ j, (B.N x i j : ℂ) * J.jdim j = 0
    rw [← J.jdim_tensor]
    ring
  have hne : J.jdim ≠ 0 := by
    intro h
    have h1 := congrFun h B.one
    simp [J.jdim_one] at h1
  have hdet : (Matrix.scalar ι (J.jdim x) - Lc).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨J.jdim, hne, hker⟩
  refine ⟨L.charpoly, L.charpoly_monic, ?_⟩
  rw [← Polynomial.eval_map, ← Matrix.charpoly_map, Matrix.eval_charpoly]
  exact hdet

theorem globalDimension_isIntegral : IsIntegral ℤ J.globalDimension := by
  apply IsIntegral.sum
  intro i _
  exact (J.jdim_isIntegral i).mul (J.jdim_isIntegral (B.dual i))

/-- Spherical actual dimensions are real. -/
theorem jdim_im_eq_zero (hJ : J.Spherical) (x : ι) : (J.jdim x).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  exact (J.jdim_dual_eq_conj x).symm.trans (J.jdim_dual_of_spherical hJ x)

/-- Field conjugation preserves all dimension-character equations of the
actual integer fusion rules. No new categorical trace is assumed. -/
def conjugate (σ : ℂ ≃+* ℂ) : PivotalData B where
  jdim i := σ (J.jdim i)
  jdim_ne_zero i := by simpa using J.jdim_ne_zero i
  jdim_one := by simp [J.jdim_one]
  jdim_tensor i j := by
    have h := congrArg σ (J.jdim_tensor i j)
    simpa only [map_mul, map_sum, map_natCast] using h

@[simp] theorem conjugate_globalDimension (σ : ℂ ≃+* ℂ) :
    (J.conjugate σ).globalDimension = σ J.globalDimension := by
  simp only [globalDimension, ndim, conjugate, map_sum, map_mul]

theorem conjugate_globalDimension_pos (σ : ℂ ≃+* ℂ) :
    0 < (σ J.globalDimension).re := by
  rw [← J.conjugate_globalDimension σ]
  exact (J.conjugate σ).globalDimension_re_pos

theorem conjugate_globalDimension_le (σ : ℂ ≃+* ℂ) :
    (σ J.globalDimension).re ≤ B.totalFPdim := by
  rw [← J.conjugate_globalDimension σ]
  exact (J.conjugate σ).globalDimension_re_le_totalFPdim

end Paper18.PivotalData
