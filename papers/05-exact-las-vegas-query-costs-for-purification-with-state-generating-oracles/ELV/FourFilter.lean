import ELV.Rotation
import ELV.AdversaryFour

/-! The four-instance filter estimate on arbitrary Hilbert-space query
vectors. The contraction constant is derived from the relative unitary. -/
noncomputable section
namespace ELV.AdversaryFour
open ELV.Stabilize ELV.Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma relative_re_inner (T : E ≃ₗᵢ[ℂ] E) (μ : ℝ)
    (hT : ∀ z, T z + T.symm z = (2*μ : ℂ) • z) (z : E) :
    (inner ℂ z (T z)).re = μ * ‖z‖^2 := by
  have hi := congrArg (fun w => (inner ℂ z w).re) (hT z)
  dsimp only at hi
  have hinv : inner ℂ z (T.symm z) = star (inner ℂ z (T z)) := by
    rw [← T.inner_map_map z (T.symm z),T.apply_symm_apply]
    exact (inner_conj_symm (𝕜 := ℂ) (T z) z).symm
  rw [inner_add_right,hinv,inner_smul_right,inner_self_eq_norm_sq_to_K] at hi
  norm_num [Complex.mul_re,Complex.mul_im] at hi
  have hr : (inner ℂ (T z) z).re = (inner ℂ z (T z)).re := by
    rw [← inner_conj_symm (𝕜 := ℂ) (T z) z]
    rfl
  have hn : ((‖z‖ : ℂ)^2).re=‖z‖^2 := by rw [← Complex.ofReal_pow]; rfl
  rw [hr,hn] at hi
  linarith

lemma residual_norm_sq (T : E ≃ₗᵢ[ℂ] E) (μ : ℝ)
    (hT : ∀ z, T z + T.symm z = (2*μ : ℂ) • z) (z : E) :
    ‖z-(μ : ℂ) • T z‖^2 = (1-μ^2)*‖z‖^2 ∧
    ‖(μ : ℂ) • z-T z‖^2 = (1-μ^2)*‖z‖^2 := by
  have hi := relative_re_inner T μ hT z
  have hn : ‖(μ : ℂ)‖^2=μ^2 := by simp [Complex.norm_real,Real.norm_eq_abs,sq_abs]
  constructor
  · rw [@norm_sub_sq ℂ, norm_smul,mul_pow,hn,T.norm_map,inner_smul_right]
    change _ - 2*((μ : ℂ)*inner ℂ z (T z)).re + _ = _
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [hi]
    ring
  · rw [@norm_sub_sq ℂ,norm_smul,mul_pow,hn,T.norm_map,inner_smul_left,Complex.conj_ofReal]
    change _ - 2*((μ : ℂ)*inner ℂ z (T z)).re + _ = _
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [hi]
    ring

/-- Low-to-high block with its actual signed-oracle filters. -/
def filterBlock (T : E ≃ₗᵢ[ℂ] E) (μ : ℝ) (y : HilbertPair E E) : HilbertPair E E :=
  WithLp.toLp 2
    ((alpha μ : ℂ) • (y.fst-T y.fst) + (beta μ : ℂ) • (y.snd+T y.snd),
     (beta μ : ℂ) • (y.fst+T y.fst) + (alpha μ : ℂ) • (y.snd-T y.snd))

lemma hadamard_filterBlock (T : E ≃ₗᵢ[ℂ] E) (μ : ℝ) (y : HilbertPair E E) :
    hadamard (filterBlock T μ y) = WithLp.toLp 2
      ((hadamard y).fst-(μ : ℂ) • T (hadamard y).fst,
       (μ : ℂ) • (hadamard y).snd-T (hadamard y).snd) := by
  apply (WithLp.equiv 2 (E × E)).injective
  apply Prod.ext
  · change (halfAmplitude : ℂ) •
      (((alpha μ : ℂ) • (y.fst-T y.fst)+(beta μ : ℂ) • (y.snd+T y.snd)) +
       ((beta μ : ℂ) • (y.fst+T y.fst)+(alpha μ : ℂ) • (y.snd-T y.snd))) =
      (halfAmplitude : ℂ) • (y.fst+y.snd) -
        (μ : ℂ) • T ((halfAmplitude : ℂ) • (y.fst+y.snd))
    simp only [map_smul,map_add]
    dsimp [alpha,beta]
    push_cast
    module
  · change (halfAmplitude : ℂ) •
      (((alpha μ : ℂ) • (y.fst-T y.fst)+(beta μ : ℂ) • (y.snd+T y.snd)) -
       ((beta μ : ℂ) • (y.fst+T y.fst)+(alpha μ : ℂ) • (y.snd-T y.snd))) =
      (μ : ℂ) • ((halfAmplitude : ℂ) • (y.fst-y.snd)) -
        T ((halfAmplitude : ℂ) • (y.fst-y.snd))
    simp only [map_smul,map_sub]
    dsimp [alpha,beta]
    push_cast
    module

lemma filterBlock_norm (T : E ≃ₗᵢ[ℂ] E) (μ s : ℝ) (hs : 0 ≤ s)
    (hcircle : μ^2+s^2=1)
    (hT : ∀ z, T z + T.symm z = (2*μ : ℂ) • z) (y : HilbertPair E E) :
    ‖filterBlock T μ y‖ = s*‖y‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hs (norm_nonneg _))).mp
  rw [← hadamard.norm_map (filterBlock T μ y),hadamard_filterBlock,
    WithLp.prod_norm_sq_eq_of_L2]
  simp only [WithLp.toLp_fst,WithLp.toLp_snd]
  rw [(residual_norm_sq T μ hT _).1,(residual_norm_sq T μ hT _).2]
  have hn := congrArg (fun r : ℝ => r^2) (hadamard.norm_map y)
  dsimp only at hn
  rw [WithLp.prod_norm_sq_eq_of_L2] at hn
  rw [mul_pow]
  nlinarith

lemma filterBlock_inner (T : E ≃ₗᵢ[ℂ] E) (μ : ℝ) (x y : HilbertPair E E) :
    inner ℂ x (filterBlock T μ y) =
      (alpha μ : ℂ)*(inner ℂ x.fst y.fst-inner ℂ x.fst (T y.fst)) +
      (beta μ : ℂ)*(inner ℂ x.fst y.snd+inner ℂ x.fst (T y.snd)) +
      (beta μ : ℂ)*(inner ℂ x.snd y.fst+inner ℂ x.snd (T y.fst)) +
      (alpha μ : ℂ)*(inner ℂ x.snd y.snd-inner ℂ x.snd (T y.snd)) := by
  simp only [filterBlock,WithLp.prod_inner_apply,WithLp.ofLp_toLp,WithLp.ofLp_fst,
    WithLp.ofLp_snd,inner_add_right,inner_sub_right,inner_smul_right]
  ring

/-- This is the operator-norm bound needed after the actual adversary
identity. It holds with arbitrary ancillary spaces, finite or infinite. -/
theorem filter_quadratic (T : E ≃ₗᵢ[ℂ] E) (μ s : ℝ) (hs : 0 ≤ s)
    (hcircle : μ^2+s^2=1)
    (hT : ∀ z, T z + T.symm z = (2*μ : ℂ) • z) (x y : HilbertPair E E) :
    2*(inner ℂ x (filterBlock T μ y)).re ≤ s*(‖x‖^2+‖y‖^2) := by
  have hb : (inner ℂ x (filterBlock T μ y)).re ≤ ‖x‖ * (s*‖y‖) := by
    calc
      _ ≤ ‖inner ℂ x (filterBlock T μ y)‖ := Complex.re_le_norm _
      _ ≤ ‖x‖*‖filterBlock T μ y‖ := norm_inner_le_norm _ _
      _ = _ := by rw [filterBlock_norm T μ s hs hcircle hT]
  nlinarith [mul_nonneg hs (sq_nonneg (‖x‖-‖y‖))]

end ELV.AdversaryFour
