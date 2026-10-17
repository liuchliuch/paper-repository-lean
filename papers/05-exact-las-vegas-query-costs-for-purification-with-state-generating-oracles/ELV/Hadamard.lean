import ELV.HilbertSum

/-! The fixed Hadamard unitary on an orthogonal pair of Hilbert spaces. -/
noncomputable section
namespace ELV.Hilbert
open ELV.Stabilize
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def halfAmplitude : ℝ := 1/Real.sqrt 2
lemma halfAmplitude_sq : halfAmplitude^2 = (1/2 : ℝ) := by
  have hn := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  unfold halfAmplitude
  field_simp
  nlinarith

lemma twice_amplitude_sq : ((halfAmplitude : ℂ)*(halfAmplitude : ℂ))*2 = 1 := by
  rw [← pow_two,← Complex.ofReal_pow,halfAmplitude_sq]
  norm_num

lemma amplitude_norm_sq : ‖(halfAmplitude : ℂ)‖ ^ 2 = (1/2 : ℝ) := by
  simpa [Complex.norm_real,Real.norm_eq_abs,sq_abs] using halfAmplitude_sq

def hadamardFun (z : HilbertPair E E) : HilbertPair E E :=
  WithLp.toLp 2 ((halfAmplitude : ℂ) • (z.fst+z.snd),
    (halfAmplitude : ℂ) • (z.fst-z.snd))

lemma hadamardFun_involutive : Function.Involutive (hadamardFun (E := E)) := by
  intro z
  apply (WithLp.equiv 2 (E × E)).injective
  apply Prod.ext
  · change (halfAmplitude : ℂ) • ((halfAmplitude : ℂ) • (z.fst+z.snd) +
      (halfAmplitude : ℂ) • (z.fst-z.snd)) = z.fst
    calc
      _ = (((halfAmplitude : ℂ)*(halfAmplitude : ℂ))*2) • z.fst := by module
      _ = _ := by rw [twice_amplitude_sq,one_smul]
  · change (halfAmplitude : ℂ) • ((halfAmplitude : ℂ) • (z.fst+z.snd) -
      (halfAmplitude : ℂ) • (z.fst-z.snd)) = z.snd
    calc
      _ = (((halfAmplitude : ℂ)*(halfAmplitude : ℂ))*2) • z.snd := by module
      _ = _ := by rw [twice_amplitude_sq,one_smul]

/-- A unitary depending on no oracle data. -/
def hadamard : HilbertPair E E ≃ₗᵢ[ℂ] HilbertPair E E where
  toLinearEquiv :=
    { toFun := hadamardFun
      invFun := hadamardFun
      left_inv := hadamardFun_involutive
      right_inv := hadamardFun_involutive
      map_add' := by
        intro x y
        apply (WithLp.equiv 2 (E × E)).injective
        apply Prod.ext <;> dsimp [hadamardFun] <;> module
      map_smul' := by
        intro a x
        apply (WithLp.equiv 2 (E × E)).injective
        apply Prod.ext <;> dsimp [hadamardFun] <;> module }
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2,WithLp.prod_norm_sq_eq_of_L2]
    change ‖(halfAmplitude : ℂ) • (z.fst+z.snd)‖ ^ 2 +
      ‖(halfAmplitude : ℂ) • (z.fst-z.snd)‖ ^ 2 = _
    rw [norm_smul,norm_smul,mul_pow,mul_pow,amplitude_norm_sq]
    have hh := parallelogram_law_with_norm ℂ z.fst z.snd
    nlinarith

@[simp] lemma hadamard_apply (x y : E) :
    hadamard (WithLp.toLp 2 (x,y)) = WithLp.toLp 2
      ((halfAmplitude : ℂ) • (x+y),(halfAmplitude : ℂ) • (x-y)) := rfl

end ELV.Hilbert
