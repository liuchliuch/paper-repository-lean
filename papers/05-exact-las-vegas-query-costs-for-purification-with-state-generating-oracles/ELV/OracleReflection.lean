import ELV.Amplification
import ELV.LineParameters

/-! The actual pulled-back answer reflection O inverse Z O, and its
expectation at the fixed known input for every oracle completion. -/
noncomputable section
namespace ELV.Model
variable {n : ℕ}

/-- The known answer reflection Z=+1 on answer 0 and -1 on answer 1. -/
def answerReflection (n : ℕ) : Mspace n ≃ₗᵢ[ℂ] Mspace n where
  toLinearEquiv :=
    { toFun := fun v => WithLp.toLp 2 (fun i => if n ≤ i.val then -v i else v i)
      invFun := fun v => WithLp.toLp 2 (fun i => if n ≤ i.val then -v i else v i)
      left_inv := by
        intro v
        apply (WithLp.equiv 2 _).injective
        funext i
        by_cases hi : n ≤ i.val <;> simp [hi]
      right_inv := by
        intro v
        apply (WithLp.equiv 2 _).injective
        funext i
        by_cases hi : n ≤ i.val <;> simp [hi]
      map_add' := by
        intro v w
        apply (WithLp.equiv 2 _).injective
        funext i
        by_cases hi : n ≤ i.val <;> simp [hi,add_comm]
      map_smul' := by
        intro c v
        apply (WithLp.equiv 2 _).injective
        funext i
        by_cases hi : n ≤ i.val <;> simp [hi] }
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [PiLp.norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : n ≤ i.val <;> simp [hi]

@[simp] theorem answerReflection_apply (v : Mspace n) (i : Fin (2*n)) :
    answerReflection n v i = if n ≤ i.val then -v i else v i := rfl

@[simp] theorem answerReflection_involutive (v : Mspace n) :
    answerReflection n (answerReflection n v) = v := by
  apply (WithLp.equiv 2 _).injective
  funext i
  by_cases hi : n ≤ i.val <;> simp [hi]

lemma answerReflection_expectation (v : Mspace n) :
    inner ℂ v (answerReflection n v) =
      ((∑ i : Fin (2*n), ‖v i‖ ^ 2) - 2*(∑ i : Fin (2*n), if n ≤ i.val then ‖v i‖ ^ 2 else 0) : ℝ) := by
  have hterm (i : Fin (2*n)) : inner ℂ (v i) (if n ≤ i.val then -v i else v i) =
      ((‖v i‖ ^ 2 : ℝ) : ℂ) - 2*((if n ≤ i.val then ‖v i‖ ^ 2 else 0 : ℝ) : ℂ) := by
    have hself : inner ℂ (v i) (v i) = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_pow] using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (v i))
    by_cases hi : n ≤ i.val
    · simp only [if_pos hi,inner_neg_right,hself]
      ring
    · simp only [if_neg hi,hself,Complex.ofReal_zero,mul_zero,sub_zero]

  change (∑ i : Fin (2*n),inner ℂ (v i) (if n ≤ i.val then -v i else v i)) = _
  simp_rw [hterm]
  push_cast
  rw [Finset.sum_sub_distrib,← Finset.mul_sum]

namespace Oracle
variable [NeZero n]

/-- The reflection in (3.1), using the full actual oracle and its inverse. -/
def pulledReflection (O : Oracle n) : Mspace n ≃ₗᵢ[ℂ] Mspace n :=
  O.unitary.trans ((answerReflection n).trans O.unitary.symm)

@[simp] lemma pulledReflection_apply (O : Oracle n) (v : Mspace n) :
    O.pulledReflection v = O.unitary.symm (answerReflection n (O.unitary v)) := rfl

@[simp] lemma pulledReflection_involutive (O : Oracle n) (v : Mspace n) :
    O.pulledReflection (O.pulledReflection v) = v := by
  simp only [pulledReflection_apply,LinearIsometryEquiv.apply_symm_apply,
    answerReflection_involutive,LinearIsometryEquiv.symm_apply_apply]

/-- The actual generated state determines the known-input expectation, but
no assumption on the unitary completion is made. -/
theorem pulledReflection_expectation (O : Oracle n) :
    inner ℂ (knownInput n) (O.pulledReflection (knownInput n)) = (1-2*O.p : ℝ) := by
  have hs : (∑ i : Fin (2*n), ‖O.phi i‖ ^ 2) = 1 := by
    rw [← PiLp.norm_sq_eq_of_L2, O.phi_norm]
    norm_num
  calc
    _ = inner ℂ (O.unitary (knownInput n)) (O.unitary (O.pulledReflection (knownInput n))) :=
      (O.unitary.inner_map_map _ _).symm
    _ = inner ℂ O.phi (answerReflection n O.phi) := by
      rw [pulledReflection_apply,LinearIsometryEquiv.apply_symm_apply]
      rfl
    _ = _ := by rw [answerReflection_expectation,hs]; rfl

end Oracle
end ELV.Model
