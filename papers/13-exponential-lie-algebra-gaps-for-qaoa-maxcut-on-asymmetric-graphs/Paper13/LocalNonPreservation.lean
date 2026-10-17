import Paper13.LocalControls
import Paper13.InvariantBlocks
noncomputable section
namespace Paper13
open Matrix
attribute [local instance] Classical.propDecidable

/-- For a Hermitian control, invariance of an orthogonal projection's range forces commutation. -/
lemma commute_of_invariant_projection {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P A : Matrix ι ι ℂ) (hP : Pᴴ=P ∧ P*P=P) (hA : Aᴴ=A)
    (hinv : InvariantUnder {A} (LinearMap.range (Matrix.toLin' P))) : P*A=A*P := by
  have hPA : P*A*P=A*P := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    change (P*A*P).mulVec x=(A*P).mulVec x
    rw [←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec,←Matrix.mulVec_mulVec]
    have hm := hinv A (Set.mem_singleton A) (P.mulVec x) ⟨x,rfl⟩
    obtain ⟨y,hy⟩ := hm
    change P.mulVec y=A.mulVec (P.mulVec x) at hy
    rw [←hy,Matrix.mulVec_mulVec,hP.2]
  have hAP := congrArg Matrix.conjTranspose hPA
  simp only [conjTranspose_mul,hP.1,hA] at hAP
  rw [←mul_assoc] at hAP
  exact hAP.symm.trans hPA

lemma invariant_control_of_iMul {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ)
    (W : Submodule ℂ (ι → ℂ)) (hinv : InvariantUnder {Complex.I • A} W) : InvariantUnder {A} W := by
  intro B hB
  have hBA : B=A := Set.mem_singleton_iff.mp hB
  subst B
  intro w hw
  have h := hinv (Complex.I • A) (Set.mem_singleton _) w hw
  have hh := W.smul_mem (-Complex.I) h
  simpa only [Matrix.smul_mulVec,smul_smul,neg_mul,Complex.I_mul_I,neg_neg,one_smul] using hh

/-- Actual failure of invariance under every non-port individual mixer generator. -/
theorem local_sector_not_invariant_X (v : Fin 7) (hv : v≠4) :
    ¬InvariantUnder {iMul (Xv v)} (LinearMap.range (Matrix.toLin' localP)) := by
  intro h
  have hc := commute_of_invariant_projection localP (Xv v) localP_isOrthProj
    (embed_conjTranspose pauliX pauliX_conjTranspose v) (invariant_control_of_iMul _ _ h)
  exact localP_not_comm_X v hv (sub_eq_zero.mpr hc)

/-- Actual failure of invariance under every internal cost-edge generator. -/
theorem local_sector_not_invariant_ZZ (u v : Fin 7) (h : H.Adj u v) :
    ¬InvariantUnder {iMul (ZZ u v)} (LinearMap.range (Matrix.toLin' localP)) := by
  intro hi
  have hc := commute_of_invariant_projection localP (ZZ u v) localP_isOrthProj
    (ZZ_hermitian u v) (invariant_control_of_iMul _ _ hi)
  exact localP_not_comm_ZZ u v h (sub_eq_zero.mpr hc)
end Paper13
