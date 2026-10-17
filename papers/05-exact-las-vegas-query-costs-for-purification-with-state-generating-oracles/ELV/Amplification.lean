import ELV.CanonicalTransducer
import ELV.Oracle

/-! Arbitrary ancillary controls and both directions of the actual unitary
oracle. The amplification acts pointwise on square summable control coordinates. -/
noncomputable section
open scoped ENNReal
namespace ELV.Query
open ELV.Stabilize

variable {C E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma map_mem_lp (O : E ≃ₗᵢ[ℂ] E) (v : lp (fun _ : C => E) 2) :
    Memℓp (fun i => O (v i)) 2 := by
  have hv := lp.memℓp v
  simpa only [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal), O.norm_map] using hv

/-- The same oracle on every orthogonal control coordinate. -/
def amplify (O : E ≃ₗᵢ[ℂ] E) : lp (fun _ : C => E) 2 ≃ₗᵢ[ℂ] lp (fun _ : C => E) 2 where
  toLinearEquiv :=
    { toFun := fun v => ⟨fun i => O (v i), map_mem_lp O v⟩
      invFun := fun v => ⟨fun i => O.symm (v i), map_mem_lp O.symm v⟩
      left_inv := by intro v; ext i; exact O.symm_apply_apply _
      right_inv := by intro v; ext i; exact O.apply_symm_apply _
      map_add' := by intro v w; ext i; exact O.map_add _ _
      map_smul' := by intro c v; ext i; exact O.map_smul c _ }
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [@norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ]
    congr 1
    simp only [lp.inner_eq_tsum]
    apply tsum_congr
    intro i
    exact O.inner_map_map _ _

@[simp] theorem amplify_apply (O : E ≃ₗᵢ[ℂ] E) (v : lp (fun _ : C => E) 2) (i : C) :
    amplify O v i = O (v i) := rfl

end ELV.Query

namespace ELV.Model.Oracle
variable {n : ℕ}

/-- Finite-dimensional norm-preserving linear maps are surjective, so the
oracle data of `Oracle` canonically determines an actual unitary and its inverse. -/
def unitary (O : Oracle n) : Mspace n ≃ₗᵢ[ℂ] Mspace n :=
  LinearIsometryEquiv.ofSurjective
    { toLinearMap := O.U, norm_map' := O.norm_preserving }
    (by
      apply (LinearMap.injective_iff_surjective).mp
      exact LinearIsometry.injective
        { toLinearMap := O.U, norm_map' := O.norm_preserving })

@[simp] theorem unitary_apply (O : Oracle n) (v : Mspace n) : O.unitary v = O.U v := rfl

end ELV.Model.Oracle

namespace ELV.Query
open ELV.Stabilize ELV.Model

abbrev OracleQuerySpace (n : ℕ) (C : Type*) :=
  lp (fun _ : C => HilbertPair (Mspace n) (Mspace n)) 2

/-- Equation (2.3): controlled forward and inverse access to the entire
oracle, with arbitrary square summable ancillary controls. -/
def bidirectional {n : ℕ} (C : Type*) (O : Oracle n) :
    OracleQuerySpace n C ≃ₗᵢ[ℂ] OracleQuerySpace n C :=
  amplify (pairCongr O.unitary O.unitary.symm)

@[simp] theorem bidirectional_apply {n : ℕ} (C : Type*) (O : Oracle n)
    (v : OracleQuerySpace n C) (i : C) :
    (bidirectional C O v i).fst = O.unitary (v i).fst := rfl

@[simp] theorem bidirectional_apply_inv {n : ℕ} (C : Type*) (O : Oracle n)
    (v : OracleQuerySpace n C) (i : C) :
    (bidirectional C O v i).snd = O.unitary.symm (v i).snd := rfl

end ELV.Query
