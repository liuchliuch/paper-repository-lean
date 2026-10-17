import ELV.Hadamard
import ELV.Costs

noncomputable section
namespace ELV.Costs
open ELV.Stabilize

def publicCoordinates : Public ≃ₗᵢ[ℂ] HilbertPair ℂ ℂ where
  toLinearEquiv :=
    { toFun := fun v => WithLp.toLp 2 (v 0,v 1)
      invFun := fun z => WithLp.toLp 2 (fun i : Fin 2 => if i=0 then z.fst else z.snd)
      left_inv := by intro v; ext i; fin_cases i <;> simp
      right_inv := by intro z; rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  norm_map' v := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [WithLp.prod_norm_sq_eq_of_L2,PiLp.norm_sq_eq_of_L2]
    simp [Fin.sum_univ_succ]

@[simp] lemma publicCoordinates_basis0 : publicCoordinates (publicBasis 0)=WithLp.toLp 2 ((1 : ℂ),0) := by
  simp [publicCoordinates,publicBasis,EuclideanSpace.basisFun_apply,EuclideanSpace.single_apply]
@[simp] lemma publicCoordinates_basis1 : publicCoordinates (publicBasis 1)=WithLp.toLp 2 ((0 : ℂ),1) := by
  simp [publicCoordinates,publicBasis,EuclideanSpace.basisFun_apply,EuclideanSpace.single_apply]

end ELV.Costs
