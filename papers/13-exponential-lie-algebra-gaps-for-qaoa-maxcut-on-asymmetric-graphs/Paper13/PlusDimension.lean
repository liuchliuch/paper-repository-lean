import Paper13.MatrixDimension
import Paper13.GraphDynamics
noncomputable section
namespace Paper13
open Matrix
attribute [local instance] Classical.propDecidable

def parityPlus (n : ℕ) : Op n := parityRefinement 1 (bitFlip n) 1

lemma parityPlus_range (n : ℕ) : LinearMap.range (Matrix.toLin' (parityPlus n))=plusSpace n := by
  have hFR : bitFlip n*parityPlus n=parityPlus n := by
    simp only [parityPlus,parityRefinement,one_smul,one_mul,Matrix.mul_smul,mul_add,mul_one,bitFlip_mul_self]
    module
  apply le_antisymm
  · rintro x ⟨y,rfl⟩
    change (bitFlip n).mulVec ((parityPlus n).mulVec y)-(parityPlus n).mulVec y=0
    rw [Matrix.mulVec_mulVec,hFR,sub_self]
  · intro x hx
    change (bitFlip n).mulVec x-x=0 at hx
    have hf : (bitFlip n).mulVec x=x := sub_eq_zero.mp hx
    refine ⟨x,?_⟩
    change (parityPlus n).mulVec x=x
    simp only [parityPlus,parityRefinement,one_smul,one_mul,Matrix.smul_mulVec,Matrix.add_mulVec,Matrix.one_mulVec,hf]
    ext v
    norm_num
    ring

/-- The actual positive-parity Hilbert space has dimension 2^(n-1). -/
theorem plusSpace_finrank (n : ℕ) (hn : 0 < n) : Module.finrank ℂ (plusSpace n)=2^(n-1) := by
  have ht : Matrix.trace ((1 : Op n)*bitFlip n)=0 := by rw [one_mul,bitFlip_trace_zero hn]
  have h := (parity_half_rank (1 : Op n) (bitFlip n) (one_mul _) (bitFlip_mul_self n)
    (by rw [one_mul,mul_one]) ht).1
  have hone : Module.finrank ℂ (LinearMap.range (Matrix.toLin' (1 : Op n)))=2^n := by
    rw [Matrix.toLin'_one,LinearMap.range_id]
    simp [QubitBasis,Fintype.card_fun]
  rw [hone,show parityRefinement (1 : Op n) (bitFlip n) 1=parityPlus n from rfl,parityPlus_range] at h
  have hp : 2^(n-1)*2=2^n := by rw [←pow_succ,show n-1+1=n by omega]
  omega
end Paper13
