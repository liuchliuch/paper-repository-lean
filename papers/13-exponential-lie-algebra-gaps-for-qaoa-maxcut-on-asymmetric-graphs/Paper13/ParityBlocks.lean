import Paper13.BlockDimension
import Paper13.InvariantBlocks
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators

/-- Both global parity pieces of each joint block. -/
def refinedBlock {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (R : β → Matrix ι ι ℂ) (F : Matrix ι ι ℂ) (b : β × Bool) : Matrix ι ι ℂ :=
  parityRefinement (R b.1) F (if b.2 then 1 else -1)

lemma parityRefinement_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R F : Matrix ι ι ℂ) : parityRefinement R F 1 + parityRefinement R F (-1) = R := by
  simp only [parityRefinement]
  module

lemma refinedBlock_sum {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (R : β → Matrix ι ι ℂ) (F : Matrix ι ι ℂ) (hsum : ∑ b, R b = 1) :
    ∑ b, refinedBlock R F b = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,refinedBlock,Bool.false_eq_true,↓reduceIte]
  have hs (b : β) : parityRefinement (R b) F (-1) + parityRefinement (R b) F 1 = R b := by
    rw [add_comm,parityRefinement_sum]
  simpa only [parityRefinement_sum] using hsum

lemma refinedBlock_commute {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (R : β → Matrix ι ι ℂ) (F A : Matrix ι ι ℂ)
    (hR : ∀ b, A*R b=R b*A) (hF : A*F=F*A) (b : β × Bool) :
    A*refinedBlock R F b = refinedBlock R F b*A := by
  have hRF : A*(R b.1*F)=(R b.1*F)*A := by rw [← mul_assoc,hR,mul_assoc,hF,← mul_assoc]
  simp only [refinedBlock,parityRefinement,Matrix.mul_smul,Matrix.smul_mul,mul_add,add_mul,hR,hRF]

/-- Each parity-refined rank is exactly half of the actual joint block rank. -/
lemma refinedBlock_twice_rank {ι β : Type*} [Fintype ι] [DecidableEq ι]
    (R : β → Matrix ι ι ℂ) (F : Matrix ι ι ℂ)
    (hR : ∀ b, R b*R b=R b) (hF : F*F=1)
    (hcomm : ∀ b, R b*F=F*R b) (htrace : ∀ b, Matrix.trace (R b*F)=0) (b : β × Bool) :
    2 * Module.finrank ℂ (LinearMap.range (Matrix.toLin' (refinedBlock R F b))) =
      Module.finrank ℂ (LinearMap.range (Matrix.toLin' (R b.1))) := by
  have hp := parity_half_rank (R b.1) F (hR _) hF (hcomm _) (htrace _)
  rcases b with ⟨b,s⟩
  cases s
  · exact hp.2
  · exact hp.1

/-- Squared-rank sums lose exactly a single global factor of two. -/
theorem refinedBlock_rank_square_sum {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (R : β → Matrix ι ι ℂ) (F : Matrix ι ι ℂ)
    (hR : ∀ b, R b*R b=R b) (hF : F*F=1)
    (hcomm : ∀ b, R b*F=F*R b) (htrace : ∀ b, Matrix.trace (R b*F)=0) :
    (∑ b, (Module.finrank ℂ (LinearMap.range (Matrix.toLin' (refinedBlock R F b))))^2) =
      (∑ b, (Module.finrank ℂ (LinearMap.range (Matrix.toLin' (R b))))^2)/2 := by
  have htwice : 2 * (∑ b, (Module.finrank ℂ (LinearMap.range (Matrix.toLin' (refinedBlock R F b))))^2) =
      ∑ b, (Module.finrank ℂ (LinearMap.range (Matrix.toLin' (R b))))^2 := by
    rw [Fintype.sum_prod_type,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Fintype.sum_bool]
    have hp := refinedBlock_twice_rank R F hR hF hcomm htrace (b,true)
    have hm := refinedBlock_twice_rank R F hR hF hcomm htrace (b,false)
    nlinarith
  omega

/-- Apply the genuine block dimension theorem after the global parity refinement. -/
theorem parity_block_dimension_bound {ι β : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype β]
    (L : Submodule ℝ (Matrix ι ι ℂ)) (R : β → Matrix ι ι ℂ) (F : Matrix ι ι ℂ)
    (hsum : ∑ b, R b=1) (hR : ∀ b, R b*R b=R b) (hF : F*F=1)
    (hcomm : ∀ b, R b*F=F*R b) (htrace : ∀ b, Matrix.trace (R b*F)=0)
    (hskew : ∀ A ∈ L, Aᴴ = -A) (htr : ∀ A ∈ L, Matrix.trace A=0)
    (hLR : ∀ A ∈ L, ∀ b, A*R b=R b*A) (hLF : ∀ A ∈ L, A*F=F*A) :
    Module.finrank ℝ L ≤ (∑ b, (Module.finrank ℂ (LinearMap.range (Matrix.toLin' (R b))))^2)/2-1 := by
  have h := traceless_skew_block_bound L (refinedBlock R F) (refinedBlock_sum R F hsum) hskew
    (fun A hA b => refinedBlock_commute R F A (hLR A hA) (hLF A hA) b) htr
  rw [refinedBlock_rank_square_sum R F hR hF hcomm htrace] at h
  exact h

/-- Every irreducible constituent injects into one of the actual parity-refined blocks. -/
theorem parity_block_irrep_bound {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    (L : Submodule ℝ (Matrix ι ι ℂ)) (R : β → Matrix ι ι ℂ) (F : Matrix ι ι ℂ)
    (hsum : ∑ b, R b=1) (hR : ∀ b, R b*R b=R b) (hF : F*F=1)
    (hcomm : ∀ b, R b*F=F*R b) (htrace : ∀ b, Matrix.trace (R b*F)=0)
    (hLR : ∀ A ∈ L, ∀ b, A*R b=R b*A) (hLF : ∀ A ∈ L, A*F=F*A)
    (D : ℕ) (hD : ∀ b, Module.finrank ℂ (LinearMap.range (Matrix.toLin' (R b))) ≤ D)
    (W : Submodule ℂ (ι → ℂ)) (hW : IrreducibleOn (L : Set (Matrix ι ι ℂ)) W) :
    Module.finrank ℂ W ≤ D/2 := by
  obtain ⟨b,hb⟩ := irreducible_le_one_block (L : Set (Matrix ι ι ℂ)) W hW (refinedBlock R F)
    (fun b A hA => (refinedBlock_commute R F A (hLR A hA) (hLF A hA) b).symm) (refinedBlock_sum R F hsum)
  have hp := refinedBlock_twice_rank R F hR hF hcomm htrace b
  have hd := hD b.1
  omega
end Paper13
