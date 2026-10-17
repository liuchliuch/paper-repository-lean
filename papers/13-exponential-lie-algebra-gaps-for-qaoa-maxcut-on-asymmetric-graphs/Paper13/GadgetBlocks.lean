import Paper13.TensorBlocks
import Paper13.LocalProjector
import Paper13.LieDim
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators

lemma localQ_finrank : Module.finrank ℂ (LinearMap.range (Matrix.toLin' (1-localP))) = 126 := by
  rw [complement_projector_finrank localP localP_isOrthProj.2, localP_finrank_two]
  norm_num [QubitBasis, Fintype.card_fun]

/-- The actual 2^k independent gadget blocks. -/
def gadgetBlock (k : ℕ) (s : Fin k → Bool) : Matrix (Fin k → QubitBasis 7) (Fin k → QubitBasis 7) ℂ :=
  tensorMatrix (fun v => binaryFactor localP (s v))

lemma gadgetBlock_complete (k : ℕ) : ∑ s, gadgetBlock k s = 1 := binary_blocks_sum localP

lemma gadgetBlock_orthogonal (k : ℕ) (s t : Fin k → Bool) (hst : s ≠ t) :
    gadgetBlock k s * gadgetBlock k t = 0 := binary_blocks_orthogonal localP localP_isOrthProj.2 s t hst

/-- Exact squared-rank sum of the actual independent sector projectors. -/
theorem gadgetBlock_sum_rank_sq (k : ℕ) :
    (∑ s, (Module.finrank ℂ (LinearMap.range (Matrix.toLin' (gadgetBlock k s))))^2) = 15880^k := by
  have h := binary_blocks_sum_rank_sq (κ := Fin k) localP localP_isOrthProj.2
  simpa only [localP_finrank_two, localQ_finrank, Fintype.card_fin] using h

lemma gadgetBlock_rank_le (k : ℕ) (s : Fin k → Bool) :
    Module.finrank ℂ (LinearMap.range (Matrix.toLin' (gadgetBlock k s))) ≤ 126^k := by
  rw [gadgetBlock, tensorMatrix_finrank _ (fun v => binaryFactor_idem localP localP_isOrthProj.2 _)]
  have hb (v : Fin k) : Module.finrank ℂ (LinearMap.range (Matrix.toLin' (binaryFactor localP (s v)))) ≤ 126 := by
    cases hs : s v <;> simp [binaryFactor, hs, localP_finrank_two, localQ_finrank]
  calc _ ≤ ∏ _v : Fin k, (126 : ℕ) := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun v _ => hb v)
       _ = 126^k := by simp
end Paper13
