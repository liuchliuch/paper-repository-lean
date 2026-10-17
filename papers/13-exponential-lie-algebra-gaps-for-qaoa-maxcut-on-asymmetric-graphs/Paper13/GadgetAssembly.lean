import Paper13.AssemblyCost
import Paper13.GraphDynamics
import Paper13.GadgetBlocks
import Paper13.ParityBlocks
import Mathlib.LinearAlgebra.Matrix.Rank
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators

lemma graphCost_H : graphCost H = Hzz_H := by
  have hm : ∀ u v : Fin 7, (u<v ∧ H.Adj u v) ↔
      (u,v) ∈ ({(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(1,5),(2,5)} : Finset (Fin 7 × Fin 7)) := by decide
  have he : graphEdges H = ({(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(1,5),(2,5)} : Finset (Fin 7 × Fin 7)) := by
    ext ⟨u,v⟩
    simp only [graphEdges,Finset.mem_filter,Finset.mem_univ,true_and]
    exact hm u v
  rw [graphCost,he]
  repeat rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_singleton]
  dsimp [Hzz_H]
  abel

lemma localP_comm_full_mixer : localP*HXFull 7=HXFull 7*localP := by
  have he : HXFull 7 = Xv (0 : Fin 7)+Xv 1+Xv 2+Xv 3+Xv 4+Xv 5+Xv 6 := by
    simp [HXFull,Fin.sum_univ_succ]
    abel
  rw [he]
  exact localP_comm_HX

lemma binary_local_comm (s : Bool) (A : Op 7) (h : localP*A=A*localP) :
    binaryFactor localP s*A=A*binaryFactor localP s := by
  cases s <;> simp [binaryFactor,sub_mul,mul_sub,h]

lemma Gk_cost_assembly (k : ℕ) :
    assemblyReindex k 7 (graphCost (GkOrdinal k)) =
      (∑ v : Fin k, liftSite v Hzz_H) +
      ∑ e ∈ graphEdges (T k), liftSite e.1 (Zv (4 : Fin 7))*liftSite e.2 (Zv (4 : Fin 7)) := by
  have h := assemblyReindex_cost H Hport (T k)
  rw [graphCost_H] at h
  exact h

lemma gadgetBlock_comm_mixer (k : ℕ) (s : Fin k → Bool) :
    gadgetBlock k s * assemblyReindex k 7 (HXFull (k*7)) =
      assemblyReindex k 7 (HXFull (k*7))*gadgetBlock k s := by
  rw [assemblyReindex_mixer]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  exact tensorMatrix_commute_liftSite (fun w => binaryFactor localP (s w)) v (HXFull 7)
    (binary_local_comm _ _ localP_comm_full_mixer)

lemma gadgetBlock_comm_cost (k : ℕ) (s : Fin k → Bool) :
    gadgetBlock k s * assemblyReindex k 7 (graphCost (GkOrdinal k)) =
      assemblyReindex k 7 (graphCost (GkOrdinal k))*gadgetBlock k s := by
  have hi (v : Fin k) : Commute (gadgetBlock k s) (liftSite v Hzz_H) :=
    tensorMatrix_commute_liftSite _ v Hzz_H (binary_local_comm _ _ (by rw [localP_mul_Hzz_H,Hzz_H_mul_localP]))
  have hp (v : Fin k) : Commute (gadgetBlock k s) (liftSite v (Zv (4 : Fin 7))) :=
    tensorMatrix_commute_liftSite _ v (Zv 4) (binary_local_comm _ _ localP_comm_Z4)
  rw [Gk_cost_assembly, mul_add,add_mul,Finset.mul_sum,Finset.sum_mul,Finset.mul_sum,Finset.sum_mul]
  congr 1
  · exact Finset.sum_congr rfl (fun v hv => (hi v).eq)
  · exact Finset.sum_congr rfl (fun e he => ((hp e.1).mul_right (hp e.2)).eq)

/-- Actual joint projectors on the original kh-qubit computational basis. -/
def actualGadgetBlock (k : ℕ) (s : Fin k → Bool) : Op (k*7) :=
  (assemblyReindex k 7).symm (gadgetBlock k s)

lemma actualGadgetBlock_sum (k : ℕ) : ∑ s, actualGadgetBlock k s=1 := by
  apply (assemblyReindex k 7).injective
  simp only [map_sum,actualGadgetBlock,AlgEquiv.apply_symm_apply,map_one,gadgetBlock_complete]

lemma actualGadgetBlock_idem (k : ℕ) (s : Fin k → Bool) :
    actualGadgetBlock k s * actualGadgetBlock k s=actualGadgetBlock k s := by
  apply (assemblyReindex k 7).injective
  simp only [map_mul,actualGadgetBlock,AlgEquiv.apply_symm_apply]
  exact tensorMatrix_idem _ (fun v => binaryFactor_idem localP localP_isOrthProj.2 _)

lemma actualGadgetBlock_rank (k : ℕ) (s : Fin k → Bool) :
    Module.finrank ℂ (LinearMap.range (Matrix.toLin' (actualGadgetBlock k s))) =
      Module.finrank ℂ (LinearMap.range (Matrix.toLin' (gadgetBlock k s))) := by
  have h := Matrix.rank_reindex (assemblyBasis k 7) (assemblyBasis k 7) (gadgetBlock k s)
  simpa only [actualGadgetBlock,assemblyReindex,Matrix.reindexAlgEquiv_symm,Matrix.reindexAlgEquiv_apply,
    Matrix.rank,← Matrix.toLin'_apply'] using h

lemma actualGadgetBlock_comm_std (k : ℕ) : ∀ A ∈ graphStd (GkOrdinal k), ∀ s,
    A*actualGadgetBlock k s=actualGadgetBlock k s*A := by
  intro A hA s
  apply gStd_commutes (HXFull (k*7)) (graphCost (GkOrdinal k)) (actualGadgetBlock k s) ?_ ?_ A hA
  · apply (assemblyReindex k 7).injective
    simpa only [map_mul,actualGadgetBlock,AlgEquiv.apply_symm_apply] using (gadgetBlock_comm_mixer k s).symm
  · apply (assemblyReindex k 7).injective
    simpa only [map_mul,actualGadgetBlock,AlgEquiv.apply_symm_apply] using (gadgetBlock_comm_cost k s).symm

lemma actualGadgetBlock_comm_parity (k : ℕ) (s : Fin k → Bool) :
    actualGadgetBlock k s * bitFlip (k*7)=bitFlip (k*7)*actualGadgetBlock k s := by
  apply (assemblyReindex k 7).injective
  simp only [map_mul,actualGadgetBlock,AlgEquiv.apply_symm_apply,assemblyReindex_bitFlip,gadgetBlock,tensorMatrix_mul]
  congr 1
  funext v
  exact binary_local_comm _ _ localP_comm_bitFlip

lemma actualGadgetBlock_parity_trace (k : ℕ) (hk : 1 ≤ k) (s : Fin k → Bool) :
    Matrix.trace (actualGadgetBlock k s * bitFlip (k*7))=0 := by
  rw [← assemblyReindex_trace, map_mul]
  simp only [actualGadgetBlock,AlgEquiv.apply_symm_apply,assemblyReindex_bitFlip,gadgetBlock,tensorMatrix_mul,tensorMatrix_trace]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨0,by omega⟩ : Fin k))
  cases hs : s ⟨0,by omega⟩ <;> simp [binaryFactor,hs,localP_parity_trace,localQ_parity_trace]

/-- The actual standard Lie algebra dimension upper bound of Theorem 1. -/
theorem Gk_std_dimension (k : ℕ) (hk : 1 ≤ k) :
    Module.finrank ℝ (graphStd (GkOrdinal k)) ≤ 15880^k/2-1 := by
  have h := parity_block_dimension_bound (graphStd (GkOrdinal k)) (actualGadgetBlock k) (bitFlip (k*7))
    (actualGadgetBlock_sum k) (actualGadgetBlock_idem k) (bitFlip_mul_self _)
    (actualGadgetBlock_comm_parity k) (actualGadgetBlock_parity_trace k hk)
    (graphStd_skew _) (graphStd_traceless _) (actualGadgetBlock_comm_std k) (graphStd_comm_bitFlip _)
  simpa only [actualGadgetBlock_rank,gadgetBlock_sum_rank_sq] using h

/-- Every actual irreducible constituent has the claimed exponentially smaller dimension. -/
theorem Gk_irreducible_dimension (k : ℕ) (hk : 1 ≤ k)
    (W : Submodule ℂ (QubitBasis (k*7) → ℂ))
    (hW : IrreducibleOn (graphStd (GkOrdinal k) : Set (Op (k*7))) W) :
    Module.finrank ℂ W ≤ 126^k/2 := by
  apply parity_block_irrep_bound (graphStd (GkOrdinal k)) (actualGadgetBlock k) (bitFlip (k*7))
    (actualGadgetBlock_sum k) (actualGadgetBlock_idem k) (bitFlip_mul_self _)
    (actualGadgetBlock_comm_parity k) (actualGadgetBlock_parity_trace k hk)
    (actualGadgetBlock_comm_std k) (graphStd_comm_bitFlip _) (126^k) ?_ W hW
  intro s
  rw [actualGadgetBlock_rank]
  exact gadgetBlock_rank_le k s
end Paper13
