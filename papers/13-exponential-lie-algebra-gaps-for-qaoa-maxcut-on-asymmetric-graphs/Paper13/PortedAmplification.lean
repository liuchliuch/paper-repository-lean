import Paper13.AssemblyCost
import Paper13.GraphDynamics
import Paper13.MixerParity
import Paper13.ParityBlocks
import Mathlib.LinearAlgebra.Matrix.Rank
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators Kronecker
set_option maxHeartbeats 1200000

def portReindex {h : ℕ} (p : Fin (h+1)) : Op (h+1) ≃ₐ[ℂ] Matrix (Fin 2 × QubitBasis h) (Fin 2 × QubitBasis h) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (Fin.insertNthEquiv (fun _ : Fin (h+1) => Fin 2) p).symm

lemma insertNth_off_port {h : ℕ} (p : Fin (h+1)) (x y : Fin 2 × QubitBasis h) :
    (∀ w, w ≠ p → Fin.insertNth (α := fun _ : Fin (h+1) => Fin 2) p x.1 x.2 w=Fin.insertNth (α := fun _ : Fin (h+1) => Fin 2) p y.1 y.2 w) ↔ x.2=y.2 := by
  constructor
  · intro ho
    funext i
    simpa only [Fin.insertNth_apply_succAbove] using ho (p.succAbove i) (Fin.succAbove_ne _ _)
  · intro he w hw
    obtain ⟨i,rfl⟩ := Fin.exists_succAbove_eq hw
    simpa only [Fin.insertNth_apply_succAbove] using congrFun he i

lemma portReindex_embed {h : ℕ} (p : Fin (h+1)) (A : Op1) :
    portReindex p (embed A p)=A ⊗ₖ (1 : Op h) := by
  ext x y
  change (if (∀ w, w ≠ p → Fin.insertNth (α := fun _ : Fin (h+1) => Fin 2) p x.1 x.2 w=Fin.insertNth (α := fun _ : Fin (h+1) => Fin 2) p y.1 y.2 w)
    then A (Fin.insertNth (α := fun _ : Fin (h+1) => Fin 2) p x.1 x.2 p) (Fin.insertNth (α := fun _ : Fin (h+1) => Fin 2) p y.1 y.2 p) else 0) = A x.1 y.1*(1 : Op h) x.2 y.2
  simp only [insertNth_off_port,Fin.insertNth_apply_same,Matrix.one_apply]
  split_ifs <;> simp_all

lemma PortedGadget.comm_port {h : ℕ} (K : PortedGadget h) (A : Op1) :
    K.projector*embed A K.port=embed A K.port*K.projector := by
  apply (portReindex K.port).injective
  simp only [map_mul,show portReindex K.port K.projector=(1 : Op1) ⊗ₖ K.remainingProjector from K.port_factor,
    portReindex_embed,← Matrix.mul_kronecker_mul,one_mul,mul_one]

lemma PortedGadget.comm_parity {h : ℕ} (K : PortedGadget h) :
    K.projector*bitFlip (h+1)=bitFlip (h+1)*K.projector :=
  commutes_bitFlip_of_commutes_mixer K.projector K.comm_mixer

lemma PortedGadget.parity_trace {h : ℕ} (K : PortedGadget h) :
    Matrix.trace (K.projector*bitFlip (h+1))=0 :=
  trace_mul_bitFlip_of_commute_port K.projector K.port (K.comm_port pauliZ)

lemma binaryFactor_comm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P A : Matrix ι ι ℂ) (h : P*A=A*P) (b : Bool) :
    binaryFactor P b*A=A*binaryFactor P b := by
  cases b <;> simp [binaryFactor,sub_mul,mul_sub,h]

/-- All actual joint binary projectors, expressed on the original qubit basis. -/
def assemblyBlock {h : ℕ} (k : ℕ) (P : Op h) (s : Fin k → Bool) : Op (k*h) :=
  (assemblyReindex k h).symm (tensorMatrix (fun v => binaryFactor P (s v)))

lemma assemblyBlock_sum {h : ℕ} (k : ℕ) (P : Op h) : ∑ s, assemblyBlock k P s=1 := by
  apply (assemblyReindex k h).injective
  simp only [assemblyBlock,map_sum,AlgEquiv.apply_symm_apply,map_one,binary_blocks_sum]

lemma assemblyBlock_idem {h : ℕ} (k : ℕ) (P : Op h) (hP : P*P=P) (s : Fin k → Bool) :
    assemblyBlock k P s*assemblyBlock k P s=assemblyBlock k P s := by
  apply (assemblyReindex k h).injective
  simp only [assemblyBlock,map_mul,AlgEquiv.apply_symm_apply]
  exact tensorMatrix_idem _ (fun v => binaryFactor_idem P hP _)

lemma assemblyBlock_rank {h : ℕ} (k : ℕ) (P : Op h) (s : Fin k → Bool) :
    Module.finrank ℂ (LinearMap.range (Matrix.toLin' (assemblyBlock k P s))) =
      Module.finrank ℂ (LinearMap.range (Matrix.toLin' (tensorMatrix (fun v => binaryFactor P (s v))))) := by
  have hr := Matrix.rank_reindex (assemblyBasis k h) (assemblyBasis k h) (tensorMatrix (fun v => binaryFactor P (s v)))
  simpa only [assemblyBlock,assemblyReindex,Matrix.reindexAlgEquiv_symm,Matrix.reindexAlgEquiv_apply,
    Matrix.rank,← Matrix.toLin'_apply'] using hr

lemma assemblyBlock_comm_parity {h : ℕ} (k : ℕ) (P : Op h) (hP : P*bitFlip h=bitFlip h*P) (s : Fin k → Bool) :
    assemblyBlock k P s*bitFlip (k*h)=bitFlip (k*h)*assemblyBlock k P s := by
  apply (assemblyReindex k h).injective
  simp only [assemblyBlock,map_mul,AlgEquiv.apply_symm_apply,assemblyReindex_bitFlip,tensorMatrix_mul]
  congr 1
  funext v
  exact binaryFactor_comm P _ hP _

lemma assemblyBlock_parity_trace {h : ℕ} (k : ℕ) (hk : 1 ≤ k) (P : Op h)
    (htrace : Matrix.trace (P*bitFlip h)=0) (hFtrace : Matrix.trace (bitFlip h)=0) (s : Fin k → Bool) :
    Matrix.trace (assemblyBlock k P s*bitFlip (k*h))=0 := by
  rw [← assemblyReindex_trace,map_mul]
  simp only [assemblyBlock,AlgEquiv.apply_symm_apply,assemblyReindex_bitFlip,tensorMatrix_mul,tensorMatrix_trace]
  apply Finset.prod_eq_zero (Finset.mem_univ (⟨0,by omega⟩ : Fin k))
  cases hs : s ⟨0,by omega⟩ <;> simp [binaryFactor,hs,sub_mul,one_mul,Matrix.trace_sub,htrace,hFtrace]

lemma assemblyBlock_comm_std {h k : ℕ} (K : PortedGadget h) (B : SimpleGraph (Fin k)) :
    ∀ A ∈ graphStd (portedAssemblyOrdinal K B), ∀ s,
      A*assemblyBlock k K.projector s=assemblyBlock k K.projector s*A := by
  intro A hA s
  apply gStd_commutes (HXFull (k*(h+1))) (graphCost (portedAssemblyOrdinal K B)) (assemblyBlock k K.projector s) ?_ ?_ A hA
  · apply (assemblyReindex k (h+1)).injective
    simp only [map_mul,assemblyBlock,AlgEquiv.apply_symm_apply,assemblyReindex_mixer,Finset.mul_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro v hv
    exact (tensorMatrix_commute_liftSite _ v _ (binaryFactor_comm _ _ K.comm_mixer _)).symm
  · apply (assemblyReindex k (h+1)).injective
    have hcost : assemblyReindex k (h+1) (graphCost (portedAssemblyOrdinal K B)) =
        (∑ v : Fin k, liftSite v (graphCost K.graph)) +
        ∑ e ∈ graphEdges B, liftSite e.1 (Zv K.port)*liftSite e.2 (Zv K.port) :=
      assemblyReindex_cost K.graph K.port B
    simp only [map_mul,assemblyBlock,AlgEquiv.apply_symm_apply]
    rw [hcost,mul_add,add_mul,Finset.mul_sum,Finset.sum_mul,Finset.mul_sum,Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro v hv
      exact (tensorMatrix_commute_liftSite _ v _ (binaryFactor_comm _ _ K.comm_cost _)).symm
    · apply Finset.sum_congr rfl
      intro e he
      have hc (v : Fin k) : Commute (tensorMatrix (fun w => binaryFactor K.projector (s w))) (liftSite v (Zv K.port)) :=
        tensorMatrix_commute_liftSite _ v _ (binaryFactor_comm _ _ (K.comm_port pauliZ) _)
      exact ((hc e.1).mul_right (hc e.2)).symm.eq

lemma assemblyBlock_sum_rank_sq {h : ℕ} (k : ℕ) (P : Op h) (hP : P*P=P) :
    let r := Module.finrank ℂ (LinearMap.range (Matrix.toLin' P))
    (∑ s, (Module.finrank ℂ (LinearMap.range (Matrix.toLin' (assemblyBlock k P s))))^2) =
      (r^2+(2^h-r)^2)^k := by
  dsimp only
  simp only [assemblyBlock_rank]
  have he : Fintype.card (QubitBasis h)=2^h := by simp [QubitBasis]
  simpa only [complement_projector_finrank P hP,he,Fintype.card_fin] using binary_blocks_sum_rank_sq (κ := Fin k) P hP

lemma assemblyBlock_rank_le {h : ℕ} (k : ℕ) (P : Op h) (hP : P*P=P) (s : Fin k → Bool) :
    let r := Module.finrank ℂ (LinearMap.range (Matrix.toLin' P))
    Module.finrank ℂ (LinearMap.range (Matrix.toLin' (assemblyBlock k P s))) ≤ (max r (2^h-r))^k := by
  dsimp only
  let r := Module.finrank ℂ (LinearMap.range (Matrix.toLin' P))
  have he : Fintype.card (QubitBasis h)=2^h := by simp [QubitBasis]
  have hf (b : Bool) : Module.finrank ℂ (LinearMap.range (Matrix.toLin' (binaryFactor P b))) =
      if b then r else 2^h-r := by
    cases b <;> simp [binaryFactor,r,complement_projector_finrank P hP,he]
  rw [assemblyBlock_rank,tensorMatrix_finrank _ (fun v => binaryFactor_idem P hP _)]
  simp only [hf]
  calc _ ≤ ∏ _v : Fin k, max r (2^h-r) := by
        apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
        intro v hv
        split_ifs
        · exact le_max_left _ _
        · exact le_max_right _ _
       _ = _ := by simp [r]

/-- The original two bounds of Proposition 5, derived for the actual assembly algebra and every actual irreducible subspace. -/
theorem ported_amplification_bounds {h k : ℕ} (hk : 1 ≤ k) (K : PortedGadget h) (B : SimpleGraph (Fin k)) :
    let r := Module.finrank ℂ (LinearMap.range (Matrix.toLin' K.projector))
    let d := 2^(h+1)
    Module.finrank ℝ (graphStd (portedAssemblyOrdinal K B)) ≤ (r^2+(d-r)^2)^k/2-1 ∧
    ∀ W : Submodule ℂ (QubitBasis (k*(h+1)) → ℂ),
      IrreducibleOn (graphStd (portedAssemblyOrdinal K B) : Set (Op (k*(h+1)))) W →
      Module.finrank ℂ W ≤ (max r (d-r))^k/2 := by
  let R := assemblyBlock k K.projector
  have hR := assemblyBlock_idem k K.projector K.orthogonal.2
  have hcomm := assemblyBlock_comm_parity k K.projector K.comm_parity
  have htr := assemblyBlock_parity_trace k hk K.projector K.parity_trace (bitFlip_trace_zero (by omega : 0 < h+1))
  have hLR := assemblyBlock_comm_std K B
  constructor
  · have hc := parity_block_dimension_bound (graphStd (portedAssemblyOrdinal K B)) R (bitFlip (k*(h+1)))
      (assemblyBlock_sum k K.projector) hR (bitFlip_mul_self _) hcomm htr
      (graphStd_skew _) (graphStd_traceless _) hLR (graphStd_comm_bitFlip _)
    rw [assemblyBlock_sum_rank_sq k K.projector K.orthogonal.2] at hc
    exact hc
  · intro W hW
    exact parity_block_irrep_bound (graphStd (portedAssemblyOrdinal K B)) R (bitFlip (k*(h+1)))
      (assemblyBlock_sum k K.projector) hR (bitFlip_mul_self _) hcomm htr hLR (graphStd_comm_bitFlip _)
      _ (assemblyBlock_rank_le k K.projector K.orthogonal.2) W hW
end Paper13
