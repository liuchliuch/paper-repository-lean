import Paper13.InvariantGap
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 4000
set_option maxHeartbeats 1200000

lemma tensorMatrix_uniform {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]
    (A : κ → Matrix ι ι ℂ) :
    (tensorMatrix A).mulVec (fun _ => 1)=fun x => ∏ v, (A v).mulVec (fun _ => 1) (x v) := by
  funext x
  simp only [Matrix.mulVec,dotProduct,mul_one,tensorMatrix]
  exact (Fintype.prod_sum (fun v y => A v (x v) y)).symm

lemma reindex_uniform {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (A : Matrix ι ι ℂ) (x : ι) :
    (Matrix.reindex e e A).mulVec (fun _ => 1) (e x)=A.mulVec (fun _ => 1) x := by
  simp only [Matrix.mulVec,dotProduct,mul_one,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
  exact Equiv.sum_comp e.symm (fun y => A x y)

lemma localQ_uniform : (1-localP).mulVec (fun _ => 1)=fun _ => 1 := by
  rw [Matrix.sub_mulVec,localP_uniform,Matrix.one_mulVec,sub_zero]

lemma actualQBlock_uniform (k : ℕ) :
    (actualGadgetBlock k (fun _ => false)).mulVec (fun _ => 1)=fun _ => 1 := by
  have h : (gadgetBlock k (fun _ => false)).mulVec (fun _ => 1)=fun _ => 1 := by
    funext x
    change (∑ y : Fin k → QubitBasis 7, (∏ v, (1-localP) (x v) (y v))*1)=1
    simp only [mul_one]
    calc
      _ = ∏ v : Fin k, ∑ y : QubitBasis 7, (1-localP) (x v) y := (Fintype.prod_sum (fun v y => (1-localP) (x v) y)).symm
      _ = 1 := by
        apply Finset.prod_eq_one
        intro v hv
        simpa only [Matrix.mulVec,dotProduct,mul_one] using congrFun localQ_uniform (x v)
  funext x
  obtain ⟨y,rfl⟩ := (assemblyBasis k 7).surjective x
  change (Matrix.reindex (assemblyBasis k 7) (assemblyBasis k 7) (gadgetBlock k (fun _ => false))).mulVec _ _ = 1
  rw [reindex_uniform,h]

lemma bitFlip_uniform (n : ℕ) : (bitFlip n).mulVec (fun _ => 1)=fun _ => 1 := by
  funext x
  simp only [Matrix.mulVec,dotProduct,mul_one,bitFlip]
  rw [Fintype.sum_eq_single (flipState x)]
  · simp
  · intro y hy; simp [hy]

/-- The positive-parity, all-complement joint sector containing the QAOA initial state. -/
def initialSectorProjector (k : ℕ) : Op (k*7) :=
  parityRefinement (actualGadgetBlock k (fun _ => false)) (bitFlip (k*7)) 1

lemma initialSector_fixes_uniform (k : ℕ) :
    (initialSectorProjector k).mulVec (fun _ => 1)=fun _ => 1 := by
  simp only [initialSectorProjector,parityRefinement,one_smul,Matrix.smul_mulVec,Matrix.add_mulVec,
    ←Matrix.mulVec_mulVec,actualQBlock_uniform,bitFlip_uniform]
  ext x
  norm_num

/-- Scalar normalization of |+>^N leaves the sector unchanged. -/
lemma initialSector_fixes_plus (k : ℕ) (z : ℂ) :
    (initialSectorProjector k).mulVec (z • (fun _ : QubitBasis (k*7) => (1 : ℂ)))=z • (fun _ : QubitBasis (k*7) => (1 : ℂ)) := by
  rw [Matrix.mulVec_smul,initialSector_fixes_uniform]

lemma actualQBlock_rank (k : ℕ) :
    Module.finrank ℂ (LinearMap.range (Matrix.toLin' (actualGadgetBlock k (fun _ => false))))=126^k := by
  rw [actualGadgetBlock_rank,gadgetBlock,tensorMatrix_finrank]
  · simp [binaryFactor,localQ_finrank]
  · intro v
    exact binaryFactor_idem localP localP_isOrthProj.2 false

/-- Exact rank of the initial-state sector, with one global parity split. -/
theorem initialSector_rank (k : ℕ) (hk : 1 ≤ k) :
    Module.finrank ℂ (LinearMap.range (Matrix.toLin' (initialSectorProjector k)))=126^k/2 := by
  have h := (parity_half_rank (actualGadgetBlock k (fun _ => false)) (bitFlip (k*7))
    (actualGadgetBlock_idem k _) (bitFlip_mul_self _) (actualGadgetBlock_comm_parity k _)
    (actualGadgetBlock_parity_trace k hk _)).1
  rw [actualQBlock_rank] at h
  change Module.finrank ℂ (LinearMap.range (Matrix.toLin' (parityRefinement _ _ 1)))=126^k/2
  omega

lemma initialSector_comm_std (k : ℕ) : ∀ A ∈ graphStd (GkOrdinal k),
    A*initialSectorProjector k=initialSectorProjector k*A := by
  intro A hA
  have hQ := actualGadgetBlock_comm_std k A hA (fun _ => false)
  have hF := graphStd_comm_bitFlip (GkOrdinal k) A hA
  have hQF : A*(actualGadgetBlock k (fun _ => false)*bitFlip (k*7))=
      (actualGadgetBlock k (fun _ => false)*bitFlip (k*7))*A := by
    rw [←mul_assoc,hQ,mul_assoc,hF,←mul_assoc]
  simp only [initialSectorProjector,parityRefinement,one_smul,Matrix.mul_smul,Matrix.smul_mul,mul_add,add_mul,hQ,hQF]

theorem initialSector_invariant (k : ℕ) :
    InvariantUnder (graphStd (GkOrdinal k) : Set (Op (k*7)))
      (LinearMap.range (Matrix.toLin' (initialSectorProjector k))) := by
  rintro A hA x ⟨y,rfl⟩
  refine ⟨A.mulVec y,?_⟩
  change (initialSectorProjector k).mulVec (A.mulVec y)=A.mulVec ((initialSectorProjector k).mulVec y)
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,initialSector_comm_std k A hA]
end Paper13
