import Paper13.PauliConstraints
noncomputable section
namespace Paper13
open Matrix
attribute [local instance] Classical.propDecidable

lemma graphMa_skew {n : ℕ} (G : SimpleGraph (Fin n)) : ∀ A ∈ graphMa G, Aᴴ= -A := by
  apply lieClosure_le (L := SkewHermOp n) ?_ (isLieSub_SkewHermOp n)
  rintro A (⟨v,rfl⟩ | ⟨e,he,rfl⟩)
  · exact iMul_skew (by exact embed_conjTranspose pauliX pauliX_conjTranspose v)
  · exact iMul_skew (ZZ_hermitian _ _)

lemma graphMa_traceless {n : ℕ} (G : SimpleGraph (Fin n)) : ∀ A ∈ graphMa G, Matrix.trace A=0 := by
  apply lieClosure_le (L := TracelessOp n) ?_ (isLieSub_TracelessOp n)
  rintro A (⟨v,rfl⟩ | ⟨e,he,rfl⟩)
  · change Matrix.trace (Complex.I • Xv v)=0
    rw [Matrix.trace_smul,trace_Xv,smul_zero]
  · change Matrix.trace (Complex.I • ZZ e.1 e.2)=0
    rw [Matrix.trace_smul,trace_ZZ _ _ (ne_of_lt (Finset.mem_filter.mp he).2.1),smul_zero]

lemma graphMa_comm_bitFlip {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ A ∈ graphMa G, A*bitFlip n=bitFlip n*A := by
  apply lieClosure_commutes
  rintro A (⟨v,rfl⟩ | ⟨e,he,rfl⟩)
  · simp only [iMul,Matrix.smul_mul,Matrix.mul_smul,bitFlip_comm_X]
  · simp only [iMul,Matrix.smul_mul,Matrix.mul_smul,bitFlip_comm_ZZ]

lemma graphMa_tracelessFlip {n : ℕ} (hn : 2 ≤ n) (G : SimpleGraph (Fin n)) :
    ∀ A ∈ graphMa G, Matrix.trace (A*bitFlip n)=0 := by
  let L : Submodule ℝ (Op n) := CommuteBitFlip n ⊓ TracelessFlip n
  have hL : IsLieSub n L := by
    intro A B hA hB
    constructor
    · change (A*B-B*A)*bitFlip n=bitFlip n*(A*B-B*A)
      have hp (C D : Op n) (hC : C*bitFlip n=bitFlip n*C) (hD : D*bitFlip n=bitFlip n*D) :
          C*D*bitFlip n=bitFlip n*(C*D) := by rw [mul_assoc,hD,←mul_assoc,hC,mul_assoc]
      rw [sub_mul,mul_sub,hp A B hA.1 hB.1,hp B A hB.1 hA.1]
    · change Matrix.trace ((A*B-B*A)*bitFlip n)=0
      rw [sub_mul,Matrix.trace_sub]
      have hB' : B*bitFlip n=bitFlip n*B := hB.1
      have ht : Matrix.trace (A*B*bitFlip n)=Matrix.trace (B*A*bitFlip n) := by
        rw [mul_assoc,hB',←mul_assoc,Matrix.trace_mul_comm (A*bitFlip n) B,mul_assoc]
      rw [ht,sub_self]
  have h : graphMa G ≤ L := by
    apply lieClosure_le ?_ hL
    rintro A (⟨v,rfl⟩ | ⟨e,he,rfl⟩)
    · constructor
      · change (Complex.I • Xv v)*bitFlip n=bitFlip n*(Complex.I • Xv v)
        simp only [iMul,Matrix.smul_mul,Matrix.mul_smul,bitFlip_comm_X]
      · change Matrix.trace ((Complex.I • Xv v)*bitFlip n)=0
        rw [Matrix.smul_mul,Matrix.trace_smul]
        have hj : ∃ j : Fin n, j≠v := by
          let z : Fin n := ⟨0,by omega⟩
          let o : Fin n := ⟨1,by omega⟩
          by_cases hv : v=z
          · exact ⟨o,by subst v; exact Fin.ne_of_val_ne (by change (1 : ℕ)≠0; omega)⟩
          · exact ⟨z,Ne.symm hv⟩
        obtain ⟨j,hj⟩ := hj
        rw [trace_mul_bitFlip_of_commute_port (Xv v) j (embed_comm_disjoint pauliX pauliZ v j hj.symm),smul_zero]
    · constructor
      · change (Complex.I • ZZ e.1 e.2)*bitFlip n=bitFlip n*(Complex.I • ZZ e.1 e.2)
        simp only [iMul,Matrix.smul_mul,Matrix.mul_smul,bitFlip_comm_ZZ]
      · change Matrix.trace ((Complex.I • ZZ e.1 e.2)*bitFlip n)=0
        rw [Matrix.smul_mul,Matrix.trace_smul]
        have hc : ZZ e.1 e.2 * Zv e.1=Zv e.1 * ZZ e.1 e.2 := by
          exact ((Commute.refl (Zv e.1)).mul_left (Zv_commute e.2 e.1)).eq
        rw [trace_mul_bitFlip_of_commute_port (ZZ e.1 e.2) e.1 hc,smul_zero]
  exact fun A hA => (h hA).2
end Paper13
