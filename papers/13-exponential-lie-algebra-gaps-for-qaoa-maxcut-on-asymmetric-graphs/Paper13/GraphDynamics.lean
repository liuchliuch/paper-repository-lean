import Paper13.QubitParity
import Paper13.TensorControls
import Paper13.GraphOperators
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators

lemma embed_eq_liftSite {n : ℕ} (A : Op1) (v : Fin n) : embed A v = liftSite v A := by
  ext x y
  simp [embed,liftSite_entry]

lemma embed_mul {n : ℕ} (A B : Op1) (v : Fin n) : embed (A*B) v = embed A v * embed B v := by
  simpa only [embed_eq_liftSite] using liftSite_mul v A B

lemma embed_one {n : ℕ} (v : Fin n) : embed (1 : Op1) v = 1 := by
  simpa only [embed_eq_liftSite] using liftSite_one (ι := Fin 2) v

lemma embed_neg {n : ℕ} (A : Op1) (v : Fin n) : embed (-A) v = -embed A v := by
  simpa only [neg_one_smul,embed_eq_liftSite] using liftSite_smul v (-1) A

lemma embed_comm_disjoint {n : ℕ} (A B : Op1) (u v : Fin n) (huv : u ≠ v) :
    embed A u * embed B v = embed B v * embed A u := by
  rw [embed_eq_liftSite,embed_eq_liftSite]
  apply tensorMatrix_commute_liftSite
  simp [Ne.symm huv]

lemma Xv_sq {n : ℕ} (v : Fin n) : Xv v * Xv v = 1 := by
  rw [Xv,← embed_mul,pauliX_mul,embed_one]

lemma Zv_sq {n : ℕ} (v : Fin n) : Zv v * Zv v = 1 := by
  rw [Zv,← embed_mul,pauliZ_mul,embed_one]

lemma Xv_Zv_anticomm {n : ℕ} (v : Fin n) : Xv v * Zv v = -(Zv v * Xv v) := by
  rw [Xv,Zv,← embed_mul,pauliX_pauliZ_anticommute,embed_neg,embed_mul]

lemma trace_zero_of_anticomm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hB : B*B=1) (hAB : A*B=-(B*A)) : Matrix.trace A=0 := by
  have hconj : B*A*B = -A := by
    rw [mul_assoc, hAB, mul_neg, ← mul_assoc,hB,one_mul]
  have ht : Matrix.trace (B*A*B) = Matrix.trace A := by
    rw [Matrix.trace_mul_comm,← mul_assoc,hB,one_mul]
  rw [hconj,Matrix.trace_neg] at ht
  have hz : (2 : ℂ)*Matrix.trace A=0 := by linear_combination -ht
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

lemma trace_Xv {n : ℕ} (v : Fin n) : Matrix.trace (Xv v)=0 :=
  trace_zero_of_anticomm (Xv v) (Zv v) (Zv_sq v) (Xv_Zv_anticomm v)

lemma trace_ZZ {n : ℕ} (u v : Fin n) (huv : u ≠ v) : Matrix.trace (ZZ u v)=0 := by
  apply trace_zero_of_anticomm (ZZ u v) (Xv u) (Xv_sq u)
  have hc : Zv v*Xv u=Xv u*Zv v := embed_comm_disjoint pauliZ pauliX v u huv.symm
  have ha : Zv u*Xv u=-(Xv u*Zv u) := by rw [Xv_Zv_anticomm,neg_neg]
  rw [ZZ,mul_assoc,hc,← mul_assoc,ha,neg_mul,mul_assoc]

lemma HXFull_hermitian (n : ℕ) : (HXFull n)ᴴ=HXFull n := by
  simp only [HXFull,Matrix.conjTranspose_sum,Xv,embed_conjTranspose pauliX pauliX_conjTranspose]

lemma HXFull_trace (n : ℕ) : Matrix.trace (HXFull n)=0 := by
  simp [HXFull,Matrix.trace_sum,trace_Xv]

lemma ZZ_hermitian {n : ℕ} (u v : Fin n) : (ZZ u v)ᴴ=ZZ u v := by
  change (embed pauliZ u * embed pauliZ v)ᴴ= _
  rw [conjTranspose_mul,embed_conjTranspose pauliZ pauliZ_conjTranspose,
    embed_conjTranspose pauliZ pauliZ_conjTranspose]
  exact (Zv_commute v u).eq

lemma graphCost_hermitian {n : ℕ} (G : SimpleGraph (Fin n)) : (graphCost G)ᴴ=graphCost G := by
  simp only [graphCost,Matrix.conjTranspose_sum,ZZ_hermitian]

lemma graphCost_trace {n : ℕ} (G : SimpleGraph (Fin n)) : Matrix.trace (graphCost G)=0 := by
  classical
  rw [graphCost,Matrix.trace_sum]
  apply Finset.sum_eq_zero
  intro e he
  have hlt : e.1<e.2 := (Finset.mem_filter.mp he).2.1
  exact trace_ZZ e.1 e.2 (ne_of_lt hlt)

lemma bitFlip_comm_graphCost {n : ℕ} (G : SimpleGraph (Fin n)) : bitFlip n*graphCost G=graphCost G*bitFlip n := by
  simp only [graphCost,Finset.mul_sum,Finset.sum_mul,bitFlip_comm_ZZ]

lemma isLieSub_SkewHermOp (n : ℕ) : IsLieSub n (SkewHermOp n) := by
  intro A B hA hB
  change (A*B-B*A)ᴴ=-(A*B-B*A)
  change Aᴴ = -A at hA
  change Bᴴ = -B at hB
  simp only [conjTranspose_sub,conjTranspose_mul,hA,hB,neg_mul_neg]
  abel

lemma isLieSub_TracelessOp (n : ℕ) : IsLieSub n (TracelessOp n) := by
  intro A B hA hB
  change Matrix.trace (A*B-B*A)=0
  rw [Matrix.trace_sub,Matrix.trace_mul_comm,sub_self]

lemma graphStd_skew {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ A ∈ graphStd G, Aᴴ = -A := by
  apply lieClosure_le (L := SkewHermOp n) ?_ (isLieSub_SkewHermOp n)
  intro A hA
  rcases mem_stdGens_iff.mp hA with rfl | rfl
  · exact iMul_skew (HXFull_hermitian n)
  · exact iMul_skew (graphCost_hermitian G)

lemma graphStd_traceless {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ A ∈ graphStd G, Matrix.trace A=0 := by
  apply lieClosure_le (L := TracelessOp n) ?_ (isLieSub_TracelessOp n)
  intro A hA
  rcases mem_stdGens_iff.mp hA with rfl | rfl
  · change Matrix.trace (Complex.I • HXFull n)=0
    rw [Matrix.trace_smul,HXFull_trace,smul_zero]
  · change Matrix.trace (Complex.I • graphCost G)=0
    rw [Matrix.trace_smul,graphCost_trace,smul_zero]

lemma graphStd_comm_bitFlip {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∀ A ∈ graphStd G, A*bitFlip n=bitFlip n*A :=
  gStd_commutes (HXFull n) (graphCost G) (bitFlip n)
    (bitFlip_comm_mixer n).symm (bitFlip_comm_graphCost G).symm
end Paper13
