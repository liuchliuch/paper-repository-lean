import Paper13.GraphDynamics
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators

/-- An unnormalised Hadamard matrix; no square roots or analytic functional calculus are needed. -/
def hadamard2 : Op1 := !![1,1;1,-1]

def bitSign (b : Fin 2) : ℂ := if b=0 then 1 else -1

def bitWeight {n : ℕ} (x : QubitBasis n) : ℕ := (Finset.univ.filter (fun v => x v=1)).card

def walsh (n : ℕ) : Op n := tensorMatrix (fun _ : Fin n => hadamard2)
def mixerEigen {n : ℕ} (x : QubitBasis n) : ℂ := ∑ v, bitSign (x v)
def parityEigen {n : ℕ} (x : QubitBasis n) : ℂ := ∏ v, bitSign (x v)

lemma hadamard2_sq : hadamard2*hadamard2=(2 : ℂ) • (1 : Op1) := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [hadamard2,Matrix.mul_apply,Fin.sum_univ_two]

lemma hadamard2_X : hadamard2*pauliX=pauliZ*hadamard2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [hadamard2,pauliX,pauliZ,Matrix.mul_apply,Fin.sum_univ_two]

lemma X_hadamard2 : pauliX*hadamard2=hadamard2*pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [hadamard2,pauliX,pauliZ,Matrix.mul_apply,Fin.sum_univ_two]

lemma tensorMatrix_smul {κ ι : Type*} [Fintype κ] (z : κ → ℂ) (A : κ → Matrix ι ι ℂ) :
    tensorMatrix (fun v => z v • A v) = (∏ v, z v) • tensorMatrix A := by
  ext x y
  simp [tensorMatrix,Finset.prod_mul_distrib]

lemma walsh_sq (n : ℕ) : walsh n * walsh n = (2^n : ℂ) • (1 : Op n) := by
  simp only [walsh,tensorMatrix_mul,hadamard2_sq,tensorMatrix_smul,Finset.prod_const,
    Finset.card_univ,Fintype.card_fin,tensorMatrix_one]

lemma walsh_X {n : ℕ} (v : Fin n) : walsh n*Xv v=Zv v*walsh n := by
  simp only [Xv,Zv,embed_eq_liftSite,walsh,liftSite,tensorMatrix_mul]
  congr 1
  funext w
  by_cases hw : w=v
  · subst w; simp only [if_pos rfl]; exact hadamard2_X
  · simp [hw]

lemma X_walsh {n : ℕ} (v : Fin n) : Xv v*walsh n=walsh n*Zv v := by
  simp only [Xv,Zv,embed_eq_liftSite,walsh,liftSite,tensorMatrix_mul]
  congr 1
  funext w
  by_cases hw : w=v
  · subst w; simp only [if_pos rfl]; exact X_hadamard2
  · simp [hw]

lemma global_Z_diagonal (n : ℕ) : (∑ v : Fin n, Zv v)=Matrix.diagonal (mixerEigen : QubitBasis n → ℂ) := by
  simp only [Zv_diagonal]
  ext x y
  by_cases h : x=y
  · subst y; simp [Matrix.sum_apply,Matrix.diagonal,mixerEigen,bitSign]
  · simp [Matrix.sum_apply,Matrix.diagonal,h]

lemma walsh_mixer (n : ℕ) : walsh n*HXFull n=Matrix.diagonal mixerEigen*walsh n := by
  rw [HXFull,Finset.mul_sum]
  simp only [walsh_X]
  rw [← Finset.sum_mul,global_Z_diagonal]

lemma mixer_walsh (n : ℕ) : HXFull n*walsh n=walsh n*Matrix.diagonal mixerEigen := by
  rw [HXFull,Finset.sum_mul]
  simp only [X_walsh]
  rw [← Finset.mul_sum,global_Z_diagonal]

lemma bitFlip_tensorX (n : ℕ) : bitFlip n=tensorMatrix (fun _ : Fin n => pauliX) := by
  ext x y
  simp only [bitFlip,tensorMatrix,pauliX_eq]
  have he : y=flipState x ↔ ∀ v, x v ≠ y v := by
    constructor
    · intro hy v
      have hv := congrFun hy v
      change y v=1-x v at hv
      exact Ne.symm ((fin2_flip_iff _ _).mp hv)
    · intro hv
      funext v
      exact (fin2_flip_iff _ _).mpr (Ne.symm (hv v))
  by_cases hy : y=flipState x
  · rw [if_pos hy]
    simp only [if_neg (he.mp hy _),Finset.prod_const_one]
  · rw [if_neg hy]
    have hn : ∃ v, x v=y v := by simpa only [he,not_forall,not_not] using hy
    obtain ⟨v,hv⟩ := hn
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    exact if_pos hv

lemma tensor_Z_diagonal (n : ℕ) : tensorMatrix (fun _ : Fin n => pauliZ)=Matrix.diagonal parityEigen := by
  ext x y
  by_cases h : x=y
  · subst y
    simp [tensorMatrix,Matrix.diagonal,pauliZ_eq,parityEigen,bitSign]
  · obtain ⟨v,hv⟩ := Function.ne_iff.mp h
    rw [Matrix.diagonal_apply_ne _ h]
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    simp [tensorMatrix,pauliZ_eq,hv]

lemma walsh_parity (n : ℕ) : walsh n*bitFlip n=Matrix.diagonal parityEigen*walsh n := by
  simp only [walsh,bitFlip_tensorX,tensorMatrix_mul,hadamard2_X]
  rw [← tensorMatrix_mul,tensor_Z_diagonal]

lemma parity_walsh (n : ℕ) : bitFlip n*walsh n=walsh n*Matrix.diagonal parityEigen := by
  simp only [walsh,bitFlip_tensorX,tensorMatrix_mul,X_hadamard2]
  rw [← tensorMatrix_mul,tensor_Z_diagonal]

lemma mixerEigen_weight {n : ℕ} (x : QubitBasis n) : mixerEigen x=(n : ℂ)-2*bitWeight x := by
  have hb : ∀ b : Fin 2, bitSign b=1-2*(if b=1 then (1 : ℂ) else 0) := by
    intro b; fin_cases b <;> norm_num [bitSign]
  simp only [mixerEigen,hb,Finset.sum_sub_distrib,← Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Finset.sum_boole,bitWeight]

lemma parityEigen_weight {n : ℕ} (x : QubitBasis n) : parityEigen x=(-1 : ℂ)^bitWeight x := by
  have hb : ∀ b : Fin 2, bitSign b=(if b=1 then (-1 : ℂ) else 1) := by
    intro b; fin_cases b <;> norm_num [bitSign]
  simp [parityEigen,hb,Finset.prod_ite,bitWeight]

lemma parityEigen_eq_of_mixerEigen_eq {n : ℕ} (x y : QubitBasis n) (h : mixerEigen x=mixerEigen y) :
    parityEigen x=parityEigen y := by
  rw [mixerEigen_weight,mixerEigen_weight] at h
  have hw : (bitWeight x : ℂ)=(bitWeight y : ℂ) := by linear_combination (-1/2 : ℂ)*h
  have hn : bitWeight x=bitWeight y := by exact_mod_cast hw
  rw [parityEigen_weight,parityEigen_weight,hn]

/-- A matrix commuting with the shared mixer commutes with global bit flip.
This proves the functional dependence by an explicit Walsh diagonalization. -/
theorem commutes_bitFlip_of_commutes_mixer {n : ℕ} (P : Op n) (hP : P*HXFull n=HXFull n*P) :
    P*bitFlip n=bitFlip n*P := by
  let S := walsh n
  let D : Op n := Matrix.diagonal mixerEigen
  let E : Op n := Matrix.diagonal parityEigen
  have hSD : S*HXFull n=D*S := walsh_mixer n
  have hDS : HXFull n*S=S*D := mixer_walsh n
  have hSE : S*bitFlip n=E*S := walsh_parity n
  have hES : bitFlip n*S=S*E := parity_walsh n
  have hPD : (S*P*S)*D=D*(S*P*S) := by
    calc _ = S*P*(S*D) := by noncomm_ring
         _ = S*P*(HXFull n*S) := by rw [← hDS]
         _ = S*(P*HXFull n)*S := by noncomm_ring
         _ = S*(HXFull n*P)*S := by rw [hP]
         _ = (S*HXFull n)*P*S := by noncomm_ring
         _ = D*(S*P*S) := by rw [hSD]; noncomm_ring
  have hPE : (S*P*S)*E=E*(S*P*S) := by
    ext x y
    have hd := congrArg (fun M : Op n => M x y) hPD
    simp only [D,Matrix.mul_diagonal,Matrix.diagonal_mul] at hd
    dsimp only [E]
    rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
    by_cases he : mixerEigen x=mixerEigen y
    · rw [parityEigen_eq_of_mixerEigen_eq x y he]; ring
    · have hz : (S*P*S) x y=0 := by
        have hh : (S*P*S) x y*(mixerEigen x-mixerEigen y)=0 := by linear_combination -hd
        exact (mul_eq_zero.mp hh).resolve_right (sub_ne_zero.mpr he)
      rw [hz]; simp
  have hinj : Function.Injective (fun A : Op n => S*A*S) := by
    intro A B hab
    have hh := congrArg (fun M : Op n => S*M*S) hab
    have he (M : Op n) : S*(S*M*S)*S=((2^n : ℂ)*(2^n : ℂ)) • M := by
      calc _ = (S*S)*M*(S*S) := by noncomm_ring
           _ = _ := by rw [show S*S=(2^n : ℂ) • (1 : Op n) from walsh_sq n]; simp [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    dsimp only at hh
    rw [he,he] at hh
    have hc : (2^n : ℂ)*(2^n : ℂ) ≠ 0 := mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
    have hi := congrArg (fun M : Op n => (((2^n : ℂ)*(2^n : ℂ))⁻¹) • M) hh
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hi
  apply hinj
  calc _ = S*P*(bitFlip n*S) := by noncomm_ring
       _ = S*P*(S*E) := by rw [hES]
       _ = (S*P*S)*E := by noncomm_ring
       _ = E*(S*P*S) := hPE
       _ = (E*S)*P*S := by noncomm_ring
       _ = (S*bitFlip n)*P*S := by rw [← hSE]
       _ = S*(bitFlip n*P)*S := by noncomm_ring
end Paper13
