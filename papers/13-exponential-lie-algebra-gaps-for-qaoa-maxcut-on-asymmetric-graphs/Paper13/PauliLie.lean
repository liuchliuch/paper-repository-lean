import Paper13.PauliWords
import Paper13.QubitEmbedding
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

lemma skewPauliWord_comm {n : ℕ} (w z : Fin n → Fin 4) :
    comm (skewPauliWord w) (skewPauliWord z) =
      (wordPhase z w - wordPhase w z) • pauliWord (wordXor w z) := by
  have hx : wordXor z w = wordXor w z := by
    funext v
    change pauliXor (z v) (w v) = pauliXor (w v) (z v)
    generalize w v = a
    generalize z v = b
    fin_cases a <;> fin_cases b <;> rfl
  have hm (a b : Fin n → Fin 4) : skewPauliWord a * skewPauliWord b = -(pauliWord a * pauliWord b) := by
    simp only [skewPauliWord,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    norm_num [Complex.I_mul_I]
  rw [comm,hm w z,hm z w,pauliWord_mul,pauliWord_mul,hx]
  module

lemma skewPauliWord_comm_neg_two {n : ℕ} (w z t : Fin n → Fin 4)
    (ht : wordXor w z=t) (hp : wordPhase w z=Complex.I) (hq : wordPhase z w= -Complex.I) :
    comm (skewPauliWord w) (skewPauliWord z) = (-2 : ℝ) • skewPauliWord t := by
  rw [skewPauliWord_comm,ht,hp,hq]
  ext x y
  simp only [skewPauliWord,Matrix.smul_apply,smul_eq_mul,Complex.real_smul]
  push_cast
  ring

lemma skewPauliWord_comm_two {n : ℕ} (w z t : Fin n → Fin 4)
    (ht : wordXor w z=t) (hp : wordPhase w z= -Complex.I) (hq : wordPhase z w=Complex.I) :
    comm (skewPauliWord w) (skewPauliWord z) = (2 : ℝ) • skewPauliWord t := by
  rw [skewPauliWord_comm,ht,hp,hq]
  ext x y
  simp only [skewPauliWord,Matrix.smul_apply,smul_eq_mul,Complex.real_smul]
  push_cast
  ring

lemma graphMa_word_bracket {n : ℕ} (G : SimpleGraph (Fin n)) (w z t : Fin n → Fin 4)
    (hw : skewPauliWord w ∈ graphMa G) (hz : skewPauliWord z ∈ graphMa G)
    (c : ℝ) (hc : c ≠ 0) (h : comm (skewPauliWord w) (skewPauliWord z)=c • skewPauliWord t) :
    skewPauliWord t ∈ graphMa G := by
  have hh : c • skewPauliWord t ∈ graphMa G := h ▸ lieClosure_comm hw hz
  have hhh := (graphMa G).smul_mem c⁻¹ hh
  simpa [smul_smul,hc] using hhh

def singlePauli {n : ℕ} (i : Fin n) (a : Fin 4) : Fin n → Fin 4 := fun v => if v=i then a else 0

lemma pauliWord_single {n : ℕ} (i : Fin n) (a : Fin 4) : pauliWord (singlePauli i a)=embed (pauliLetter a) i := by
  rw [embed_eq_liftSite]
  apply congrArg tensorMatrix
  funext v
  simp only [singlePauli]
  split_ifs <;> rfl

lemma pauliWord_single_X {n : ℕ} (i : Fin n) : pauliWord (singlePauli i 1)=Xv i :=
  pauliWord_single i 1
lemma pauliWord_single_Z {n : ℕ} (i : Fin n) : pauliWord (singlePauli i 3)=Zv i :=
  pauliWord_single i 3

lemma graphMa_single_X {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) :
    skewPauliWord (singlePauli i 1) ∈ graphMa G := by
  rw [skewPauliWord,pauliWord_single_X]
  exact subset_lieClosure (Or.inl ⟨i,rfl⟩)

def pairZPauli {n : ℕ} (i j : Fin n) : Fin n → Fin 4 := fun v => if v=i ∨ v=j then 3 else 0

lemma pauliWord_pair_Z {n : ℕ} (i j : Fin n) (hij : i≠j) : pauliWord (pairZPauli i j)=ZZ i j := by
  rw [ZZ,←pauliWord_single_Z,←pauliWord_single_Z]
  simp only [pauliWord,tensorMatrix_mul]
  apply congrArg tensorMatrix
  funext v
  by_cases hi : v=i
  · subst v; simp [pairZPauli,singlePauli,hij,pauliLetter]
  · by_cases hj : v=j
    · subst v; simp [pairZPauli,singlePauli,hi,pauliLetter]
    · simp [pairZPauli,singlePauli,hi,hj,pauliLetter]

lemma graphMa_ZZ {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) (h : G.Adj i j) :
    Complex.I • ZZ i j ∈ graphMa G := by
  apply subset_lieClosure
  right
  rcases lt_or_gt_of_ne h.ne with hij | hij
  · exact ⟨(i,j),by simp [graphEdges,hij,h],rfl⟩
  · refine ⟨(j,i),by simp [graphEdges,hij,G.symm h],?_⟩
    congr 1
    exact (Zv_commute _ _).eq

lemma graphMa_pair_Z {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) (h : G.Adj i j) :
    skewPauliWord (pairZPauli i j) ∈ graphMa G := by
  rw [skewPauliWord,pauliWord_pair_Z i j h.ne]
  exact graphMa_ZZ G i j h
end Paper13
