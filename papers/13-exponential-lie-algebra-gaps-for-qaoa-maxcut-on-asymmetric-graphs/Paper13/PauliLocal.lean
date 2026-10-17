import Paper13.PauliLie
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

@[simp] lemma pauliXor_zero_right (a : Fin 4) : pauliXor a 0=a := by fin_cases a <;> rfl
@[simp] lemma pauliXor_zero_left (a : Fin 4) : pauliXor 0 a=a := rfl

def twoPauli {n : ℕ} (i j : Fin n) (a b : Fin 4) : Fin n → Fin 4 :=
  fun v => if v=i then a else if v=j then b else 0

lemma wordPhase_two_right {n : ℕ} (w : Fin n → Fin 4) (i j : Fin n) (hij : i≠j) (a b : Fin 4) :
    wordPhase w (twoPauli i j a b) = pauliPhase (w i) a * pauliPhase (w j) b := by
  unfold wordPhase
  rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i)]
  rw [Finset.prod_eq_mul_prod_diff_singleton (show j ∈ Finset.univ \ {i} by simp [hij.symm])]
  have hrest : (∏ v ∈ (Finset.univ \ {i}) \ {j}, pauliPhase (w v) (twoPauli i j a b v)) = 1 := by
    apply Finset.prod_eq_one
    intro v hv
    have h := Finset.mem_sdiff.mp hv
    have hi := Finset.mem_sdiff.mp h.1
    simp only [Finset.mem_singleton] at hi h
    simp [twoPauli,hi.2,h.2,pauliPhase]
  rw [hrest,mul_one]
  simp [twoPauli,hij.symm]

lemma wordPhase_two_left {n : ℕ} (w : Fin n → Fin 4) (i j : Fin n) (hij : i≠j) (a b : Fin 4) :
    wordPhase (twoPauli i j a b) w = pauliPhase a (w i) * pauliPhase b (w j) := by
  unfold wordPhase
  rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i)]
  rw [Finset.prod_eq_mul_prod_diff_singleton (show j ∈ Finset.univ \ {i} by simp [hij.symm])]
  have hrest : (∏ v ∈ (Finset.univ \ {i}) \ {j}, pauliPhase (twoPauli i j a b v) (w v)) = 1 := by
    apply Finset.prod_eq_one
    intro v hv
    have h := Finset.mem_sdiff.mp hv
    have hi := Finset.mem_sdiff.mp h.1
    simp only [Finset.mem_singleton] at hi h
    simp [twoPauli,hi.2,h.2,pauliPhase]
  rw [hrest,mul_one]
  simp [twoPauli,hij.symm]

lemma wordXor_two {n : ℕ} (w : Fin n → Fin 4) (i j : Fin n) (hij : i≠j) (a b : Fin 4) :
    wordXor w (twoPauli i j a b) = Function.update (Function.update w i (pauliXor (w i) a)) j (pauliXor (w j) b) := by
  funext v
  by_cases hi : v=i
  · subst v; simp [wordXor,twoPauli,hij,Function.update_of_ne]
  · by_cases hj : v=j
    · subst v; simp [wordXor,twoPauli,hi]
    · simp only [wordXor,twoPauli,if_neg hi,if_neg hj,Function.update_of_ne hi,Function.update_of_ne hj]
      generalize w v = a
      fin_cases a <;> rfl
lemma pauliWord_two {n : ℕ} (i j : Fin n) (hij : i≠j) (a b : Fin 4) :
    pauliWord (twoPauli i j a b) = embed (pauliLetter a) i * embed (pauliLetter b) j := by
  rw [←pauliWord_single,←pauliWord_single]
  simp only [pauliWord,tensorMatrix_mul]
  apply congrArg tensorMatrix
  funext v
  by_cases hi : v=i
  · subst v; simp [twoPauli,singlePauli,hij,pauliLetter]
  · by_cases hj : v=j
    · subst v; simp [twoPauli,singlePauli,hi,pauliLetter]
    · simp [twoPauli,singlePauli,hi,hj,pauliLetter]

lemma graphMa_word_step {n : ℕ} (G : SimpleGraph (Fin n)) (w t : Fin n → Fin 4)
    (i j : Fin n) (hij : i≠j) (a b : Fin 4)
    (hw : skewPauliWord w ∈ graphMa G) (hg : skewPauliWord (twoPauli i j a b) ∈ graphMa G)
    (ht : wordXor w (twoPauli i j a b)=t)
    (hp : (pauliPhase (w i) a * pauliPhase (w j) b=Complex.I ∧
           pauliPhase a (w i) * pauliPhase b (w j)= -Complex.I) ∨
          (pauliPhase (w i) a * pauliPhase (w j) b= -Complex.I ∧
           pauliPhase a (w i) * pauliPhase b (w j)=Complex.I)) :
    skewPauliWord t ∈ graphMa G := by
  rcases hp with ⟨hp,hq⟩ | ⟨hp,hq⟩
  · apply graphMa_word_bracket G _ _ _ hw hg (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two _ _ _ ht
    · rwa [wordPhase_two_right _ _ _ hij]
    · rwa [wordPhase_two_left _ _ _ hij]
  · apply graphMa_word_bracket G _ _ _ hw hg 2 (by norm_num)
    apply skewPauliWord_comm_two _ _ _ ht
    · rwa [wordPhase_two_right _ _ _ hij]
    · rwa [wordPhase_two_left _ _ _ hij]

/-- X controls rotate either end of a ZZ edge to Y. -/
theorem graphMa_two_YZ {n : ℕ} (G : SimpleGraph (Fin n)) (i j : Fin n) (hij : G.Adj i j)
    (a b : Fin 4) (ha : a=2 ∨ a=3) (hb : b=2 ∨ b=3) :
    skewPauliWord (twoPauli i j a b) ∈ graphMa G := by
  have hne := hij.ne
  have hZZ : skewPauliWord (twoPauli i j 3 3) ∈ graphMa G := by
    rw [skewPauliWord,pauliWord_two _ _ hne]
    exact graphMa_ZZ G i j hij
  have hXi : skewPauliWord (twoPauli i j 1 0) ∈ graphMa G := by
    have he : twoPauli i j 1 0=singlePauli i 1 := by
      funext v; simp [twoPauli,singlePauli]
    rw [he]; exact graphMa_single_X G i
  have hXj : skewPauliWord (twoPauli i j 0 1) ∈ graphMa G := by
    have he : twoPauli i j 0 1=singlePauli j 1 := by
      funext v
      by_cases hi : v=i
      · subst v; simp [twoPauli,singlePauli,hne]
      · simp [twoPauli,singlePauli,hi]
    rw [he]; exact graphMa_single_X G j
  have hYZ : skewPauliWord (twoPauli i j 2 3) ∈ graphMa G := by
    apply graphMa_word_step G _ _ i j hne 1 0 hZZ hXi
    · funext v
      simp only [wordXor,twoPauli]
      split_ifs <;> rfl
    · left; norm_num [twoPauli,hne.symm,pauliPhase]
  have hZY : skewPauliWord (twoPauli i j 3 2) ∈ graphMa G := by
    apply graphMa_word_step G _ _ i j hne 0 1 hZZ hXj
    · funext v
      simp only [wordXor,twoPauli]
      split_ifs <;> rfl
    · left; norm_num [twoPauli,hne.symm,pauliPhase]
  have hYY : skewPauliWord (twoPauli i j 2 2) ∈ graphMa G := by
    apply graphMa_word_step G _ _ i j hne 0 1 hYZ hXj
    · funext v
      simp only [wordXor,twoPauli]
      split_ifs <;> rfl
    · left; norm_num [twoPauli,hne.symm,pauliPhase]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact hYY
  · exact hYZ
  · exact hZY
  · exact hZZ
end Paper13
