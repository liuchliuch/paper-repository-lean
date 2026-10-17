import Paper13.PauliReach
noncomputable section
namespace Paper13
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def pauliGrade (a : Fin 4) : ℤ := if a.val < 2 then 1 else -1
def wordGrade {n : ℕ} (w : Fin n → Fin 4) : ℤ := ∏ v, pauliGrade (w v)
def wordSupport {n : ℕ} (w : Fin n → Fin 4) : Finset (Fin n) := Finset.univ.filter (fun v => w v ≠ 0)
def EvenPauli {n : ℕ} (w : Fin n → Fin 4) : Prop := wordGrade w=1
def AdmissiblePauli {n : ℕ} (w : Fin n → Fin 4) : Prop :=
  EvenPauli w ∧ w ≠ (fun _ => 0) ∧ w ≠ (fun _ => 1)

@[simp] lemma pauliGrade_zero : pauliGrade 0=1 := rfl
@[simp] lemma pauliGrade_one : pauliGrade 1=1 := rfl
@[simp] lemma pauliGrade_two : pauliGrade 2= -1 := rfl
@[simp] lemma pauliGrade_three : pauliGrade 3= -1 := rfl
lemma pauliGrade_sq (a : Fin 4) : pauliGrade a * pauliGrade a=1 := by fin_cases a <;> rfl
lemma wordGrade_sq {n : ℕ} (w : Fin n → Fin 4) : wordGrade w * wordGrade w=1 := by
  rw [wordGrade,← Finset.prod_mul_distrib]
  simp [pauliGrade_sq]

lemma wordGrade_update {n : ℕ} (w : Fin n → Fin 4) (i : Fin n) (a : Fin 4) :
    wordGrade (Function.update w i a)=pauliGrade a * pauliGrade (w i) * wordGrade w := by
  have he : (fun v => pauliGrade (Function.update w i a v)) = Function.update (fun v => pauliGrade (w v)) i (pauliGrade a) := by
    funext v
    by_cases h : v=i
    · subst v; simp
    · simp [h]
  unfold wordGrade
  rw [he,Finset.prod_update_of_mem (Finset.mem_univ i),Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ i)]
  have hg := pauliGrade_sq (w i)
  linear_combination -(pauliGrade a * ∏ x ∈ Finset.univ \ {i}, pauliGrade (w x)) * hg

lemma pairChange_eq_update {n : ℕ} (w : Fin n → Fin 4) (i j : Fin n) (hij : i≠j) (a b : Fin 4) :
    pairChange w i j a b=Function.update (Function.update w i a) j b := by
  funext v
  by_cases hi : v=i
  · subst v; simp [pairChange,hij]
  · by_cases hj : v=j
    · subst v; simp [pairChange,hi]
    · simp [pairChange,hi,hj]

lemma triplePauli_eq_update {n : ℕ} (w : Fin n → Fin 4) (i j k : Fin n)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) (a b c : Fin 4) :
    triplePauli w i j k a b c=Function.update (Function.update (Function.update w i a) j b) k c := by
  funext v
  by_cases hi : v=i
  · subst v; simp [triplePauli,hij,hik]
  · by_cases hj : v=j
    · subst v; simp [triplePauli,hi,hjk]
    · by_cases hk : v=k
      · subst v; simp [triplePauli,hi,hj]
      · simp [triplePauli,hi,hj,hk]

lemma wordGrade_pairChange {n : ℕ} (w : Fin n → Fin 4) (i j : Fin n) (hij : i≠j) (a b : Fin 4) :
    wordGrade (pairChange w i j a b)=pauliGrade a * pauliGrade (w i) * pauliGrade b * pauliGrade (w j) * wordGrade w := by
  rw [pairChange_eq_update _ _ _ hij,wordGrade_update,wordGrade_update]
  simp only [Function.update_of_ne hij.symm]
  ring

lemma wordGrade_triple {n : ℕ} (w : Fin n → Fin 4) (i j k : Fin n)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) (a b c : Fin 4) :
    wordGrade (triplePauli w i j k a b c)=pauliGrade a * pauliGrade (w i) * pauliGrade b * pauliGrade (w j) *
      pauliGrade c * pauliGrade (w k) * wordGrade w := by
  rw [triplePauli_eq_update _ _ _ _ hij hik hjk]
  simp only [wordGrade_update,Function.update_of_ne hik.symm,Function.update_of_ne hjk.symm,Function.update_of_ne hij.symm]
  ring

lemma wordSupport_mem {n : ℕ} (w : Fin n → Fin 4) (v : Fin n) : v ∈ wordSupport w ↔ w v ≠ 0 := by
  simp [wordSupport]

lemma wordSupport_update_zero {n : ℕ} (w : Fin n → Fin 4) (i : Fin n) :
    wordSupport (Function.update w i 0)=(wordSupport w).erase i := by
  ext v
  by_cases hv : v=i <;> simp [wordSupport,hv]

lemma wordSupport_update_nonzero {n : ℕ} (w : Fin n → Fin 4) (i : Fin n) (a : Fin 4) (ha : a≠0) :
    wordSupport (Function.update w i a)=insert i (wordSupport w) := by
  ext v
  by_cases hv : v=i <;> simp [wordSupport,hv,ha]

lemma wordGrade_single {n : ℕ} (i : Fin n) (a : Fin 4) : wordGrade (singlePauli i a)=pauliGrade a := by
  have he : singlePauli i a=Function.update (fun _ => 0) i a := by
    funext v
    by_cases h : v=i
    · subst v; simp [singlePauli]
    · simp [singlePauli,h]
  rw [he,wordGrade_update]
  simp [wordGrade]

lemma yz_of_nonzero_not_X (a : Fin 4) (ha : a≠0) (hx : a≠1) : a=2 ∨ a=3 := by
  fin_cases a <;> simp_all
end Paper13
