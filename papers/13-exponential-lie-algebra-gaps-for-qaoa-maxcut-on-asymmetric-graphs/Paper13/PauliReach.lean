import Paper13.PauliLocal
noncomputable section
namespace Paper13
open Matrix
attribute [local instance] Classical.propDecidable

def triplePauli {n : ℕ} (w : Fin n → Fin 4) (i j k : Fin n) (a b c : Fin 4) : Fin n → Fin 4 :=
  fun v => if v=i then a else if v=j then b else if v=k then c else w v

lemma triplePauli_self {n : ℕ} (w : Fin n → Fin 4) (i j k : Fin n) :
    triplePauli w i j k (w i) (w j) (w k)=w := by
  funext v
  simp only [triplePauli]
  split_ifs <;> simp_all

/-- Three explicit commutators insert X on a second site using an identity spectator. -/
theorem complete_word_insert_X {n : ℕ} (w : Fin n → Fin 4) (i j k : Fin n)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (hw : skewPauliWord (triplePauli w i j k 1 0 0) ∈ graphMa (⊤ : SimpleGraph (Fin n))) :
    skewPauliWord (triplePauli w i j k 1 1 0) ∈ graphMa (⊤ : SimpleGraph (Fin n)) := by
  have h1 : skewPauliWord (triplePauli w i j k 3 2 0) ∈ graphMa (⊤ : SimpleGraph (Fin n)) := by
    apply graphMa_word_step _ _ _ i j hij 2 2 hw
      (graphMa_two_YZ ⊤ i j hij 2 2 (Or.inl rfl) (Or.inl rfl))
    · funext v
      by_cases hi : v=i <;> by_cases hj : v=j <;> by_cases hk : v=k <;>
        simp_all [wordXor,twoPauli,triplePauli] <;> rfl
    · left; norm_num [triplePauli,hij.symm,hik.symm,hjk.symm,pauliPhase]
  have h2 : skewPauliWord (triplePauli w i j k 1 2 2) ∈ graphMa (⊤ : SimpleGraph (Fin n)) := by
    apply graphMa_word_step _ _ _ i k hik 2 2 h1
      (graphMa_two_YZ ⊤ i k hik 2 2 (Or.inl rfl) (Or.inl rfl))
    · funext v
      by_cases hi : v=i <;> by_cases hj : v=j <;> by_cases hk : v=k <;>
        simp_all [wordXor,twoPauli,triplePauli] <;> rfl
    · right; norm_num [triplePauli,hij.symm,hik.symm,hjk.symm,pauliPhase]
  apply graphMa_word_step _ _ _ j k hjk 3 2 h2
    (graphMa_two_YZ ⊤ j k hjk 3 2 (Or.inr rfl) (Or.inl rfl))
  · funext v
    by_cases hi : v=i <;> by_cases hj : v=j <;> by_cases hk : v=k <;>
      simp_all [wordXor,twoPauli,triplePauli] <;> rfl
  · left; norm_num [triplePauli,hij.symm,hik.symm,hjk.symm,pauliPhase]

def pairChange {n : ℕ} (w : Fin n → Fin 4) (i j : Fin n) (a b : Fin 4) : Fin n → Fin 4 :=
  fun v => if v=i then a else if v=j then b else w v

lemma pairChange_self {n : ℕ} (w : Fin n → Fin 4) (i j : Fin n) :
    pairChange w i j (w i) (w j)=w := by
  funext v; simp only [pairChange]; split_ifs <;> simp_all

/-- Replaces Y,I by X,Y or X,Z, preserving every other tensor factor. -/
theorem complete_word_X_YZ {n : ℕ} (w : Fin n → Fin 4) (i j : Fin n) (hij : i≠j)
    (b : Fin 4) (hb : b=2 ∨ b=3)
    (hw : skewPauliWord (pairChange w i j 2 0) ∈ graphMa (⊤ : SimpleGraph (Fin n))) :
    skewPauliWord (pairChange w i j 1 b) ∈ graphMa (⊤ : SimpleGraph (Fin n)) := by
  apply graphMa_word_step _ _ _ i j hij 3 b hw
    (graphMa_two_YZ ⊤ i j hij 3 b (Or.inr rfl) hb)
  · funext v
    by_cases hi : v=i <;> by_cases hj : v=j <;>
      simp_all [wordXor,twoPauli,pairChange] <;> rfl
  · left; norm_num [pairChange,hij.symm,pauliPhase]

/-- Inserts two Y/Z factors by two commutators, while restoring the first Y/Z factor. -/
theorem complete_word_insert_YZ {n : ℕ} (w : Fin n → Fin 4) (i j k : Fin n)
    (hij : i≠j) (hik : i≠k) (hjk : j≠k) (a b c : Fin 4)
    (ha : a=2 ∨ a=3) (hb : b=2 ∨ b=3) (hc : c=2 ∨ c=3)
    (hw : skewPauliWord (triplePauli w i j k a 0 0) ∈ graphMa (⊤ : SimpleGraph (Fin n))) :
    skewPauliWord (triplePauli w i j k a b c) ∈ graphMa (⊤ : SimpleGraph (Fin n)) := by
  let p : Fin 4 := match a.val with | 2 => 3 | _ => 2
  have hp : p=2 ∨ p=3 := by rcases ha with rfl | rfl <;> simp [p]
  have h1 : skewPauliWord (triplePauli w i j k 1 b 0) ∈ graphMa (⊤ : SimpleGraph (Fin n)) := by
    apply graphMa_word_step _ _ _ i j hij p b hw
      (graphMa_two_YZ ⊤ i j hij p b hp hb)
    · funext v
      rcases ha with rfl | rfl <;>
        by_cases hi : v=i <;> by_cases hj : v=j <;> by_cases hk : v=k <;>
        simp_all [wordXor,twoPauli,triplePauli,p] <;> rfl
    · rcases ha with rfl | rfl
      · left; norm_num [triplePauli,hij.symm,p,pauliPhase]
      · right; norm_num [triplePauli,hij.symm,p,pauliPhase]
  apply graphMa_word_step _ _ _ i k hik p c h1
    (graphMa_two_YZ ⊤ i k hik p c hp hc)
  · funext v
    rcases ha with rfl | rfl <;>
      by_cases hi : v=i <;> by_cases hj : v=j <;> by_cases hk : v=k <;>
      simp_all [wordXor,twoPauli,triplePauli,p] <;> rfl
  · rcases ha with rfl | rfl
    · right; norm_num [triplePauli,hik.symm,hjk.symm,p,pauliPhase]
    · left; norm_num [triplePauli,hik.symm,hjk.symm,p,pauliPhase]
end Paper13
