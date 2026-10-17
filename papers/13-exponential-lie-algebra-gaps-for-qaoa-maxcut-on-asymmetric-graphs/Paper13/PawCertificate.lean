import Paper13.PauliLie
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def pawGraph : SimpleGraph (Fin 4) where
  Adj i j := i ≠ j ∧ ((i < 3 ∧ j < 3) ∨ (i=2 ∧ j=3) ∨ (i=3 ∧ j=2))
  symm := by intro i j h; exact ⟨h.1.symm,by tauto⟩
  loopless := by intro i h; exact h.1 rfl

def word4 (a b c d : Fin 4) : Fin 4 → Fin 4 := ![a,b,c,d]

/-- Explicit Pauli-bracket certificate for the two missing edges of a paw. -/
theorem paw_missing_edges :
    Complex.I • ZZ (0 : Fin 4) 3 ∈ graphMa pawGraph ∧
    Complex.I • ZZ (1 : Fin 4) 3 ∈ graphMa pawGraph := by
  have h10 : (1 : Fin 4) ≠ 0 := by decide
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h3300 : skewPauliWord (word4 3 3 0 0) ∈ graphMa pawGraph := by
    have he : (word4 3 3 0 0) = pairZPauli (0 : Fin 4) 1 := by decide
    rw [he]
    exact graphMa_pair_Z pawGraph _ _ (by dsimp [pawGraph]; decide)
  have h1000 : skewPauliWord (word4 1 0 0 0) ∈ graphMa pawGraph := by
    have he : (word4 1 0 0 0) = singlePauli (0 : Fin 4) 1 := by decide
    rw [he]
    exact graphMa_single_X pawGraph _
  have h2300 : skewPauliWord (word4 2 3 0 0) ∈ graphMa pawGraph := by
    apply graphMa_word_bracket pawGraph _ _ _ h3300 h1000 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h0010 : skewPauliWord (word4 0 0 1 0) ∈ graphMa pawGraph := by
    have he : (word4 0 0 1 0) = singlePauli (2 : Fin 4) 1 := by decide
    rw [he]
    exact graphMa_single_X pawGraph _
  have h3030 : skewPauliWord (word4 3 0 3 0) ∈ graphMa pawGraph := by
    have he : (word4 3 0 3 0) = pairZPauli (0 : Fin 4) 2 := by decide
    rw [he]
    exact graphMa_pair_Z pawGraph _ _ (by dsimp [pawGraph]; decide)
  have h3020 : skewPauliWord (word4 3 0 2 0) ∈ graphMa pawGraph := by
    apply graphMa_word_bracket pawGraph _ _ _ h0010 h3030 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h1320 : skewPauliWord (word4 1 3 2 0) ∈ graphMa pawGraph := by
    apply graphMa_word_bracket pawGraph _ _ _ h2300 h3020 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h0033 : skewPauliWord (word4 0 0 3 3) ∈ graphMa pawGraph := by
    have he : (word4 0 0 3 3) = pairZPauli (2 : Fin 4) 3 := by decide
    rw [he]
    exact graphMa_pair_Z pawGraph _ _ (by dsimp [pawGraph]; decide)
  have h0330 : skewPauliWord (word4 0 3 3 0) ∈ graphMa pawGraph := by
    have he : (word4 0 3 3 0) = pairZPauli (1 : Fin 4) 2 := by decide
    rw [he]
    exact graphMa_pair_Z pawGraph _ _ (by dsimp [pawGraph]; decide)
  have h0320 : skewPauliWord (word4 0 3 2 0) ∈ graphMa pawGraph := by
    apply graphMa_word_bracket pawGraph _ _ _ h0010 h0330 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h0313 : skewPauliWord (word4 0 3 1 3) ∈ graphMa pawGraph := by
    apply graphMa_word_bracket pawGraph _ _ _ h0033 h0320 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h2030 : skewPauliWord (word4 2 0 3 0) ∈ graphMa pawGraph := by
    apply graphMa_word_bracket pawGraph _ _ _ h3030 h1000 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h2323 : skewPauliWord (word4 2 3 2 3) ∈ graphMa pawGraph := by
    apply graphMa_word_bracket pawGraph _ _ _ h0313 h2030 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h3003 : skewPauliWord (word4 3 0 0 3) ∈ graphMa pawGraph := by
    apply graphMa_word_bracket pawGraph _ _ _ h1320 h2323 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h0100 : skewPauliWord (word4 0 1 0 0) ∈ graphMa pawGraph := by
    have he : (word4 0 1 0 0) = singlePauli (1 : Fin 4) 1 := by decide
    rw [he]
    exact graphMa_single_X pawGraph _
  have h0230 : skewPauliWord (word4 0 2 3 0) ∈ graphMa pawGraph := by
    apply graphMa_word_bracket pawGraph _ _ _ h0330 h0100 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h0220 : skewPauliWord (word4 0 2 2 0) ∈ graphMa pawGraph := by
    apply graphMa_word_bracket pawGraph _ _ _ h0010 h0230 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h3200 : skewPauliWord (word4 3 2 0 0) ∈ graphMa pawGraph := by
    apply graphMa_word_bracket pawGraph _ _ _ h0100 h3300 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h3130 : skewPauliWord (word4 3 1 3 0) ∈ graphMa pawGraph := by
    apply graphMa_word_bracket pawGraph _ _ _ h3200 h0330 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h0023 : skewPauliWord (word4 0 0 2 3) ∈ graphMa pawGraph := by
    apply graphMa_word_bracket pawGraph _ _ _ h0010 h0033 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h3013 : skewPauliWord (word4 3 0 1 3) ∈ graphMa pawGraph := by
    apply graphMa_word_bracket pawGraph _ _ _ h3030 h0023 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h0123 : skewPauliWord (word4 0 1 2 3) ∈ graphMa pawGraph := by
    apply graphMa_word_bracket pawGraph _ _ _ h3130 h3013 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h0303 : skewPauliWord (word4 0 3 0 3) ∈ graphMa pawGraph := by
    apply graphMa_word_bracket pawGraph _ _ _ h0220 h0123 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word4,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  constructor
  · have he : word4 3 0 0 3 = pairZPauli (0 : Fin 4) 3 := by decide
    simpa only [he,skewPauliWord,pauliWord_pair_Z (0 : Fin 4) 3 (by decide)] using h3003
  · have he : word4 0 3 0 3 = pairZPauli (1 : Fin 4) 3 := by decide
    simpa only [he,skewPauliWord,pauliWord_pair_Z (1 : Fin 4) 3 (by decide)] using h0303
end Paper13
