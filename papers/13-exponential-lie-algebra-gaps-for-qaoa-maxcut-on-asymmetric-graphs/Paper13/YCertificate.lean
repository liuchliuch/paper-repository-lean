import Paper13.PauliLie
noncomputable section
namespace Paper13
open Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def yGraph : SimpleGraph (Fin 5) where
  Adj i j := (i=0 ∧ j=2) ∨ (i=2 ∧ j=0) ∨ (i=1 ∧ j=2) ∨ (i=2 ∧ j=1) ∨
    (i=2 ∧ j=3) ∨ (i=3 ∧ j=2) ∨ (i=3 ∧ j=4) ∨ (i=4 ∧ j=3)
  symm := by intro i j h; tauto
  loopless := by intro i h; rcases h with h | h | h | h | h | h | h | h <;> omega

def word5 (a b c d e : Fin 4) : Fin 5 → Fin 4 := ![a,b,c,d,e]

/-- Kernel-checked Y-configuration certificate. -/
theorem y_missing_edges :
    Complex.I • ZZ (0 : Fin 5) 4 ∈ graphMa yGraph ∧
    Complex.I • ZZ (1 : Fin 5) 4 ∈ graphMa yGraph := by
  have h10 : (1 : Fin 4) ≠ 0 := by decide
  have h20 : (2 : Fin 4) ≠ 0 := by decide
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  have h12 : (1 : Fin 4) ≠ 2 := by decide
  have h13 : (1 : Fin 4) ≠ 3 := by decide
  have h23 : (2 : Fin 4) ≠ 3 := by decide
  have h30300 : skewPauliWord (word5 3 0 3 0 0) ∈ graphMa yGraph := by
    have he : (word5 3 0 3 0 0) = pairZPauli (0 : Fin 5) 2 := by decide
    rw [he]
    exact graphMa_pair_Z yGraph _ _ (by dsimp [yGraph]; decide)
  have h00330 : skewPauliWord (word5 0 0 3 3 0) ∈ graphMa yGraph := by
    have he : (word5 0 0 3 3 0) = pairZPauli (2 : Fin 5) 3 := by decide
    rw [he]
    exact graphMa_pair_Z yGraph _ _ (by dsimp [yGraph]; decide)
  have h00100 : skewPauliWord (word5 0 0 1 0 0) ∈ graphMa yGraph := by
    have he : (word5 0 0 1 0 0) = singlePauli (2 : Fin 5) 1 := by decide
    rw [he]
    exact graphMa_single_X yGraph _
  have h00230 : skewPauliWord (word5 0 0 2 3 0) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h00330 h00100 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h30130 : skewPauliWord (word5 3 0 1 3 0) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h30300 h00230 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h03300 : skewPauliWord (word5 0 3 3 0 0) ∈ graphMa yGraph := by
    have he : (word5 0 3 3 0 0) = pairZPauli (1 : Fin 5) 2 := by decide
    rw [he]
    exact graphMa_pair_Z yGraph _ _ (by dsimp [yGraph]; decide)
  have h03200 : skewPauliWord (word5 0 3 2 0 0) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h00100 h03300 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h10000 : skewPauliWord (word5 1 0 0 0 0) ∈ graphMa yGraph := by
    have he : (word5 1 0 0 0 0) = singlePauli (0 : Fin 5) 1 := by decide
    rw [he]
    exact graphMa_single_X yGraph _
  have h20300 : skewPauliWord (word5 2 0 3 0 0) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h30300 h10000 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h23100 : skewPauliWord (word5 2 3 1 0 0) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h03200 h20300 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h13030 : skewPauliWord (word5 1 3 0 3 0) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h30130 h23100 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h00010 : skewPauliWord (word5 0 0 0 1 0) ∈ graphMa yGraph := by
    have he : (word5 0 0 0 1 0) = singlePauli (3 : Fin 5) 1 := by decide
    rw [he]
    exact graphMa_single_X yGraph _
  have h00320 : skewPauliWord (word5 0 0 3 2 0) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h00330 h00010 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h03120 : skewPauliWord (word5 0 3 1 2 0) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h03200 h00320 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h23220 : skewPauliWord (word5 2 3 2 2 0) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h03120 h20300 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h00033 : skewPauliWord (word5 0 0 0 3 3) ∈ graphMa yGraph := by
    have he : (word5 0 0 0 3 3) = pairZPauli (3 : Fin 5) 4 := by decide
    rw [he]
    exact graphMa_pair_Z yGraph _ _ (by dsimp [yGraph]; decide)
  have h00023 : skewPauliWord (word5 0 0 0 2 3) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h00033 h00010 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h00213 : skewPauliWord (word5 0 0 2 1 3) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h00230 h00023 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h23033 : skewPauliWord (word5 2 3 0 3 3) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h23220 h00213 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h30003 : skewPauliWord (word5 3 0 0 0 3) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h13030 h23033 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h01000 : skewPauliWord (word5 0 1 0 0 0) ∈ graphMa yGraph := by
    have he : (word5 0 1 0 0 0) = singlePauli (1 : Fin 5) 1 := by decide
    rw [he]
    exact graphMa_single_X yGraph _
  have h02300 : skewPauliWord (word5 0 2 3 0 0) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h01000 h03300 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h30200 : skewPauliWord (word5 3 0 2 0 0) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h30300 h00100 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h32100 : skewPauliWord (word5 3 2 1 0 0) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h02300 h30200 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h32330 : skewPauliWord (word5 3 2 3 3 0) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h00230 h32100 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h31210 : skewPauliWord (word5 3 1 2 1 0) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h32330 h03120 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h00313 : skewPauliWord (word5 0 0 3 1 3) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h00023 h00330 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h32213 : skewPauliWord (word5 3 2 2 1 3) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h32100 h00313 (2) (by norm_num)
    apply skewPauliWord_comm_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  have h03003 : skewPauliWord (word5 0 3 0 0 3) ∈ graphMa yGraph := by
    apply graphMa_word_bracket yGraph _ _ _ h31210 h32213 (-2) (by norm_num)
    apply skewPauliWord_comm_neg_two
    · funext i; fin_cases i <;> rfl
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
    · norm_num [wordPhase,word5,pauliPhase,Fin.prod_univ_succ,h10,h20,h30,h12,h13,h23]
  constructor
  · have he : word5 3 0 0 0 3 = pairZPauli (0 : Fin 5) 4 := by decide
    simpa only [he,skewPauliWord,pauliWord_pair_Z (0 : Fin 5) 4 (by decide)] using h30003
  · have he : word5 0 3 0 0 3 = pairZPauli (1 : Fin 5) 4 := by decide
    simpa only [he,skewPauliWord,pauliWord_pair_Z (1 : Fin 5) 4 (by decide)] using h03003
end Paper13
