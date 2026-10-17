import Paper12.Statements
import Paper12.OneHotComplete
import Paper12.OuterComplete
import Paper12.Universality
import Paper12.ChoiComplete
import Paper12.BlockFailure

/-! Source-level proofs of every numbered result and the substantive
construction identities, including the conditional Appendix A reduction. -/
namespace Paper12.Paper
open Classical

theorem definition_2_1 : PaperStatements.definition_2_1 := by
  intro X W _ _ Γ C U
  refine ⟨?_, Iff.rfl, rfl⟩
  constructor
  · rintro ⟨h⟩ γ
    exact ⟨h.lift γ, h.restrict γ, h.preserves γ⟩
  · intro h
    choose e hr hp using h
    exact ⟨⟨e, hr, hp⟩⟩

theorem lemma_2_2 : PaperStatements.lemma_2_2 := by
  intro X W _ _ Γ U C hsym hclean
  exact Paper12.lemma_2_2 hsym hclean

theorem lemma_2_3 : PaperStatements.lemma_2_3 := by
  intro X _ Γ U hU heq
  exact ⟨fun γ hγ w => Paper12.coeff_orbit (heq γ hγ) w, Paper12.coeff_l2 U hU⟩

theorem lemma_2_4 : PaperStatements.lemma_2_4 := by
  intro d k θ P S G hD
  exact Paper12.two_reflection_bundle hD

theorem lemma_2_5 : PaperStatements.lemma_2_5 := by
  intro X _ α hmass
  obtain ⟨B, hprep, hsize, hsym⟩ := Paper12.lemma_2_5_circuit α hmass
  refine ⟨B, ?_, hsize, hsym⟩
  have hχ : Paper12.weightedOneHot (Paper12.selectorD α) = PaperStatements.chi α := by
    funext b
    unfold Paper12.weightedOneHot PaperStatements.chi
    apply Finset.sum_congr (by ext q; simp)
    intro q _
    dsimp only [Paper12.selectorD]
    have hh : @Paper12.oneHot (Paper12.SelectorWire α) (Classical.decEq _) q = Paper12.oneHot q :=
      congrArg (fun d : DecidableEq (Paper12.SelectorWire α) => @Paper12.oneHot _ d q)
        (Subsingleton.elim _ _)
    simp only [hh]
  rw [hχ] at hprep
  exact hprep


theorem lemma_4_1 : PaperStatements.lemma_4_1 := by
  intro X W _ _ Γ A V p hV hsym hp hp1 hb
  obtain ⟨C, hs, hsymC, hc, he⟩ :=
    Paper12.lemma_4_1_actual A V p hV hsym hp hp1 hb
  exact ⟨C, hs, hsymC, hc, he⟩


theorem theorem_1_1 : PaperStatements.theorem_1_1 := by
  intro X _ Γ U hU
  refine ⟨Paper12.theorem_1_1_equivalence U hU,
    (fun hn heq => Paper12.theorem_1_1_sufficiency U hU hn heq), ?_,
    Paper12.pauli_support_bound U, Paper12.coeff_mass_bounds U hU,
    Paper12.sizeBound_le U hU⟩
  intro hz
  letI : IsEmpty X := Fintype.card_eq_zero_iff.mp hz
  exact Paper12.theorem_1_1_of_isEmpty Γ U hU

theorem corollary_4_2 : PaperStatements.corollary_4_2 := by
  intro X G _ _ ρ U hU heq
  exact Paper12.corollary_4_2_action ρ U hU heq


theorem equation_2 : PaperStatements.equation_2 := by
  intro J _ g
  exact Paper12.equality_unitary_expansion g

theorem equation_4 : PaperStatements.equation_4 := by
  intro X _ U
  exact Paper12.pauliExpand_eq U

theorem empty_case : PaperStatements.empty_case := by
  intro X _ _ Γ U hU
  exact Paper12.theorem_1_1_of_isEmpty Γ U hU

theorem equation_23 : PaperStatements.equation_23 := by
  intro X _ U ψ b
  exact Paper12.choi_contraction U ψ b

theorem equation_13 : PaperStatements.equation_13 := by
  intro X _ α q ψ
  have h := Paper12.fullSelection_sector α q ψ
  have hh : @Paper12.oneHot (Paper12.SelectorWire α) (Classical.decEq _) q = Paper12.oneHot q :=
    congrArg (fun d : DecidableEq (Paper12.SelectorWire α) => @Paper12.oneHot _ d q)
      (Subsingleton.elim _ _)
  simpa only [hh] using h

theorem equation_16 : PaperStatements.equation_16 := by
  intro X _ U hU
  exact Paper12.blockCircuit_encoding U hU

theorem equation_17 : PaperStatements.equation_17 := by
  intro X W _ _ A U p hU hp hp1 hb
  exact Paper12.block_failure_decomposition A U p hU hp hp1 hb

theorem equation_18 : PaperStatements.equation_18 := by
  intro X _ α hn
  exact Paper12.blockCircuit_size α hn

theorem appendix_choi : PaperStatements.appendix_choi := by
  intro X T _ _ Γ CJ U hU hprep hs
  exact Paper12.appendix_choi_construction CJ U hU hprep hs

end Paper12.Paper
