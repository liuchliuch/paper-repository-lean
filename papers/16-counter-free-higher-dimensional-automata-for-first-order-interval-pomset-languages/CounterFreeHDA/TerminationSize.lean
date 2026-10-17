import CounterFreeHDA.TerminatorGlue

namespace CounterFreeHDA.TerminatorGlue
universe u
variable {Lab : Type u} (P : PomsetData Lab) (i : Fin P.srcLen)
    (ht : ¬ P.inTgt (P.src i))

theorem remaining_size : (remaining P i).card + 1 = P.srcLen := by
  classical
  have hi : 0 < P.srcLen := Nat.zero_lt_of_lt i.isLt
  simp only [remaining,Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin]
  omega

theorem residual_size : (residual P i ht).n + 1 = P.n := by
  classical
  have hi : 0 < P.n := Nat.zero_lt_of_lt (P.src i).isLt
  simp only [residual,Induced.data,Induced.Event,keep,Fintype.card_subtype_compl,
    Fintype.card_subtype_eq,Fintype.card_fin]
  omega

theorem residual_target_size : (residual P i ht).tgtLen = P.tgtLen := by
  classical
  exact Finset.card_univ.trans (Fintype.card_fin _)

end CounterFreeHDA.TerminatorGlue
