import CounterFreeHDA.GluingIso
import CounterFreeHDA.InterfaceEnumeration

namespace CounterFreeHDA.PomsetIso
universe u
variable {Lab : Type u} {P Q : PomsetData Lab}

theorem source_type (φ : PomsetIso P Q) : P.srcType = Q.srcType := by
  have hn : P.srcLen = Q.srcLen := by simpa only [Fintype.card_fin] using Fintype.card_congr φ.srcEquiv
  apply Fin.sigma_eq_iff_eq_comp_cast.mpr
  refine ⟨hn,funext fun i => ?_⟩
  have hi : φ.srcEquiv i = Fin.cast hn i := Fin.ext (φ.srcEquiv_val i)
  change P.lab (P.src i) = Q.lab (Q.src (Fin.cast hn i))
  rw [← hi,← φ.src_eq,φ.lab_eq]

theorem target_type (φ : PomsetIso P Q) : P.tgtType = Q.tgtType := by
  have hn : P.tgtLen = Q.tgtLen := by simpa only [Fintype.card_fin] using Fintype.card_congr φ.tgtEquiv
  apply Fin.sigma_eq_iff_eq_comp_cast.mpr
  refine ⟨hn,funext fun i => ?_⟩
  have hi : φ.tgtEquiv i = Fin.cast hn i := Fin.ext (φ.tgtEquiv_val i)
  change P.lab (P.tgt i) = Q.lab (Q.tgt (Fin.cast hn i))
  rw [← hi,← φ.tgt_eq,φ.lab_eq]

end CounterFreeHDA.PomsetIso
