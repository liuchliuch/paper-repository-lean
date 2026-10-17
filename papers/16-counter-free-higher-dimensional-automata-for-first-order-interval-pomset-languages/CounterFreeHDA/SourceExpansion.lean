import CounterFreeHDA.StarterGlue
import CounterFreeHDA.EmbeddingFace

/-! Starting one new minimal event expands the actual source antichain.
The discrete starter and the residual recover the original pomset exactly. -/
namespace CounterFreeHDA.SourceExpansion
universe u
variable {Lab : Type u} (P : PomsetData Lab) (hP : IsIntervalPom P)
    (e : Fin P.n) (he : P.Startable e)

noncomputable def events : Finset (Fin P.n) := insert e (Reinterface.sourceSet P)

include hP he in
theorem antichain : P.Antichain (events P e) :=
  Reinterface.insert_source_antichain P hP he.2

noncomputable def residual : PomsetData Lab :=
  Reinterface.data P hP (events P e) (Reinterface.targetSet P)
    (antichain P hP e he) (Reinterface.target_antichain P hP)

theorem residual_wf : IsIntervalPom (residual P hP e he) := by
  apply Reinterface.isIntervalPom
  · intro f hf
    rcases Finset.mem_insert.mp hf with rfl | hf
    · exact he.2
    · exact hP.src_minimal f ((Reinterface.mem_sourceSet P f).mp hf)
  · intro f hf
    exact hP.tgt_maximal f ((Reinterface.mem_targetSet P f).mp hf)

theorem source_mem (i : Fin P.srcLen) : P.src i ∈ events P e := by
  apply Finset.mem_insert_of_mem
  exact (Reinterface.mem_sourceSet P _).mpr ⟨i,rfl⟩

noncomputable def position (i : Fin P.srcLen) : Fin (events P e).card :=
  Classical.choose ((Antichain.enumeration P hP _ (antichain P hP e he)).surjective
    (P.src i) (source_mem P e i))

theorem position_spec (i : Fin P.srcLen) :
    (residual P hP e he).src (position P hP e he i) = P.src i :=
  Classical.choose_spec ((Antichain.enumeration P hP _ (antichain P hP e he)).surjective
    (P.src i) (source_mem P e i))

noncomputable def embedding : Fin P.srcLen ↪o Fin (residual P hP e he).srcLen :=
  OrderEmbedding.ofStrictMono (position P hP e he) (by
    intro i j hij
    apply ((Antichain.enumeration P hP _ (antichain P hP e he)).ordered _ _).mp
    change P.eord ((residual P hP e he).src _) ((residual P hP e he).src _)
    rw [position_spec,position_spec]
    exact (hP.src_eord i j).mpr hij)

/-- Exactly one event is added to the actual active interface. -/
theorem source_size : (residual P hP e he).srcLen = P.srcLen + 1 := by
  classical
  have hn : e ∉ Reinterface.sourceSet P := fun h => he.1 ((Reinterface.mem_sourceSet P e).mp h)
  change (insert e (Reinterface.sourceSet P)).card = _
  rw [Finset.card_insert_of_notMem hn,Reinterface.sourceSet_card]

noncomputable def restrictedIso :
    PomsetIso (StarterGlue.residualSource (residual P hP e he) (embedding P hP e he)) P where
  toEquiv := Equiv.refl _
  lab_eq _ := rfl
  srcEquiv := Equiv.refl _
  tgtEquiv := (Reinterface.restoredIso P hP).tgtEquiv
  src_mono _ _ := Iff.rfl
  tgt_mono := (Reinterface.restoredIso P hP).tgt_mono
  src_eq := position_spec P hP e he
  tgt_eq := (Reinterface.restoredIso P hP).tgt_eq
  prec_iff _ _ := Iff.rfl
  eord_iff _ _ := Iff.rfl

/-- Actual starter/residual factorization with no representation hypothesis. -/
noncomputable def iso : PomsetIso
    (glueData (StarterGlue.starter (residual P hP e he) (embedding P hP e he)).val
      (residual P hP e he) (StarterGlue.matching _ _)) P :=
  (StarterGlue.iso (residual P hP e he) (residual_wf P hP e he) (embedding P hP e he)).symm.trans
    (restrictedIso P hP e he)

end CounterFreeHDA.SourceExpansion
