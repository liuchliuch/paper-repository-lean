import CounterFreeHDA.IntervalPeel

/-! Replacing interfaces by any ordered antichains of minimal/maximal events.
Events, labels, precedence and event order are all retained exactly. -/
namespace CounterFreeHDA.Reinterface
universe u
variable {Lab : Type u} (P : PomsetData Lab) (hP : IsIntervalPom P)
    (S T : Finset (Fin P.n)) (hS : P.Antichain S) (hT : P.Antichain T)

noncomputable def data : PomsetData Lab where
  n := P.n
  lab := P.lab
  prec := P.prec
  eord := P.eord
  srcLen := S.card
  tgtLen := T.card
  src := (Antichain.enumeration P hP S hS).event
  tgt := (Antichain.enumeration P hP T hT).event
  src_inj := (Antichain.enumeration P hP S hS).injective
  tgt_inj := (Antichain.enumeration P hP T hT).injective

theorem inSrc_iff (e : Fin P.n) : (data P hP S T hS hT).inSrc e ↔ e ∈ S := by
  constructor
  · rintro ⟨i,rfl⟩; exact (Antichain.enumeration P hP S hS).mem i
  · exact (Antichain.enumeration P hP S hS).surjective e

theorem inTgt_iff (e : Fin P.n) : (data P hP S T hS hT).inTgt e ↔ e ∈ T := by
  constructor
  · rintro ⟨i,rfl⟩; exact (Antichain.enumeration P hP T hT).mem i
  · exact (Antichain.enumeration P hP T hT).surjective e

theorem isIntervalPom (hs : ∀ e ∈ S, P.Minimal e)
    (ht : ∀ e ∈ T, ∀ f, ¬ P.prec e f) : IsIntervalPom (data P hP S T hS hT) where
  prec_irrefl := hP.prec_irrefl
  prec_trans := hP.prec_trans
  eord_irrefl := hP.eord_irrefl
  eord_acyclic := hP.eord_acyclic
  trichotomy := hP.trichotomy
  src_minimal e he := hs e ((inSrc_iff P hP S T hS hT e).mp he)
  tgt_maximal e he := ht e ((inTgt_iff P hP S T hS hT e).mp he)
  src_eord := (Antichain.enumeration P hP S hS).ordered
  tgt_eord := (Antichain.enumeration P hP T hT).ordered
  interval_rep := hP.interval_rep

noncomputable def sourceSet : Finset (Fin P.n) := by
  classical
  exact Finset.univ.image P.src

noncomputable def targetSet : Finset (Fin P.n) := by
  classical
  exact Finset.univ.image P.tgt

theorem mem_sourceSet (e : Fin P.n) : e ∈ sourceSet P ↔ P.inSrc e := by
  classical
  simp only [sourceSet,Finset.mem_image,Finset.mem_univ,true_and,PomsetData.inSrc,Set.mem_range]

theorem mem_targetSet (e : Fin P.n) : e ∈ targetSet P ↔ P.inTgt e := by
  classical
  simp only [targetSet,Finset.mem_image,Finset.mem_univ,true_and,PomsetData.inTgt,Set.mem_range]

theorem sourceSet_card : (sourceSet P).card = P.srcLen := by
  classical
  rw [sourceSet,Finset.card_image_of_injective _ P.src_inj,Finset.card_univ,Fintype.card_fin]

theorem targetSet_card : (targetSet P).card = P.tgtLen := by
  classical
  rw [targetSet,Finset.card_image_of_injective _ P.tgt_inj,Finset.card_univ,Fintype.card_fin]

include hP in
theorem source_antichain : P.Antichain (sourceSet P) := by
  intro e he f hf
  exact hP.src_minimal f ((mem_sourceSet P f).mp hf) e

include hP in
theorem target_antichain : P.Antichain (targetSet P) := by
  intro e he f hf
  exact hP.tgt_maximal e ((mem_targetSet P e).mp he) f

include hP in
/-- Adding a minimal event is a legal new active interface. -/
theorem insert_source_antichain {e : Fin P.n} (he : P.Minimal e) :
    P.Antichain (insert e (sourceSet P)) := by
  classical
  intro a ha b hb
  rcases Finset.mem_insert.mp ha with rfl | ha
  · rcases Finset.mem_insert.mp hb with rfl | hb
    · exact hP.prec_irrefl _
    · exact hP.src_minimal b ((mem_sourceSet P b).mp hb) _
  · rcases Finset.mem_insert.mp hb with rfl | hb
    · exact he a
    · exact source_antichain P hP a ha b hb

end CounterFreeHDA.Reinterface
