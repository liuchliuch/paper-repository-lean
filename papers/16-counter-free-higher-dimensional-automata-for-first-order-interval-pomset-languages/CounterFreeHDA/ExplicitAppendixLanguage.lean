import CounterFreeHDA.UnaryBlockPomsets
import CounterFreeHDA.WordLabelComposition

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

theorem cPom_width : cPom.pom.val.WidthLE 2 := cWord.label_width
theorem aPom_width : aPom.pom.val.WidthLE 2 := Unary.a.label_width

theorem pairStarIso {p : ClosedWord} (hp : PairStar p) :
    ∃ n : ℕ, Nonempty (PomsetIso p.label.pom.val (cPom.pow n).pom.val) := by
  induction hp with
  | nil => exact ⟨0,⟨PomsetIso.refl _⟩⟩
  | @cons c p hc hp ih =>
    obtain ⟨n,⟨φ⟩⟩ := ih
    have ψ := (c.appendLabelIso p).trans
      (BoundedArrow.compIso (A := BoundedArrow.ofWord c) (A' := cPom.bounded cPom_width)
        (B := BoundedArrow.ofWord p) (B' := cPom.boundedPower cPom_width n) (concurrentBlockIso hc) φ)
    have η : PomsetIso ((cPom.bounded cPom_width).comp (cPom.boundedPower cPom_width n)).pom.val
        (cPom.pow (n+1)).pom.val := by
      have hz : PomsetIso (cPom.pow 1).pom.val cPom.pom.val := (cPom.bounded cPom_width).identityLeftIso
      have ht := (BoundedArrow.compIso (A := cPom.bounded cPom_width) (A' := cPom.boundedPower cPom_width 1)
        (B := cPom.boundedPower cPom_width n) (B' := cPom.boundedPower cPom_width n) hz.symm (PomsetIso.refl (cPom.pow n).pom.val)).trans (cPom.powerAddIso cPom_width 1 n)
      simpa only [Nat.add_comm 1 n] using ht
    exact ⟨n+1,⟨ψ.trans η⟩⟩

/-- Actual finite gluing powers of the two-concurrent-event pomset C. -/
def CStar (P : IntervalPom Unit) : Prop := ∃ n, IntervalPomIso (cPom.pow n).pom P

/-- The displayed formula C* union C*aP+, with P+ quantified over all
nonempty actual closed unary interval pomsets of width at most two. -/
def ExplicitLanguage (P : IntervalPom Unit) : Prop :=
  CStar P ∨ ∃ (n : ℕ) (Q : Tail Completion.emptyCube), 0 < Q.pom.n ∧
    IntervalPomIso (((cPom.boundedPower cPom_width n).comp (aPom.bounded aPom_width)).comp Q).pom P

/-- The accepted ST expression maps to exactly the actual displayed formula. -/
theorem expression_label_formula {p : ClosedWord} (hp : ExpressionWord p) : ExplicitLanguage p.label.pom := by
  cases hp with
  | star hc =>
    obtain ⟨n,⟨φ⟩⟩ := pairStarIso hc
    exact Or.inl ⟨n,⟨φ.symm⟩⟩
  | @tail c a p hc ha hp =>
    obtain ⟨n,⟨φ⟩⟩ := pairStarIso hc
    let Q := BoundedArrow.ofWord p
    have hn : 0 < Q.pom.n := (empty_interface_size Q p (PomsetIso.refl _)).mp hp
    have η : PomsetIso (a.append p).label.pom.val ((aPom.bounded aPom_width).comp Q).pom.val :=
      (a.appendLabelIso p).trans
        (BoundedArrow.compIso (A := BoundedArrow.ofWord a) (A' := aPom.bounded aPom_width)
          (B := Q) (B' := Q) (singleBlockIso ha) (PomsetIso.refl p.label.pom.val))
    have ψ := (c.appendLabelIso (a.append p)).trans
      ((BoundedArrow.compIso (A := BoundedArrow.ofWord c) (A' := cPom.boundedPower cPom_width n)
        (B := BoundedArrow.ofWord (a.append p)) (B' := (aPom.bounded aPom_width).comp Q) φ η).trans
          (BoundedArrow.assocIso (cPom.boundedPower cPom_width n) (aPom.bounded aPom_width) Q).symm)
    exact Or.inr ⟨n,Q,hn,⟨ψ.symm⟩⟩

theorem cPom_returns (n : ℕ) : Actual.indexCell Completion.emptyCube 0 ∈
    Actual.originalHDA.toPrecubical.dPom (Actual.indexCell Completion.emptyCube 0) (cPom.pow n).pom := by
  induction n with
  | zero =>
    exact ⟨.nil _,.nil _,⟨PomsetIso.refl _⟩⟩
  | succ n ih =>
    apply (Actual.originalHDA.toPrecubical.dPom_comp (cPom.boundedPower cPom_width n) (cPom.bounded cPom_width) _ _).mpr
    refine ⟨Actual.indexCell Completion.emptyCube 0,ih,?_⟩
    change Actual.indexCell Completion.emptyCube 0 ∈ Actual.originalHDA.toPrecubical.dPom
      (Actual.indexCell Completion.emptyCube 0) cWord.label.pom
    rw [Actual.originalHDA.toPrecubical.dPom_word,← Actual.wordRel_iff]
    decide

/-- The explicit formula is sufficient: C loops at the initial vertex, a
reaches the second vertex, and every nonempty suffix is accepted from there. -/
theorem formula_accepts (P : IntervalPom Unit) (hP : ExplicitLanguage P) : P ∈ Actual.originalHDA.LangPom := by
  rcases hP with ⟨n,⟨φ⟩⟩ | ⟨n,Q,hn,⟨φ⟩⟩
  · apply (Actual.originalHDA.language_iso φ).mp
    exact (original_closed_acceptance _).mpr (cPom_returns n)
  · apply (Actual.originalHDA.language_iso φ).mp
    apply (original_closed_acceptance _).mpr
    apply (Actual.originalHDA.toPrecubical.dPom_comp _ Q _ _).mpr
    refine ⟨Actual.indexCell Completion.emptyCube 1,?_,?_⟩
    · apply (Actual.originalHDA.toPrecubical.dPom_comp _ (aPom.bounded aPom_width) _ _).mpr
      refine ⟨Actual.indexCell Completion.emptyCube 0,cPom_returns n,?_⟩
      change Actual.indexCell Completion.emptyCube 1 ∈ Actual.originalHDA.toPrecubical.dPom
        (Actual.indexCell Completion.emptyCube 0) Unary.a.label.pom
      rw [Actual.originalHDA.toPrecubical.dPom_word Unary.a,← Actual.wordRel_iff]
      decide
    · have hB : Q ∈ residualLanguage Completion.emptyCube (1 : Fin 4) := by rw [residual_B]; exact hn
      change ∃ i : Fin 2, representative (0 : Fin 3) (1 : Fin 4) i = true ∧ _ at hB
      have hm : ∀ i : Fin 2, representative (0 : Fin 3) (1 : Fin 4) i = true ↔ i = 1 := by decide
      simpa only [hm,exists_eq_left,true_and] using hB

/-- Appendix A.1's exact interval-pomset language formula. -/
theorem explicit_language_formula : Actual.originalHDA.LangPom = {P | ExplicitLanguage P} := by
  ext P
  constructor
  · intro hP
    obtain ⟨p,hp,⟨φ⟩⟩ := (original_language_iff P).mp hP
    have ha : acceptBit (wordKind p (0 : Fin 4)) = true := by
      have hm := residual_mem_ofWord p (0 : Fin 4)
      have h0 := (represents_acceptance _ _ (execute_represents p (mask 2 1) (0 : Fin 4) represents_initial)).mp hp
      exact decide_eq_true_eq.mpr h0
    rcases expression_label_formula (accepts_expression p ha) with ⟨n,⟨ψ⟩⟩ | ⟨n,Q,hn,⟨ψ⟩⟩
    · exact Or.inl ⟨n,⟨ψ.trans φ⟩⟩
    · exact Or.inr ⟨n,Q,hn,⟨ψ.trans φ⟩⟩
  · exact formula_accepts P

end CounterFreeHDA.Appendix.Residual
