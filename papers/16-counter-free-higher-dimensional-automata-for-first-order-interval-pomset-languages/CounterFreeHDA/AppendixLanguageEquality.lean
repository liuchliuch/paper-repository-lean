import CounterFreeHDA.AppendixWordLanguages

namespace CounterFreeHDA.Appendix.Compare
open Cubical

private theorem original_initial_index (i : Fin 2) :
    Actual.originalHDA.initial (Actual.indexCell Completion.emptyCube i) ↔ i = 0 := by
  constructor
  · intro h
    exact h.2 Fin.elim0
  · rintro rfl
    exact ⟨rfl,fun _ => rfl⟩

private theorem original_accept_index (i : Fin 2) :
    Actual.originalHDA.accepting (Actual.indexCell Completion.emptyCube i) ↔ i = 0 := original_initial_index i

private theorem completed_initial_index (i : Fin 3) :
    Completion.completionHDA.initial (Completion.indexCell Completion.emptyCube i) ↔ i = 0 := by
  constructor
  · intro h
    exact h.2 Fin.elim0
  · rintro rfl
    exact ⟨rfl,fun _ => rfl⟩

private theorem completed_accept_index (i : Fin 3) :
    Completion.completionHDA.accepting (Completion.indexCell Completion.emptyCube i) ↔ i = 0 ∨ i = 2 := by
  have he : Completion.completionHDA.accepting (Completion.indexCell Completion.emptyCube i) ↔ i ≠ 1 := by
    constructor
    · intro h
      exact h.2 Fin.elim0
    · intro h
      exact ⟨rfl,fun _ => h⟩
  exact he.trans (by fin_cases i <;> decide)

/-- Normalize the actual marked language to the fixed empty-interface ST
word relation. Labels retain their full event/order isomorphism witness. -/
theorem original_language_iff (P : IntervalPom Unit) :
    P ∈ Actual.originalHDA.LangPom ↔
      ∃ p : Word Completion.emptyCube Completion.emptyCube,
        originalExecute p (mask 2 1) 0 = true ∧ IntervalPomIso p.label.pom P := by
  constructor
  · rintro ⟨U,V,x,y,hx,hy,p,hr,hi⟩
    have hu := cube_eq_empty hx.1
    have hv := cube_eq_empty hy.1
    subst U
    subst V
    obtain ⟨i,rfl⟩ := Actual.indexCell_surjective Completion.emptyCube x
    obtain ⟨j,rfl⟩ := Actual.indexCell_surjective Completion.emptyCube y
    have hi0 := (original_initial_index i).mp hx
    have hj0 := (original_accept_index j).mp hy
    subst i
    subst j
    exact ⟨p,(originalExecute_initial p 0).mpr hr,hi⟩
  · rintro ⟨p,hp,hi⟩
    exact ⟨Completion.emptyCube,Completion.emptyCube,Actual.indexCell _ 0,Actual.indexCell _ 0,
      (original_initial_index 0).mpr rfl,(original_accept_index 0).mpr rfl,p,
      (originalExecute_initial p 0).mp hp,hi⟩

theorem completed_language_iff (P : IntervalPom Unit) :
    P ∈ Completion.completionHDA.LangPom ↔
      ∃ p : Word Completion.emptyCube Completion.emptyCube,
        (completedExecute p (mask 3 1) 0 = true ∨ completedExecute p (mask 3 1) 2 = true) ∧
          IntervalPomIso p.label.pom P := by
  constructor
  · rintro ⟨U,V,x,y,hx,hy,p,hr,hi⟩
    have hu := cube_eq_empty hx.1
    have hv := cube_eq_empty hy.1
    subst U
    subst V
    obtain ⟨i,rfl⟩ := Completion.indexCell_surjective Completion.emptyCube x
    obtain ⟨j,rfl⟩ := Completion.indexCell_surjective Completion.emptyCube y
    have hi0 := (completed_initial_index i).mp hx
    subst i
    have hj := (completed_accept_index j).mp hy
    rcases hj with rfl | rfl
    · exact ⟨p,Or.inl ((completedExecute_initial p 0).mpr hr),hi⟩
    · exact ⟨p,Or.inr ((completedExecute_initial p 2).mpr hr),hi⟩
  · rintro ⟨p,hp,hi⟩
    rcases hp with hp | hp
    · exact ⟨Completion.emptyCube,Completion.emptyCube,Completion.indexCell _ 0,Completion.indexCell _ 0,
        (completed_initial_index 0).mpr rfl,(completed_accept_index 0).mpr (Or.inl rfl),p,
        (completedExecute_initial p 0).mp hp,hi⟩
    · exact ⟨Completion.emptyCube,Completion.emptyCube,Completion.indexCell _ 0,Completion.indexCell _ 2,
        (completed_initial_index 0).mpr rfl,(completed_accept_index 2).mpr (Or.inr rfl),p,
        (completedExecute_initial p 2).mp hp,hi⟩

/-- Appendix A's original counter-free HDA and the non-counter-free displayed
completion have exactly the same genuine interval-pomset language. -/
theorem actual_language_equality : Actual.originalHDA.LangPom = Completion.completionHDA.LangPom := by
  ext P
  rw [original_language_iff,completed_language_iff]
  exact exists_congr (fun p => and_congr (closed_word_acceptance p) Iff.rfl)

end CounterFreeHDA.Appendix.Compare
