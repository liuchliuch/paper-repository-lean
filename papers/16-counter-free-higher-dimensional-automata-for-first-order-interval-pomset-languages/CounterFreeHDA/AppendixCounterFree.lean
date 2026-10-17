import CounterFreeHDA.AppendixRelations
import CounterFreeHDA.PomsetRun

namespace CounterFreeHDA.Appendix.Actual
open Cubical

/-- Actual bounded pomset relations equal the computed relation of their
chosen ST word, including every nondeterministic endpoint. -/
theorem pomset_relation {U V : UCube} (A : BoundedArrow U V)
    (i : Fin (size U.1)) (j : Fin (size V.1)) :
    indexCell V j ∈ originalHDA.toPrecubical.dPom (indexCell U i) A.pom ↔
      wordRel A.representative i j = true := by
  rw [← originalHDA.toPrecubical.dPom_iso A.representativeIso (indexCell U i),originalHDA.toPrecubical.dPom_word]
  exact (wordRel_iff A.representative i j).symm

theorem power_relation {U : UCube} (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE 2)
    (n : ℕ) (i j : Fin (size U.1)) :
    indexCell U j ∈ originalHDA.toPrecubical.dPom (indexCell U i) (P.pow n).pom ↔
      pow (wordRel (P.bounded hw).representative) n i j = true := by
  induction n generalizing i j with
  | zero =>
    have he := originalHDA.toPrecubical.dPom_word (.nil U) (indexCell U i) (indexCell U j)
    change (indexCell U j ∈ originalHDA.toPrecubical.dPom (indexCell U i) (Word.nil U).label.pom) ↔ ident _ i j = true
    rw [he,originalHDA.toPrecubical.run_nil_iff]
    simp only [ident,decide_eq_true_eq]
    exact ⟨fun h => indexCell_injective U h,fun h => congrArg (indexCell U) h⟩
  | succ n ih =>
    have he := originalHDA.toPrecubical.dPom_comp (P.boundedPower hw n) (P.bounded hw) (indexCell U i) (indexCell U j)
    change (indexCell U j ∈ originalHDA.toPrecubical.dPom (indexCell U i) ((P.boundedPower hw n).comp (P.bounded hw)).pom) ↔ _
    rw [he]
    simp only [pow,comp,decide_eq_true_eq]
    constructor
    · rintro ⟨z,hz,hj⟩
      obtain ⟨l,rfl⟩ := indexCell_surjective U z
      exact ⟨l,(ih i l).mp hz,(pomset_relation (P.bounded hw) l j).mp hj⟩
    · rintro ⟨l,hl,hj⟩
      exact ⟨indexCell U l,(ih i l).mpr hl,(pomset_relation (P.bounded hw) l j).mpr hj⟩

/-- Appendix A.1's actual eight-cell HDA is counter-free at exponent three
on all cells and all genuine endomorphism pomset labels. -/
theorem original_counterFreePom : originalHDA.toPrecubical.CounterFreePom := by
  refine ⟨3,by decide,?_⟩
  intro U x P
  ext y
  classical
  by_cases hw : P.pom.val.WidthLE 2
  · obtain ⟨i,rfl⟩ := indexCell_surjective U x
    obtain ⟨j,rfl⟩ := indexCell_surjective U y
    rw [power_relation P hw 3 i j,power_relation P hw 4 i j]
    rw [table_exponent U.1 _ (word_table (P.bounded hw).representative)]
  · constructor
    · intro hr
      exact False.elim (hw (P.width_of_positive_power (by decide : 1 ≤ 3) (originalHDA.toPrecubical.reachable_width hr)))
    · intro hr
      exact False.elim (hw (P.width_of_positive_power (by decide : 1 ≤ 4) (originalHDA.toPrecubical.reachable_width hr)))

end CounterFreeHDA.Appendix.Actual
