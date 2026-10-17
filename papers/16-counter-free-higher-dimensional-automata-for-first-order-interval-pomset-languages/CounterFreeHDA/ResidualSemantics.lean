import CounterFreeHDA.AppendixLanguageEquality

namespace CounterFreeHDA.Cubical.HDA
universe u v
variable {Lab : Type u} {k : ℕ} (X : HDA.{u,v} Lab k)

theorem language_iso {P Q : IntervalPom Lab} (φ : PomsetIso P.val Q.val) :
    P ∈ X.LangPom ↔ Q ∈ X.LangPom := by
  constructor
  · rintro ⟨U,V,x,y,hi,hf,p,hr,⟨ψ⟩⟩
    exact ⟨U,V,x,y,hi,hf,p,hr,⟨ψ.trans φ⟩⟩
  · rintro ⟨U,V,x,y,hi,hf,p,hr,⟨ψ⟩⟩
    exact ⟨U,V,x,y,hi,hf,p,hr,⟨ψ.trans φ.symm⟩⟩

end CounterFreeHDA.Cubical.HDA

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare
abbrev UCube := Cube Unit 2
abbrev Tail (U : UCube) := BoundedArrow U Completion.emptyCube
abbrev Prefix (U : UCube) := BoundedArrow Completion.emptyCube U

/-- The actual canonical suffix residual r(P), defined by actual pomset
gluing and actual accepted language, with no finite-state surrogate premise. -/
def prefixResidual {U : UCube} (P : Prefix U) : Set (Tail U) :=
  {Q | (P.comp Q).pom ∈ Actual.originalHDA.LangPom}

/-- The suffix language of a subset of actual cells, at its actual interface. -/
def suffix {U : UCube} (x : Subset (size U.1)) : Set (Tail U) :=
  {Q | ∃ i, x i = true ∧ Actual.indexCell Completion.emptyCube 0 ∈
    Actual.originalHDA.toPrecubical.dPom (Actual.indexCell U i) Q.pom}

noncomputable def prefixSubset {U : UCube} (P : Prefix U) : Subset (size U.1) :=
  originalExecute P.representative (mask 2 1)

theorem original_closed_acceptance (P : IntervalPom Unit) :
    P ∈ Actual.originalHDA.LangPom ↔ Actual.indexCell Completion.emptyCube 0 ∈
      Actual.originalHDA.toPrecubical.dPom (Actual.indexCell Completion.emptyCube 0) P := by
  rw [original_language_iff]
  constructor
  · rintro ⟨p,hp,hi⟩
    exact ⟨p,(originalExecute_initial p 0).mp hp,hi⟩
  · rintro ⟨p,hp,hi⟩
    exact ⟨p,(originalExecute_initial p 0).mpr hp,hi⟩

theorem prefixSubset_iff {U : UCube} (P : Prefix U) (i : Fin (size U.1)) :
    prefixSubset P i = true ↔ Actual.indexCell U i ∈
      Actual.originalHDA.toPrecubical.dPom (Actual.indexCell Completion.emptyCube 0) P.pom := by
  rw [← Actual.originalHDA.toPrecubical.dPom_iso P.representativeIso (Actual.indexCell Completion.emptyCube 0),
    Actual.originalHDA.toPrecubical.dPom_word]
  exact originalExecute_initial P.representative i

/-- Actual prefix residuals are exactly the suffix languages of the actual
reachable cell subsets; all nondeterministic intermediate cells are retained. -/
theorem prefixResidual_eq_suffix {U : UCube} (P : Prefix U) : prefixResidual P = suffix (prefixSubset P) := by
  ext Q
  change (P.comp Q).pom ∈ Actual.originalHDA.LangPom ↔ _
  rw [original_closed_acceptance,Actual.originalHDA.toPrecubical.dPom_comp]
  constructor
  · rintro ⟨z,hz,hQ⟩
    obtain ⟨i,rfl⟩ := Actual.indexCell_surjective U z
    exact ⟨i,(prefixSubset_iff P i).mpr hz,hQ⟩
  · rintro ⟨i,hi,hQ⟩
    exact ⟨Actual.indexCell U i,(prefixSubset_iff P i).mp hi,hQ⟩

/-- Canonical suffix-residual equality is preserved by every further actual
prefix extension; this proves the right action is well-defined. -/
theorem prefixResidual_extension {U V : UCube} (P Q : Prefix U) (E : BoundedArrow U V)
    (hPQ : prefixResidual P = prefixResidual Q) : prefixResidual (P.comp E) = prefixResidual (Q.comp E) := by
  ext R
  change ((P.comp E).comp R).pom ∈ Actual.originalHDA.LangPom ↔ ((Q.comp E).comp R).pom ∈ Actual.originalHDA.LangPom
  have hm := (congrArg (fun s => E.comp R ∈ s) hPQ).to_iff
  exact (Actual.originalHDA.language_iso (BoundedArrow.assocIso P E R)).trans
    (hm.trans (Actual.originalHDA.language_iso (BoundedArrow.assocIso Q E R)).symm)

theorem suffix_empty (U : UCube) : suffix (mask (size U.1) 0) = ∅ := by
  ext Q
  simp only [suffix,Set.mem_setOf_eq,Set.mem_empty_iff_false,mask,Nat.zero_testBit,Bool.false_eq_true,false_and,exists_false]

end CounterFreeHDA.Appendix.Residual
