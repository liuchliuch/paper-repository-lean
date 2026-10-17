import CounterFreeHDA.ResidualClassification
import CounterFreeHDA.UnarySteps

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

theorem prefixSubset_ofWord {U : UCube} (p : Word Completion.emptyCube U) :
    prefixSubset (BoundedArrow.ofWord p) = originalExecute p (mask 2 1) := by
  funext i
  apply Bool.eq_iff_iff.mpr
  exact (prefixSubset_iff (BoundedArrow.ofWord p) i).trans
    ((Actual.originalHDA.toPrecubical.dPom_word p _ _).trans (originalExecute_initial p i).symm)

theorem prefixResidual_ofWord {U : UCube} (p : Word Completion.emptyCube U) :
    prefixResidual (BoundedArrow.ofWord p) = residualLanguage U (wordKind p (0 : Fin 4)) := by
  rw [prefixResidual_eq_suffix,prefixSubset_ofWord]
  exact represented_suffix_eq (execute_represents p (mask 2 1) (0 : Fin 4) represents_initial)
    (representative_represents U _)

/-- Short actual prefixes reach every displayed semantic residual, including
all three typed empty residuals. -/
theorem prefixWord_exists (U : UCube) (r : Kind U) :
    ∃ p : Word Completion.emptyCube U, wordKind p (0 : Fin 4) = r := by
  rcases U with ⟨n,lab⟩
  fin_cases n
  · have hl : lab = (Fin.elim0 : Fin 0 → Unit) := Subsingleton.elim _ _
    subst lab
    change Fin 4 at r
    fin_cases r
    · exact ⟨.nil _,rfl⟩
    · exact ⟨Unary.a,rfl⟩
    · exact ⟨Unary.a.append Unary.a,rfl⟩
    · exact ⟨Unary.dead0,rfl⟩
  · have hl : lab = (fun _ : Fin 1 => ()) := Subsingleton.elim _ _
    subst lab
    change Fin 4 at r
    fin_cases r
    · exact ⟨Unary.E,rfl⟩
    · exact ⟨Unary.F,rfl⟩
    · exact ⟨Unary.G,rfl⟩
    · exact ⟨Unary.dead1,rfl⟩
  · have hl : lab = (fun _ : Fin 2 => ()) := Subsingleton.elim _ _
    subst lab
    change Fin 3 at r
    fin_cases r
    · exact ⟨Unary.H,rfl⟩
    · exact ⟨Unary.I,rfl⟩
    · exact ⟨Unary.dead2,rfl⟩

theorem every_residual_reachable (U : UCube) (r : Kind U) :
    ∃ P : Prefix U, prefixResidual P = residualLanguage U r := by
  obtain ⟨p,hp⟩ := prefixWord_exists U r
  exact ⟨BoundedArrow.ofWord p,by rw [prefixResidual_ofWord,hp]⟩

def acceptBit (r : Fin 4) : Bool := decide (r = 0 ∨ r = 2)

theorem suffix_ofWord {U : UCube} (x : Subset (size U.1)) (p : Word U Completion.emptyCube) :
    BoundedArrow.ofWord p ∈ suffix x ↔ originalExecute p x 0 = true := by
  change (∃ i, x i = true ∧ Actual.indexCell Completion.emptyCube 0 ∈
    Actual.originalHDA.toPrecubical.dPom (Actual.indexCell U i) p.label.pom) ↔ _
  rw [originalExecute_iff]
  exact exists_congr (fun i => and_congr Iff.rfl (Actual.originalHDA.toPrecubical.dPom_word p _ _))

theorem residual_mem_ofWord {U : UCube} (p : Word U Completion.emptyCube) (r : Kind U) :
    BoundedArrow.ofWord p ∈ residualLanguage U r ↔ acceptBit (wordKind p r) = true := by
  change BoundedArrow.ofWord p ∈ suffix (representative U.1 r) ↔ _
  rw [suffix_ofWord]
  simpa only [acceptBit,decide_eq_true_eq] using
    represents_acceptance _ _ (execute_represents p (representative U.1 r) r (representative_represents U r))

theorem separate0 : ∀ r s : Fin 4, r ≠ s → ∃ b : Bool,
    acceptBit (wordKind (if b then Unary.a else .nil Unary.zero) r) ≠
      acceptBit (wordKind (if b then Unary.a else .nil Unary.zero) s) := by decide

theorem separate1 : ∀ r s : Fin 4, r ≠ s → ∃ b : Bool,
    acceptBit (wordKind (if b then Unary.end1.append Unary.a else Unary.end1) r) ≠
      acceptBit (wordKind (if b then Unary.end1.append Unary.a else Unary.end1) s) := by decide

theorem separate2 : ∀ r s : Fin 3, r ≠ s → ∃ b : Bool,
    acceptBit (wordKind (if b then Unary.end2.append Unary.a else Unary.end2) r) ≠
      acceptBit (wordKind (if b then Unary.end2.append Unary.a else Unary.end2) s) := by decide

theorem separating_actual_suffix (U : UCube) (r s : Kind U) (hrs : r ≠ s) :
    ∃ p : Word U Completion.emptyCube, acceptBit (wordKind p r) ≠ acceptBit (wordKind p s) := by
  rcases U with ⟨n,lab⟩
  fin_cases n
  · have hl : lab = (Fin.elim0 : Fin 0 → Unit) := Subsingleton.elim _ _
    subst lab
    obtain ⟨b,hb⟩ := separate0 r s hrs
    exact ⟨if b then Unary.a else .nil Unary.zero,hb⟩
  · have hl : lab = (fun _ : Fin 1 => ()) := Subsingleton.elim _ _
    subst lab
    obtain ⟨b,hb⟩ := separate1 r s hrs
    exact ⟨if b then Unary.end1.append Unary.a else Unary.end1,hb⟩
  · have hl : lab = (fun _ : Fin 2 => ()) := Subsingleton.elim _ _
    subst lab
    obtain ⟨b,hb⟩ := separate2 r s hrs
    exact ⟨if b then Unary.end2.append Unary.a else Unary.end2,hb⟩

/-- Distinctness is proved by actual suffix pomsets, rather than merely by
unequal finite names or transition-table rows. -/
theorem residualLanguage_injective (U : UCube) : Function.Injective (residualLanguage U) := by
  intro r s h
  by_contra hrs
  obtain ⟨p,hp⟩ := separating_actual_suffix U r s hrs
  apply hp
  apply Bool.eq_iff_iff.mpr
  exact (residual_mem_ofWord p r).symm.trans
    (((congrArg (fun R => BoundedArrow.ofWord p ∈ R) h).to_iff).trans (residual_mem_ofWord p s))

theorem nondead_language_nonempty (U : UCube) (r : Kind U) (hr : r ≠ dead U.1) :
    (residualLanguage U r).Nonempty := by
  apply Set.nonempty_iff_ne_empty.mpr
  intro he
  exact hr (residualLanguage_injective U (he.trans (dead_language U).symm))

end CounterFreeHDA.Appendix.Residual
