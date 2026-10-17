import CounterFreeHDA.ResidualSubsetTable

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

theorem suffix_mem_execute {U : UCube} (x : Subset (size U.1)) (Q : Tail U) :
    Q ∈ suffix x ↔ originalExecute Q.representative x 0 = true := by
  change (∃ i, x i = true ∧ Actual.indexCell Completion.emptyCube 0 ∈
    Actual.originalHDA.toPrecubical.dPom (Actual.indexCell U i) Q.pom) ↔ _
  rw [originalExecute_iff]
  exact exists_congr (fun i => and_congr Iff.rfl
    ((Actual.pomset_relation Q i 0).trans (Actual.wordRel_iff Q.representative i 0)))

/-- Subset identifications in the finite residual table preserve all genuine
suffix languages, since their equality is propagated through every ST word. -/
theorem represented_suffix_eq {U : UCube} {x y : Subset (size U.1)} {r : Kind U}
    (hx : Represents U x r) (hy : Represents U y r) : suffix x = suffix y := by
  ext Q
  rw [suffix_mem_execute,suffix_mem_execute]
  exact (represents_acceptance _ _ (execute_represents Q.representative x r hx)).trans
    (represents_acceptance _ _ (execute_represents Q.representative y r hy)).symm

/-- These names denote actual sets of suffix pomsets, rather than only
finite states; the displayed representatives are the actual cell subsets. -/
def residualLanguage (U : UCube) (r : Kind U) : Set (Tail U) := suffix (representative U.1 r)

/-- Exhaustiveness of the actual prefix suffix-residuals. Every original
bounded prefix is represented by one of the finite semantic residuals. -/
theorem prefixResidual_classification {U : UCube} (P : Prefix U) :
    prefixResidual P = residualLanguage U (wordKind P.representative (0 : Fin 4)) := by
  rw [prefixResidual_eq_suffix]
  exact represented_suffix_eq (execute_represents P.representative (mask 2 1) (0 : Fin 4) represents_initial)
    (representative_represents U _)

theorem actual_residual_exhaustiveness {U : UCube} (P : Prefix U) :
    ∃ r : Kind U, prefixResidual P = residualLanguage U r := ⟨_,prefixResidual_classification P⟩

def dead : (a : Fin 3) → Fin (residualSize a)
  | ⟨0,_⟩ => 3
  | ⟨1,_⟩ => 3
  | ⟨2,_⟩ => 2
  | ⟨n+3,h⟩ => False.elim (by omega)

theorem dead_representative : ∀ a : Fin 3, representative a (dead a) = mask (size a) 0 := by decide

theorem dead_language (U : UCube) : residualLanguage U (dead U.1) = ∅ := by
  unfold residualLanguage
  rw [dead_representative]
  exact suffix_empty U

/-- At the empty interface, A is exactly the original accepted language,
restricted to typed closed suffixes. -/
theorem residual_A : residualLanguage Completion.emptyCube (0 : Fin 4) =
    {Q : Tail Completion.emptyCube | Q.pom ∈ Actual.originalHDA.LangPom} := by
  ext Q
  change (∃ i : Fin 2, mask 2 1 i = true ∧ Actual.indexCell Completion.emptyCube 0 ∈
    Actual.originalHDA.toPrecubical.dPom (Actual.indexCell Completion.emptyCube i) Q.pom) ↔ _
  have hm : ∀ i : Fin 2, mask 2 1 i = true ↔ i = 0 := by decide
  simp only [hm,exists_eq_left,true_and,Set.mem_setOf_eq]
  exact (original_closed_acceptance Q.pom).symm

/-- The two displayed suffix-equivalent pairs are proved at the actual
one- and two-event interfaces, with arbitrary labels of suffix pomsets. -/
theorem residual_G_merge (U : UCube) (hU : U.dim = 1) :
    suffix (mask (size U.1) 6) = suffix (mask (size U.1) 7) := by
  have h : ∀ U : UCube, U.dim = 1 → ∃ r : Kind U,
      Represents U (mask (size U.1) 6) r ∧ Represents U (mask (size U.1) 7) r := by decide
  obtain ⟨r,hx,hy⟩ := h U hU
  exact represented_suffix_eq hx hy

theorem residual_I_merge (U : UCube) (hU : U.dim = 2) :
    suffix (mask (size U.1) 6) = suffix (mask (size U.1) 7) := by
  have h : ∀ U : UCube, U.dim = 2 → ∃ r : Kind U,
      Represents U (mask (size U.1) 6) r ∧ Represents U (mask (size U.1) 7) r := by decide
  obtain ⟨r,hx,hy⟩ := h U hU
  exact represented_suffix_eq hx hy

end CounterFreeHDA.Appendix.Residual
