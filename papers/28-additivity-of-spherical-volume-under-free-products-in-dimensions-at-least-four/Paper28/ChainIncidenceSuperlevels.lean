import Paper28.CoordinateBarycentricOrbits

/-! Positive incidence profiles on a nested finite face chain have all
nonnegative superlevel sets in that same chain (or the empty face). This
is the coordinate reconstruction step for closed barycentric cells. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
variable {α : Type*} [DecidableEq α]

def chainIncidenceProfile (C : Finset (Finset α)) (w : Finset α → ℝ) (x : α) : ℝ :=
  ∑ F ∈ C, if x ∈ F then w F else 0

theorem chainIncidenceProfile_nonneg (C : Finset (Finset α)) (w : Finset α → ℝ)
    (hW : ∀ F ∈ C, 0 ≤ w F) (x : α) : 0 ≤ chainIncidenceProfile C w x := by
  apply Finset.sum_nonneg
  intro F hF
  split_ifs
  · exact hW F hF
  · exact le_rfl

theorem chainIncidenceProfile_eq_zero_outside (C : Finset (Finset α)) (w : Finset α → ℝ)
    (E : Finset α) (hMax : ∀ F ∈ C, F ⊆ E) (x : α) (hx : x ∉ E) :
    chainIncidenceProfile C w x = 0 := by
  apply Finset.sum_eq_zero
  intro F hF
  exact if_neg (fun h => hx (hMax F hF h))

theorem chainIncidenceProfile_superlevel (C : Finset (Finset α)) (w : Finset α → ℝ)
    (hW : ∀ F ∈ C, 0 ≤ w F)
    (hChain : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F) (a : ℝ) (ha : 0 ≤ a) :
    ∃ F ∈ insert ∅ C, ∀ x, a < chainIncidenceProfile C w x ↔ x ∈ F := by
  revert hW hChain a
  refine Finset.strongInductionOn C ?_
  intro C ih hW hChain a ha
  by_cases hEmpty : C = ∅
  · subst C
    refine ⟨∅,Finset.mem_insert_self _ _,?_⟩
    intro x
    simp [chainIncidenceProfile,not_lt_of_ge ha]
  · have hNonempty : C.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
    obtain ⟨E,hE,hMax⟩ := finite_face_chain_has_maximum C hNonempty hChain
    have hSplit : ∀ x, chainIncidenceProfile C w x =
        chainIncidenceProfile (C.erase E) w x+(if x ∈ E then w E else 0) := by
      intro x
      exact (Finset.sum_erase_add _ _ hE).symm
    by_cases hw : w E ≤ a
    · obtain ⟨F,hF,hLevel⟩ := ih (C.erase E) (Finset.erase_ssubset hE)
        (fun A hA => hW A (Finset.mem_of_mem_erase hA))
        (fun A hA B hB => hChain A (Finset.mem_of_mem_erase hA) B (Finset.mem_of_mem_erase hB))
        (a-w E) (sub_nonneg.mpr hw)
      have hFC : F ∈ insert ∅ C := by
        rcases Finset.mem_insert.mp hF with he | he
        · exact Finset.mem_insert.mpr (Or.inl he)
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_of_mem_erase he))
      have hFE : F ⊆ E := by
        rcases Finset.mem_insert.mp hF with he | he
        · subst F
          exact Finset.empty_subset _
        · exact hMax F (Finset.mem_of_mem_erase he)
      refine ⟨F,hFC,?_⟩
      intro x
      by_cases hx : x ∈ E
      · rw [hSplit,if_pos hx]
        exact (show a < chainIncidenceProfile (C.erase E) w x+w E ↔
          a-w E < chainIncidenceProfile (C.erase E) w x by constructor <;> intro h <;> linarith).trans (hLevel x)
      · rw [chainIncidenceProfile_eq_zero_outside C w E hMax x hx]
        exact iff_of_false (not_lt_of_ge ha) (fun h => hx (hFE h))
    · refine ⟨E,Finset.mem_insert_of_mem hE,?_⟩
      intro x
      by_cases hx : x ∈ E
      · rw [hSplit,if_pos hx]
        have hNonneg := chainIncidenceProfile_nonneg (C.erase E) w
          (fun F hF => hW F (Finset.mem_of_mem_erase hF)) x
        exact iff_of_true (by linarith) hx
      · rw [chainIncidenceProfile_eq_zero_outside C w E hMax x hx]
        exact iff_of_false (not_lt_of_ge ha) hx

end Paper28
