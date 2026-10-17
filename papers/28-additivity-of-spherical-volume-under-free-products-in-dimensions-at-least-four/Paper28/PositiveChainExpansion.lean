import Paper28.ChainIncidenceSuperlevels

/-! Every finitely supported nonnegative coordinate function is an actual
positive incidence profile of a nested chain of nonempty finite faces.
The construction subtracts its least positive level and inducts on support. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
variable {α : Type*} [DecidableEq α]

structure PositiveChainExpansion (F : Finset α) (f : α → ℝ) where
  faces : Finset (Finset α)
  chain : ∀ A ∈ faces, ∀ B ∈ faces, A ⊆ B ∨ B ⊆ A
  nonempty_faces : ∀ A ∈ faces, A.Nonempty
  support : ∀ A ∈ faces, A ⊆ F
  weight : Finset α → ℝ
  positive : ∀ A ∈ faces, 0 < weight A
  formula : ∀ x, chainIncidenceProfile faces weight x = f x

theorem exists_positive_chain_expansion (F : Finset α) (f : α → ℝ)
    (hn : ∀ x, 0 ≤ f x) (hs : ∀ x ∉ F, f x = 0) : Nonempty (PositiveChainExpansion F f) := by
  revert f
  refine Finset.strongInductionOn F ?_
  intro F ih f hn hs
  by_cases hz : ∀ x, f x = 0
  · exact ⟨{ faces := ∅
             chain := by simp
             nonempty_faces := by simp
             support := by simp
             weight := fun _ => 0
             positive := by simp
             formula := by intro x; simp [chainIncidenceProfile,hz x] }⟩
  · obtain ⟨x,hx⟩ := not_forall.mp hz
    have hxF : x ∈ F := by by_contra h; exact hx (hs x h)
    have hxPos : 0 < f x := lt_of_le_of_ne (hn x) (Ne.symm hx)
    let S : Finset α := F.filter (fun x => 0 < f x)
    have hS : S.Nonempty := ⟨x,Finset.mem_filter.mpr ⟨hxF,hxPos⟩⟩
    obtain ⟨g,hg,hMin⟩ := Finset.exists_min_image S f hS
    have hgF : g ∈ F := (Finset.mem_filter.mp hg).1
    have ha : 0 < f g := (Finset.mem_filter.mp hg).2
    let E := S.erase g
    have hEF : E ⊂ F := Finset.ssubset_iff_subset_ne.mpr ⟨(Finset.erase_subset g S).trans (Finset.filter_subset _ _),by
      intro he
      have hh : g ∈ E := he ▸ hgF
      exact Finset.notMem_erase g S hh⟩
    let f' : α → ℝ := fun x => if x ∈ S then f x-f g else 0
    have hn' : ∀ x, 0 ≤ f' x := by
      intro x
      by_cases hxS : x ∈ S
      · change 0 ≤ (if x ∈ S then f x-f g else 0)
        rw [if_pos hxS]
        exact sub_nonneg.mpr (hMin x hxS)
      · simp [f',hxS]
    have hs' : ∀ x ∉ E, f' x = 0 := by
      intro x hxE
      by_cases hxS : x ∈ S
      · have hxg : x = g := by
          by_contra h
          exact hxE (Finset.mem_erase.mpr ⟨h,hxS⟩)
        simp [f',hxg]
      · simp [f',hxS]
    obtain ⟨D⟩ := ih E hEF f' hn' hs'
    have hSC : S ∉ D.faces := by
      intro h
      exact Finset.notMem_erase g S (D.support S h hg)
    let w : Finset α → ℝ := fun A => if A = S then f g else D.weight A
    have hwOld : ∀ A ∈ D.faces, w A = D.weight A := by
      intro A hA
      change (if A = S then f g else D.weight A) = D.weight A
      exact if_neg (fun (he : A = S) => hSC (he ▸ hA))
    have hDecomp : ∀ x, f x = f' x+(if x ∈ S then f g else 0) := by
      intro x
      by_cases hxS : x ∈ S
      · simp only [f',if_pos hxS]
        ring
      · have hfx : f x = 0 := by
          by_cases hxF : x ∈ F
          · exact le_antisymm (not_lt.mp (fun h => hxS (Finset.mem_filter.mpr ⟨hxF,h⟩))) (hn x)
          · exact hs x hxF
        simp [f',hxS,hfx]
    refine ⟨{ faces := insert S D.faces
              chain := ?_
              nonempty_faces := ?_
              support := ?_
              weight := w
              positive := ?_
              formula := ?_ }⟩
    · intro A hA B hB
      rcases Finset.mem_insert.mp hA with rfl | hA
      · rcases Finset.mem_insert.mp hB with rfl | hB
        · exact Or.inl (Finset.Subset.refl _)
        · exact Or.inr ((D.support B hB).trans (Finset.erase_subset g S))
      · rcases Finset.mem_insert.mp hB with rfl | hB
        · exact Or.inl ((D.support A hA).trans (Finset.erase_subset g S))
        · exact D.chain A hA B hB
    · intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · exact hS
      · exact D.nonempty_faces A hA
    · intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · exact Finset.filter_subset _ _
      · exact (D.support A hA).trans ((Finset.erase_subset g S).trans (Finset.filter_subset _ _))
    · intro A hA
      rcases Finset.mem_insert.mp hA with rfl | hA
      · simpa only [w,if_pos rfl] using ha
      · rw [hwOld A hA]
        exact D.positive A hA
    · intro x
      have hOld : chainIncidenceProfile D.faces w x = f' x := by
        rw [← D.formula x]
        apply Finset.sum_congr rfl
        intro A hA
        rw [hwOld A hA]
      rw [chainIncidenceProfile,Finset.sum_insert hSC]
      change (if x ∈ S then w S else 0)+chainIncidenceProfile D.faces w x = _
      rw [hOld,show w S = f g from if_pos rfl]
      exact (add_comm _ _).trans (hDecomp x).symm

end Paper28
