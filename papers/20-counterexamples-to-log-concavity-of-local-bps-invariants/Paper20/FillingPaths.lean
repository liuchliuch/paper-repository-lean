import Paper20.StandardFillings

namespace Paper20.YoungShapes
open Finset Paper20.YoungCorners
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

@[simp] lemma position_last {n : ℕ} {μ : Shape (n+1)} (t : Path (n+1) μ) :
    position t (Fin.last n)=(stepCorner t.1).val := by
  change (cellList t.2 ++ [(stepCorner t.1).val]).get _=_
  simp only [List.get_eq_getElem,List.getElem_append,cellList_length,Fin.val_last,lt_self_iff_false,
    ↓reduceDIte,Nat.sub_self,List.getElem_singleton]

@[simp] lemma position_castSucc {n : ℕ} {μ : Shape (n+1)} (t : Path (n+1) μ) (i : Fin n) :
    position t i.castSucc=position t.2 i := by
  change (cellList t.2 ++ [(stepCorner t.1).val]).get _=(cellList t.2).get _
  simp only [List.get_eq_getElem,List.getElem_append,cellList_length,Fin.coe_castSucc,i.isLt,↓reduceDIte]

/-- Delete the largest label recursively to obtain an actual saturated
path from any genuine standard filling. -/
def fillingPath : (n : ℕ) → (μ : Shape n) → StandardFilling μ → Path n μ
  | 0,_,_ => PUnit.unit
  | n+1,_,t =>
    ⟨⟨fillingPrevious t,erase_covers _ _ (filling_last_removable t)⟩,
      fillingPath n (fillingPrevious t) (fillingPrefix t)⟩

lemma fillingPath_corner {n : ℕ} {μ : Shape (n+1)} (t : StandardFilling μ) :
    (stepCorner (fillingPath (n+1) μ t).1).val=(t.val (Fin.last n)).val := by
  apply erase_injective μ.val _ _ (stepCorner_removable _) (filling_last_removable t)
  exact (previous_eq_erase (fillingPath (n+1) μ t).1).symm

/-- Reconstruction by genuine corner deletion recovers every actual
standard filling, including the complete labels and cells. -/
theorem pathFilling_fillingPath (n : ℕ) : ∀ (μ : Shape n) (t : StandardFilling μ),
    pathFilling (fillingPath n μ t)=t := by
  induction n with
  | zero =>
    intro μ t
    apply Subtype.ext
    apply Equiv.ext
    intro i
    exact Fin.elim0 i
  | succ n ih =>
    intro μ t
    apply Subtype.ext
    apply Equiv.ext
    intro i
    apply Subtype.ext
    change position (fillingPath (n+1) μ t) i=(t.val i).val
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [position_last,fillingPath_corner]
    · rw [position_castSucc]
      have he := congrArg (fun s : StandardFilling (fillingPrevious t) => (s.val j).val)
        (ih (fillingPrevious t) (fillingPrefix t))
      exact he

/-- Two actual saturated paths with the same standard filling coincide.
Their last corner determines the preceding diagram, and then the finite
prefix filling determines the entire preceding path. -/
theorem pathFilling_injective (n : ℕ) : ∀ μ : Shape n,
    Function.Injective (pathFilling (μ:=μ)) := by
  induction n with
  | zero => intro μ t u he; exact Subsingleton.elim (α:=PUnit) t u
  | succ n ih =>
    intro μ t u he
    have hc : (stepCorner t.1).val=(stepCorner u.1).val := by
      have h := congrArg (fun s : StandardFilling μ => (s.val (Fin.last n)).val) he
      change position t (Fin.last n)=position u (Fin.last n) at h
      simpa only [position_last] using h
    have hk : t.1=u.1 := by
      apply Subtype.ext
      apply Subtype.ext
      rw [previous_eq_erase t.1,previous_eq_erase u.1]
      congr 1
    rcases t with ⟨κ,t⟩
    rcases u with ⟨ν,u⟩
    dsimp only at hk
    subst ν
    have ht : pathFilling t=pathFilling u := by
      apply Subtype.ext
      apply Equiv.ext
      intro j
      apply Subtype.ext
      have h := congrArg (fun s : StandardFilling μ => (s.val j.castSucc).val) he
      change position (⟨κ,t⟩:Path (n+1) μ) j.castSucc=
        position (⟨κ,u⟩:Path (n+1) μ) j.castSucc at h
      simpa only [position_castSucc] using h
    have htu := ih κ.val ht
    exact Sigma.ext rfl (heq_of_eq htu)

/-- Actual saturated paths and genuine standard Young fillings are in
bijection. No independent tableau-count or representation axiom is used. -/
def pathEquivFilling {n : ℕ} (μ : Shape n) : Path n μ ≃ StandardFilling μ :=
  Equiv.ofBijective pathFilling ⟨pathFilling_injective n μ,by
    intro t
    exact ⟨fillingPath n μ t,pathFilling_fillingPath n μ t⟩⟩

theorem standardFilling_card {n : ℕ} (μ : Shape n) :
    Fintype.card (StandardFilling μ)=dimension μ.val := by
  rw [← Fintype.card_congr (pathEquivFilling μ),path_card]

end
end Paper20.YoungShapes
