import Paper20.FillingExtension

namespace Paper20.YoungShapes
open Paper20.YoungCorners
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

/-- Any two actual standard Young fillings of the same actual shape are
connected by genuine valid adjacent exchanges. A maximal target cell is
first moved to the last label, then the exact smaller-shape induction is
lifted while retaining that final cell. -/
theorem filling_connected (n : ℕ) : ∀ (μ : Shape n) (t u : StandardFilling μ),
    FillingReachable t u := by
  induction n with
  | zero =>
    intro μ t u
    have he : t=u := by
      apply Subtype.ext
      apply Equiv.ext
      intro i
      exact Fin.elim0 i
    subst u
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    intro μ t u
    obtain ⟨w,htw,hlast⟩ := filling_move_corner_to_last t
      (u.val (Fin.last n)).val (filling_last_removable u)
    have hprev : fillingPrevious w=fillingPrevious u := by
      apply Subtype.ext
      change erase μ.val (w.val (Fin.last n)).val (filling_last_removable w)=
        erase μ.val (u.val (Fin.last n)).val (filling_last_removable u)
      congr 1
    let s : StandardFilling (fillingPrevious u) := hprev ▸ fillingPrefix w
    have hs := ih (fillingPrevious u) s (fillingPrefix u)
    have hup := extendFilling_reachable μ (fillingPrevious u)
      (erase_covers _ _ (filling_last_removable u)) hs
    have hew := (extendFilling_cast μ (fillingPrevious w) (fillingPrevious u) hprev
      (erase_covers _ _ (filling_last_removable w)) (erase_covers _ _ (filling_last_removable u))
      (fillingPrefix w)).trans (extendFilling_prefix w)
    dsimp only [s] at hup
    rw [hew,extendFilling_prefix] at hup
    exact htw.trans hup

end
end Paper20.YoungShapes
