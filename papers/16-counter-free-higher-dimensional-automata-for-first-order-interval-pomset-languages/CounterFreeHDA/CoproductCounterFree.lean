import CounterFreeHDA.IdealCounterFree

namespace CounterFreeHDA.Cubical.OrderedPomsetRecognizer
universe u v
variable {Lab : Type u} {k h : ℕ} {L : Set (IntervalPom Lab)}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h) {U V S T : Cube Lab k}

theorem component_reachability (P : IntervalPom Lab)
    (x : IdealDiagram F.C F.order F.stepImage S U) (y : IdealDiagram F.C F.order F.stepImage S V) :
    (⟨S,y⟩ : F.hda.Cell V) ∈ F.hda.toPrecubical.dPom ⟨S,x⟩ P ↔
      y ∈ (ideal F.C F.order F.stepImage S).dPom x P := by
  constructor
  · rintro ⟨p,hr,hi⟩
    obtain ⟨he,hr'⟩ := run_component F.C F.order F.stepImage F.J p x y hr
    exact ⟨p,by simpa only [eq_rec_constant] using hr',hi⟩
  · rintro ⟨p,hr,hi⟩
    exact ⟨p,(componentInclusion F.C F.order F.stepImage F.J S).map_run hr,hi⟩

theorem no_cross_component (hne : S ≠ T) (P : IntervalPom Lab)
    (x : IdealDiagram F.C F.order F.stepImage S U) (y : IdealDiagram F.C F.order F.stepImage T V) :
    (⟨T,y⟩ : F.hda.Cell V) ∉ F.hda.toPrecubical.dPom ⟨S,x⟩ P := by
  rintro ⟨p,hr,_⟩
  exact hne (run_component F.C F.order F.stepImage F.J p x y hr).choose

/-- Full reachability stabilization, including labels without a supplied
width bound. Positive reachable powers force the original label's width. -/
theorem full_power_stable (P : EndoPom (cubeInterface U)) (x y : F.hda.Cell U)
    (n : ℕ) (hn : 2*k+h ≤ n) (hi : k+1 ≤ n) :
    y ∈ F.hda.toPrecubical.dPom x (P.pow n).pom ↔
    y ∈ F.hda.toPrecubical.dPom x (P.pow (n+1)).pom := by
  classical
  by_cases hw : P.pom.val.WidthLE k
  · rcases x with ⟨S,x⟩
    rcases y with ⟨T,y⟩
    by_cases he : S = T
    · subst T
      exact (F.component_reachability _ x y).trans
        ((F.component_power_stable P hw x y n hn hi).trans (F.component_reachability _ x y).symm)
    · exact iff_of_false (F.no_cross_component he _ x y) (F.no_cross_component he _ x y)
  · constructor
    · intro hr
      exact False.elim (hw (P.width_of_positive_power (by omega) (F.hda.toPrecubical.reachable_width hr)))
    · intro hr
      exact False.elim (hw (P.width_of_positive_power (by omega) (F.hda.toPrecubical.reachable_width hr)))

/-- The actual constructed HDA satisfies the full pomset counter-free
condition with one exponent for all cells and all endomorphism pomsets. -/
theorem counterFreePom : F.hda.toPrecubical.CounterFreePom := by
  refine ⟨max 1 (2*k+h),by omega,?_⟩
  intro U x P
  ext y
  exact F.full_power_stable P x y _ (by omega) (by omega)

end CounterFreeHDA.Cubical.OrderedPomsetRecognizer
