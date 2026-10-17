import CounterFreeHDA.ProfileFaces

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

noncomputable def templateProfile (U : UCube) (i : Fin (Completion.profileSize U.1)) : ActualProfile U :=
  ⟨templateCode U i,live_profile_reachable U i⟩

/-- Every run of the displayed completion is a run of the full semantic
profile completion, with all actual prefix-deletion coordinates retained. -/
theorem fullProfile_of_completion {U V : UCube} (p : Word U V)
    (i : Fin (Completion.profileSize U.1)) (j : Fin (Completion.profileSize V.1))
    (hr : Completion.completionHDA.Run p (Completion.indexCell U i) (Completion.indexCell V j)) :
    FullProfileRun p (templateProfile U i) (templateProfile V j) := by
  induction p with
  | nil U =>
    have he := (Completion.completionHDA.toPrecubical.run_nil_iff _ _).mp hr
    have hij := Completion.indexCell_injective U he
    subst j
    exact .nil _
  | cons s p ih =>
    cases s with
    | start f hf hd =>
      obtain ⟨z,hiz,hrest⟩ := (Completion.completionHDA.toPrecubical.run_start_iff f hf hd p _ _).mp hr
      obtain ⟨l,rfl⟩ := Completion.indexCell_surjective _ z
      obtain ⟨a,hcode,hface⟩ := lower_profile_faces _ _ f hf l
      have he := Completion.indexCell_injective _ (hiz.trans hface)
      subst a
      exact .start f hf hd (z := templateProfile _ l) hcode.symm (ih l j hrest)
    | stop f hf hd =>
      have hrest := (Completion.completionHDA.toPrecubical.run_stop_iff f hf hd p _ _).mp hr
      obtain ⟨a,hcode,hface⟩ := upper_profile_faces _ _ f hf hd i
      rw [hface] at hrest
      exact .stop f hf hd hcode.symm (ih a j hrest)

/-- A run whose target is live never leaves the ten live tuples. This is the
formal no-return argument, covering every dead actual prefix profile. -/
theorem completion_of_fullProfile {U V : UCube} {p : Word U V}
    {x : ActualProfile U} {y : ActualProfile V} (hr : FullProfileRun p x y) (hy : liveCode V y.val) :
    ∃ (i : Fin (Completion.profileSize U.1)) (j : Fin (Completion.profileSize V.1)),
      x.val = templateCode U i ∧ y.val = templateCode V j ∧
        Completion.completionHDA.Run p (Completion.indexCell U i) (Completion.indexCell V j) := by
  induction hr with
  | nil x =>
    obtain ⟨P,hP⟩ := x.property
    obtain ⟨i,hi⟩ := live_profile_exhaustive P (hP.symm ▸ hy)
    exact ⟨i,i,hP.symm.trans hi,hP.symm.trans hi,.nil _⟩
  | @start U V W f hf hd p x z y he hr ih =>
    have hz : liveCode V z.val := by
      by_contra h
      exact dead_no_return hr h hy
    obtain ⟨l,j,hz',hy',hrest⟩ := ih hy
    obtain ⟨i,hcode,hface⟩ := lower_profile_faces U V f hf l
    have hx' : x.val = templateCode U i := he.trans (by rw [hz']; exact hcode)
    exact ⟨i,j,hx',hy',by
      apply (Completion.completionHDA.toPrecubical.run_start_iff f hf hd p _ _).mpr
      exact ⟨Completion.indexCell V l,hface.symm,hrest⟩⟩
  | @stop U V W f hf hd p x z y he hr ih =>
    have hx : liveCode U x.val := by
      by_contra h
      have hz : ¬ liveCode V z.val := by
        unfold liveCode at h ⊢
        push_neg at h ⊢
        rw [he,update_empty,h,code_dead_step (.stop f hf hd)]
      exact dead_no_return hr hz hy
    obtain ⟨P,hP⟩ := x.property
    obtain ⟨i,hi⟩ := live_profile_exhaustive P (hP.symm ▸ hx)
    have hx' := hP.symm.trans hi
    obtain ⟨a,hcode,hface⟩ := upper_profile_faces V U f hf hd i
    obtain ⟨l,j,hz',hy',hrest⟩ := ih hy
    have hal : a = l := templateCode_injective V
      ((hcode.symm.trans (by rw [← hx']; exact he.symm)).trans hz')
    subst l
    exact ⟨i,j,hx',hy',by
      apply (Completion.completionHDA.toPrecubical.run_stop_iff f hf hd p _ _).mpr
      rw [hface]
      exact hrest⟩

/-- Retaining the omitted dead profiles changes no live endpoint set. -/
theorem full_completion_live_endpoints {U V : UCube} (p : Word U V)
    (i : Fin (Completion.profileSize U.1)) (j : Fin (Completion.profileSize V.1)) :
    FullProfileRun p (templateProfile U i) (templateProfile V j) ↔
      Completion.completionHDA.Run p (Completion.indexCell U i) (Completion.indexCell V j) := by
  constructor
  · intro hr
    obtain ⟨a,b,ha,hb,h⟩ := completion_of_fullProfile hr (templateCode_live V j)
    have hai := templateCode_injective U ha
    have hbj := templateCode_injective V hb
    subst a
    subst b
    exact h
  · exact fullProfile_of_completion p i j

end CounterFreeHDA.Appendix.Residual

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

def fullProfileDPom {U V : UCube} (x : ActualProfile U) (P : IntervalPom Unit) : Set (ActualProfile V) :=
  {y | ∃ p : Word U V, FullProfileRun p x y ∧ IntervalPomIso p.label.pom P}

theorem full_profile_pomset_endpoints {U V : UCube} (P : IntervalPom Unit)
    (i : Fin (Completion.profileSize U.1)) (j : Fin (Completion.profileSize V.1)) :
    templateProfile V j ∈ fullProfileDPom (templateProfile U i) P ↔
      Completion.indexCell V j ∈ Completion.completionHDA.toPrecubical.dPom (Completion.indexCell U i) P := by
  exact exists_congr (fun p => and_congr (full_completion_live_endpoints p i j) Iff.rfl)

/-- Adding every omitted dead actual deletion profile preserves the
period-two endpoint relation on the three live vertices. -/
theorem full_completion_period_two (n : ℕ) (i j : Fin 3) :
    templateProfile Completion.emptyCube j ∈ fullProfileDPom (templateProfile Completion.emptyCube i)
      (Completion.letter.pow n).pom ↔ pow residualA n i j = true := by
  exact (full_profile_pomset_endpoints (U := Completion.emptyCube) (V := Completion.emptyCube) (Completion.letter.pow n).pom i j).trans (Completion.power_relation n i j)

theorem full_completion_no_exponent : ¬ ∃ N : ℕ, 1 ≤ N ∧
    ∀ (U : UCube) (x : ActualProfile U) (P : EndoPom (cubeInterface U)),
      fullProfileDPom (V := U) x (P.pow N).pom = fullProfileDPom x (P.pow (N+1)).pom := by
  rintro ⟨N,hN,H⟩
  apply residual_pow_ne_succ N hN
  funext i j
  apply Bool.eq_iff_iff.mpr
  exact (full_completion_period_two N i j).symm.trans
    (((congrArg (fun s => templateProfile Completion.emptyCube j ∈ s)
      (H Completion.emptyCube (templateProfile Completion.emptyCube i) Completion.letter)).to_iff).trans
        (full_completion_period_two (N+1) i j))

end CounterFreeHDA.Appendix.Residual
