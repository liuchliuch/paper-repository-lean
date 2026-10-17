import CounterFreeHDA.CornerGluing
import CounterFreeHDA.EndoDeletionRestrictions

namespace CounterFreeHDA.EndoPom
universe u
open Cubical
variable {Lab : Type u} {k : ℕ} {U A B T : Cube Lab k}

theorem compatible_mul (P Q : EndoPom (cubeInterface U))
    (hP : P.pom.val.WidthLE k) (hQ : Q.pom.val.WidthLE k)
    (α : Cubical.Face A U) (γ : Cubical.Face T U) (β : Cubical.Face B U)
    (ha : (P.bounded hP).toArrow.Compatible α γ)
    (hb : (Q.bounded hQ).toArrow.Compatible γ β) :
    ((P.bounded hP).comp (Q.bounded hQ)).toArrow.Compatible α β := by
  intro i j hij
  change (P.mul Q).Shared i j at hij
  obtain ⟨l,hil,hlj⟩ := (shared_mul P Q i j).mp hij
  exact (ha i l hil).trans (hb l j hlj)

/-- Actual corner gluing from exact propagation of the zero and one seam
assignments. The construction derives the event bijection and both orders. -/
noncomputable def cornerMulIso (P Q : EndoPom (cubeInterface U))
    (hP : P.pom.val.WidthLE k) (hQ : Q.pom.val.WidthLE k)
    (α : Cubical.Face A U) (γ : Cubical.Face T U) (β : Cubical.Face B U)
    (ha : (P.bounded hP).toArrow.Compatible α γ)
    (hb : (Q.bounded hQ).toArrow.Compatible γ β)
    (hc : ((P.bounded hP).comp (Q.bounded hQ)).toArrow.Compatible α β)
    (hleft : ∀ i j, Q.Shared i j → β.status j = Status.zero → γ.status i = Status.zero)
    (hright : ∀ i j, P.Shared i j → α.status i = Status.one → γ.status j = Status.one)
    (hzero : ∀ i, γ.status i = Status.zero → Q.Shared i i ∧ β.status i = Status.zero)
    (hone : ∀ i, γ.status i = Status.one → P.Shared i i ∧ α.status i = Status.one) :
    PomsetIso (((P.bounded hP).toArrow.corner hP α γ ha).comp
      ((Q.bounded hQ).toArrow.corner hQ γ β hb)).pom.val
      (((P.bounded hP).comp (Q.bounded hQ)).toArrow.corner
        (Cubical.TrackGlue.width_glue _ P.pom.property Q.pom.property hP hQ) α β hc).pom.val := by
  let m := P.mulMatch Q
  let f := P.sourceStatus α.status
  let g := P.targetStatus γ.status
  let h := Q.targetStatus β.status
  have hgs : Corners.seamStatus m g = Q.sourceStatus γ.status := by
    funext i
    exact congrArg γ.status (Fin.ext rfl)
  have hα : Corners.Compatible P.pom.val f g :=
    (P.bounded hP).toArrow.compatible_raw α γ ha
  have hβ : Corners.Compatible Q.pom.val (Corners.seamStatus m g) h := by
    rw [hgs]
    exact (Q.bounded hQ).toArrow.compatible_raw γ β hb
  have hC : Corners.Compatible (glueData P.pom.val Q.pom.val m) f h :=
    ((P.bounded hP).comp (Q.bounded hQ)).toArrow.compatible_raw α β hc
  have hl : ∀ e, Corners.Deleted (glueData P.pom.val Q.pom.val m) f h (Cubical.TrackGlue.leftEvent m e) ↔
      Corners.Deleted P.pom.val f g e := P.deleted_left Q α.status γ.status β.status hleft hzero
  have hr : ∀ e, Corners.Deleted (glueData P.pom.val Q.pom.val m) f h (Cubical.TrackGlue.rightEvent m e) ↔
      Corners.Deleted Q.pom.val (Corners.seamStatus m g) h e := by
    rw [hgs]
    exact P.deleted_right Q α.status γ.status β.status hright hone
  let R := Corners.gluingAtlas m f g h hα hβ hC hl hr P.pom.property Q.pom.property
    (P.retained_seam_star α.status γ.status hα hone)
  let φ := R.iso (Corners.isIntervalPom _ _ _ P.pom.property hα)
    (Corners.isIntervalPom _ _ _ Q.pom.property hβ)
    (Corners.isIntervalPom _ _ _ (glueData_isIntervalPom m P.pom.property Q.pom.property) hC)
  have hdata : Corners.data Q.pom.val (Corners.seamStatus m g) h hβ =
      Corners.data Q.pom.val (Q.sourceStatus γ.status) h
        ((Q.bounded hQ).toArrow.compatible_raw γ β hb) := by
    congr 1
  have ψ : PomsetIso ((Q.bounded hQ).toArrow.corner hQ γ β hb).pom.val
      (Corners.data Q.pom.val (Corners.seamStatus m g) h hβ) := by
    rw [hdata]
    exact PomsetIso.refl _
  exact (PomsetIso.glueIso (PomsetIso.refl _) ψ _ _).trans φ

end CounterFreeHDA.EndoPom
