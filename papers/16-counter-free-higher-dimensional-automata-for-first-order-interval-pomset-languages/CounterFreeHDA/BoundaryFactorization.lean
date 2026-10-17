import CounterFreeHDA.BoundaryFactors

namespace CounterFreeHDA.EndoPom
universe u
open Cubical
variable {Lab : Type u} {k : ℕ} {U A B : Cube Lab k}
    (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) (hw : P.pom.val.WidthLE k)

noncomputable def middleCorner (n : ℕ) :
    BoundedArrow (Cubical.Face.activeCube U (P.boundaryStatus α β)) (Cubical.Face.activeCube U (P.boundaryStatus α β)) :=
  (P.boundedPower hw n).toArrow.corner (P.width_pow hw n) (P.boundaryFace α β) (P.boundaryFace α β)
    (P.boundary_middle_compatible α β hw n)

noncomputable def rightCorner (n : ℕ) (hn : k ≤ n) :
    BoundedArrow (Cubical.Face.activeCube U (P.boundaryStatus α β)) B :=
  (P.boundedPower hw n).toArrow.corner (P.width_pow hw n) (P.boundaryFace α β) β
    (P.boundary_right_compatible α β hc hw hn)

noncomputable def rightSplitIso (m : ℕ) :
    PomsetIso ((P.middleCorner α β hw m).comp (P.rightFactor α β hc hw)).pom.val
      (P.rightCorner α β hc hw (m+k) (by omega)).pom.val := by
  let γ := P.boundaryFace α β
  let hm := P.boundary_middle_compatible α β hw m
  let ht := P.boundary_right_compatible α β hc hw (le_refl k)
  let hg := (P.pow m).compatible_mul (P.pow k) (P.width_pow hw m) (P.width_pow hw k) γ γ β hm ht
  have hleft : ∀ i j, (P.pow k).Shared i j → β.status j = Status.zero → γ.status i = Status.zero := by
    intro i j hij hj
    simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using
      P.boundary_zero_reached α β hc (le_refl k) i j hij hj
  have hright : ∀ i j, (P.pow m).Shared i j → γ.status i = Status.one → γ.status j = Status.one := by
    intro i j hij hi
    simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using
      P.boundary_one_through α β m i j hij (by simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using hi)
  have hzero : ∀ i, γ.status i = Status.zero → (P.pow k).Shared i i ∧ β.status i = Status.zero := by
    intro i hi
    exact P.boundary_zero_persistent α β hc k i (by simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using hi)
  have hone : ∀ i, γ.status i = Status.one → (P.pow m).Shared i i ∧ γ.status i = Status.one := by
    intro i hi
    exact ⟨(P.boundary_one_persistent α β m i (by simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using hi)).1,hi⟩
  let φ := (P.pow m).cornerMulIso (P.pow k) (P.width_pow hw m) (P.width_pow hw k)
    γ γ β hm ht hg hleft hright hzero hone
  let ψ := Arrow.cornerIso _ _ (P.powerAddIso hw m k)
    (Cubical.TrackGlue.width_glue _ (P.pow m).pom.property (P.pow k).pom.property (P.width_pow hw m) (P.width_pow hw k))
    (P.width_pow hw (m+k)) γ β hg (P.boundary_right_compatible α β hc hw (by omega))
  exact φ.trans ψ

noncomputable def leftSplitIso (m : ℕ) :
    PomsetIso ((P.leftFactor α β hc hw).comp (P.rightCorner α β hc hw (m+k) (by omega))).pom.val
      ((P.boundedPower hw (k+(m+k))).toArrow.corner (P.width_pow hw (k+(m+k))) α β
        (P.power_compatible α β hc hw (by omega))).pom.val := by
  let γ := P.boundaryFace α β
  let hh := P.boundary_left_compatible α β hc hw (le_refl k)
  let ht := P.boundary_right_compatible α β hc hw (show k ≤ m+k by omega)
  let hg := (P.pow k).compatible_mul (P.pow (m+k)) (P.width_pow hw k) (P.width_pow hw (m+k)) α γ β hh ht
  have hleft : ∀ i j, (P.pow (m+k)).Shared i j → β.status j = Status.zero → γ.status i = Status.zero := by
    intro i j hij hj
    simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using
      P.boundary_zero_reached α β hc (show k ≤ m+k by omega) i j hij hj
  have hright : ∀ i j, (P.pow k).Shared i j → α.status i = Status.one → γ.status j = Status.one := by
    intro i j hij hi
    simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using P.boundary_one_reached α β (le_refl k) i j hij hi
  have hzero : ∀ i, γ.status i = Status.zero → (P.pow (m+k)).Shared i i ∧ β.status i = Status.zero := by
    intro i hi
    exact P.boundary_zero_persistent α β hc (m+k) i (by simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using hi)
  have hone : ∀ i, γ.status i = Status.one → (P.pow k).Shared i i ∧ α.status i = Status.one := by
    intro i hi
    exact P.boundary_one_persistent α β k i (by simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using hi)
  let φ := (P.pow k).cornerMulIso (P.pow (m+k)) (P.width_pow hw k) (P.width_pow hw (m+k))
    α γ β hh ht hg hleft hright hzero hone
  let ψ := Arrow.cornerIso _ _ (P.powerAddIso hw k (m+k))
    (Cubical.TrackGlue.width_glue _ (P.pow k).pom.property (P.pow (m+k)).pom.property (P.width_pow hw k) (P.width_pow hw (m+k)))
    (P.width_pow hw (k+(m+k))) α β hg (P.power_compatible α β hc hw (by omega))
  exact φ.trans ψ

/-- **Lemma 4.3.** Fixed actual outside factors and the actual reduced pomset
factor every sufficiently large actual corner, including zero middle power. -/
noncomputable def lemma_4_3 (n : ℕ) (hn : 2*k ≤ n) :
    PomsetIso (((P.leftFactor α β hc hw).comp
      ((P.boundaryReduced α β hw).boundedPower (P.boundaryReduced_width α β hw) (n-2*k))).comp
      (P.rightFactor α β hc hw)).pom.val
      ((P.boundedPower hw n).toArrow.corner (P.width_pow hw n) α β
        (P.power_compatible α β hc hw (by omega))).pom.val := by
  let M := P.middleCorner α β hw (n-2*k)
  let A := P.leftFactor α β hc hw
  let B := P.rightFactor α β hc hw
  have φ : PomsetIso (((A.comp ((P.boundaryReduced α β hw).boundedPower
      (P.boundaryReduced_width α β hw) (n-2*k))).comp B).pom.val) ((A.comp M).comp B).pom.val :=
    BoundedArrow.compIso (BoundedArrow.compIso (PomsetIso.refl A.pom.val)
      (P.boundaryReducedMiddleIso α β hw (n-2*k))) (PomsetIso.refl B.pom.val)
  have ψ := (BoundedArrow.assocIso A M B).trans
    ((BoundedArrow.compIso (PomsetIso.refl A.pom.val) (P.rightSplitIso α β hc hw (n-2*k))).trans
      (P.leftSplitIso α β hc hw (n-2*k)))
  have he : k + (n-2*k+k) = n := by omega
  exact φ.trans (by simpa only [he] using ψ)

end CounterFreeHDA.EndoPom
