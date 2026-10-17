import CounterFreeHDA.InterfaceBoundaryFactors

namespace CounterFreeHDA.EndoPom
universe u
open Cubical
variable {Lab : Type u} {k : ℕ} {U A B : Cube Lab k}
    (P : EndoPom (cubeInterface U)) (α : Cubical.Face A U) (β : Cubical.Face B U)
    (hc : P.StableCompatible α β) (hw : P.pom.val.WidthLE k)

noncomputable def rightCornerInterface (n : ℕ) (hn : U.dim ≤ n) :
    BoundedArrow (Cubical.Face.activeCube U (P.boundaryStatus α β)) B :=
  (P.boundedPower hw n).toArrow.corner (P.width_pow hw n) (P.boundaryFace α β) β
    (P.boundary_right_compatible_interface α β hc hw hn)

noncomputable def rightSplitIsoInterface (m : ℕ) :
    PomsetIso ((P.middleCorner α β hw m).comp (P.rightFactorInterface α β hc hw)).pom.val
      (P.rightCornerInterface α β hc hw (m+U.dim) (by omega)).pom.val := by
  let γ := P.boundaryFace α β
  let hm := P.boundary_middle_compatible α β hw m
  let ht := P.boundary_right_compatible_interface α β hc hw (le_refl U.dim)
  let hg := (P.pow m).compatible_mul (P.pow U.dim) (P.width_pow hw m) (P.width_pow hw U.dim) γ γ β hm ht
  have hleft : ∀ i j, (P.pow U.dim).Shared i j → β.status j = Status.zero → γ.status i = Status.zero := by
    intro i j hij hj
    simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using
      P.boundary_zero_reached_interface α β hc (le_refl U.dim) i j hij hj
  have hright : ∀ i j, (P.pow m).Shared i j → γ.status i = Status.one → γ.status j = Status.one := by
    intro i j hij hi
    simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using
      P.boundary_one_through α β m i j hij (by simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using hi)
  have hzero : ∀ i, γ.status i = Status.zero → (P.pow U.dim).Shared i i ∧ β.status i = Status.zero := by
    intro i hi
    exact P.boundary_zero_persistent α β hc U.dim i (by simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using hi)
  have hone : ∀ i, γ.status i = Status.one → (P.pow m).Shared i i ∧ γ.status i = Status.one := by
    intro i hi
    exact ⟨(P.boundary_one_persistent α β m i (by simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using hi)).1,hi⟩
  let φ := (P.pow m).cornerMulIso (P.pow U.dim) (P.width_pow hw m) (P.width_pow hw U.dim)
    γ γ β hm ht hg hleft hright hzero hone
  let ψ := Arrow.cornerIso _ _ (P.powerAddIso hw m U.dim)
    (Cubical.TrackGlue.width_glue _ (P.pow m).pom.property (P.pow U.dim).pom.property (P.width_pow hw m) (P.width_pow hw U.dim))
    (P.width_pow hw (m+U.dim)) γ β hg (P.boundary_right_compatible_interface α β hc hw (by omega))
  exact φ.trans ψ

noncomputable def leftSplitIsoInterface (m : ℕ) :
    PomsetIso ((P.leftFactorInterface α β hc hw).comp (P.rightCornerInterface α β hc hw (m+U.dim) (by omega))).pom.val
      ((P.boundedPower hw (U.dim+(m+U.dim))).toArrow.corner (P.width_pow hw (U.dim+(m+U.dim))) α β
        (P.power_compatible_interface α β hc hw (by omega))).pom.val := by
  let γ := P.boundaryFace α β
  let hh := P.boundary_left_compatible_interface α β hc hw (le_refl U.dim)
  let ht := P.boundary_right_compatible_interface α β hc hw (show U.dim ≤ m+U.dim by omega)
  let hg := (P.pow U.dim).compatible_mul (P.pow (m+U.dim)) (P.width_pow hw U.dim) (P.width_pow hw (m+U.dim)) α γ β hh ht
  have hleft : ∀ i j, (P.pow (m+U.dim)).Shared i j → β.status j = Status.zero → γ.status i = Status.zero := by
    intro i j hij hj
    simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using
      P.boundary_zero_reached_interface α β hc (show U.dim ≤ m+U.dim by omega) i j hij hj
  have hright : ∀ i j, (P.pow U.dim).Shared i j → α.status i = Status.one → γ.status j = Status.one := by
    intro i j hij hi
    simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using P.boundary_one_reached_interface α β (le_refl U.dim) i j hij hi
  have hzero : ∀ i, γ.status i = Status.zero → (P.pow (m+U.dim)).Shared i i ∧ β.status i = Status.zero := by
    intro i hi
    exact P.boundary_zero_persistent α β hc (m+U.dim) i (by simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using hi)
  have hone : ∀ i, γ.status i = Status.one → (P.pow U.dim).Shared i i ∧ α.status i = Status.one := by
    intro i hi
    exact P.boundary_one_persistent α β U.dim i (by simpa only [γ,boundaryFace,Cubical.Face.ofStatuses_status] using hi)
  let φ := (P.pow U.dim).cornerMulIso (P.pow (m+U.dim)) (P.width_pow hw U.dim) (P.width_pow hw (m+U.dim))
    α γ β hh ht hg hleft hright hzero hone
  let ψ := Arrow.cornerIso _ _ (P.powerAddIso hw U.dim (m+U.dim))
    (Cubical.TrackGlue.width_glue _ (P.pow U.dim).pom.property (P.pow (m+U.dim)).pom.property (P.width_pow hw U.dim) (P.width_pow hw (m+U.dim)))
    (P.width_pow hw (U.dim+(m+U.dim))) α β hg (P.power_compatible_interface α β hc hw (by omega))
  exact φ.trans ψ

/-- **Lemma 4.3.** Fixed actual outside factors and the actual reduced pomset
factor every sufficiently large actual corner, including zero middle power. -/
noncomputable def lemma_4_3_interface (n : ℕ) (hn : 2*U.dim ≤ n) :
    PomsetIso (((P.leftFactorInterface α β hc hw).comp
      ((P.boundaryReduced α β hw).boundedPower (P.boundaryReduced_width α β hw) (n-2*U.dim))).comp
      (P.rightFactorInterface α β hc hw)).pom.val
      ((P.boundedPower hw n).toArrow.corner (P.width_pow hw n) α β
        (P.power_compatible_interface α β hc hw (by omega))).pom.val := by
  let M := P.middleCorner α β hw (n-2*U.dim)
  let A := P.leftFactorInterface α β hc hw
  let B := P.rightFactorInterface α β hc hw
  have φ : PomsetIso (((A.comp ((P.boundaryReduced α β hw).boundedPower
      (P.boundaryReduced_width α β hw) (n-2*U.dim))).comp B).pom.val) ((A.comp M).comp B).pom.val :=
    BoundedArrow.compIso (BoundedArrow.compIso (PomsetIso.refl A.pom.val)
      (P.boundaryReducedMiddleIso α β hw (n-2*U.dim))) (PomsetIso.refl B.pom.val)
  have ψ := (BoundedArrow.assocIso A M B).trans
    ((BoundedArrow.compIso (PomsetIso.refl A.pom.val) (P.rightSplitIsoInterface α β hc hw (n-2*U.dim))).trans
      (P.leftSplitIsoInterface α β hc hw (n-2*U.dim)))
  have he : U.dim + (n-2*U.dim+U.dim) = n := by omega
  exact φ.trans (by simpa only [he] using ψ)

end CounterFreeHDA.EndoPom
