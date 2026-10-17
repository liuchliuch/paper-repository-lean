import CounterFreeHDA.PersistentBasis
import CounterFreeHDA.Identity

namespace CounterFreeHDA.EndoPom
universe u
open Cubical
variable {Lab : Type u} {k : ℕ} {U : Cube Lab k}

/-- The exponent-zero reduced event set is exactly a reduced identity. Its
interface type is obtained from the actual reduced gluing seam to P-R. -/
noncomputable def reducedZeroIso (P : EndoPom (cubeInterface U)) (R : Finset (Fin U.dim))
    (hR : P.PersistentSet R) (hw : P.pom.val.WidthLE k) :
    PomsetIso ((P.reduced R hR hw).pow 0).pom.val ((P.pow 0).deleteData R) := by
  classical
  let D := (P.pow 0).deleteData R
  let W := P.reducedCube R hw
  have hD : IsIntervalPom D := (P.pow 0).deleteData_wf R
  have hs : ∀ e, D.inSrc e := by
    intro e
    apply (Deletion.inSrc_iff (P.pow 0).pom.val ((P.pow 0).keep R) e).mpr
    exact ⟨Deletion.inclusion (P.pow 0).pom.val ((P.pow 0).keep R) e,rfl⟩
  have ht : ∀ e, D.inTgt e := by
    intro e
    apply (Deletion.inTgt_iff (P.pow 0).pom.val ((P.pow 0).keep R) e).mpr
    exact ⟨Deletion.inclusion (P.pow 0).pom.val ((P.pow 0).keep R) e,rfl⟩
  let φ := FullIdentity.iso D hD hs ht
  have hseam : D.tgtType = (P.deleteData R).srcType := (P.powerDeletionPlan R hR 0).glueMatch.type_eq
  have hsource : D.srcType = cubeInterface W := (φ.source_type.trans φ.target_type.symm).trans hseam
  let Q : EndoPom (cubeInterface W) := { pom := ⟨D,hD⟩,source := hsource,target := hseam }
  have hcard : D.srcLen = D.n := by
    simpa only [Fintype.card_fin] using Fintype.card_congr (Equiv.ofBijective D.src ⟨D.src_inj,hs⟩)
  have hn : Q.pom.n = (cubeInterface W).1 := hcard.symm.trans (congrArg Sigma.fst hsource)
  exact (Q.isoIdentityOfSizeEq hn).symm

/-- Actual persistent-event deletion commutes with every actual power,
including the zero-exponent identity and all induced ordered interfaces. -/
noncomputable def deletionPowerIso (P : EndoPom (cubeInterface U)) (R : Finset (Fin U.dim))
    (hR : P.PersistentSet R) (hw : P.pom.val.WidthLE k) (n : ℕ) :
    PomsetIso ((P.reduced R hR hw).pow n).pom.val ((P.pow n).deleteData R) := by
  classical
  induction n with
  | zero => exact P.reducedZeroIso R hR hw
  | succ n ih =>
    let Q := P.reduced R hR hw
    let mq := GlueMatch.ofType ((Q.pow n).target.trans Q.source.symm)
    let md := (P.powerDeletionPlan R hR n).glueMatch
    have hg : PomsetIso (glueData (Q.pow n).pom.val Q.pom.val mq)
        (glueData ((P.pow n).deleteData R) (P.deleteData R) md) :=
      PomsetIso.glueIso ih (PomsetIso.refl (P.deleteData R)) mq md
    exact hg.trans (P.deletionPowerStepIso R hR n)

end CounterFreeHDA.EndoPom
