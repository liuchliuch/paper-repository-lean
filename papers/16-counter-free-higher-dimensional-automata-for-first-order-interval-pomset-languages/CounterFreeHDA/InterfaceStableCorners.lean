import CounterFreeHDA.InterfaceFactorization
import CounterFreeHDA.RecognizedPowers

namespace CounterFreeHDA.Cubical.OrderedPomsetRecognizer
universe u v
variable {Lab : Type u} {k h : ℕ} {L : Set (IntervalPom Lab)}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h) {U A B : Cube Lab k}

/-- **Corollary 4.4.** Actual corner images stabilize at 2r+h, where r is the interface size. The fixed
factorization is constructed by Lemma 4.3; no corner-stability premise occurs. -/
theorem corollary_4_4_interface (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE k)
    (α : Face A U) (β : Face B U) (hc : P.StableCompatible α β)
    (n : ℕ) (hn : 2*U.dim+h ≤ n) :
    F.map ((P.boundedPower hw n).toArrow.corner (P.width_pow hw n) α β
      (P.power_compatible_interface α β hc hw (by omega))) =
    F.map ((P.boundedPower hw (n+1)).toArrow.corner (P.width_pow hw (n+1)) α β
      (P.power_compatible_interface α β hc hw (by omega))) := by
  let A := P.leftFactorInterface α β hc hw
  let B := P.rightFactorInterface α β hc hw
  let Q := P.boundaryReduced α β hw
  let hwQ := P.boundaryReduced_width α β hw
  let Cn := (P.boundedPower hw n).toArrow.corner (P.width_pow hw n) α β
    (P.power_compatible_interface α β hc hw (by omega))
  let Cn' := (P.boundedPower hw (n+1)).toArrow.corner (P.width_pow hw (n+1)) α β
    (P.power_compatible_interface α β hc hw (by omega))
  have he : n+1-2*U.dim = (n-2*U.dim)+1 := by omega
  have hm : F.map (Q.boundedPower hwQ (n-2*U.dim)) = F.map (Q.boundedPower hwQ (n+1-2*U.dim)) := by
    rw [he]
    exact F.map_actual_power_stable Q hwQ (by omega)
  calc
    F.map Cn = F.map ((A.comp (Q.boundedPower hwQ (n-2*U.dim))).comp B) :=
      (F.map_iso _ _ (P.lemma_4_3_interface α β hc hw n (by omega))).symm
    _ = F.map ((A.comp (Q.boundedPower hwQ (n+1-2*U.dim))).comp B) := by
      simp only [F.map_comp,hm]
    _ = F.map Cn' := F.map_iso _ _ (P.lemma_4_3_interface α β hc hw (n+1) (by omega))

end CounterFreeHDA.Cubical.OrderedPomsetRecognizer
