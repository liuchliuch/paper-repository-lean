import CounterFreeHDA.BoundaryFactorization
import CounterFreeHDA.RecognizedPowers

namespace CounterFreeHDA.Cubical.OrderedPomsetRecognizer
universe u v
variable {Lab : Type u} {k h : ℕ} {L : Set (IntervalPom Lab)}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h) {U A B : Cube Lab k}

/-- **Corollary 4.4.** Actual corner images stabilize at 2k+h. The fixed
factorization is constructed by Lemma 4.3; no corner-stability premise occurs. -/
theorem corollary_4_4 (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE k)
    (α : Face A U) (β : Face B U) (hc : P.StableCompatible α β)
    (n : ℕ) (hn : 2*k+h ≤ n) :
    F.map ((P.boundedPower hw n).toArrow.corner (P.width_pow hw n) α β
      (P.power_compatible α β hc hw (by omega))) =
    F.map ((P.boundedPower hw (n+1)).toArrow.corner (P.width_pow hw (n+1)) α β
      (P.power_compatible α β hc hw (by omega))) := by
  let A := P.leftFactor α β hc hw
  let B := P.rightFactor α β hc hw
  let Q := P.boundaryReduced α β hw
  let hwQ := P.boundaryReduced_width α β hw
  let Cn := (P.boundedPower hw n).toArrow.corner (P.width_pow hw n) α β
    (P.power_compatible α β hc hw (by omega))
  let Cn' := (P.boundedPower hw (n+1)).toArrow.corner (P.width_pow hw (n+1)) α β
    (P.power_compatible α β hc hw (by omega))
  have he : n+1-2*k = (n-2*k)+1 := by omega
  have hm : F.map (Q.boundedPower hwQ (n-2*k)) = F.map (Q.boundedPower hwQ (n+1-2*k)) := by
    rw [he]
    exact F.map_actual_power_stable Q hwQ (by omega)
  calc
    F.map Cn = F.map ((A.comp (Q.boundedPower hwQ (n-2*k))).comp B) :=
      (F.map_iso _ _ (P.lemma_4_3 α β hc hw n (by omega))).symm
    _ = F.map ((A.comp (Q.boundedPower hwQ (n+1-2*k))).comp B) := by
      simp only [F.map_comp,hm]
    _ = F.map Cn' := F.map_iso _ _ (P.lemma_4_3 α β hc hw (n+1) (by omega))

end CounterFreeHDA.Cubical.OrderedPomsetRecognizer
