import CounterFreeHDA.AutomaticST
import CounterFreeHDA.Refinement

namespace CounterFreeHDA.Refinement
universe u v
open Cubical
variable {Lab : Type u} {k : ℕ} {P Q : IntervalPom Lab}

namespace Witness

theorem source_type (R : Witness P Q) : P.val.srcType = Q.val.srcType := by
  apply Fin.sigma_eq_iff_eq_comp_cast.mpr
  refine ⟨R.source_len,funext fun i => ?_⟩
  exact (R.labels (P.src i)).trans (congrArg Q.lab (R.source i))

theorem target_type (R : Witness P Q) : P.val.tgtType = Q.val.tgtType := by
  apply Fin.sigma_eq_iff_eq_comp_cast.mpr
  refine ⟨R.target_len,funext fun i => ?_⟩
  exact (R.labels (P.tgt i)).trans (congrArg Q.lab (R.target i))

end Witness

@[simp] theorem transport_source {U V : Cube Lab k} (A B : Arrow U V)
    (R : Witness A.pom B.pom) : transport R A.sourceCell = B.sourceCell := by
  classical
  apply TrackCell.status_injective
  funext a
  obtain ⟨e,rfl⟩ := R.event.surjective a
  change (transport R A.sourceCell).status (R.event e) = B.sourceCell.status (R.event e)
  rw [transport_status]
  change (if A.pom.val.inSrc e then Status.star else Status.zero) =
    (if B.pom.val.inSrc (R.event e) then Status.star else Status.zero)
  rw [source_image]

@[simp] theorem transport_target {U V : Cube Lab k} (A B : Arrow U V)
    (R : Witness A.pom B.pom) : transport R A.targetCell = B.targetCell := by
  classical
  apply TrackCell.status_injective
  funext a
  obtain ⟨e,rfl⟩ := R.event.surjective a
  change (transport R A.targetCell).status (R.event e) = B.targetCell.status (R.event e)
  rw [transport_status]
  change (if A.pom.val.inTgt e then Status.star else Status.one) =
    (if B.pom.val.inTgt (R.event e) then Status.star else Status.one)
  rw [target_image]

/-- Every subsumption of P labels a complete path in the actual B(P).
This is the constructive inclusion in Lemma 3.1(a). -/
theorem complete_path {U V : Cube Lab k} (A B : Arrow U V)
    (h : A.pom ⊑ₛ B.pom) (hw : A.pom.val.WidthLE k) :
    B.targetCell ∈ (track B.pom.val).dPom B.sourceCell A.pom := by
  let R := witness h
  obtain ⟨p,hr,hp⟩ := A.complete_path hw
  have hm := (map (k := k) R).map_run hr
  change (track B.pom.val).Run p (transport R A.sourceCell) (transport R A.targetCell) at hm
  rw [transport_source,transport_target] at hm
  exact ⟨p,hm,hp⟩

/-- Actual endpoint reachability is closed under subsumption within the
bounded-width interval-pomset source. -/
theorem reachability_downward {U V : Cube Lab k} (A B : Arrow U V)
    {Y : Precubical.{u,v} Lab k} (x : Y.Cell U) (y : Y.Cell V)
    (h : A.pom ⊑ₛ B.pom) (hw : A.pom.val.WidthLE k)
    (hy : y ∈ Y.dPom x B.pom) : y ∈ Y.dPom x A.pom := by
  let R := witness h
  obtain ⟨a,ha,hb⟩ := B.map_of_dPom x y hy
  apply (A.lemma_3_1_b hw x y).mpr
  refine ⟨(map (k := k) R).comp a,?_,?_⟩
  · change a.app (transport R A.sourceCell) = x
    rw [transport_source]
    exact ha
  · change a.app (transport R A.targetCell) = y
    rw [transport_target]
    exact hb

end CounterFreeHDA.Refinement
