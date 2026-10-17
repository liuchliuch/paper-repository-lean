import CounterFreeHDA.TrackDiscrete
import CounterFreeHDA.TrackGlueUniversal

namespace CounterFreeHDA.Cubical
universe u v w
variable {Lab : Type u} {k : ℕ}

namespace Map

def total {X : Precubical.{u,w} Lab k} {Y : Precubical.{u,v} Lab k} (p : Map X Y) :
    (Σ U, X.Cell U) → (Σ U, Y.Cell U) := fun c => ⟨c.1,p.app c.2⟩

end Map

namespace Arrow
variable {U V W : Cube Lab k}

theorem src_len (A : Arrow U V) : A.pom.srcLen = U.dim := congrArg Sigma.fst A.source
theorem tgt_len (A : Arrow U V) : A.pom.tgtLen = V.dim := congrArg Sigma.fst A.target

theorem source_label (A : Arrow U V) (i : Fin U.dim) :
    A.pom.lab (A.pom.src (Fin.cast A.src_len.symm i)) = U.lab i := by
  obtain ⟨hl,hlabels⟩ := Fin.sigma_eq_iff_eq_comp_cast.mp A.source
  have h := congrFun hlabels (Fin.cast A.src_len.symm i)
  simpa only [cubeInterface,Function.comp_apply,Fin.cast_cast,Fin.cast_refl,id_eq] using h

theorem target_label (A : Arrow U V) (i : Fin V.dim) :
    A.pom.lab (A.pom.tgt (Fin.cast A.tgt_len.symm i)) = V.lab i := by
  obtain ⟨hl,hlabels⟩ := Fin.sigma_eq_iff_eq_comp_cast.mp A.target
  have h := congrFun hlabels (Fin.cast A.tgt_len.symm i)
  simpa only [cubeInterface,Function.comp_apply,Fin.cast_cast,Fin.cast_refl,id_eq] using h

noncomputable def sourceCell (A : Arrow U V) : TrackCell A.pom.val U := by
  classical
  exact {
    status e := if A.pom.val.inSrc e then Status.star else Status.zero
    config e f hef hf := by
      have hf' : A.pom.val.inSrc f := by by_contra h; exact hf (if_neg h)
      exact False.elim (A.pom.property.src_minimal f hf' e hef)
    occ i := A.pom.src (Fin.cast A.src_len.symm i)
    inj := by
      intro i j hij
      have h := A.pom.val.src_inj hij
      exact Fin.ext (congrArg (fun t : Fin A.pom.srcLen => t.val) h)
    active i := if_pos ⟨_,rfl⟩
    covers e he := by
      by_cases h : A.pom.val.inSrc e
      · obtain ⟨j,hj⟩ := h
        exact ⟨Fin.cast A.src_len j,by simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using hj⟩
      · rw [if_neg h] at he
        exact False.elim ((by decide : Status.zero ≠ Status.star) he)
    labels := A.source_label
    ordered i j := A.pom.property.src_eord _ _ }

noncomputable def targetCell (A : Arrow U V) : TrackCell A.pom.val V := by
  classical
  exact {
    status e := if A.pom.val.inTgt e then Status.star else Status.one
    config e f hef _ := by
      by_cases h : A.pom.val.inTgt e
      · exact False.elim (A.pom.property.tgt_maximal e h f hef)
      · exact if_neg h
    occ i := A.pom.tgt (Fin.cast A.tgt_len.symm i)
    inj := by
      intro i j hij
      have h := A.pom.val.tgt_inj hij
      exact Fin.ext (congrArg (fun t : Fin A.pom.tgtLen => t.val) h)
    active i := if_pos ⟨_,rfl⟩
    covers e he := by
      by_cases h : A.pom.val.inTgt e
      · obtain ⟨j,hj⟩ := h
        exact ⟨Fin.cast A.tgt_len j,by simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using hj⟩
      · rw [if_neg h] at he
        exact False.elim ((by decide : Status.one ≠ Status.star) he)
    labels := A.target_label
    ordered i j := A.pom.property.tgt_eord _ _ }

theorem source_bound (A : Arrow U V) : A.pom.srcLen ≤ k := by
  rw [A.src_len]
  exact Nat.le_of_lt_succ U.1.isLt

theorem target_bound (A : Arrow U V) : A.pom.tgtLen ≤ k := by
  rw [A.tgt_len]
  exact Nat.le_of_lt_succ V.1.isLt

/-- Typed source/target cells agree with the canonical distinguished cubes,
including their actual type, recovered from active event statuses. -/
theorem target_total (A : Arrow U V) :
    (⟨targetCube A.pom.val A.target_bound,tau A.pom.val A.pom.property A.target_bound⟩ :
      Σ T : Cube Lab k, TrackCell A.pom.val T) = ⟨V,A.targetCell⟩ :=
  TrackCell.total_status_injective rfl

theorem source_total_at_seam (A : Arrow U V) (B : Arrow V W) :
    (⟨targetCube A.pom.val A.target_bound,
      TrackGlue.rightBoundary (GlueMatch.ofType (A.target.trans B.source.symm)) B.pom.property A.target_bound⟩ :
      Σ T : Cube Lab k, TrackCell B.pom.val T) = ⟨V,B.sourceCell⟩ :=
  TrackCell.total_status_injective rfl

variable {Y : Precubical.{u,v} Lab k}

theorem canonicalSeam (A : Arrow U V) (B : Arrow V W)
    (p : Map (track A.pom.val) Y) (q : Map (track B.pom.val) Y)
    (seam : p.app A.targetCell = q.app B.sourceCell) :
    p.app (tau A.pom.val A.pom.property A.target_bound) =
      q.app (TrackGlue.rightBoundary (GlueMatch.ofType (A.target.trans B.source.symm))
        B.pom.property A.target_bound) := by
  let m := GlueMatch.ofType (A.target.trans B.source.symm)
  have hl := congrArg p.total A.target_total
  have hr := congrArg q.total (source_total_at_seam A B)
  have hs : (⟨V,p.app A.targetCell⟩ : Σ T : Cube Lab k, Y.Cell T) = ⟨V,q.app B.sourceCell⟩ :=
    congrArg (fun y : Y.Cell V => (⟨V,y⟩ : Σ T : Cube Lab k, Y.Cell T)) seam
  have hc := hl.trans (hs.trans hr.symm)
  have seam' : p.app (tau A.pom.val A.pom.property A.target_bound) =
      q.app (TrackGlue.rightBoundary m B.pom.property A.target_bound) := by
    simpa only [Map.total,Sigma.mk.inj_iff,heq_eq_eq,true_and] using hc
  exact seam'


/-- Compatible actual maps on typed factors extend to their actual gluing. -/
noncomputable def glueMap (A : Arrow U V) (B : Arrow V W)
    (p : Map (track A.pom.val) Y) (q : Map (track B.pom.val) Y)
    (seam : p.app A.targetCell = q.app B.sourceCell) : Map (track (A.comp B).pom.val) Y :=
  TrackGlue.glueMap (GlueMatch.ofType (A.target.trans B.source.symm)) A.pom.property B.pom.property
    A.target_bound p q (canonicalSeam A B p q seam)

end Arrow
end CounterFreeHDA.Cubical
