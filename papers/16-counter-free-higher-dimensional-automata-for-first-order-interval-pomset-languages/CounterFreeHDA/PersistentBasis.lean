import CounterFreeHDA.PersistentDeletion

namespace CounterFreeHDA.GlueMatch
universe u
variable {Lab : Type u} {P Q : PomsetData Lab}

theorem type_eq (m : GlueMatch P Q) : P.tgtType = Q.srcType := by
  apply Fin.sigma_eq_iff_eq_comp_cast.mpr
  exact ⟨m.len_eq,funext m.lab_eq⟩

end CounterFreeHDA.GlueMatch

namespace CounterFreeHDA.EndoPom
universe u
open Cubical
variable {Lab : Type u} {k : ℕ} {U : Cube Lab k}

theorem keep_source_iff (P : EndoPom (cubeInterface U)) (R : Finset (Fin U.dim)) (i : Fin U.dim) :
    P.keep R (P.pom.src (Fin.cast P.src_len.symm i)) ↔ i ∉ R := by
  constructor
  · intro h hi
    exact h ⟨i,hi,rfl⟩
  · rintro hi ⟨j,hj,hji⟩
    have he := P.pom.val.src_inj hji
    have hv : j = i := Fin.ext (congrArg (fun x : Fin P.pom.srcLen => x.val) he)
    exact hi (hv ▸ hj)

theorem keep_target_iff (P : EndoPom (cubeInterface U)) (R : Finset (Fin U.dim))
    (hR : P.PersistentSet R) (i : Fin U.dim) :
    P.keep R (P.pom.tgt (Fin.cast P.tgt_len.symm i)) ↔ i ∉ R := by
  constructor
  · intro h hi
    exact h ⟨i,hi,hR i hi⟩
  · rintro hi ⟨j,hj,hji⟩
    have he := P.pom.val.tgt_inj ((hR j hj).symm.trans hji)
    have hv : j = i := Fin.ext (congrArg (fun x : Fin P.pom.tgtLen => x.val) he)
    exact hi (hv ▸ hj)

theorem deleteData_wf (P : EndoPom (cubeInterface U)) (R : Finset (Fin U.dim)) :
    IsIntervalPom (P.deleteData R) := by
  classical
  exact Deletion.isIntervalPom P.pom.val (P.keep R) P.pom.property

theorem deleteData_width (P : EndoPom (cubeInterface U)) (R : Finset (Fin U.dim))
    (hw : P.pom.val.WidthLE k) : (P.deleteData R).WidthLE k := by
  classical
  exact Deletion.widthLE P.pom.val (P.keep R) hw

/-- Persistent deletion removes the same ordered interface positions at
both ends, so the reduced pomset is still an endomorphism. -/
noncomputable def reducedMatch (P : EndoPom (cubeInterface U)) (R : Finset (Fin U.dim))
    (hR : P.PersistentSet R) : GlueMatch (P.deleteData R) (P.deleteData R) := by
  classical
  let m := GlueMatch.ofType (P.target.trans P.source.symm)
  apply (Deletion.matching m (P.keep R) (P.keep R) ?_).toGlueMatch
  intro i
  let j := Fin.cast P.tgt_len i
  have ht : P.keep R (P.pom.tgt i) ↔ j ∉ R := by
    simpa only [j,Fin.cast_cast,Fin.cast_refl,id_eq] using P.keep_target_iff R hR j
  have hs : P.keep R (P.pom.src (Fin.cast m.len_eq i)) ↔ j ∉ R :=
    (congrArg (fun a => P.keep R (P.pom.src a)) (show Fin.cast m.len_eq i = Fin.cast P.src_len.symm j from Fin.ext rfl)).to_iff.trans
      (P.keep_source_iff R j)
  exact ht.trans hs.symm

noncomputable def reducedCube (P : EndoPom (cubeInterface U)) (R : Finset (Fin U.dim))
    (hw : P.pom.val.WidthLE k) : Cube Lab k :=
  sourceCube (P.deleteData R) ((P.deleteData_width R hw).source_bound (P.deleteData_wf R))

noncomputable def reduced (P : EndoPom (cubeInterface U)) (R : Finset (Fin U.dim))
    (hR : P.PersistentSet R) (hw : P.pom.val.WidthLE k) : EndoPom (cubeInterface (P.reducedCube R hw)) where
  pom := ⟨P.deleteData R,P.deleteData_wf R⟩
  source := rfl
  target := (P.reducedMatch R hR).type_eq

end CounterFreeHDA.EndoPom
