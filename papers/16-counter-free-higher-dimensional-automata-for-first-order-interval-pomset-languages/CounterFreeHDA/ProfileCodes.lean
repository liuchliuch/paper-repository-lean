import CounterFreeHDA.ReducedStepMeasure
import CounterFreeHDA.ProfileSemantics

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

theorem residualSize_le_four : ∀ n : Fin 3, residualSize n ≤ 4 := by decide

def embedKind {U : UCube} (r : Kind U) : Fin 4 := ⟨r.val,lt_of_lt_of_le r.isLt (residualSize_le_four U.1)⟩

def codeTransition (sd td : ℕ) (r : Fin 4) : Fin 4 :=
  if sd = td then r else if sd < td then
    if sd = 0 then ![0,2,2,3] r else ![0,2,1,2] r
  else if sd = 1 then ![1,0,2,3] r else ![1,2,3,3] r

abbrev Code (U : UCube) := Finset (Fin U.dim) → Fin 4
noncomputable def profileCode {U : UCube} (P : Prefix U) : Code U := fun D => embedKind (profile P D)

theorem code_step {U V : UCube} (s : Step U V) (r : Kind U) :
    embedKind (stepKind s r) = codeTransition U.dim V.dim (embedKind r) := by
  have hs : ∀ (U V : UCube) (f : Cubical.Face U V) (hl : f.Lower) (hd : V.dim = U.dim+1), ∀ r : Kind U,
      embedKind (startKind U.1 V.1 r) = codeTransition U.dim V.dim (embedKind r) := by
    let dec : Decidable (∀ (U V : UCube) (f : Cubical.Face U V) (hl : f.Lower) (hd : V.dim = U.dim+1), ∀ r : Kind U,
        embedKind (startKind U.1 V.1 r) = codeTransition U.dim V.dim (embedKind r)) := by
      refine @Fintype.decidableForallFintype _ _ (fun U => ?_) inferInstance
      refine @Fintype.decidableForallFintype _ _ (fun V => ?_) inferInstance
      refine @Fintype.decidableForallFintype _ _ (fun f => ?_) (Effective.faceFintype U V)
      infer_instance
    exact of_decide_eq_true (by rfl : @decide _ dec = true)
  have ht : ∀ (U V : UCube) (f : Cubical.Face U V) (hu : f.Upper) (hd : V.dim = U.dim+1), ∀ r : Kind V,
      embedKind (stopKind V.1 U.1 r) = codeTransition V.dim U.dim (embedKind r) := by
    let dec : Decidable (∀ (U V : UCube) (f : Cubical.Face U V) (hu : f.Upper) (hd : V.dim = U.dim+1), ∀ r : Kind V,
        embedKind (stopKind V.1 U.1 r) = codeTransition V.dim U.dim (embedKind r)) := by
      refine @Fintype.decidableForallFintype _ _ (fun U => ?_) inferInstance
      refine @Fintype.decidableForallFintype _ _ (fun V => ?_) inferInstance
      refine @Fintype.decidableForallFintype _ _ (fun f => ?_) (Effective.faceFintype U V)
      infer_instance
    exact of_decide_eq_true (by rfl : @decide _ dec = true)
  cases s with
  | start f hl hd => exact hs _ _ f hl hd r
  | stop f hu hd => exact ht _ _ f hu hd r

theorem code_short_word {U V : UCube} (p : Word U V) (hl : p.length ≤ 1) (r : Kind U) :
    embedKind (wordKind p r) = codeTransition U.dim V.dim (embedKind r) := by
  cases p with
  | nil => simp [wordKind,codeTransition]
  | cons s p =>
    cases p with
    | nil => exact code_step s r
    | cons t p => change (p.length+1)+1 ≤ 1 at hl; omega

theorem deleted_step_measure_le {U V : UCube} (s : Step U V) (D : Finset (Fin V.dim)) :
    stMeasure (deletedArrow (BoundedArrow.ofStep s) D).pom.val ≤ 1 := by
  rw [deletedArrow_measure]
  cases s with
  | start f hl hd =>
    have hm := reduced_start_measure _ _ f hl hd D
    rw [Effective.stepLabel_eq] at hm
    change 2 * keptEvents (Step.start f hl hd).label D -
      reducedDim _ ((Step.start f hl hd).label.pullTargetDeletion D) - reducedDim _ D ≤ 1
    omega
  | stop f hu hd =>
    have hm := reduced_stop_measure _ _ f hu hd D
    rw [Effective.stepLabel_eq] at hm
    exact le_of_eq hm.1

def updateCode {U V : UCube} (s : Step U V) (c : Code U) : Code V := fun D =>
  let E := (Effective.stepLabel s).pullTargetDeletion D
  codeTransition (reducedDim U E) (reducedDim V D) (c E)

/-- All update coordinates are computed from the actual deletion semantics;
the finite code is a verified encoding of r(P-D), not a replacement definition. -/
theorem profileCode_update {U V : UCube} (P : Prefix U) (s : Step U V) :
    profileCode (P.comp (BoundedArrow.ofStep s)) = updateCode s (profileCode P) := by
  funext D
  unfold profileCode updateCode
  rw [Effective.stepLabel_eq,profile_comp_coordinate]
  let B := deletedArrow (BoundedArrow.ofStep s) D
  have hl : B.representative.length ≤ 1 := by
    rw [← B.representative.stMeasure_label,stMeasure_iso B.representativeIso]
    exact deleted_step_measure_le s D
  exact (code_short_word B.representative hl _).trans
    (by rw [activeCube_deletion_dim,activeCube_deletion_dim]; rfl)

end CounterFreeHDA.Appendix.Residual
