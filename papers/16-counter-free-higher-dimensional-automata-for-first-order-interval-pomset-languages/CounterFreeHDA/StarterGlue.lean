import CounterFreeHDA.InterfaceEnumeration

/-! Prepending a discrete starter changes precisely the source interface.
The proof identifies the actual gluing events and both orders. -/
namespace CounterFreeHDA
universe u
variable {Lab : Type u} {P Q : PomsetData Lab}

namespace GluedE

theorem rightMap_surjective (m : GlueMatch P Q) (hP : ∀ e, P.inTgt e) :
    Function.Surjective (rightMap P Q m.len_eq) := by
  classical
  intro a
  cases a with
  | left e => exact False.elim (e.property (hP e.val))
  | right e =>
    refine ⟨e.val,?_⟩
    unfold rightMap
    exact dif_neg e.property
  | mid i =>
    refine ⟨Q.src (Fin.cast m.len_eq i),?_⟩
    rw [rightMap_src]
    simp only [Fin.cast_cast,Fin.cast_refl,id_eq]

end GluedE

namespace StarterGlue
open Cubical
variable (Q : PomsetData Lab) (hQ : IsIntervalPom Q) {r : ℕ}
    (a : Fin r ↪o Fin Q.srcLen)

noncomputable def starter : IntervalPom Lab :=
  discretePom (Q.lab ∘ Q.src) a (OrderEmbedding.ofStrictMono id (fun _ _ h => h))

def residualSource : PomsetData Lab := { Q with
  srcLen := r
  src := Q.src ∘ a
  src_inj := Q.src_inj.comp a.injective }

include hQ in
theorem residualSource_wf : IsIntervalPom (residualSource Q a) := { hQ with
  src_minimal := by
    rintro e ⟨i,rfl⟩ f
    exact hQ.src_minimal _ ⟨a i,rfl⟩ f
  src_eord := by
    intro i j
    change Q.eord (Q.src (a i)) (Q.src (a j)) ↔ i.val < j.val
    rw [hQ.src_eord]
    exact a.strictMono.lt_iff_lt }

def matching : GlueMatch (starter Q a).val Q where
  len_eq := rfl
  lab_eq _ := rfl

noncomputable def eventEquiv : Fin Q.n ≃ Fin (glueData (starter Q a).val Q (matching Q a)).n :=
  Equiv.ofBijective (TrackGlue.rightEvent (matching Q a))
    ⟨(TrackGlue.index _).injective.comp (GluedE.rightMap_inj _ _ _),
      (TrackGlue.index _).surjective.comp (GluedE.rightMap_surjective (matching Q a) (fun e => ⟨e,rfl⟩))⟩

/-- Actual pomset isomorphism for the starter factorization. -/
noncomputable def iso : PomsetIso (residualSource Q a)
    (glueData (starter Q a).val Q (matching Q a)) where
  toEquiv := eventEquiv Q a
  lab_eq e := by
    change (glueData (starter Q a).val Q (matching Q a)).lab (TrackGlue.rightEvent (matching Q a) e) = Q.lab e
    change glueLab (matching Q a) ((TrackGlue.index (matching Q a)).symm
      (TrackGlue.index (matching Q a) (GluedE.rightMap (starter Q a).val Q rfl e))) = Q.lab e
    rw [Equiv.symm_apply_apply]
    exact glueLab_right (matching Q a) e
  srcEquiv := Equiv.refl _
  tgtEquiv := Equiv.refl _
  src_mono _ _ := Iff.rfl
  tgt_mono _ _ := Iff.rfl
  src_eq i := by
    change TrackGlue.index (matching Q a) (GluedE.rightMap (starter Q a).val Q rfl (Q.src (a i))) =
      TrackGlue.index (matching Q a) (GluedE.leftMap (starter Q a).val Q (a i))
    apply congrArg (TrackGlue.index _)
    rw [GluedE.rightMap_src]
    exact (GluedE.leftMap_tgt (starter Q a).val Q (a i)).symm
  tgt_eq _ := rfl
  prec_iff e f := TrackGlue.rightEvent_prec (matching Q a) hQ e f
  eord_iff e f := by
    change glueEord _ ((TrackGlue.index _).symm (TrackGlue.index _ _))
      ((TrackGlue.index _).symm (TrackGlue.index _ _)) ↔ Q.eord e f
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    exact glueEord_right (matching Q a) (starter Q a).property hQ e f

end StarterGlue
end CounterFreeHDA
