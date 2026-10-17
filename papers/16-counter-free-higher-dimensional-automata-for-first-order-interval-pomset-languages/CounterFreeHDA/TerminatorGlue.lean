import CounterFreeHDA.Induced
import CounterFreeHDA.StarterGlue
import CounterFreeHDA.GluingRealization

/-! Exact elementary termination: delete one source event from the residual
and recover the original pomset by actual interface gluing. -/
namespace CounterFreeHDA.TerminatorGlue
universe u
open Cubical
variable {Lab : Type u} (P : PomsetData Lab) (i : Fin P.srcLen)

noncomputable def remaining : Finset (Fin P.srcLen) := Finset.univ.erase i

theorem mem_remaining (j : Fin P.srcLen) : j ∈ remaining P i ↔ j ≠ i := by
  simp only [remaining,Finset.mem_erase,Finset.mem_univ,and_true]

noncomputable def terminator : IntervalPom Lab :=
  discretePom (P.lab ∘ P.src) (OrderEmbedding.ofStrictMono id (fun _ _ h => h)) ((remaining P i).orderEmbOfFin rfl)

def keep (e : Fin P.n) : Prop := e ≠ P.src i

theorem source_kept (j : Fin P.srcLen) (hj : j ∈ remaining P i) : keep P i (P.src j) := by
  exact fun h => ((mem_remaining P i j).mp hj) (P.src_inj h)

variable (ht : ¬ P.inTgt (P.src i))

include ht in
theorem target_kept (j : Fin P.tgtLen) (_ : j ∈ (Finset.univ : Finset (Fin P.tgtLen))) :
    keep P i (P.tgt j) := fun h => ht ⟨j,h⟩

noncomputable def residual : PomsetData Lab := by
  classical
  exact Induced.data P (keep P i) (remaining P i) Finset.univ
    (source_kept P i) (target_kept P i ht)

noncomputable def inclusion : Fin (residual P i ht).n ↪ Fin P.n := by
  classical
  exact Induced.includeEvent P (keep P i) (remaining P i) Finset.univ
    (source_kept P i) (target_kept P i ht)

theorem inclusion_kept (e : Fin (residual P i ht).n) : keep P i (inclusion P i ht e) := by
  classical
  exact ((Induced.index P (keep P i)).symm e).property

theorem inclusion_source (j : Fin (remaining P i).card) :
    inclusion P i ht ((residual P i ht).src j) = P.src ((remaining P i).orderEmbOfFin rfl j) := by
  classical
  exact congrArg Subtype.val ((Induced.index P (keep P i)).symm_apply_apply _)

theorem inclusion_target (j : Fin (Finset.univ : Finset (Fin P.tgtLen)).card) :
    inclusion P i ht ((residual P i ht).tgt j) =
      P.tgt (Finset.univ.orderEmbOfFin rfl j) := by
  classical
  exact congrArg Subtype.val ((Induced.index P (keep P i)).symm_apply_apply _)

/-- The surviving source interface consists of all original source events
that remain in the residual event set. -/
theorem residual_inSrc (e : Fin (residual P i ht).n) :
    (residual P i ht).inSrc e ↔ P.inSrc (inclusion P i ht e) := by
  classical
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨_,(inclusion_source P i ht j).symm⟩
  · rintro ⟨j,hj⟩
    have hji : j ≠ i := by
      intro h
      subst j
      exact inclusion_kept P i ht e hj.symm
    have hm : j ∈ remaining P i := (mem_remaining P i j).mpr hji
    let j' := (remaining P i).orderIsoOfFin rfl |>.symm ⟨j,hm⟩
    have hpos : (remaining P i).orderEmbOfFin rfl j' = j := by
      exact congrArg Subtype.val ((remaining P i).orderIsoOfFin rfl |>.apply_symm_apply ⟨j,hm⟩)
    refine ⟨j', (inclusion P i ht).injective ?_⟩
    rw [inclusion_source,hpos]
    exact hj

def matching : GlueMatch (terminator P i).val (residual P i ht) where
  len_eq := rfl
  lab_eq j := by
    classical
    change P.lab (P.src ((remaining P i).orderEmbOfFin rfl j)) =
      P.lab (((Induced.index P (keep P i)).symm
        ((Induced.index P (keep P i)) _)).val)
    rw [Equiv.symm_apply_apply]
    rfl

theorem terminator_not_target {j : Fin P.srcLen}
    (hj : ¬ (terminator P i).val.inTgt j) : j = i := by
  classical
  by_contra hn
  have hm := (mem_remaining P i j).mpr hn
  let j' := (remaining P i).orderIsoOfFin rfl |>.symm ⟨j,hm⟩
  apply hj
  exact ⟨j',congrArg Subtype.val ((remaining P i).orderIsoOfFin rfl |>.apply_symm_apply ⟨j,hm⟩)⟩

private theorem univ_position {n : ℕ}
    (j : Fin (Finset.univ : Finset (Fin n)).card) :
    (Finset.univ.orderEmbOfFin rfl j).val = j.val := by
  let h : (Finset.univ : Finset (Fin n)).card = n := by simp
  let f : Fin n → Fin n := fun j => Finset.univ.orderEmbOfFin rfl (Fin.cast h.symm j)
  have hf : StrictMono f := (Finset.univ.orderEmbOfFin rfl).strictMono.comp (fun _ _ h => h)
  have he := le_antisymm (hf.le_id (Fin.cast h j)) (hf.id_le (Fin.cast h j))
  simpa only [f,Fin.cast_cast,Fin.cast_refl,id_eq] using congrArg Fin.val he

noncomputable def realization (hP : IsIntervalPom P)
    (hc : ∀ e, ¬ P.inSrc e → P.prec (P.src i) e) :
    GluingRealization (matching P i ht) P where
  left := ⟨P.src,P.src_inj⟩
  right := inclusion P i ht
  left_lab _ := rfl
  right_lab _ := rfl
  left_prec e f := iff_false_intro (hP.src_minimal _ ⟨f,rfl⟩ _)
  right_prec _ _ := Iff.rfl
  left_eord := hP.src_eord
  right_eord _ _ := Iff.rfl
  seam j := (inclusion_source P i ht j).symm
  overlap e f hef := by
    classical
    have hne : e ≠ i := by
      intro h
      subst e
      exact inclusion_kept P i ht f hef.symm
    have hm := (mem_remaining P i e).mpr hne
    let j := (remaining P i).orderIsoOfFin rfl |>.symm ⟨e,hm⟩
    have hpos : (remaining P i).orderEmbOfFin rfl j = e :=
      congrArg Subtype.val ((remaining P i).orderIsoOfFin rfl |>.apply_symm_apply ⟨e,hm⟩)
    refine ⟨j,hpos,(inclusion P i ht).injective ?_⟩
    rw [inclusion_source]
    simp only [Fin.cast_refl,id_eq]
    rw [hpos]
    exact hef
  cover e := by
    classical
    by_cases he : e = P.src i
    · exact Or.inl ⟨i,he.symm⟩
    · refine Or.inr ⟨Induced.index P (keep P i) ⟨e,he⟩,?_⟩
      exact congrArg Subtype.val ((Induced.index P (keep P i)).symm_apply_apply _)
  cross e f he hf := by
    have hei := terminator_not_target P i he
    change P.prec (P.src e) (inclusion P i ht f)
    rw [hei]
    exact hc _ (fun h => hf ((residual_inSrc P i ht f).mpr h))
  source_len := rfl
  target_len := by
    classical
    exact Finset.card_univ.trans (Fintype.card_fin _)
  source _ := rfl
  target j := by
    rw [inclusion_target]
    apply congrArg P.tgt
    apply Fin.ext
    exact univ_position j

/-- The full elementary-termination factorization, including actual events,
precedence, event order, labels and both ordered interfaces. -/
noncomputable def iso (hP : IsIntervalPom P)
    (hc : ∀ e, ¬ P.inSrc e → P.prec (P.src i) e) :
    PomsetIso (glueData (terminator P i).val (residual P i ht) (matching P i ht)) P := by
  classical
  exact (realization P i ht hP hc).iso (terminator P i).property
    (Induced.isIntervalPom P (keep P i) hP _ _ _ _) hP

end CounterFreeHDA.TerminatorGlue
