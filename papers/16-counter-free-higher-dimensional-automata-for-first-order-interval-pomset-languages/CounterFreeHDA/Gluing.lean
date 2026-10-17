import CounterFreeHDA.Amalgam
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-! Well-formedness of genuine interface gluing. The interval representation
is constructed explicitly by moving the two factors into separated real
ranges and extending each common-interface event across the seam. -/

namespace CounterFreeHDA
universe u

variable {Lab : Type u} {P Q : PomsetData Lab} (m : GlueMatch P Q)

theorem gluePrec_irrefl (hP : IsIntervalPom P) (hQ : IsIntervalPom Q) :
    ∀ e : GluedE P Q, ¬ gluePrec m.len_eq e e := by
  rintro (e | e | i)
  · exact hP.prec_irrefl _
  · exact hQ.prec_irrefl _
  · exact not_false

theorem gluePrec_trans (hP : IsIntervalPom P) (hQ : IsIntervalPom Q) :
    ∀ {e f g : GluedE P Q}, gluePrec m.len_eq e f → gluePrec m.len_eq f g →
      gluePrec m.len_eq e g := by
  rintro (e | e | i) (f | f | j) (g | g | l) <;>
    simp only [gluePrec, false_implies, implies_true, true_implies]
  · exact hP.prec_trans
  · exact hP.prec_trans
  · exact hQ.prec_trans
  · exact hQ.prec_trans

/-- A bounded representation is obtained by a strictly increasing arctangent,
so no finite search for particular real endpoints is needed. -/
theorem gluePrec_interval_rep (hP : IsIntervalPom P) (hQ : IsIntervalPom Q) :
    ∃ s t : GluedE P Q → ℝ, ∀ e f, gluePrec m.len_eq e f ↔ t e < s f := by
  obtain ⟨sP,tP,hrepP⟩ := hP.interval_rep
  obtain ⟨sQ,tQ,hrepQ⟩ := hQ.interval_rep
  let s : GluedE P Q → ℝ
    | .left e => Real.arctan (sP e.val)
    | .right e => Real.arctan (sQ e.val) + 2*Real.pi
    | .mid i => Real.arctan (sP (P.tgt i))
  let t : GluedE P Q → ℝ
    | .left e => Real.arctan (tP e.val)
    | .right e => Real.arctan (tQ e.val) + 2*Real.pi
    | .mid i => Real.arctan (tQ (Q.src (Fin.cast m.len_eq i))) + 2*Real.pi
  have sep : ∀ a b : ℝ, Real.arctan a < Real.arctan b + 2*Real.pi := by
    intro a b
    have ha := Real.arctan_lt_pi_div_two a
    have hb := Real.neg_pi_div_two_lt_arctan b
    have hp := Real.pi_pos
    linarith
  refine ⟨s,t,?_⟩
  rintro (e | e | i) (f | f | j)
  · exact (hrepP _ _).trans Real.arctan_lt_arctan_iff.symm
  · exact iff_of_true trivial (sep _ _)
  · exact (hrepP _ _).trans Real.arctan_lt_arctan_iff.symm
  · exact iff_of_false not_false (not_lt_of_gt (sep _ _))
  · change Q.prec _ _ ↔ Real.arctan _ + 2*Real.pi < Real.arctan _ + 2*Real.pi
    rw [add_lt_add_iff_right]
    exact (hrepQ _ _).trans Real.arctan_lt_arctan_iff.symm
  · exact iff_of_false not_false (not_lt_of_gt (sep _ _))
  · exact iff_of_false not_false (not_lt_of_gt (sep _ _))
  · change Q.prec _ _ ↔ Real.arctan _ + 2*Real.pi < Real.arctan _ + 2*Real.pi
    rw [add_lt_add_iff_right]
    exact (hrepQ _ _).trans Real.arctan_lt_arctan_iff.symm
  · exact iff_of_false not_false (not_lt_of_gt (sep _ _))

theorem glueEord_left (hP : IsIntervalPom P) (e f : Fin P.n) :
    glueEord m.len_eq (GluedE.leftMap P Q e) (GluedE.leftMap P Q f) ↔ P.eord e f := by
  classical
  unfold GluedE.leftMap
  split_ifs with he hf hf
  · have he' := Classical.choose_spec he
    have hf' := Classical.choose_spec hf
    simp only [glueEord, he',hf']
  · simp only [glueEord, Classical.choose_spec he]
  · simp only [glueEord, Classical.choose_spec hf]
  · rfl

theorem glueEord_right (hP : IsIntervalPom P) (hQ : IsIntervalPom Q) (e f : Fin Q.n) :
    glueEord m.len_eq (GluedE.rightMap P Q m.len_eq e) (GluedE.rightMap P Q m.len_eq f) ↔
      Q.eord e f := by
  classical
  unfold GluedE.rightMap
  split_ifs with he hf hf
  · have he' := Classical.choose_spec he
    have hf' := Classical.choose_spec hf
    simp only [glueEord, hP.tgt_eord]
    have hq := hQ.src_eord (Classical.choose he) (Classical.choose hf)
    simp only [he',hf'] at hq
    simpa only [Fin.cast_lt_cast] using hq.symm
  · simp only [glueEord, Fin.cast_cast, Fin.cast_refl, id_eq, Classical.choose_spec he]
  · simp only [glueEord, Fin.cast_cast, Fin.cast_refl, id_eq, Classical.choose_spec hf]
  · rfl

theorem gluePrec_no_into_source (hP : IsIntervalPom P) (i : Fin P.srcLen) :
    ∀ e : GluedE P Q, ¬ gluePrec m.len_eq e (GluedE.leftMap P Q (P.src i)) := by
  classical
  intro e
  unfold GluedE.leftMap
  split_ifs with hi
  · have he := Classical.choose_spec hi
    cases e with
    | left e => simpa only [gluePrec,he] using hP.src_minimal _ ⟨i,rfl⟩ e.val
    | right e => exact not_false
    | mid j => exact not_false
  · cases e with
    | left e => exact hP.src_minimal _ ⟨i,rfl⟩ e.val
    | right e => exact not_false
    | mid j => exact not_false

theorem gluePrec_no_out_target (hQ : IsIntervalPom Q) (i : Fin Q.tgtLen) :
    ∀ e : GluedE P Q, ¬ gluePrec m.len_eq (GluedE.rightMap P Q m.len_eq (Q.tgt i)) e := by
  classical
  intro e
  unfold GluedE.rightMap
  split_ifs with hi
  · have he := Classical.choose_spec hi
    cases e with
    | right e => simpa only [gluePrec,Fin.cast_cast,Fin.cast_refl,id_eq,he] using
        hQ.tgt_maximal _ ⟨i,rfl⟩ e.val
    | left e => exact not_false
    | mid j => exact not_false
  · cases e with
    | right e => exact hQ.tgt_maximal _ ⟨i,rfl⟩ e.val
    | left e => exact not_false
    | mid j => exact not_false

theorem glue_trichotomy (hP : IsIntervalPom P) (hQ : IsIntervalPom Q)
    (e f : GluedE P Q) (hef : e ≠ f) :
    (gluePrec m.len_eq e f ∨ gluePrec m.len_eq f e ∨ glueEord m.len_eq e f ∨ glueEord m.len_eq f e) ∧
    (gluePrec m.len_eq e f → ¬ gluePrec m.len_eq f e ∧ ¬ glueEord m.len_eq e f ∧ ¬ glueEord m.len_eq f e) ∧
    (gluePrec m.len_eq f e → ¬ gluePrec m.len_eq e f ∧ ¬ glueEord m.len_eq e f ∧ ¬ glueEord m.len_eq f e) ∧
    (glueEord m.len_eq e f → ¬ gluePrec m.len_eq e f ∧ ¬ gluePrec m.len_eq f e ∧ ¬ glueEord m.len_eq f e) ∧
    (glueEord m.len_eq f e → ¬ gluePrec m.len_eq e f ∧ ¬ gluePrec m.len_eq f e ∧ ¬ glueEord m.len_eq e f) := by
  have pmax : ∀ i x, ¬ P.prec (P.tgt i) x := fun i x => hP.tgt_maximal _ ⟨i,rfl⟩ x
  have qmin : ∀ i x, ¬ Q.prec x (Q.src i) := fun i x => hQ.src_minimal _ ⟨i,rfl⟩ x
  cases e with
  | left e =>
    cases f with
    | left f => exact hP.trichotomy _ _ (fun h => hef (congrArg GluedE.left (Subtype.ext h)))
    | right f => simp only [gluePrec,glueEord]; tauto
    | mid j =>
      have he : e.val ≠ P.tgt j := fun h => e.property ⟨j,h.symm⟩
      simpa only [gluePrec,glueEord,pmax] using hP.trichotomy e.val (P.tgt j) he
  | right e =>
    cases f with
    | left f => simp only [gluePrec,glueEord]; tauto
    | right f => exact hQ.trichotomy _ _ (fun h => hef (congrArg GluedE.right (Subtype.ext h)))
    | mid j =>
      have he : e.val ≠ Q.src (Fin.cast m.len_eq j) := fun h => e.property ⟨_,h.symm⟩
      simpa only [gluePrec,glueEord,qmin] using hQ.trichotomy e.val (Q.src _) he
  | mid i =>
    cases f with
    | left f =>
      have he : P.tgt i ≠ f.val := fun h => f.property ⟨i,h⟩
      simpa only [gluePrec,glueEord,pmax] using hP.trichotomy (P.tgt i) f.val he
    | right f =>
      have he : Q.src (Fin.cast m.len_eq i) ≠ f.val := fun h => f.property ⟨_,h⟩
      simpa only [gluePrec,glueEord,qmin] using hQ.trichotomy (Q.src _) f.val he
    | mid j =>
      have he : P.tgt i ≠ P.tgt j := fun h => hef (congrArg GluedE.mid (P.tgt_inj h))
      simpa only [gluePrec,glueEord,pmax] using hP.trichotomy (P.tgt i) (P.tgt j) he

/-- Gluing is an actual interval pomset, not merely raw data. -/
theorem glueData_isIntervalPom (hP : IsIntervalPom P) (hQ : IsIntervalPom Q) :
    IsIntervalPom (glueData P Q m) := by
  let ev := (Fintype.equivFin (GluedE P Q)).symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e; exact gluePrec_irrefl m hP hQ (ev e)
  · intro e f g hef hfg; exact gluePrec_trans m hP hQ hef hfg
  · intro e he
    exact glueEord_acyclic m.len_eq hP hQ _ (.single he)
  · intro e he
    have lift : ∀ {a b}, Relation.TransGen (glueData P Q m).eord a b →
        Relation.TransGen (glueEord m.len_eq) (ev a) (ev b) := by
      intro a b hab
      induction hab with
      | single h => exact .single h
      | tail _ h ih => exact ih.tail h
    exact glueEord_acyclic m.len_eq hP hQ _ (lift he)
  · intro e f hef
    exact glue_trichotomy m hP hQ (ev e) (ev f) (fun h => hef (ev.injective h))
  · intro e he f hf
    obtain ⟨i,rfl⟩ := he
    apply gluePrec_no_into_source m hP i (ev f)
    simpa only [glueData,ev,Equiv.symm_apply_apply] using hf
  · intro e he f hf
    obtain ⟨i,rfl⟩ := he
    apply gluePrec_no_out_target m hQ i (ev f)
    simpa only [glueData,ev,Equiv.symm_apply_apply] using hf
  · intro i j
    change glueEord m.len_eq (ev _) (ev _) ↔ i.val < j.val
    simp only [glueData,Equiv.symm_apply_apply,ev,glueEord_left m hP,hP.src_eord]
  · intro i j
    change glueEord m.len_eq (ev _) (ev _) ↔ i.val < j.val
    simp only [glueData,Equiv.symm_apply_apply,ev,glueEord_right m hP hQ,hQ.tgt_eord]
  · obtain ⟨s,t,hrep⟩ := gluePrec_interval_rep m hP hQ
    exact ⟨s ∘ ev,t ∘ ev,fun e f => hrep _ _⟩

noncomputable def glue (P Q : IntervalPom Lab) (m : GlueMatch P.val Q.val) : IntervalPom Lab :=
  ⟨glueData P.val Q.val m,glueData_isIntervalPom m P.property Q.property⟩

end CounterFreeHDA
