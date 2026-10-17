import CounterFreeHDA.CornerPaths

namespace CounterFreeHDA.PomsetData
universe u
variable {Lab : Type u} {A B P : PomsetData Lab} {k : ℕ}

theorem widthLE_of_size_le (P : PomsetData Lab) (h : P.n ≤ k) : P.WidthLE k := by
  intro S _
  exact le_trans (by simpa only [Finset.card_univ,Fintype.card_fin] using Finset.card_le_card (Finset.subset_univ S)) h

/-- An antichain covered by one embedded factor has at most that factor's
width. The event-order data are retained by the ambient gluing separately. -/
theorem antichain_card_le_of_cover (hw : A.WidthLE k) (f : Fin A.n ↪ Fin P.n)
    (hp : ∀ e g, A.prec e g → P.prec (f e) (f g)) (S : Finset (Fin P.n))
    (hS : P.Antichain S) (hc : ∀ e ∈ S, ∃ a, f a = e) : S.card ≤ k := by
  classical
  let T := Finset.univ.filter (fun a => f a ∈ S)
  have him : T.image f = S := by
    ext e
    constructor
    · rintro he
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp he
      exact (Finset.mem_filter.mp ha).2
    · intro he
      obtain ⟨a,rfl⟩ := hc e he
      exact Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ a,he⟩,rfl⟩
  have hcard : T.card = S.card := by
    rw [← him,Finset.card_image_of_injective _ f.injective]
  rw [← hcard]
  apply hw
  intro e he g hg hprec
  exact hS (f e) (Finset.mem_filter.mp he).2 (f g) (Finset.mem_filter.mp hg).2 (hp e g hprec)

end CounterFreeHDA.PomsetData

namespace CounterFreeHDA.Cubical.TrackGlue
universe u
variable {Lab : Type u} {A B : PomsetData Lab} {k : ℕ}

/-- Gluing introduces precedence from every left non-interface event to
every right non-interface event, so each antichain lies in one factor. -/
theorem width_glue (m : GlueMatch A B) (hA : IsIntervalPom A) (hB : IsIntervalPom B)
    (hwA : A.WidthLE k) (hwB : B.WidthLE k) : (glueData A B m).WidthLE k := by
  classical
  intro S hS
  by_cases hl : ∃ a : {e : Fin A.n // ¬ A.inTgt e}, index m (.left a) ∈ S
  · obtain ⟨a,ha⟩ := hl
    apply PomsetData.antichain_card_le_of_cover hwA
      ⟨leftEvent m,(index m).injective.comp (GluedE.leftMap_inj A B)⟩
      (fun e f h => (leftEvent_prec m hA e f).mpr h) S hS
    intro e he
    cases hh : (index m).symm e with
    | left b =>
      refine ⟨b.val,?_⟩
      change index m (GluedE.leftMap A B b.val) = e
      have hb : GluedE.leftMap A B b.val = .left b := by unfold GluedE.leftMap; exact dif_neg b.property
      exact (congrArg (index m) hb).trans ((congrArg (index m) hh).symm.trans ((index m).apply_symm_apply e))
    | mid i =>
      refine ⟨A.tgt i,?_⟩
      exact (congrArg (index m) (GluedE.leftMap_tgt A B i)).trans
        ((congrArg (index m) hh).symm.trans ((index m).apply_symm_apply e))
    | right b =>
      have hp : (glueData A B m).prec (index m (.left a)) e := by
        change gluePrec m.len_eq ((index m).symm (index m (.left a))) ((index m).symm e)
        rw [Equiv.symm_apply_apply,hh]
        trivial
      exact False.elim (hS _ ha e he hp)
  · apply PomsetData.antichain_card_le_of_cover hwB
      ⟨rightEvent m,(index m).injective.comp (GluedE.rightMap_inj A B m.len_eq)⟩
      (fun e f h => (rightEvent_prec m hB e f).mpr h) S hS
    intro e he
    cases hh : (index m).symm e with
    | left a =>
      apply False.elim
      apply hl
      have heq : index m (.left a) = e := (congrArg (index m) hh).symm.trans ((index m).apply_symm_apply e)
      exact ⟨a,heq.symm ▸ he⟩
    | right b =>
      refine ⟨b.val,?_⟩
      change index m (GluedE.rightMap A B m.len_eq b.val) = e
      have hb : GluedE.rightMap A B m.len_eq b.val = .right b := by unfold GluedE.rightMap; exact dif_neg b.property
      exact (congrArg (index m) hb).trans ((congrArg (index m) hh).symm.trans ((index m).apply_symm_apply e))
    | mid i =>
      refine ⟨B.src (Fin.cast m.len_eq i),?_⟩
      change index m (GluedE.rightMap A B m.len_eq (B.src (Fin.cast m.len_eq i))) = e
      have hm := GluedE.rightMap_src A B m.len_eq (Fin.cast m.len_eq i)
      have hcast : Fin.cast m.len_eq.symm (Fin.cast m.len_eq i) = i := Fin.ext rfl
      exact (congrArg (index m) (hm.trans (congrArg GluedE.mid hcast))).trans
        ((congrArg (index m) hh).symm.trans ((index m).apply_symm_apply e))

end CounterFreeHDA.Cubical.TrackGlue

namespace CounterFreeHDA.Cubical
universe u v
variable {Lab : Type u} {k : ℕ}

namespace Step

theorem label_width {U V : Cube Lab k} (s : Step U V) : s.label.pom.val.WidthLE k := by
  apply PomsetData.widthLE_of_size_le
  cases s with
  | start f hl hd => exact Nat.le_of_lt_succ V.1.isLt
  | stop f hu hd => exact Nat.le_of_lt_succ U.1.isLt

end Step

namespace Word

theorem label_width {U V : Cube Lab k} (p : Word U V) : p.label.pom.val.WidthLE k := by
  induction p with
  | nil U => exact PomsetData.widthLE_of_size_le _ (Nat.le_of_lt_succ U.1.isLt)
  | cons s p ih => exact TrackGlue.width_glue _ s.label.pom.property p.label.pom.property s.label_width ih

end Word

namespace HDA

theorem accepted_width (X : HDA.{u,v} Lab k) {P : IntervalPom Lab} (h : P ∈ X.LangPom) : P.val.WidthLE k := by
  obtain ⟨U,V,x,y,_,_,p,_,⟨φ⟩⟩ := h
  apply p.label_width.ofEmbedding φ.toEquiv.symm.toEmbedding
  intro e f hef
  exact (φ.symm.prec_iff e f).mp hef

end HDA
end CounterFreeHDA.Cubical
