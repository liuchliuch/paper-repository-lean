import CounterFreeHDA.Gluing

namespace CounterFreeHDA
universe u
variable {Lab : Type u} (P Q : PomsetData Lab)

private def gluedEquiv : GluedE P Q ≃
    ({e : Fin P.n // ¬ P.inTgt e} ⊕ {e : Fin Q.n // ¬ Q.inSrc e}) ⊕ Fin P.tgtLen where
  toFun := GluedE.toSum P Q
  invFun
    | .inl (.inl e) => .left e
    | .inl (.inr e) => .right e
    | .inr i => .mid i
  left_inv e := by cases e <;> rfl
  right_inv e := by rcases e with (e|e)|i <;> rfl

theorem srcLen_le : P.srcLen ≤ P.n := by simpa using Fintype.card_le_of_injective P.src P.src_inj

theorem tgtLen_le : P.tgtLen ≤ P.n := by simpa using Fintype.card_le_of_injective P.tgt P.tgt_inj

noncomputable instance sourceFintype : Fintype {e : Fin P.n // P.inSrc e} := Fintype.ofFinite _
noncomputable instance targetFintype : Fintype {e : Fin P.n // P.inTgt e} := Fintype.ofFinite _

theorem card_source : Fintype.card {e : Fin P.n // P.inSrc e} = P.srcLen := by
  classical
  simpa only [Fintype.card_fin] using (@Fintype.card_congr (Fin P.srcLen) {e : Fin P.n // P.inSrc e} _ (sourceFintype P) (Equiv.ofInjective P.src P.src_inj)).symm

theorem card_target : Fintype.card {e : Fin P.n // P.inTgt e} = P.tgtLen := by
  classical
  simpa only [Fintype.card_fin] using (@Fintype.card_congr (Fin P.tgtLen) {e : Fin P.n // P.inTgt e} _ (targetFintype P) (Equiv.ofInjective P.tgt P.tgt_inj)).symm

/-- Gluing identifies exactly one copy of each common-interface event. -/
theorem glue_card (m : GlueMatch P Q) :
    (glueData P Q m).n + P.tgtLen = P.n + Q.n := by
  classical
  change Fintype.card (GluedE P Q) + P.tgtLen = _
  rw [Fintype.card_congr (gluedEquiv P Q),Fintype.card_sum,Fintype.card_sum,
    Fintype.card_fin,Fintype.card_subtype_compl,Fintype.card_subtype_compl,
    card_target,card_source]
  have hp := tgtLen_le P
  have hq := srcLen_le Q
  have hm := m.len_eq
  simp only [Fintype.card_fin]
  omega

variable {P Q}

theorem glueLab_left (m : GlueMatch P Q) (e : Fin P.n) :
    glueLab m (GluedE.leftMap P Q e) = P.lab e := by
  classical
  unfold GluedE.leftMap
  split_ifs with h
  · exact congrArg P.lab (Classical.choose_spec h)
  · rfl

theorem glueLab_right (m : GlueMatch P Q) (e : Fin Q.n) :
    glueLab m (GluedE.rightMap P Q m.len_eq e) = Q.lab e := by
  classical
  unfold GluedE.rightMap
  split_ifs with h
  · change P.lab (P.tgt (Fin.cast m.len_eq.symm (Classical.choose h))) = _
    have hl := m.lab_eq (Fin.cast m.len_eq.symm (Classical.choose h))
    simpa only [Fin.cast_cast,Fin.cast_refl,id_eq,Classical.choose_spec h] using hl
  · rfl

/-- A source interface type retains both its length and every position label. -/
def PomsetData.srcType (P : PomsetData Lab) : Σ n : ℕ, Fin n → Lab := ⟨P.srcLen,P.lab ∘ P.src⟩
def PomsetData.tgtType (P : PomsetData Lab) : Σ n : ℕ, Fin n → Lab := ⟨P.tgtLen,P.lab ∘ P.tgt⟩

theorem glue_srcType (m : GlueMatch P Q) : (glueData P Q m).srcType = P.srcType := by
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  funext i
  simp only [PomsetData.srcType,Function.comp_apply,glueData,Equiv.symm_apply_apply,glueLab_left]

theorem glue_tgtType (m : GlueMatch P Q) : (glueData P Q m).tgtType = Q.tgtType := by
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  funext i
  simp only [PomsetData.tgtType,Function.comp_apply,glueData,Equiv.symm_apply_apply,glueLab_right]

noncomputable def GlueMatch.ofType (h : P.tgtType = Q.srcType) : GlueMatch P Q := by
  obtain ⟨hl,hlabels⟩ := (Fin.sigma_eq_iff_eq_comp_cast).mp h
  exact ⟨hl,fun i => congrFun hlabels i⟩

end CounterFreeHDA
