import CounterFreeHDA.TrackIso

namespace CounterFreeHDA.PomsetIso
universe u
variable {Lab : Type u} {P P' Q Q' : PomsetData Lab}

theorem srcEquiv_val (φ : PomsetIso P P') (i : Fin P.srcLen) : (φ.srcEquiv i).val = i.val := by
  have hn : P.srcLen = P'.srcLen := by simpa only [Fintype.card_fin] using Fintype.card_congr φ.srcEquiv
  let f : Fin P.srcLen → Fin P.srcLen := fun i => Fin.cast hn.symm (φ.srcEquiv i)
  have hf : StrictMono f := fun _ _ h => (φ.src_mono _ _).mpr h
  have hi := le_antisymm (hf.le_id i) (hf.id_le i)
  exact congrArg Fin.val hi

theorem tgtEquiv_val (φ : PomsetIso P P') (i : Fin P.tgtLen) : (φ.tgtEquiv i).val = i.val := by
  have hn : P.tgtLen = P'.tgtLen := by simpa only [Fintype.card_fin] using Fintype.card_congr φ.tgtEquiv
  let f : Fin P.tgtLen → Fin P.tgtLen := fun i => Fin.cast hn.symm (φ.tgtEquiv i)
  have hf : StrictMono f := fun _ _ h => (φ.tgt_mono _ _).mpr h
  have hi := le_antisymm (hf.le_id i) (hf.id_le i)
  exact congrArg Fin.val hi

def rawMap (φ : PomsetIso P P') (ψ : PomsetIso Q Q') : GluedE P Q → GluedE P' Q'
  | .left e => .left ⟨φ.toEquiv e.val,fun h => e.property ((φ.inTgt_image_iff e.val).mp h)⟩
  | .right e => .right ⟨ψ.toEquiv e.val,fun h => e.property ((ψ.inSrc_image_iff e.val).mp h)⟩
  | .mid i => .mid (φ.tgtEquiv i)

def rawEquiv (φ : PomsetIso P P') (ψ : PomsetIso Q Q') : GluedE P Q ≃ GluedE P' Q' where
  toFun := rawMap φ ψ
  invFun := rawMap φ.symm ψ.symm
  left_inv e := by
    cases e with
    | left e => apply congrArg GluedE.left; apply Subtype.ext; exact φ.toEquiv.symm_apply_apply _
    | right e => apply congrArg GluedE.right; apply Subtype.ext; exact ψ.toEquiv.symm_apply_apply _
    | mid i => exact congrArg GluedE.mid (φ.tgtEquiv.symm_apply_apply i)
  right_inv e := by
    cases e with
    | left e => apply congrArg GluedE.left; apply Subtype.ext; exact φ.toEquiv.apply_symm_apply _
    | right e => apply congrArg GluedE.right; apply Subtype.ext; exact ψ.toEquiv.apply_symm_apply _
    | mid i => exact congrArg GluedE.mid (φ.tgtEquiv.apply_symm_apply i)

variable (φ : PomsetIso P P') (ψ : PomsetIso Q Q') (m : GlueMatch P Q) (m' : GlueMatch P' Q')

theorem seam_indices (i : Fin P.tgtLen) :
    Fin.cast m'.len_eq (φ.tgtEquiv i) = ψ.srcEquiv (Fin.cast m.len_eq i) := by
  apply Fin.ext
  change (φ.tgtEquiv i).val = (ψ.srcEquiv (Fin.cast m.len_eq i)).val
  rw [tgtEquiv_val,srcEquiv_val]
  rfl

theorem seam_events (i : Fin P.tgtLen) :
    P'.tgt (φ.tgtEquiv i) = φ.toEquiv (P.tgt i) ∧
    Q'.src (Fin.cast m'.len_eq (φ.tgtEquiv i)) = ψ.toEquiv (Q.src (Fin.cast m.len_eq i)) := by
  exact ⟨(φ.tgt_eq i).symm,by rw [seam_indices φ ψ m m']; exact (ψ.src_eq _).symm⟩

theorem rawMap_left (e : Fin P.n) :
    rawMap φ ψ (GluedE.leftMap P Q e) = GluedE.leftMap P' Q' (φ.toEquiv e) := by
  classical
  by_cases he : P.inTgt e
  · obtain ⟨i,rfl⟩ := he
    rw [GluedE.leftMap_tgt,rawMap,φ.tgt_eq,GluedE.leftMap_tgt]
  · have hn : ¬ P'.inTgt (φ.toEquiv e) := fun h => he ((φ.inTgt_image_iff e).mp h)
    have hl : GluedE.leftMap P Q e = .left ⟨e,he⟩ := by unfold GluedE.leftMap; exact dif_neg he
    rw [hl]
    change GluedE.left _ = GluedE.leftMap P' Q' (φ.toEquiv e)
    unfold GluedE.leftMap
    rw [dif_neg hn]

theorem rawMap_right (e : Fin Q.n) :
    rawMap φ ψ (GluedE.rightMap P Q m.len_eq e) = GluedE.rightMap P' Q' m'.len_eq (ψ.toEquiv e) := by
  classical
  by_cases he : Q.inSrc e
  · obtain ⟨i,rfl⟩ := he
    rw [GluedE.rightMap_src,rawMap,ψ.src_eq,GluedE.rightMap_src]
    apply congrArg GluedE.mid
    apply Fin.ext
    change (φ.tgtEquiv (Fin.cast m.len_eq.symm i)).val = (ψ.srcEquiv i).val
    rw [tgtEquiv_val,srcEquiv_val]
    rfl
  · have hn : ¬ Q'.inSrc (ψ.toEquiv e) := fun h => he ((ψ.inSrc_image_iff e).mp h)
    have hl : GluedE.rightMap P Q m.len_eq e = .right ⟨e,he⟩ := by unfold GluedE.rightMap; exact dif_neg he
    rw [hl]
    change GluedE.right _ = GluedE.rightMap P' Q' m'.len_eq (ψ.toEquiv e)
    unfold GluedE.rightMap
    rw [dif_neg hn]

theorem raw_lab (e : GluedE P Q) : glueLab m' (rawMap φ ψ e) = glueLab m e := by
  cases e with
  | left e => exact φ.lab_eq e.val
  | right e => exact ψ.lab_eq e.val
  | mid i =>
    change P'.lab (P'.tgt (φ.tgtEquiv i)) = _
    rw [← φ.tgt_eq]
    exact φ.lab_eq _

theorem raw_prec (e f : GluedE P Q) :
    gluePrec m'.len_eq (rawMap φ ψ e) (rawMap φ ψ f) ↔ gluePrec m.len_eq e f := by
  cases e <;> cases f <;> change _ ↔ _
  · exact φ.prec_iff _ _
  · rfl
  · change P'.prec _ (P'.tgt _) ↔ _
    rw [← φ.tgt_eq]
    exact φ.prec_iff _ _
  · rfl
  · exact ψ.prec_iff _ _
  · rfl
  · rfl
  · change Q'.prec (Q'.src _) _ ↔ _
    rw [(seam_events φ ψ m m' _).2]
    exact ψ.prec_iff _ _
  · rfl

theorem raw_eord (e f : GluedE P Q) :
    glueEord m'.len_eq (rawMap φ ψ e) (rawMap φ ψ f) ↔ glueEord m.len_eq e f := by
  cases e <;> cases f <;> change _ ↔ _
  · exact φ.eord_iff _ _
  · rfl
  · change P'.eord _ (P'.tgt _) ↔ _
    rw [← φ.tgt_eq]
    exact φ.eord_iff _ _
  · rfl
  · exact ψ.eord_iff _ _
  · change Q'.eord _ (Q'.src _) ↔ _
    rw [(seam_events φ ψ m m' _).2]
    exact ψ.eord_iff _ _
  · change P'.eord (P'.tgt _) _ ↔ _
    rw [← φ.tgt_eq]
    exact φ.eord_iff _ _
  · change Q'.eord (Q'.src _) _ ↔ _
    rw [(seam_events φ ψ m m' _).2]
    exact ψ.eord_iff _ _
  · change P'.eord (P'.tgt _) (P'.tgt _) ↔ _
    rw [← φ.tgt_eq,← φ.tgt_eq]
    exact φ.eord_iff _ _

/-- Actual gluing preserves event, order, label and interface isomorphisms. -/
noncomputable def glueIso : PomsetIso (glueData P Q m) (glueData P' Q' m') where
  toEquiv := (Fintype.equivFin (GluedE P Q)).symm.trans ((rawEquiv φ ψ).trans (Fintype.equivFin (GluedE P' Q')))
  lab_eq e := by
    change glueLab m' ((Fintype.equivFin (GluedE P' Q')).symm ((Fintype.equivFin (GluedE P' Q'))
      (rawMap φ ψ ((Fintype.equivFin (GluedE P Q)).symm e)))) = _
    rw [Equiv.symm_apply_apply]
    exact raw_lab φ ψ m m' _
  srcEquiv := φ.srcEquiv
  tgtEquiv := ψ.tgtEquiv
  src_mono := φ.src_mono
  tgt_mono := ψ.tgt_mono
  src_eq i := by
    change (Fintype.equivFin (GluedE P' Q')) (rawMap φ ψ ((Fintype.equivFin (GluedE P Q)).symm
      ((Fintype.equivFin (GluedE P Q)) (GluedE.leftMap P Q (P.src i))))) = _
    rw [Equiv.symm_apply_apply,rawMap_left,φ.src_eq]
    rfl
  tgt_eq i := by
    change (Fintype.equivFin (GluedE P' Q')) (rawMap φ ψ ((Fintype.equivFin (GluedE P Q)).symm
      ((Fintype.equivFin (GluedE P Q)) (GluedE.rightMap P Q m.len_eq (Q.tgt i))))) = _
    rw [Equiv.symm_apply_apply,rawMap_right φ ψ m m',ψ.tgt_eq]
    rfl
  prec_iff e f := by
    change gluePrec m'.len_eq
      ((Fintype.equivFin (GluedE P' Q')).symm ((Fintype.equivFin (GluedE P' Q')) (rawMap φ ψ _)))
      ((Fintype.equivFin (GluedE P' Q')).symm ((Fintype.equivFin (GluedE P' Q')) (rawMap φ ψ _))) ↔ _
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    exact raw_prec φ ψ m m' _ _
  eord_iff e f := by
    change glueEord m'.len_eq
      ((Fintype.equivFin (GluedE P' Q')).symm ((Fintype.equivFin (GluedE P' Q')) (rawMap φ ψ _)))
      ((Fintype.equivFin (GluedE P' Q')).symm ((Fintype.equivFin (GluedE P' Q')) (rawMap φ ψ _))) ↔ _
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    exact raw_eord φ ψ m m' _ _

end CounterFreeHDA.PomsetIso
