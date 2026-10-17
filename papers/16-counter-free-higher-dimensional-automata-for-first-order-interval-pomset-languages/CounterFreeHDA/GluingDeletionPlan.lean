import CounterFreeHDA.DeletionEmbedding

namespace CounterFreeHDA.Deletion
universe u
open Cubical.TrackGlue
variable {Lab : Type u} {A B : PomsetData Lab}

/-- A deletion on a real gluing whose restrictions to both factors agree
with the selected factor deletions, including every identified seam event. -/
structure Plan (m : GlueMatch A B) where
  keepA : Fin A.n → Prop
  keepB : Fin B.n → Prop
  keepG : Fin (glueData A B m).n → Prop
  [decA : DecidablePred keepA]
  [decB : DecidablePred keepB]
  [decG : DecidablePred keepG]
  left_iff : ∀ e, keepG (leftEvent m e) ↔ keepA e
  right_iff : ∀ e, keepG (rightEvent m e) ↔ keepB e

attribute [instance] Plan.decA Plan.decB Plan.decG

namespace Plan
variable {m : GlueMatch A B} (D : Plan m)

noncomputable abbrev leftData := data A D.keepA
noncomputable abbrev rightData := data B D.keepB
noncomputable abbrev gluedData := data (glueData A B m) D.keepG

theorem seam_kept (i : Fin A.tgtLen) : D.keepA (A.tgt i) ↔ D.keepB (B.src (Fin.cast m.len_eq i)) := by
  have hs := congrArg (index m) (GluedE.identified A B m.len_eq i)
  exact (D.left_iff _).symm.trans ((congrArg D.keepG hs).to_iff.trans (D.right_iff _))

noncomputable def reducedMatch : Match m D.keepA D.keepB := matching m D.keepA D.keepB D.seam_kept
noncomputable def glueMatch : GlueMatch D.leftData D.rightData := D.reducedMatch.toGlueMatch

theorem positions (i : Fin (target A D.keepA).card) :
    Fin.cast m.len_eq ((target A D.keepA).orderEmbOfFin rfl i) =
      (source B D.keepB).orderEmbOfFin rfl (Fin.cast D.glueMatch.len_eq i) := D.reducedMatch.positions i

noncomputable def left : Fin D.leftData.n ↪ Fin D.gluedData.n :=
  lift D.keepA D.keepG ⟨leftEvent m,(index m).injective.comp (GluedE.leftMap_inj A B)⟩
    (fun e he => (D.left_iff e).mpr he)

noncomputable def right : Fin D.rightData.n ↪ Fin D.gluedData.n :=
  lift D.keepB D.keepG ⟨rightEvent m,(index m).injective.comp (GluedE.rightMap_inj A B m.len_eq)⟩
    (fun e he => (D.right_iff e).mpr he)

@[simp] theorem inclusion_left (e : Fin D.leftData.n) :
    inclusion (glueData A B m) D.keepG (D.left e) = leftEvent m (inclusion A D.keepA e) :=
  inclusion_lift D.keepA D.keepG _ _ e

@[simp] theorem inclusion_right (e : Fin D.rightData.n) :
    inclusion (glueData A B m) D.keepG (D.right e) = rightEvent m (inclusion B D.keepB e) :=
  inclusion_lift D.keepB D.keepG _ _ e

/-- Outer retained source positions are exactly the retained left source. -/
theorem source_eq : source (glueData A B m) D.keepG = source A D.keepA := by
  ext i
  simp only [source,Finset.mem_filter,Finset.mem_univ,true_and]
  exact D.left_iff (A.src i)

/-- Outer retained target positions are exactly the retained right target. -/
theorem target_eq : target (glueData A B m) D.keepG = target B D.keepB := by
  ext i
  simp only [target,Finset.mem_filter,Finset.mem_univ,true_and]
  exact D.right_iff (B.tgt i)

theorem seam (i : Fin D.leftData.tgtLen) :
    D.left (D.leftData.tgt i) = D.right (D.rightData.src (Fin.cast D.glueMatch.len_eq i)) := by
  apply (inclusion (glueData A B m) D.keepG).injective
  calc
    _ = leftEvent m (inclusion A D.keepA (D.leftData.tgt i)) := D.inclusion_left _
    _ = leftEvent m (A.tgt ((target A D.keepA).orderEmbOfFin rfl i)) :=
      congrArg (leftEvent m) (inclusion_target A D.keepA i)
    _ = rightEvent m (B.src (Fin.cast m.len_eq ((target A D.keepA).orderEmbOfFin rfl i))) :=
      congrArg (index m) (GluedE.identified A B m.len_eq _)
    _ = rightEvent m (B.src ((source B D.keepB).orderEmbOfFin rfl (Fin.cast D.glueMatch.len_eq i))) :=
      congrArg (fun j => rightEvent m (B.src j)) (D.positions i)
    _ = rightEvent m (inclusion B D.keepB (D.rightData.src (Fin.cast D.glueMatch.len_eq i))) :=
      congrArg (rightEvent m) (inclusion_source B D.keepB _).symm
    _ = _ := (D.inclusion_right _).symm

end Plan
end CounterFreeHDA.Deletion
