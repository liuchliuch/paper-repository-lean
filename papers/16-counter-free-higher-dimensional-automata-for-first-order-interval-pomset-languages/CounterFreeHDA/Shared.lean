import CounterFreeHDA.ActualPower
import CounterFreeHDA.Survival

namespace CounterFreeHDA
universe u
variable {Lab : Type u} {P Q : PomsetData Lab}

/-- A left and a right event are identified exactly when they are the same
ordered event of the gluing interface. -/
theorem glued_identified_iff (len : P.tgtLen = Q.srcLen) (e : Fin P.n) (f : Fin Q.n) :
    GluedE.leftMap P Q e = GluedE.rightMap P Q len f ↔
      ∃ i : Fin P.tgtLen, P.tgt i = e ∧ Q.src (Fin.cast len i) = f := by
  classical
  constructor
  · intro h
    unfold GluedE.leftMap GluedE.rightMap at h
    split_ifs at h with he hf hf
    · have hi := GluedE.mid.inj h
      refine ⟨Classical.choose he,Classical.choose_spec he,?_⟩
      have hcast := congrArg (Fin.cast len) hi
      simp only [Fin.cast_cast,Fin.cast_refl,id_eq] at hcast
      rw [hcast]
      exact Classical.choose_spec hf
  · rintro ⟨i,he,hf⟩
    calc
      GluedE.leftMap P Q e = GluedE.leftMap P Q (P.tgt i) := congrArg _ he.symm
      _ = GluedE.rightMap P Q len (Q.src (Fin.cast len i)) := GluedE.identified P Q len i
      _ = GluedE.rightMap P Q len f := congrArg _ hf

/-- Sharing an event between the outer interfaces of a glued product is
relational composition of the two sharing relations. -/
theorem glue_shared_iff (m : GlueMatch P Q) (i : Fin P.srcLen) (j : Fin Q.tgtLen) :
    (glueData P Q m).src i = (glueData P Q m).tgt j ↔
      ∃ l : Fin P.tgtLen, P.src i = P.tgt l ∧ Q.src (Fin.cast m.len_eq l) = Q.tgt j := by
  change (Fintype.equivFin (GluedE P Q)) (GluedE.leftMap P Q (P.src i)) =
    (Fintype.equivFin (GluedE P Q)) (GluedE.rightMap P Q m.len_eq (Q.tgt j)) ↔ _
  rw [(Fintype.equivFin (GluedE P Q)).injective.eq_iff,glued_identified_iff]
  exact exists_congr (fun l => and_congr_left (fun _ => eq_comm))

namespace EndoPom
variable {U : Interface Lab}

def Shared (P : EndoPom U) (i j : Fin U.1) : Prop :=
  P.pom.src (Fin.cast P.src_len.symm i) = P.pom.tgt (Fin.cast P.tgt_len.symm j)

theorem shared_mul (P Q : EndoPom U) (i j : Fin U.1) :
    (P.mul Q).Shared i j ↔ ∃ l : Fin U.1, P.Shared i l ∧ Q.Shared l j := by
  unfold Shared
  have h := glue_shared_iff (GlueMatch.ofType (P.target.trans Q.source.symm))
    (Fin.cast P.src_len.symm i) (Fin.cast Q.tgt_len.symm j)
  change (glueData _ _ _).src _ = (glueData _ _ _).tgt _ ↔ _
  rw [h]
  constructor
  · rintro ⟨l,hl,hr⟩
    refine ⟨Fin.cast P.tgt_len l, ?_, ?_⟩
    · simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using hl
    · convert hr using 1 <;> apply congrArg <;> apply Fin.ext <;> rfl
  · rintro ⟨l,hl,hr⟩
    refine ⟨Fin.cast P.tgt_len.symm l,hl,?_⟩
    convert hr using 1 <;> apply congrArg <;> apply Fin.ext <;> rfl

end EndoPom
end CounterFreeHDA
