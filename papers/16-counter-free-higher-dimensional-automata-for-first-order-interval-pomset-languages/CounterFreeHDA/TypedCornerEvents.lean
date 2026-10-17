import CounterFreeHDA.TypedCorners

namespace CounterFreeHDA.Cubical.Arrow
universe u
variable {Lab : Type u} {k : ℕ} {U V T W : Cube Lab k}

theorem corner_deleted_iff (A : Arrow U V) (α : Face T U) (β : Face W V) (e : Fin A.pom.n) :
    Corners.Deleted A.pom.val (A.sourceFace α).status (A.targetFace β).status e ↔
      (∃ i : Fin U.dim, A.pom.src (Fin.cast A.src_len.symm i) = e ∧ α.status i = Status.one) ∨
      (∃ j : Fin V.dim, A.pom.tgt (Fin.cast A.tgt_len.symm j) = e ∧ β.status j = Status.zero) := by
  constructor
  · rintro (⟨i,hi,hα⟩ | ⟨j,hj,hβ⟩)
    · refine Or.inl ⟨Fin.cast A.src_len i,?_,hα⟩
      simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using hi
    · refine Or.inr ⟨Fin.cast A.tgt_len j,?_,hβ⟩
      simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using hj
  · rintro (⟨i,hi,hα⟩ | ⟨j,hj,hβ⟩)
    · refine Or.inl ⟨Fin.cast A.src_len.symm i,hi,?_⟩
      change α.status (Fin.cast A.src_len (Fin.cast A.src_len.symm i)) = Status.one
      simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using hα
    · refine Or.inr ⟨Fin.cast A.tgt_len.symm j,hj,?_⟩
      change β.status (Fin.cast A.tgt_len (Fin.cast A.tgt_len.symm j)) = Status.zero
      simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using hβ

end CounterFreeHDA.Cubical.Arrow
