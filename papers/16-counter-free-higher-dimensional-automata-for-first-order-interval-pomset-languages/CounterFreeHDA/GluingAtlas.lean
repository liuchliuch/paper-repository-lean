import CounterFreeHDA.GluingDeletion

namespace CounterFreeHDA
universe u v

/-- Ordered enumerations of the same actual interface agree at every position. -/
theorem ordered_enumerations_eq {E : Type u} {r s : ℕ} (R : E → E → Prop)
    (a : Fin r → E) (b : Fin s → E) (ha : Function.Injective a) (hb : Function.Injective b)
    (hoa : ∀ i j, R (a i) (a j) ↔ i < j) (hob : ∀ i j, R (b i) (b j) ↔ i < j)
    (hr : Set.range a = Set.range b) (i : Fin r) (j : Fin s) (hij : i.val = j.val) : a i = b j := by
  let e := enumerationEquiv a b ha hb hr
  have he : ∀ i, b (e i) = a i := enumerationEquiv_event _ _ _ _ _
  have hm : StrictMono e := by
    intro i j hij
    apply (hob _ _).mp
    rw [he,he]
    exact (hoa _ _).mpr hij
  exact (he i).symm.trans (congrArg b (Fin.ext ((increasingEquiv_val e hm i).trans hij)))

variable {Lab : Type u} {A B P : PomsetData Lab}

/-- Event-level gluing data with actual interface image sets. Ordered positions
are recovered from those sets, so no seam permutation is an extra assumption. -/
structure GluingAtlas (A B P : PomsetData Lab) where
  left : Fin A.n ↪ Fin P.n
  right : Fin B.n ↪ Fin P.n
  left_lab : ∀ e, P.lab (left e) = A.lab e
  right_lab : ∀ e, P.lab (right e) = B.lab e
  left_prec : ∀ e f, P.prec (left e) (left f) ↔ A.prec e f
  right_prec : ∀ e f, P.prec (right e) (right f) ↔ B.prec e f
  left_eord : ∀ e f, P.eord (left e) (left f) ↔ A.eord e f
  right_eord : ∀ e f, P.eord (right e) (right f) ↔ B.eord e f
  seam_range : Set.range (left ∘ A.tgt) = Set.range (right ∘ B.src)
  overlap : ∀ e f, left e = right f → A.inTgt e ∧ B.inSrc f
  cover : ∀ e, (∃ a, left a = e) ∨ (∃ b, right b = e)
  cross : ∀ e f, ¬ A.inTgt e → ¬ B.inSrc f → P.prec (left e) (right f)
  source_range : Set.range (left ∘ A.src) = Set.range P.src
  target_range : Set.range (right ∘ B.tgt) = Set.range P.tgt

namespace GluingRealization
variable {m : GlueMatch A B} (R : GluingRealization m P)

def atlas : GluingAtlas A B P where
  left := R.left
  right := R.right
  left_lab := R.left_lab
  right_lab := R.right_lab
  left_prec := R.left_prec
  right_prec := R.right_prec
  left_eord := R.left_eord
  right_eord := R.right_eord
  seam_range := by
    ext e
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨Fin.cast m.len_eq i,(R.seam i).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨Fin.cast m.len_eq.symm i,(R.seam _).trans (congrArg (fun j => R.right (B.src j)) (Fin.ext rfl))⟩
  overlap := by
    intro e f hef
    obtain ⟨i,hi,hj⟩ := R.overlap e f hef
    exact ⟨⟨i,hi⟩,⟨_,hj⟩⟩
  cover := R.cover
  cross := R.cross
  source_range := by
    ext e
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨Fin.cast R.source_len i,(R.source i).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨Fin.cast R.source_len.symm i,(R.source _).trans (congrArg P.src (Fin.ext rfl))⟩
  target_range := by
    ext e
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨Fin.cast R.target_len i,(R.target i).symm⟩
    · rintro ⟨i,rfl⟩
      exact ⟨Fin.cast R.target_len.symm i,(R.target _).trans (congrArg P.tgt (Fin.ext rfl))⟩

end GluingRealization

namespace GluingAtlas
variable (R : GluingAtlas A B P) (hA : IsIntervalPom A) (hB : IsIntervalPom B) (hP : IsIntervalPom P)

noncomputable def matching : GlueMatch A B := by
  let e := enumerationEquiv (R.left ∘ A.tgt) (R.right ∘ B.src)
    (R.left.injective.comp A.tgt_inj) (R.right.injective.comp B.src_inj) R.seam_range
  have hn : A.tgtLen = B.srcLen := by simpa only [Fintype.card_fin] using Fintype.card_congr e
  refine ⟨hn,fun i => ?_⟩
  have he := ordered_enumerations_eq P.eord (R.left ∘ A.tgt) (R.right ∘ B.src)
    (R.left.injective.comp A.tgt_inj) (R.right.injective.comp B.src_inj)
    (fun i j => (R.left_eord _ _).trans (hA.tgt_eord i j))
    (fun i j => (R.right_eord _ _).trans (hB.src_eord i j)) R.seam_range i (Fin.cast hn i) rfl
  exact (R.left_lab _).symm.trans ((congrArg P.lab he).trans (R.right_lab _))

noncomputable def realization : GluingRealization (R.matching hA hB) P := by
  let m := R.matching hA hB
  have hs : A.srcLen = P.srcLen := by
    let e := enumerationEquiv (R.left ∘ A.src) P.src (R.left.injective.comp A.src_inj) P.src_inj R.source_range
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  have ht : B.tgtLen = P.tgtLen := by
    let e := enumerationEquiv (R.right ∘ B.tgt) P.tgt (R.right.injective.comp B.tgt_inj) P.tgt_inj R.target_range
    simpa only [Fintype.card_fin] using Fintype.card_congr e
  have hseam : ∀ i, R.left (A.tgt i) = R.right (B.src (Fin.cast m.len_eq i)) := fun i =>
    ordered_enumerations_eq P.eord _ _ (R.left.injective.comp A.tgt_inj) (R.right.injective.comp B.src_inj)
      (fun i j => (R.left_eord _ _).trans (hA.tgt_eord i j))
      (fun i j => (R.right_eord _ _).trans (hB.src_eord i j)) R.seam_range i _ rfl
  exact {
    left := R.left,right := R.right,left_lab := R.left_lab,right_lab := R.right_lab
    left_prec := R.left_prec,right_prec := R.right_prec,left_eord := R.left_eord,right_eord := R.right_eord
    seam := hseam
    overlap := by
      intro e f hef
      obtain ⟨⟨i,hi⟩,_⟩ := R.overlap e f hef
      exact ⟨i,hi,R.right.injective ((hseam i).symm.trans ((congrArg R.left hi).trans hef))⟩
    cover := R.cover,cross := R.cross,source_len := hs,target_len := ht
    source := fun i => ordered_enumerations_eq P.eord _ _ (R.left.injective.comp A.src_inj) P.src_inj
      (fun i j => (R.left_eord _ _).trans (hA.src_eord i j)) hP.src_eord R.source_range i _ rfl
    target := fun i => ordered_enumerations_eq P.eord _ _ (R.right.injective.comp B.tgt_inj) P.tgt_inj
      (fun i j => (R.right_eord _ _).trans (hB.tgt_eord i j)) hP.tgt_eord R.target_range i _ rfl }

noncomputable def iso : PomsetIso (glueData A B (R.matching hA hB)) P :=
  (R.realization hA hB hP).iso hA hB hP

end GluingAtlas
end CounterFreeHDA
