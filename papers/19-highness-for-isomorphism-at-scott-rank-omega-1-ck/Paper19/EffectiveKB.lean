import Paper19.KleeneBrouwer
import Paper19.EffectiveRank

namespace Paper19

def Agree (p : Node × Node) (n : ℕ) : Prop :=
  ∀ i < n, p.1.getD i 0 = p.2.getD i 0

theorem agree_cons (a b : ℕ) (x y : Node) (n : ℕ) :
    Agree (a::x,b::y) (n+1) ↔ a=b ∧ Agree (x,y) n := by
  constructor
  · intro h
    exact ⟨by simpa [Agree] using h 0 (by omega),
      fun i hi => by simpa using h (i+1) (by omega)⟩
  · rintro ⟨hab, h⟩ i hi
    cases i with
    | zero => simpa using hab
    | succ i => simpa using h i (by omega)

def KBTest (x y : Node) : Prop :=
  (y.length < x.length ∧ Agree (x,y) y.length) ∨
    ∃ i < min x.length y.length, Agree (x,y) i ∧ x.getD i 0 < y.getD i 0

theorem kbTest_cons (a b : ℕ) (x y : Node) :
    KBTest (a::x) (b::y) ↔ a<b ∨ a=b ∧ KBTest x y := by
  constructor
  · rintro (⟨hlen, hpre⟩ | ⟨i, hi, hpre, hlt⟩)
    · obtain ⟨hab, ht⟩ := (agree_cons a b x y y.length).mp hpre
      exact Or.inr ⟨hab, Or.inl ⟨by simpa using hlen, ht⟩⟩
    · cases i with
      | zero => exact Or.inl (by simpa using hlt)
      | succ i =>
        obtain ⟨hab, ht⟩ := (agree_cons a b x y i).mp hpre
        exact Or.inr ⟨hab, Or.inr ⟨i, by simpa using hi, ht, by simpa using hlt⟩⟩
  · rintro (hlt | ⟨hab, htail⟩)
    · exact Or.inr ⟨0, by simp, by simp [Agree], by simpa using hlt⟩
    · rcases htail with ⟨hlen,hpre⟩ | ⟨i,hi,hpre,hlt⟩
      · exact Or.inl ⟨by simpa using hlen, (agree_cons a b x y y.length).mpr ⟨hab,hpre⟩⟩
      · exact Or.inr ⟨i+1, by simpa using hi, (agree_cons a b x y i).mpr ⟨hab,hpre⟩,
          by simpa using hlt⟩

theorem kbTest_iff (x y : Node) : KBTest x y ↔ KB x y := by
  induction x generalizing y with
  | nil => simp [KBTest,KB]
  | cons a x ih =>
    cases y with
    | nil => simp [KBTest, KB, Agree]
    | cons b y => rw [kbTest_cons, KB, ih]

theorem agree_computable : ComputablePred (fun p : (Node × Node) × ℕ => Agree p.1 p.2) := by
  have hg : PrimrecPred (fun p : ((Node × Node) × ℕ) × ℕ =>
      p.1.1.1.getD p.2 0 = p.1.1.2.getD p.2 0) :=
    Primrec.eq.comp ((Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
      ((Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
  exact hg.computablePred.boundedAll Computable.snd

theorem KB_computable : ComputablePred (fun p : Node × Node => KB p.1 p.2) := by
  have hl : PrimrecPred (fun p : Node × Node => p.2.length < p.1.length) :=
    Primrec.nat_lt.comp (Primrec.list_length.comp Primrec.snd) (Primrec.list_length.comp Primrec.fst)
  have hp := agree_computable.comp' (Computable.id.pair (Computable.list_length.comp Computable.snd))
  have hi : PrimrecPred (fun p : (Node × Node) × ℕ => p.1.1.getD p.2 0 < p.1.2.getD p.2 0) :=
    Primrec.nat_lt.comp ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have hdiff := agree_computable.and' hi.computablePred
  have hf := hdiff.not.boundedAll
    (Primrec.nat_min.comp (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd)).to_comp
  have he : ComputablePred (fun p : Node × Node =>
      ∃ i < min p.1.length p.2.length, Agree p i ∧ p.1.getD i 0 < p.2.getD i 0) :=
    hf.not.of_eq (by simp [and_assoc])
  exact ((hl.computablePred.and' hp).or' he).of_eq (fun p => kbTest_iff p.1 p.2)

end Paper19
