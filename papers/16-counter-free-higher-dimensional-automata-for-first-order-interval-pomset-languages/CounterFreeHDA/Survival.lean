import CounterFreeHDA.Pomset
import CounterFreeHDA.Iterate

/-! The actual interface survival map f_P, connected to the proved finite
order-preserving partial-injection theorem (Lemma 4.1). -/

namespace CounterFreeHDA
universe u

variable {Lab : Type u} (P : PomsetData Lab) (endo : IsEndo P)

noncomputable def survivalMap (i : Fin P.srcLen) : Option (Fin P.srcLen) := by
  classical
  exact if h : P.inTgt (P.src i) then
    some (Fin.cast endo.len_eq.symm (Classical.choose h)) else none

/-- The computed partial map records exactly equality of actual source and
target events, with the original ordered interface positions. -/
theorem survivalMap_some_iff (i j : Fin P.srcLen) :
    survivalMap P endo i = some j ↔ P.src i = P.tgt (Fin.cast endo.len_eq j) := by
  classical
  unfold survivalMap
  split_ifs with h
  · constructor
    · intro he
      have hj := Option.some.inj he
      have hcast : Classical.choose h = Fin.cast endo.len_eq j := by
        have hh := congrArg (Fin.cast endo.len_eq) hj
        simpa only [Fin.cast_cast,Fin.cast_refl] using hh
      rw [← hcast]
      exact (Classical.choose_spec h).symm
    · intro he
      have hchosen := P.tgt_inj ((Classical.choose_spec h).trans he)
      apply congrArg some
      rw [hchosen]
      simp
  · constructor
    · intro hn; cases hn
    · intro he
      exact False.elim (h ⟨_,he.symm⟩)

noncomputable def survival (hP : IsIntervalPom P) : PartialInjectiveOrder P.srcLen where
  toFun := survivalMap P endo
  orderPreserving := by
    intro i j a b hij hi hj
    have hi' := (survivalMap_some_iff P endo i a).mp hi
    have hj' := (survivalMap_some_iff P endo j b).mp hj
    have horder := (hP.src_eord i j).mpr hij
    rw [hi',hj',hP.tgt_eord] at horder
    simpa using horder
  partialInjective := by
    intro i j a hi hj
    have hi' := (survivalMap_some_iff P endo i a).mp hi
    have hj' := (survivalMap_some_iff P endo j a).mp hj
    exact P.src_inj (hi'.trans hj'.symm)

/-- **Lemma 4.1**, now for the actual survival map of an interval pomset. -/
theorem lemma_4_1_pomset (hP : IsIntervalPom P) {k n : ℕ}
    (hk : P.srcLen ≤ k) (hn : k ≤ n) :
    ∀ i : Fin P.srcLen, ((survival P endo hP).pow n).toFun i =
      if P.src i = P.tgt (Fin.cast endo.len_eq i) then some i else none := by
  classical
  have h := lemma_4_1 (survival P endo hP) (le_trans hk hn)
  intro i
  have he : IsFixed (survival P endo hP).toFun i ↔
      P.src i = P.tgt (Fin.cast endo.len_eq i) := survivalMap_some_iff P endo i i
  simpa only [he] using h i

end CounterFreeHDA
