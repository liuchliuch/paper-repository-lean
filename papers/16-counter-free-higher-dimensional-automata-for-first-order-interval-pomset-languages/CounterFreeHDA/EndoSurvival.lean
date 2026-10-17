import CounterFreeHDA.Shared

namespace CounterFreeHDA.EndoPom
universe u
variable {Lab : Type u} {U : Interface Lab}

private theorem option_eq_of_some_iff {A : Type} (x y : Option A)
    (h : ∀ a, x = some a ↔ y = some a) : x = y := by
  cases x with
  | none => cases y with
    | none => rfl
    | some b => exact False.elim (by simpa using (h b).mpr rfl)
  | some a => exact ((h a).mp rfl).symm

theorem shared_target_unique (P : EndoPom U) {i j l : Fin U.1}
    (hj : P.Shared i j) (hl : P.Shared i l) : j = l := by
  have h := P.pom.val.tgt_inj (hj.symm.trans hl)
  exact Fin.ext (congrArg (fun x : Fin P.pom.tgtLen => x.val) h)

noncomputable def survivalU (P : EndoPom U) (i : Fin U.1) : Option (Fin U.1) := by
  classical
  exact if h : ∃ j, P.Shared i j then some (Classical.choose h) else none

theorem survivalU_some_iff (P : EndoPom U) (i j : Fin U.1) :
    P.survivalU i = some j ↔ P.Shared i j := by
  classical
  unfold survivalU
  split_ifs with h
  · constructor
    · intro hj
      have hh := Classical.choose_spec h
      rwa [Option.some.inj hj] at hh
    · intro hj
      exact congrArg some (shared_target_unique P (Classical.choose_spec h) hj)
  · constructor
    · intro hn; cases hn
    · intro hj; exact False.elim (h ⟨j,hj⟩)

noncomputable def survivalOrder (P : EndoPom U) : PartialInjectiveOrder U.1 where
  toFun := P.survivalU
  orderPreserving := by
    intro i j a b hij hi hj
    have hi' := (survivalU_some_iff P i a).mp hi
    have hj' := (survivalU_some_iff P j b).mp hj
    have horder := (P.pom.property.src_eord
      (Fin.cast P.src_len.symm i) (Fin.cast P.src_len.symm j)).mpr hij
    change P.pom.eord (P.pom.src (Fin.cast P.src_len.symm i))
      (P.pom.src (Fin.cast P.src_len.symm j)) at horder
    rw [hi',hj'] at horder
    exact (P.pom.property.tgt_eord _ _).mp horder
  partialInjective := by
    intro i j a hi hj
    have hi' := (survivalU_some_iff P i a).mp hi
    have hj' := (survivalU_some_iff P j a).mp hj
    have h := P.pom.val.src_inj (hi'.trans hj'.symm)
    exact Fin.ext (congrArg (fun x : Fin P.pom.srcLen => x.val) h)

theorem survivalU_identity : (identity U).survivalU = PartialMap.pid U.1 := by
  funext i
  exact (survivalU_some_iff (identity U) i i).mpr rfl

theorem survivalU_mul (P Q : EndoPom U) :
    (P.mul Q).survivalU = PartialMap.comp P.survivalU Q.survivalU := by
  funext i
  apply option_eq_of_some_iff
  intro j
  simp only [survivalU_some_iff,shared_mul,PartialMap.comp,PartialMap.bind_eq_some_iff]

theorem survivalU_pow (P : EndoPom U) (n : ℕ) :
    (P.pow n).survivalU = PartialMap.pow P.survivalU n := by
  induction n with
  | zero => exact survivalU_identity
  | succ n ih => rw [pow,survivalU_mul,ih]; rfl

/-- **Lemma 4.1 in full actual-power form.** Shared outer-interface events
of Pⁿ are exactly persistent events at their original positions. -/
theorem lemma_4_1_actual (P : EndoPom U) {k n : ℕ} (hk : U.1 ≤ k) (hn : k ≤ n)
    (i j : Fin U.1) :
    (P.pow n).Shared i j ↔ i = j ∧ P.Shared i i := by
  classical
  rw [← survivalU_some_iff,survivalU_pow]
  have h := CounterFreeHDA.lemma_4_1 P.survivalOrder (le_trans hk hn) i
  change PartialMap.pow P.survivalU n i = _ at h
  have hfix : IsFixed P.survivalOrder.toFun i ↔ P.Shared i i := survivalU_some_iff P i i
  simp only [hfix] at h
  rw [h]
  by_cases hp : P.Shared i i <;> simp [hp]

/-- Compatibility of boundary faces becomes independent of the exponent
once interface survival has stabilised. -/
theorem compatible_pow_iff (P : EndoPom U) {k n : ℕ} (hk : U.1 ≤ k) (hn : k ≤ n)
    {A : Type} [Preorder A] (α β : Fin U.1 → A) :
    (∀ i j, (P.pow n).Shared i j → α i ≤ β j) ↔
      (∀ i, P.Shared i i → α i ≤ β i) := by
  constructor
  · intro h i hi
    exact h i i ((lemma_4_1_actual P hk hn i i).mpr ⟨rfl,hi⟩)
  · intro h i j hij
    obtain ⟨rfl,hi⟩ := (lemma_4_1_actual P hk hn i j).mp hij
    exact h i hi

end CounterFreeHDA.EndoPom
