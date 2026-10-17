import CounterFreeHDA.GluingCount

/-! Actual powers, using well-formed interface gluing at every multiplication.
The counting formula and the interior-event consequence of Lemma 4.2 are
proved for these pomsets rather than assumed abstract counting data. -/

namespace CounterFreeHDA
universe u
variable {Lab : Type u}

abbrev Interface (Lab : Type u) := Σ n : ℕ, Fin n → Lab

structure EndoPom (U : Interface Lab) where
  pom : IntervalPom Lab
  source : pom.val.srcType = U
  target : pom.val.tgtType = U

namespace EndoPom
variable {U : Interface Lab}

def identity (U : Interface Lab) : EndoPom U where
  pom := identityPom Lab U.1 U.2
  source := rfl
  target := rfl

noncomputable def mul (P Q : EndoPom U) : EndoPom U where
  pom := glue P.pom Q.pom (GlueMatch.ofType (P.target.trans Q.source.symm))
  source := (glue_srcType _).trans P.source
  target := (glue_tgtType _).trans Q.target

noncomputable def pow (P : EndoPom U) : ℕ → EndoPom U
  | 0 => identity U
  | n + 1 => mul (pow P n) P

theorem src_len (P : EndoPom U) : P.pom.srcLen = U.1 := congrArg Sigma.fst P.source

theorem tgt_len (P : EndoPom U) : P.pom.tgtLen = U.1 := congrArg Sigma.fst P.target

theorem size_ge (P : EndoPom U) : U.1 ≤ P.pom.n := by
  rw [← P.src_len]
  exact srcLen_le P.pom.val

theorem size_mul (P Q : EndoPom U) : (P.mul Q).pom.n + U.1 = P.pom.n + Q.pom.n := by
  have h := glue_card P.pom.val Q.pom.val (GlueMatch.ofType (P.target.trans Q.source.symm))
  change (P.mul Q).pom.n + P.pom.tgtLen = P.pom.n + Q.pom.n at h
  rwa [P.tgt_len] at h

/-- The displayed formula |Pⁿ| = r + n(|P|-r), for actual powers. -/
theorem size_pow (P : EndoPom U) (n : ℕ) :
    (P.pow n).pom.n = U.1 + n * (P.pom.n - U.1) := by
  induction n with
  | zero => change U.1 = U.1 + 0 * (P.pom.n - U.1); omega
  | succ n ih =>
    have h := size_mul (P.pow n) P
    have hp := P.size_ge
    change ((P.pow n).mul P).pom.n = _
    rw [Nat.succ_mul]
    rw [ih] at h
    omega

/-- Lemma 4.2's quantitative bound for actual interface-gluing powers. -/
theorem pow_size_gt_two_interfaces (P : EndoPom U) {k n : ℕ}
    (hk : U.1 ≤ k) (hproper : U.1 < P.pom.n) (hn : k+1 ≤ n) :
    2 * U.1 < (P.pow n).pom.n := by
  rw [size_pow]
  have hd : 1 ≤ P.pom.n - U.1 := by omega
  have hmul : n ≤ n * (P.pom.n - U.1) := by nlinarith
  omega

end EndoPom

theorem exists_interior_of_card (P : PomsetData Lab)
    (h : P.srcLen + P.tgtLen < P.n) :
    ∃ e : Fin P.n, ¬ P.inSrc e ∧ ¬ P.inTgt e := by
  classical
  by_contra hn
  push_neg at hn
  have covered : ∀ e : Fin P.n, P.inSrc e ∨ P.inTgt e := by
    intro e
    by_cases he : P.inSrc e
    · exact Or.inl he
    · exact Or.inr (hn e he)
  let f : Fin P.srcLen ⊕ Fin P.tgtLen → Fin P.n := Sum.elim P.src P.tgt
  have hf : Function.Surjective f := by
    intro e
    rcases covered e with ⟨i,hi⟩ | ⟨j,hj⟩
    · exact ⟨.inl i,hi⟩
    · exact ⟨.inr j,hj⟩
  have hc := Fintype.card_le_of_surjective f hf
  simp only [Fintype.card_fin,Fintype.card_sum] at hc
  omega

/-- **Lemma 4.2**, the actual existence of an event separating the two
boundary cubes of a sufficiently large nontrivial power. -/
theorem lemma_4_2_actual {U : Interface Lab} (P : EndoPom U) {k n : ℕ}
    (hk : U.1 ≤ k) (hproper : U.1 < P.pom.n) (hn : k+1 ≤ n) :
    ∃ e : Fin (P.pow n).pom.n,
      ¬ (P.pow n).pom.val.inSrc e ∧ ¬ (P.pow n).pom.val.inTgt e := by
  apply exists_interior_of_card
  change (P.pow n).pom.srcLen + (P.pow n).pom.tgtLen < (P.pow n).pom.n
  rw [(P.pow n).src_len,(P.pow n).tgt_len]
  have h := P.pow_size_gt_two_interfaces hk hproper hn
  omega

end CounterFreeHDA
