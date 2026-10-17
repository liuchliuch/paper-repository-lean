import Paper19.Infinitary
import Paper19.EffectiveRank

namespace Paper19.Infinitary
open Paper19
open scoped symmDiff

def Term.numeral : ℕ → Term
  | 0 => .zero
  | n + 1 => .succ (numeral n)

@[simp] theorem numeral_eval {T : Tree} (tag : Bool) (e : ℕ → Carrier T) (n : ℕ) :
    (Term.numeral n).eval tag e = Carrier.idx n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [Term.numeral, Term.eval] using congrArg Carrier.succ ih

def Term.lower : ℕ → ℕ → Term → Term
  | 0, _, t => t
  | n + 1, k, t => if k < n + 1 then lower n k (.proj t) else t

theorem lower_eval {T : Tree} (tag : Bool) (e : ℕ → Carrier T)
    {n k : ℕ} {t : Term} {F : Finset Node} (hk : k ≤ n)
    (ht : (t.eval tag e).val = Dom.vec n F) :
    ((Term.lower n k t).eval tag e).val = Dom.vec k (projectTo T n F k) := by
  induction n generalizing t F with
  | zero =>
    have : k = 0 := by omega
    subst k; exact ht
  | succ n ih =>
    by_cases hn : k = n + 1
    · subst k; simpa [Term.lower] using ht
    · have hk' : k < n + 1 := by omega
      simp only [Term.lower, if_pos hk', projectTo]
      have hp : ((Term.proj t).eval tag e).val = Dom.vec n (proj T n F) := by
        change Dom.projD (t.eval tag e).val = _
        rw [ht]; rfl
      simpa [hk'] using ih (by omega) hp

theorem isD_exact {T : Tree} {n : ℕ} {H F : Finset Node}
    (hH : GMem T n H) (y : Dom T) :
    isD (.idx (encIndex n H)) (.vec n F) y ↔ y = .vec n (F ∆ H) := by
  constructor
  · rintro ⟨code, m, m', A, B, K, hk, hx, hy, hmm, hc, hK, hd⟩
    have hcode := Dom.idx.inj hk
    obtain ⟨hn, hA⟩ := Dom.vec.inj hx
    subst m; subst m'; subst A
    have hKH : K = H := (encIndex_injective (hcode.trans hc).symm).2
    subst K
    rw [hy, hd]
  · rintro rfl
    exact ⟨encIndex n H, n, n, F, F ∆ H, H,
      rfl, rfl, rfl, rfl, rfl, hH, rfl⟩

def rootClause (tag : Bool) (N v : ℕ) : Formula :=
  if tag then .rel (Term.numeral (encIndex 0 {[]})) .named (Term.lower N 0 (.var v))
  else .eq (Term.lower N 0 (.var v)) .named

theorem rootClause_realize {T : Tree} (tag : Bool) (e : ℕ → Carrier T)
    {N v : ℕ} {z : Finset Node} (hz : (e v).val = Dom.vec N z) :
    (rootClause tag N v).Realize tag e ↔ projectTo T N z 0 = ∅ := by
  have ht := lower_eval tag e (Nat.zero_le N) (t := Term.var v) hz
  cases tag with
  | false =>
    change ((Term.lower N 0 (.var v)).eval false e) = Carrier.zeroVec 0 ↔ _
    rw [Subtype.ext_iff, ht]
    simp [Carrier.zeroVec, Carrier.vec]
  | true =>
    simp only [rootClause, Bool.true_eq, if_true, Formula.Realize, numeral_eval]
    change isD (.idx (encIndex 0 {[]})) (.vec 0 {[]}) _ ↔ _
    have hH : GMem T 0 ({[]} : Finset Node) := GMem_singleton ⟨(STree T).mem_nil, rfl⟩
    rw [isD_exact hH, ht, symmDiff_self]
    simp [Carrier.zeroVec, Carrier.vec]

def coordinateClause {T : Tree} (N v i : ℕ) (a : Carrier T) : Formula :=
  match a.val with
  | .idx k => .eq (.var i) (Term.numeral k)
  | .vec n F => .rel (Term.numeral (encIndex n F)) (Term.lower N n (.var v)) (.var i)

theorem coordinateClause_realize {T : Tree} (tag : Bool) (e : ℕ → Carrier T)
    {N v i : ℕ} {z : Finset Node} (a : Carrier T) (hN : vectorLevel a ≤ N)
    (hz : (e v).val = Dom.vec N z) :
    (coordinateClause N v i a).Realize tag e ↔ LocalAction T N z a (e i) := by
  rcases a with ⟨a, ha⟩
  cases a with
  | idx k =>
    simp only [coordinateClause, Formula.Realize, Term.eval, numeral_eval, Subtype.ext_iff]
    cases he : (e i).val <;> simp [LocalAction, he, Carrier.idx]
  | vec n F =>
    have hn : n ≤ N := hN
    have ht := lower_eval tag e hn (t := Term.var v) hz
    simp only [coordinateClause, Formula.Realize, numeral_eval]
    change isD (.idx (encIndex n F)) _ (e i).val ↔ _
    rw [ht, isD_exact ha]
    cases he : (e i).val <;> simp [LocalAction, he, symmDiff_comm]

/-- An explicit parameter-free formula in exactly the finite language of
Section 3. Tuple entries appear only through finite numeral codes. -/
noncomputable def orbitFormula {T : Tree} (hT : ComputablePred T.mem)
    (tag : Bool) {m : ℕ} (N : ℕ) (a : Fin m → Carrier T) : Formula := by
  letI : DecidableRel (LocalRel T N) := fun x y => (LocalRel_computable T hT N).choose (x, y)
  exact .ex m (.and (.neg (.index (.var m)))
    (.and (.eq (.level (.var m)) (Term.numeral N))
      (.and (rankFormula (LocalRel T N) none (local_root_accessible T N) m)
        (.and (rootClause tag N m)
          (.all (fun i => if hi : i < m then coordinateClause N m i (a ⟨i, hi⟩) else .top))))))

def tupleEnv {T : Tree} {m : ℕ} (b : Fin m → Carrier T) : ℕ → Carrier T :=
  fun i => if hi : i < m then b ⟨i, hi⟩ else Carrier.idx 0

/-- Full semantic correctness of the explicit infinitary orbit formula. -/
theorem orbitFormula_realize {T : Tree} (hT : ComputablePred T.mem)
    (tag : Bool) {m N : ℕ} (a b : Fin m → Carrier T) (hN : ∀ i, vectorLevel (a i) ≤ N) :
    (orbitFormula hT tag N a).Realize tag (tupleEnv b) ↔ ActualTupleFormula T N a b := by
  letI : DecidableRel (LocalRel T N) := fun x y => (LocalRel_computable T hT N).choose (x, y)
  simp only [orbitFormula, Formula.Realize, Term.eval, numeral_eval, Function.update_self]
  constructor
  · rintro ⟨w, hw, hlev, hrank, hroot, hcoords⟩
    obtain ⟨z, hz⟩ : ∃ z, w.val = Dom.vec N z := by
      cases he : w.val with
      | idx k => exact False.elim (hw (by simp [Carrier.isIdx, he, isIndex]))
      | vec n z =>
        have h := congrArg Subtype.val hlev
        change Dom.levelOf w.val = Dom.idx N at h
        rw [he] at h
        have hn := Dom.idx.inj h
        subst n; exact ⟨z, rfl⟩
    have hg : GMem T N z := by simpa [GoodDom, hz] using w.property
    have henv : (Function.update (tupleEnv b) m w m).val = Dom.vec N z := by simpa using hz
    refine ⟨z, hg, ?_, (rootClause_realize tag _ henv).mp hroot, ?_⟩
    · simpa [localBound, hz] using (rankFormula_realize (LocalRel T N) (local_root_accessible T N) tag m _).mp hrank
    · intro i
      have hh := hcoords i.val
      simp only [dif_pos i.is_lt] at hh
      have hh := (coordinateClause_realize tag _ (a i) (hN i) henv).mp hh
      simpa [tupleEnv, Function.update_of_ne (show i.val ≠ m by omega), i.is_lt] using hh
  · rintro ⟨z, hg, hrank, hroot, hcoords⟩
    let w : Carrier T := Carrier.vec N z hg
    have henv : (Function.update (tupleEnv b) m w m).val = Dom.vec N z := by simp [w, Carrier.vec]
    refine ⟨w, by simp [w, Carrier.isIdx, Carrier.vec, isIndex], rfl, ?_,
      (rootClause_realize tag _ henv).mpr hroot, ?_⟩
    · apply (rankFormula_realize (LocalRel T N) (local_root_accessible T N) tag m _).mpr
      simpa [localBound] using hrank
    · intro i
      by_cases hi : i < m
      · simp only [dif_pos hi]
        apply (coordinateClause_realize tag _ (a ⟨i, hi⟩) (hN ⟨i, hi⟩) henv).mpr
        simpa [tupleEnv, Function.update_of_ne (show i ≠ m by omega), hi] using hcoords ⟨i, hi⟩
      · simp [hi, Formula.Realize]

end Paper19.Infinitary
