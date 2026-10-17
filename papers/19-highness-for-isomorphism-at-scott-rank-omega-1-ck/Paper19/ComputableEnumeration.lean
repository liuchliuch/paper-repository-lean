import Paper19.GraphComputable
import Mathlib.Data.Nat.Nth

namespace Paper19

theorem count_computable (p : ℕ → Prop) [DecidablePred p] (hp : ComputablePred p) : Computable (Nat.count p) := by
  classical
  have hstep : Computable₂ (fun (_ : ℕ) (q : ℕ × ℕ) => q.2 + if p q.1 then 1 else 0) :=
    by simpa [Bool.cond_decide] using Computable.to₂ (Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
      (Computable.cond (hp.decide.comp (Computable.fst.comp Computable.snd))
        (Computable.const 1) (Computable.const 0)))
  have hr := Computable.nat_rec Computable.id (Computable.const 0) hstep
  apply hr.of_eq
  intro n
  induction n with
  | zero => simp [Nat.count]
  | succ n ih =>
    change Nat.rec (motive := fun _ => ℕ) 0
      (fun i s => s + if p i then 1 else 0) n + (if p n then 1 else 0) = _
    change Nat.rec (motive := fun _ => ℕ) 0 (fun i s => s + if p i then 1 else 0) n = _ at ih
    rw [ih, Nat.count_succ]

theorem nth_computable (p : ℕ → Prop) [DecidablePred p] (hp : ComputablePred p) (hInf : Set.Infinite {n | p n}) :
    Computable (Nat.nth p) := by
  classical
  have hn := count_computable p hp
  have hg := (hp.comp' (Computable.snd : Computable (fun q : ℕ × ℕ => q.2))).and'
    ((Primrec.eq.decide.to_comp.comp (hn.comp Computable.snd) Computable.fst).computablePred)
  apply computable_of_graph
  apply hg.of_eq
  rintro ⟨k,n⟩
  constructor
  · rintro ⟨hpn,hc⟩
    rw [← hc]
    exact Nat.nth_count hpn
  · intro h
    change Nat.nth p k = n at h
    subst n
    exact ⟨Nat.nth_mem_of_infinite hInf k, Nat.count_nth_of_infinite hInf k⟩

/-- Effective increasing enumeration and effective inverse for an infinite
computable subset of Nat. This supplies the source's recoding onto ω. -/
theorem computable_enumeration (p : ℕ → Prop) [DecidablePred p] (hp : ComputablePred p)
    (hInf : Set.Infinite {n | p n}) :
    ∃ e r : ℕ → ℕ, Computable e ∧ Computable r ∧
      (∀ n, p (e n)) ∧ (∀ n, r (e n) = n) ∧ (∀ k, p k → e (r k) = k) := by
  exact ⟨Nat.nth p, Nat.count p, nth_computable p hp hInf, count_computable p hp,
    Nat.nth_mem_of_infinite hInf, Nat.count_nth_of_infinite hInf,
    fun k hk => Nat.nth_count hk⟩

end Paper19
