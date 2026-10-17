import Paper19.UniformChoice
import Paper19.ComputableEnumeration

namespace Paper19
open UniformOracleComputable

noncomputable def countProgram (p : Stream → ℕ → Bool) (o : Stream) : ℕ → ℕ :=
  Nat.count (fun k => p o k=true)

noncomputable def nthProgram (p : Stream → ℕ → Bool) (o : Stream) : ℕ → ℕ :=
  Nat.nth (fun k => p o k=true)

theorem countProgram_uniform {p : Stream → ℕ → Bool} (hp : UniformOracleComputable p) :
    UniformOracleComputable (countProgram p) := by
  have hp' : UniformOracleComputable (fun o (q : ℕ × (ℕ × ℕ)) => p o q.2.1) := hp.comp (fst.comp snd)
  have hc : UniformOracleComputable (fun o (q : ℕ × (ℕ × ℕ)) => bif p o q.2.1 then (1 : ℕ) else 0) :=
    cond hp' (const 1) (const 0)
  have ha : UniformOracleComputable (fun _ (q : ℕ × ℕ) => q.1+q.2) := base Primrec.nat_add.to_comp
  have hr := UniformOracleComputable.nat_rec id (const 0) (ha.comp ((snd.comp snd).pair hc))
  apply hr.of_eq
  intro o n
  induction n with
  | zero => simp [countProgram,Nat.count]
  | succ n ih =>
    change Nat.rec (motive := fun _ => ℕ) 0
      (fun i s => s + (bif p o i then 1 else 0)) n + (bif p o n then 1 else 0) = _
    change Nat.rec (motive := fun _ => ℕ) 0 (fun i s => s + (bif p o i then 1 else 0)) n = _ at ih
    rw [ih]
    simp [countProgram,Nat.count_succ]

theorem nthProgram_uniform {p : Stream → ℕ → Bool} (hp : UniformOracleComputable p)
    (hInf : ∀ o, Set.Infinite {n | p o n=true}) : UniformOracleComputable (nthProgram p) := by
  have heq : UniformOracleComputable (fun _ (q : ℕ × ℕ) => decide (q.1=q.2)) := base Primrec.eq.decide.to_comp
  have hg := (base Primrec.and.to_comp).comp ((hp.comp snd).pair
    (heq.comp (((countProgram_uniform hp).comp snd).pair fst)))
  apply uniform_of_graph hg
  intro o k n
  simp only [Bool.and_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨hn,hc⟩
    rw [← hc]
    exact Nat.nth_count hn
  · intro he
    change Nat.nth (fun j => p o j=true) k=n at he
    subst n
    exact ⟨Nat.nth_mem_of_infinite (hInf o) k,Nat.count_nth_of_infinite (hInf o) k⟩

end Paper19
