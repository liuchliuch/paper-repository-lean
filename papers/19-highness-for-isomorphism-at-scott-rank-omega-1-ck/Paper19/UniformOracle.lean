import Paper19.Oracle

namespace Paper19

/-- One finite oracle-program derivation, shared by all oracles. In
particular this is stronger than ∀ o, ∃ a program recursive in o. -/
inductive UniformRecursive : (Stream → ℕ →. ℕ) → Prop
  | base (f : ℕ →. ℕ) (hf : Nat.Partrec f) : UniformRecursive (fun _ => f)
  | query : UniformRecursive (fun o n => Part.some (o n))
  | pair {f g} (hf : UniformRecursive f) (hg : UniformRecursive g) :
      UniformRecursive (fun o n => Nat.pair <$> f o n <*> g o n)
  | comp {f g} (hf : UniformRecursive f) (hg : UniformRecursive g) :
      UniformRecursive (fun o n => g o n >>= f o)
  | prec {f g} (hf : UniformRecursive f) (hg : UniformRecursive g) :
      UniformRecursive (fun o p =>
        let (a,n) := Nat.unpair p
        n.rec (f o a) (fun i h => h.bind (fun b => g o (Nat.pair a (Nat.pair i b)))))

  | rfind {f} (hf : UniformRecursive f) :
      UniformRecursive (fun o a => Nat.rfind (fun n => (fun m => m=0) <$> f o (Nat.pair a n)))

theorem UniformRecursive.specialize {f} (h : UniformRecursive f) (o : Stream) :
    RecursiveIn {fun n => Part.some (o n)} (f o) := by
  induction h with
  | base f hf => exact hf.turingReducible
  | query => exact RecursiveIn.oracle _ (by simp)
  | pair _ _ ih₁ ih₂ => exact RecursiveIn.pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact RecursiveIn.comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact RecursiveIn.prec ih₁ ih₂
  | rfind _ ih => exact RecursiveIn.rfind ih

theorem UniformRecursive.substitute {F : Stream → ℕ →. ℕ} (hF : UniformRecursive F)
    {g : Stream → Stream} (hg : UniformRecursive (fun o n => Part.some (g o n))) :
    UniformRecursive (fun o => F (g o)) := by
  induction hF with
  | base f hf => exact UniformRecursive.base f hf
  | query => exact hg
  | pair _ _ ih₁ ih₂ => exact UniformRecursive.pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact UniformRecursive.comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact UniformRecursive.prec ih₁ ih₂
  | rfind _ ih => exact UniformRecursive.rfind ih

def UniformOracleComputable {α β : Type} [Primcodable α] [Primcodable β]
    (f : Stream → α → β) : Prop := UniformRecursive (fun o => encodedFunction (f o))

namespace UniformOracleComputable
variable {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]

theorem specialize {f : Stream → α → β} (h : UniformOracleComputable f) (o : Stream) :
    OracleComputable o (f o) := UniformRecursive.specialize h o

theorem base {f : α → β} (hf : Computable f) : UniformOracleComputable (fun _ => f) := by
  apply UniformRecursive.base
  simpa [encodedFunction, Computable, Partrec] using hf

theorem query : UniformOracleComputable (fun o => o) := by
  unfold UniformOracleComputable
  convert UniformRecursive.query using 1
  funext o n
  simp [encodedFunction]

theorem of_eq {f g : Stream → α → β} (hf : UniformOracleComputable f)
    (he : ∀ o a, f o a = g o a) : UniformOracleComputable g := by
  have : f = g := funext (fun o => funext (he o))
  exact this ▸ hf

theorem comp {f : Stream → β → γ} {g : Stream → α → β}
    (hf : UniformOracleComputable f) (hg : UniformOracleComputable g) :
    UniformOracleComputable (fun o a => f o (g o a)) := by
  unfold UniformOracleComputable
  convert UniformRecursive.comp hf hg using 1
  funext o n
  cases hd : Encodable.decode (α := α) n <;> simp [encodedFunction, hd]

theorem pair {f : Stream → α → β} {g : Stream → α → γ}
    (hf : UniformOracleComputable f) (hg : UniformOracleComputable g) :
    UniformOracleComputable (fun o a => (f o a, g o a)) := by
  unfold UniformOracleComputable
  convert UniformRecursive.pair hf hg using 1
  funext o n
  cases hd : Encodable.decode (α := α) n <;> simp [encodedFunction, hd, Seq.seq]

theorem const (b : β) : UniformOracleComputable (fun _ (_ : α) => b) := base (Computable.const b)
theorem id : UniformOracleComputable (fun _ => @id α) := base Computable.id
theorem fst : UniformOracleComputable (fun _ => @Prod.fst α β) := base Computable.fst
theorem snd : UniformOracleComputable (fun _ => @Prod.snd α β) := base Computable.snd

theorem nat_rec_pair {g : Stream → α → β} {h : Stream → α × (ℕ × β) → β}
    (hg : UniformOracleComputable g) (hh : UniformOracleComputable h) :
    UniformOracleComputable (fun o (p : α × ℕ) =>
      Nat.rec (motive := fun _ => β) (g o p.1) (fun i b => h o (p.1, i, b)) p.2) := by
  unfold UniformOracleComputable
  convert UniformRecursive.prec hg hh using 1
  funext o n
  simp only [encodedFunction]
  generalize ha : (Nat.unpair n).1 = a
  generalize hk : (Nat.unpair n).2 = k
  simp only [Encodable.decode_prod_val, Encodable.decode_nat, ha, hk]
  clear hk ha n
  cases hd : Encodable.decode (α := α) a with
  | none =>
    induction k with
    | zero => simp [encodedFunction, hd]
    | succ k ih =>
      simp [encodedFunction, hd, Encodable.decode_prod_val, Nat.unpair_pair] at ih ⊢
      rw [← ih]; simp
  | some x =>
    induction k with
    | zero => simp [encodedFunction, hd]
    | succ k ih =>
      simp [encodedFunction, hd, Encodable.decode_prod_val, Nat.unpair_pair] at ih ⊢
      rw [← ih]; simp

theorem nat_rec {f : Stream → α → ℕ} {g : Stream → α → β} {h : Stream → α × (ℕ × β) → β}
    (hf : UniformOracleComputable f) (hg : UniformOracleComputable g) (hh : UniformOracleComputable h) :
    UniformOracleComputable (fun o a => Nat.rec (motive := fun _ => β) (g o a)
      (fun i b => h o (a, i, b)) (f o a)) :=
  (nat_rec_pair hg hh).comp (id.pair hf)

theorem cond {c : Stream → α → Bool} {f g : Stream → α → β}
    (hc : UniformOracleComputable c) (hf : UniformOracleComputable f) (hg : UniformOracleComputable g) :
    UniformOracleComputable (fun o a => bif c o a then f o a else g o a) := by
  have hb : Primrec (fun p : Bool × (β × β) => bif p.1 then p.2.1 else p.2.2) :=
    Primrec.cond Primrec.fst (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact (base hb.to_comp).comp (hc.pair (hf.pair hg))

theorem substitute {f : Stream → α → β} {g : Stream → Stream}
    (hf : UniformOracleComputable f) (hg : UniformOracleComputable g) :
    UniformOracleComputable (fun o => f (g o)) := by
  apply UniformRecursive.substitute hf
  unfold UniformOracleComputable at hg
  convert hg using 1
  funext o n
  simp [encodedFunction]

end UniformOracleComputable
end Paper19
