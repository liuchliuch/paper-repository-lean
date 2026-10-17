import Paper19.EffectiveRank
import Mathlib.Computability.TuringDegree

namespace Paper19
open Encodable

def encodedFunction {α β : Type} [Primcodable α] [Primcodable β] (f : α → β) : ℕ →. ℕ :=
  fun n => Part.bind (decode (α := α) n) (fun a => Part.some (encode (f a)))

def OracleComputable (o : Stream) {α β : Type} [Primcodable α] [Primcodable β]
    (f : α → β) : Prop := RecursiveIn {fun n => Part.some (o n)} (encodedFunction f)

namespace OracleComputable
variable {o : Stream} {α β γ δ : Type}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ]

theorem of_computable {f : α → β} (h : Computable f) : OracleComputable o f := by
  apply Nat.Partrec.turingReducible
  simpa [encodedFunction, Computable, Partrec] using h

theorem oracle : OracleComputable o o := by
  have h : RecursiveIn {fun n => Part.some (o n)} (fun n => Part.some (o n)) :=
    RecursiveIn.oracle _ (by simp)
  unfold OracleComputable
  convert h using 1
  funext n
  simp [encodedFunction]

theorem of_eq {f g : α → β} (h : OracleComputable o f) (he : ∀ a, f a = g a) :
    OracleComputable o g := (funext he : f = g) ▸ h

theorem comp {f : β → γ} {g : α → β} (hf : OracleComputable o f) (hg : OracleComputable o g) :
    OracleComputable o (fun a => f (g a)) := by
  have h := RecursiveIn.comp hf hg
  unfold OracleComputable
  convert h using 1
  funext n
  cases hd : decode (α := α) n <;> simp [encodedFunction, hd, Part.bind_assoc]

theorem pair {f : α → β} {g : α → γ} (hf : OracleComputable o f) (hg : OracleComputable o g) :
    OracleComputable o (fun a => (f a, g a)) := by
  have h := RecursiveIn.pair hf hg
  unfold OracleComputable
  convert h using 1
  funext n
  cases hd : decode (α := α) n <;> simp [encodedFunction, hd, Seq.seq]

theorem const (b : β) : OracleComputable o (fun _ : α => b) :=
  of_computable (Computable.const b)

theorem id : OracleComputable o (@id α) := of_computable Computable.id

theorem fst : OracleComputable o (@Prod.fst α β) := of_computable Computable.fst
theorem snd : OracleComputable o (@Prod.snd α β) := of_computable Computable.snd

theorem nat_rec_pair {g : α → β} {h : α × (ℕ × β) → β}
    (hg : OracleComputable o g) (hh : OracleComputable o h) :
    OracleComputable o (fun p : α × ℕ =>
      Nat.rec (motive := fun _ => β) (g p.1) (fun i b => h (p.1, i, b)) p.2) := by
  have hr := RecursiveIn.prec hg hh
  unfold OracleComputable
  convert hr using 1
  funext n
  simp only [encodedFunction]
  generalize ha : (Nat.unpair n).1 = a
  generalize hk : (Nat.unpair n).2 = k
  simp only [decode_prod_val, decode_nat, ha, hk]
  clear hk ha n
  cases hd : decode (α := α) a with
  | none =>
    induction k with
    | zero => simp [encodedFunction, hd]
    | succ k ih =>
      simp [encodedFunction, hd, decode_prod_val, Nat.unpair_pair] at ih ⊢
      rw [← ih]
      simp
  | some x =>
    induction k with
    | zero => simp [encodedFunction, hd]
    | succ k ih =>
      simp [encodedFunction, hd, decode_prod_val, Nat.unpair_pair] at ih ⊢
      rw [← ih]
      simp

theorem nat_rec {f : α → ℕ} {g : α → β} {h : α × (ℕ × β) → β}
    (hf : OracleComputable o f) (hg : OracleComputable o g) (hh : OracleComputable o h) :
    OracleComputable o (fun a => Nat.rec (motive := fun _ => β) (g a)
      (fun i b => h (a, i, b)) (f a)) :=
  (nat_rec_pair hg hh).comp (id.pair hf)

end OracleComputable
end Paper19
