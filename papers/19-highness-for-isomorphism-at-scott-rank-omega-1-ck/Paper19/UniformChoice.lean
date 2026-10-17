import Paper19.UniformOracle

namespace Paper19
open UniformOracleComputable

/-- Uniform search of a computable graph; the result family is not assumed
computable, and its uniform program is derived from the Boolean graph. -/
theorem uniform_of_graph {p : Stream → ℕ × ℕ → Bool} {f : Stream → ℕ → ℕ}
    (hp : UniformOracleComputable p) (hspec : ∀ o a n, p o (a,n)=true ↔ f o a=n) :
    UniformOracleComputable f := by
  let q := fun o (v : ℕ × ℕ) => if p o v then (0 : ℕ) else 1
  have hq : UniformOracleComputable q :=
    (base (Primrec.dom_bool (fun b => if b then (0 : ℕ) else 1)).to_comp).comp hp
  unfold UniformOracleComputable
  convert UniformRecursive.rfind hq using 1
  funext o a
  have ht : (fun n => (fun m => decide (m=0)) <$> encodedFunction (q o) (Nat.pair a n)) =
      (fun n => Part.some (p o (a,n))) := by
    funext n
    simp [encodedFunction,q,Encodable.decode_prod_val,Nat.unpair_pair]
  rw [show encodedFunction (f o) a = Part.some (f o a) by simp [encodedFunction]]
  rw [ht]
  apply Part.ext
  intro n
  rw [Nat.mem_rfind]
  constructor
  · intro hn
    have he : f o a=n := by simpa [eq_comm] using hn
    refine ⟨by simpa using (hspec o a n).mpr he,?_⟩
    intro m hm
    have hf : p o (a,m)=false := Bool.eq_false_of_not_eq_true (fun hp' => by
      have he' := (hspec o a m).mp hp'
      omega)
    simp [hf]
  · rintro ⟨hn,_⟩
    have hh : p o (a,n)=true := by simpa using hn
    simpa [eq_comm] using (hspec o a n).mp hh

/-- Bounded oracle conjunction, with an oracle-computable bound. -/
def foldAll {α : Type} (p : Stream → α × ℕ → Bool) (b : Stream → α → ℕ) (o : Stream) (a : α) : Bool :=
  Nat.rec true (fun i s => s && p o (a,i)) (b o a)

theorem foldAll_uniform {α : Type} [Primcodable α] {p : Stream → α × ℕ → Bool}
    {b : Stream → α → ℕ} (hp : UniformOracleComputable p) (hb : UniformOracleComputable b) :
    UniformOracleComputable (foldAll p b) := by
  have hc : UniformOracleComputable (fun o (q : α × (ℕ × Bool)) => p o (q.1,q.2.1)) :=
    hp.comp (fst.pair (fst.comp snd))
  have hand : UniformOracleComputable (fun _ (q : Bool × Bool) => q.1 && q.2) := base Primrec.and.to_comp
  exact UniformOracleComputable.nat_rec hb (const true) (hand.comp ((snd.comp snd).pair hc))

theorem foldAll_true {α : Type} (p : Stream → α × ℕ → Bool) (b : Stream → α → ℕ) (o : Stream) (a : α) :
    foldAll p b o a=true ↔ ∀ i<b o a, p o (a,i)=true := by
  unfold foldAll
  induction b o a with
  | zero => simp
  | succ n ih => simp [ih,Nat.forall_lt_succ_right]

def listAllProgram {α β : Type} (d : β) (l : α → List β) (p : Stream → α × β → Bool) : Stream → α → Bool :=
  foldAll (fun o q => p o (q.1,(l q.1).getD q.2 d)) (fun _ a => (l a).length)

theorem listAllProgram_uniform {α β : Type} [Primcodable α] [Primcodable β]
    (d : β) {l : α → List β} (hl : Computable l) {p : Stream → α × β → Bool}
    (hp : UniformOracleComputable p) : UniformOracleComputable (listAllProgram d l p) := by
  have hi : Computable (fun q : α × ℕ => (q.1,(l q.1).getD q.2 d)) :=
    Computable.fst.pair ((Primrec.list_getD d).to_comp.comp (hl.comp Computable.fst) Computable.snd)
  exact foldAll_uniform (hp.comp (base hi)) (base (Computable.list_length.comp hl))

theorem listAllProgram_true {α β : Type} (d : β) (l : α → List β) (p : Stream → α × β → Bool)
    (o : Stream) (a : α) :
    listAllProgram d l p o a=true ↔ ∀ x∈l a, p o (a,x)=true := by
  rw [listAllProgram,foldAll_true,List.forall_mem_iff_getElem]
  constructor <;> intro h i hi <;> simpa only [List.getD_eq_getElem _ d hi] using h i hi

end Paper19
