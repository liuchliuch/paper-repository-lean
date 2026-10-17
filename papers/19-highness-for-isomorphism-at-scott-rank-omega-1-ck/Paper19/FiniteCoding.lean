import Paper19.OracleCoding
import Paper19.GraphComputable

namespace Paper19.FiniteCoding
open Paper19 Encodable Denumerable

def shift (n : ℕ) (l : List ℕ) : List ℕ := l.map (fun a => a + n)

theorem shift_primrec : Primrec₂ shift :=
  Primrec.list_map Primrec.snd (Primrec.to₂ (Primrec.nat_add.comp Primrec.snd (Primrec.fst.comp Primrec.fst)))

def raiseZero : List ℕ → List ℕ :=
  List.rec [] (fun a _ ih => a :: shift (a + 1) ih)

theorem raiseZero_primrec : Primrec raiseZero :=
  Primrec.list_rec Primrec.id (Primrec.const []) (Primrec.to₂
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
      (shift_primrec.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

theorem raise_offset (l : List ℕ) (n : ℕ) :
    Denumerable.raise' l n = shift n (Denumerable.raise' l 0) := by
  induction l generalizing n with
  | nil => rfl
  | cons a l ih =>
    simp only [Denumerable.raise', Nat.add_zero, shift, List.map_cons]
    rw [ih (a + n + 1), ih (a + 1)]
    simp [shift, List.map_map, Function.comp_def, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem raiseZero_eq (l : List ℕ) : raiseZero l = Denumerable.raise' l 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change a :: shift (a + 1) (raiseZero l) = _
    rw [ih, ← raise_offset]
    simp [Denumerable.raise']

theorem raise_primrec : Primrec₂ Denumerable.raise' := by
  have h := shift_primrec.comp Primrec.snd (raiseZero_primrec.comp Primrec.fst)
  exact h.to₂.of_eq (fun l n => by rw [raiseZero_eq, ← raise_offset])

/-- Canonical finite enumeration in the standard Denumerable Finset encoding. -/
def nodes (F : Finset Node) : List Node :=
  (Denumerable.raise' (Denumerable.ofNat (List ℕ) (@Encodable.encode (Finset Node) (Primcodable.toEncodable) F)) 0).map
    (Denumerable.ofNat Node)

theorem nodes_primrec : Primrec nodes :=
  Primrec.list_map (raise_primrec.comp ((Primrec.ofNat (List ℕ)).comp Primrec.encode) (Primrec.const 0))
    (Primrec.to₂ ((Primrec.ofNat Node).comp Primrec.snd))

theorem nodes_toFinset (F : Finset Node) : (nodes F).toFinset = F := by
  have hn (n : ℕ) :
      ((Denumerable.raise' (Denumerable.ofNat (List ℕ) n) 0).map
        (Denumerable.ofNat Node)).toFinset = Denumerable.ofNat (Finset Node) n := by
    change _ = Finset.map (Denumerable.eqv Node).symm.toEmbedding
      (Denumerable.raise'Finset (Denumerable.ofNat (List ℕ) n) 0)
    ext σ
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_map]
    rfl
  exact (hn _).trans (Denumerable.ofNat_encode F)

@[simp] theorem mem_nodes (F : Finset Node) (σ : Node) : σ ∈ nodes F ↔ σ ∈ F := by
  rw [← List.mem_toFinset, nodes_toFinset]

theorem list_mem_primrec : PrimrecRel (fun x : Node => fun l : List Node => x ∈ l) :=
  ((Primrec.eq : PrimrecRel (Eq : Node → Node → Prop)).exists_mem_list.of_eq (by simp)).swap

theorem list_toFinset_computable : Computable (fun l : List Node => l.toFinset) := by
  apply computable_of_graph
  have hleft := list_mem_primrec.forall_mem_list.comp Primrec.fst (nodes_primrec.comp Primrec.snd)
  have hright := list_mem_primrec.forall_mem_list.comp (nodes_primrec.comp Primrec.snd) Primrec.fst
  apply (hleft.and hright).computablePred.of_eq
  rintro ⟨l, F⟩
  simp only [mem_nodes]
  rw [Finset.ext_iff]
  simp only [List.mem_toFinset]
  constructor
  · rintro ⟨hL, hF⟩ σ
    exact ⟨hL σ, hF σ⟩
  · intro h
    exact ⟨fun σ hσ => (h σ).mp hσ, fun σ hσ => (h σ).mpr hσ⟩

end Paper19.FiniteCoding
