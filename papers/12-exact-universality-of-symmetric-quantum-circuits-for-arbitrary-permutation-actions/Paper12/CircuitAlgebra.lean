import Paper12.CircuitUnitary
import Paper12.Parallel

noncomputable section
namespace Paper12
open Matrix Classical
open scoped Function
variable {J : Type*} [Fintype J]

def OneQubit.adjoint (g : OneQubit J) : OneQubit J :=
  ⟨g.wire, g.uᴴ, by
    rw [Matrix.conjTranspose_conjTranspose]
    exact Matrix.mul_eq_one_comm.mp g.isUnitary⟩

@[simp] theorem OneQubit.adjoint_unitary (g : OneQubit J) :
    g.adjoint.unitary = g.unitaryᴴ := by
  rw [← tensor_atWire g.adjoint, ← tensor_atWire g, tensorOp_adjoint]
  congr 1
  funext x
  by_cases hx : x = g.wire
  · subst x; simp [OneQubit.adjoint, atWire]
  · simp [OneQubit.adjoint, atWire, hx]

def Gate.adjoint : Gate J → Gate J
  | .one g => .one g.adjoint
  | .thr g => .thr g

@[simp] theorem Gate.adjoint_unitary (g : Gate J) : g.adjoint.unitary = g.unitaryᴴ := by
  cases g with
  | one g => exact g.adjoint_unitary
  | thr g => exact g.adjoint_eq.symm

@[simp] theorem Gate.adjoint_adjoint (g : Gate J) : g.adjoint.adjoint = g := by
  cases g with
  | one g =>
    cases g
    simp [Gate.adjoint, OneQubit.adjoint]
  | thr g => rfl

def Gate.adjointEmbedding : Gate J ↪ Gate J where
  toFun := Gate.adjoint
  inj' := by
    intro a b h
    have hh := congrArg Gate.adjoint h
    simpa using hh

@[simp] theorem Gate.map_adjoint (e : J ≃ J) (g : Gate J) :
    Gate.map e g.adjoint = (Gate.map e g).adjoint := by
  cases g <;> rfl

def adjointPairwise {ι : Type*} (s : Finset ι) (f : ι → Op J)
    (comm : (s : Set ι).Pairwise (Commute on f)) :
    (s : Set ι).Pairwise (Commute on fun x => (f x)ᴴ) := by
  intro a ha b hb hne
  simpa only [Matrix.conjTranspose_mul] using
    (congrArg Matrix.conjTranspose (comm ha hb hne)).symm

theorem noncommProd_adjoint {ι : Type*} (s : Finset ι) (f : ι → Op J)
    (comm : (s : Set ι).Pairwise (Commute on f)) :
    (s.noncommProd f comm)ᴴ =
      s.noncommProd (fun x => (f x)ᴴ) (adjointPairwise s f comm) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha,
      Finset.noncommProd_insert_of_notMem _ _ _ _ ha,
      Matrix.conjTranspose_mul, ih]
    have hcomm : Commute (f a)ᴴ
        (s.noncommProd (fun x => (f x)ᴴ) (adjointPairwise s f
          (comm.mono (by intro x hx; exact Finset.mem_insert_of_mem hx)))) := by
      apply Finset.noncommProd_commute
      intro b hb
      exact adjointPairwise (insert a s) f comm (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem hb) (fun hab => ha (hab ▸ hb))
    exact hcomm.eq.symm

def Layer.adjoint (L : Layer J) : Layer J where
  gates := L.gates.map Gate.adjointEmbedding
  commute := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hb
    simp only [Gate.adjointEmbedding, Function.Embedding.coeFn_mk, Gate.adjoint_unitary]
    simpa only [Matrix.conjTranspose_mul] using
      (congrArg Matrix.conjTranspose (L.commute x hx y hy)).symm

@[simp] theorem Layer.adjoint_unitary (L : Layer J) : L.adjoint.unitary = L.unitaryᴴ := by
  have hL := pairwiseCommute_to_set L.gates L.commute
  have hA := pairwiseCommute_to_set L.adjoint.gates L.adjoint.commute
  rw [Layer.unitary, dif_pos hA, Layer.unitary, dif_pos hL, noncommProd_adjoint]
  have hx : (L.gates : Set (Gate J)).Pairwise (Commute on fun g => g.adjoint.unitary) := by
    simpa only [Gate.adjoint_unitary] using adjointPairwise L.gates Gate.unitary hL
  have hm : L.adjoint.gates.noncommProd Gate.unitary hA =
      L.gates.noncommProd (fun g => g.adjoint.unitary) hx := by
    simp only [Layer.adjoint, Finset.noncommProd, Finset.map_val, Multiset.map_map]
    rfl
  rw [hm]
  exact Finset.noncommProd_congr rfl (fun g _ => g.adjoint_unitary) hx

@[simp] theorem Layer.adjoint_card (L : Layer J) : L.adjoint.gates.card = L.gates.card := by
  simp [Layer.adjoint]

theorem Layer.adjoint_map (e : J ≃ J) (L : Layer J) :
    Layer.map e L.adjoint = (Layer.map e L).adjoint := by
  apply Layer.ext
  simp only [Layer.map, Layer.adjoint, relabelGates, Finset.map_map]
  congr 1
  apply Function.Embedding.ext
  intro g
  exact Gate.map_adjoint e g

def Circuit.mul (C D : Circuit J) : Circuit J := ⟨C.layers ++ D.layers⟩
def Circuit.id : Circuit J := ⟨[]⟩
def Circuit.adjoint (C : Circuit J) : Circuit J := ⟨C.layers.reverse.map Layer.adjoint⟩
def Circuit.power (C : Circuit J) : ℕ → Circuit J
  | 0 => Circuit.id
  | k + 1 => C.mul (C.power k)

@[simp] theorem Circuit.id_unitary : (Circuit.id : Circuit J).unitary = 1 := rfl
@[simp] theorem Circuit.id_size : (Circuit.id : Circuit J).size = 0 := rfl

@[simp] theorem Circuit.mul_unitary (C D : Circuit J) :
    (C.mul D).unitary = C.unitary * D.unitary := by
  have h : ∀ (ls : List (Layer J)),
      ((ls ++ D.layers).map Layer.unitary).foldr (· * ·) 1 =
        (ls.map Layer.unitary).foldr (· * ·) 1 * D.unitary := by
    intro ls
    induction ls with
    | nil => simp [Circuit.unitary]
    | cons L ls ih =>
      simp only [List.cons_append, List.map_cons, List.foldr_cons, ih, Matrix.mul_assoc]
  exact h C.layers

@[simp] theorem Circuit.mul_size (C D : Circuit J) : (C.mul D).size = C.size + D.size := by
  simp [Circuit.mul, Circuit.size]

@[simp] theorem Circuit.adjoint_unitary (C : Circuit J) : C.adjoint.unitary = C.unitaryᴴ := by
  change ((C.layers.reverse.map Layer.adjoint).map Layer.unitary).prod =
    (C.layers.map Layer.unitary).prodᴴ
  rw [Matrix.conjTranspose_list_prod]
  simp only [List.map_map, List.map_reverse, Function.comp_def, Layer.adjoint_unitary]

@[simp] theorem Circuit.adjoint_size (C : Circuit J) : C.adjoint.size = C.size := by
  simp [Circuit.adjoint, Circuit.size, List.map_map, Function.comp_def]

@[simp] theorem Circuit.power_unitary (C : Circuit J) (k : ℕ) : (C.power k).unitary = C.unitary ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [Circuit.power, ih, pow_succ']

@[simp] theorem Circuit.power_size (C : Circuit J) (k : ℕ) : (C.power k).size = k * C.size := by
  induction k with
  | zero => simp [Circuit.power]
  | succ k ih => simp [Circuit.power, ih]; ring

/-- One common lift must preserve every component that is concatenated. -/
def Circuit.Preserved (e : J ≃ J) (C : Circuit J) : Prop :=
  ∀ L ∈ C.layers, Layer.map e L = L

theorem Circuit.preserved_mul {e : J ≃ J} {C D : Circuit J}
    (hC : C.Preserved e) (hD : D.Preserved e) : (C.mul D).Preserved e := by
  intro L hL
  rcases List.mem_append.mp hL with h | h
  · exact hC L h
  · exact hD L h

theorem Circuit.preserved_adjoint {e : J ≃ J} {C : Circuit J}
    (hC : C.Preserved e) : C.adjoint.Preserved e := by
  intro L hL
  obtain ⟨K, hK, rfl⟩ := List.mem_map.mp hL
  rw [Layer.adjoint_map, hC K (List.mem_reverse.mp hK)]

theorem Circuit.preserved_power {e : J ≃ J} {C : Circuit J}
    (hC : C.Preserved e) (k : ℕ) : (C.power k).Preserved e := by
  induction k with
  | zero => intro L hL; simp [Circuit.power, Circuit.id] at hL
  | succ k ih => exact Circuit.preserved_mul hC ih
end Paper12
