import Paper12.Tensor

/-! The actual commuting layer of arbitrary one-qubit rotations, together
with exact tensor semantics and its gate count. -/
noncomputable section
namespace Paper12
open Matrix Complex Classical
open scoped Function
variable {J : Type*} [Fintype J]

def atWirePairwise (m : J → QMat) (s : Finset J) :
    (s : Set J).Pairwise (Commute on fun x => atWire x (m x)) := by
  intro x _ y _ hne
  exact atWire_commute hne (m x) (m y)

theorem atWire_prod (m : J → QMat) (s : Finset J) :
    s.noncommProd (fun x => atWire x (m x)) (atWirePairwise m s) =
      fun y => if y ∈ s then m y else 1 := by
  induction s using Finset.induction_on with
  | empty => ext y; simp
  | @insert x s hx ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hx, ih]
    funext y
    by_cases hy : y = x
    · subst y; simp [atWire, hx]
    · simp [atWire, hy]

def wireGate (m : J → QMat) (hm : ∀ x, (m x)ᴴ * m x = 1) (x : J) : Gate J :=
  .one ⟨x, m x, hm x⟩

def wireGateEmbedding (m : J → QMat) (hm : ∀ x, (m x)ᴴ * m x = 1) : J ↪ Gate J where
  toFun := wireGate m hm
  inj' := by
    intro x y h
    exact congrArg OneQubit.wire (Gate.one.inj h)

def parallelLayer (m : J → QMat) (hm : ∀ x, (m x)ᴴ * m x = 1) : Layer J where
  gates := Finset.univ.map (wireGateEmbedding m hm)
  commute := by
    intro a ha b hb
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hb
    by_cases h : x = y
    · subst y; rfl
    · exact one_qubit_disjoint_commute ⟨x, m x, hm x⟩ ⟨y, m y, hm y⟩ h

@[simp] theorem parallelLayer_card (m : J → QMat) (hm : ∀ x, (m x)ᴴ * m x = 1) :
    (parallelLayer m hm).gates.card = Fintype.card J := by
  simp [parallelLayer]

theorem parallelLayer_unitary (m : J → QMat) (hm : ∀ x, (m x)ᴴ * m x = 1) :
    (parallelLayer m hm).unitary = tensorOp m := by
  let L := parallelLayer m hm
  have hc : (↑L.gates : Set (Gate J)).Pairwise (Commute on Gate.unitary) :=
    pairwiseCommute_to_set _ L.commute
  have hx : ((Finset.univ : Finset J) : Set J).Pairwise (Commute on fun x => (wireGate m hm x).unitary) := by
    intro x _ y _ hne
    exact one_qubit_disjoint_commute ⟨x, m x, hm x⟩ ⟨y, m y, hm y⟩ hne
  change L.unitary = _
  rw [Layer.unitary, dif_pos hc]
  have hmap : L.gates.noncommProd Gate.unitary hc =
      Finset.univ.noncommProd (fun x => (wireGate m hm x).unitary) hx := by
    simp only [L, parallelLayer, Finset.noncommProd, Finset.map_val, Multiset.map_map]
    rfl
  rw [hmap]
  have heq : ∀ x ∈ (Finset.univ : Finset J),
      (wireGate m hm x).unitary = tensorHom (atWire x (m x)) := by
    intro x _
    exact (tensor_atWire ⟨x, m x, hm x⟩).symm
  rw [Finset.noncommProd_congr rfl heq hx]
  rw [← Finset.map_noncommProd _ _ (atWirePairwise m Finset.univ) tensorHom, atWire_prod]
  simp only [Finset.mem_univ, if_true]
  rfl

def parallelCircuit (m : J → QMat) (hm : ∀ x, (m x)ᴴ * m x = 1) : Circuit J :=
  ⟨[parallelLayer m hm]⟩

@[simp] theorem parallelCircuit_unitary (m : J → QMat) (hm : ∀ x, (m x)ᴴ * m x = 1) :
    (parallelCircuit m hm).unitary = tensorOp m := by
  simp [parallelCircuit, Circuit.unitary, parallelLayer_unitary]

@[simp] theorem parallelCircuit_size (m : J → QMat) (hm : ∀ x, (m x)ᴴ * m x = 1) :
    (parallelCircuit m hm).size = Fintype.card J := by
  simp [parallelCircuit, Circuit.size]
theorem wireGate_map (m : J → QMat) (hm : ∀ x, (m x)ᴴ * m x = 1)
    (e : J ≃ J) (hinv : ∀ x, m (e x) = m x) (x : J) :
    Gate.map e (wireGate m hm x) = wireGate m hm (e x) := by
  change Gate.one ⟨e x, m x, hm x⟩ = Gate.one ⟨e x, m (e x), hm (e x)⟩
  congr 1
  have h := hinv x
  congr 1
  exact h.symm

theorem parallelLayer_map (m : J → QMat) (hm : ∀ x, (m x)ᴴ * m x = 1)
    (e : J ≃ J) (hinv : ∀ x, m (e x) = m x) :
    Layer.map e (parallelLayer m hm) = parallelLayer m hm := by
  apply Layer.ext
  ext g
  constructor
  · intro hg
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hg
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp ha
    change Gate.map e (wireGate m hm x) ∈ _
    rw [wireGate_map m hm e hinv]
    exact Finset.mem_map.mpr ⟨e x, Finset.mem_univ _, rfl⟩
  · intro hg
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hg
    refine Finset.mem_map.mpr ⟨wireGate m hm (e.symm y), ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨e.symm y, Finset.mem_univ _, rfl⟩
    · change Gate.map e (wireGate m hm (e.symm y)) = wireGate m hm y
      rw [wireGate_map m hm e hinv, Equiv.apply_symm_apply]

end Paper12
