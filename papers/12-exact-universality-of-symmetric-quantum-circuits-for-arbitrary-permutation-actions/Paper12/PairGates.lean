import Paper12.IncidenceSymmetry
import Paper12.PauliChanges

noncomputable section
namespace Paper12
open Matrix Classical
open scoped Function
variable {X : Type*} [Fintype X]

def bitXor (a c : Fin 2) : Fin 2 := if c = 1 then 1 - a else a

theorem bitXor_zero (a : Fin 2) : bitXor a 0 = a := by simp [bitXor]
theorem bitXor_self (a : Fin 2) : bitXor a a = 0 := by fin_cases a <;> decide

def pairAct (s : Finset X) (b : Basis (X ⊕ X)) : Basis (X ⊕ X) :=
  Sum.elim (fun x => if x ∈ s then bitXor (b (Sum.inl x)) (b (Sum.inr x)) else b (Sum.inl x))
    (fun x => b (Sum.inr x))

theorem pairAct_insert (x : X) (s : Finset X) (hx : x ∉ s) (b : Basis (X ⊕ X)) :
    pairAct s ((cnotThreshold x x).act b) = pairAct (insert x s) b := by
  funext z
  cases z with
  | inr y => simp [pairAct, cnot_control]
  | inl y =>
    by_cases hy : y = x
    · subst y
      by_cases hc : b (Sum.inr x) = 1 <;> simp [pairAct, cnot_act, bitXor, hx, hc]
    · by_cases hc : b (Sum.inr x) = 1 <;>
        simp [pairAct, cnot_act, bitXor, hy, hc]

def pairEmbedding : X ↪ Gate (X ⊕ X) where
  toFun x := .thr (cnotThreshold x x)
  inj' := by
    intro x y h
    exact Sum.inl.inj (congrArg Threshold.head (Gate.thr.inj h))

def pairLayer : Layer (X ⊕ X) where
  gates := Finset.univ.map pairEmbedding
  commute := by
    intro a ha b hb
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨y, _, rfl⟩ := Finset.mem_map.mp hb
    exact cnot_unitary_commute x y x y

def pairCNOT : Circuit (X ⊕ X) := ⟨[pairLayer]⟩

theorem pairCNOT_size : (pairCNOT (X := X)).size = Fintype.card X := by
  simp [pairCNOT, Circuit.size, pairLayer]

theorem pair_prod_apply (s : Finset X)
    (hc : (s : Set X).Pairwise (Commute on fun x => (cnotThreshold x x).unitary))
    (ψ : Vec (X ⊕ X)) (b : Basis (X ⊕ X)) :
    applyOp (s.noncommProd (fun x => (cnotThreshold x x).unitary) hc) ψ b = ψ (pairAct s b) := by
  induction s using Finset.induction_on generalizing b with
  | empty =>
    simp only [Finset.noncommProd_empty, applyOp_one]
    congr 1
    funext z
    cases z <;> simp [pairAct]
  | @insert x s hx ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hx, applyOp_mul, Threshold.apply_eq]
    rw [ih, pairAct_insert x s hx]

theorem pairCNOT_apply (ψ : Vec (X ⊕ X)) (b : Basis (X ⊕ X)) :
    applyOp (pairCNOT (X := X)).unitary ψ b = ψ (pairAct Finset.univ b) := by
  have hc : ((Finset.univ : Finset X) : Set X).Pairwise
      (Commute on fun x => (cnotThreshold x x).unitary) :=
    fun x _ y _ _ => cnot_unitary_commute x y x y
  have hu : (pairCNOT (X := X)).unitary =
      Finset.univ.noncommProd (fun x => (cnotThreshold x x).unitary) hc := by
    simp only [pairCNOT, Circuit.unitary, List.map_cons, List.map_nil,
      List.foldr_cons, List.foldr_nil, mul_one, Layer.unitary]
    rw [dif_pos (pairwiseCommute_to_set _ pairLayer.commute)]
    simp only [pairLayer, Finset.noncommProd, Finset.map_val, Multiset.map_map]
    rfl
  rw [hu, pair_prod_apply]

theorem pairCNOT_preserved (γ : X ≃ X) :
    (pairCNOT (X := X)).Preserved (γ.sumCongr γ) := by
  intro L hL
  simp only [pairCNOT, List.mem_singleton] at hL
  subst L
  apply Layer.ext
  ext g
  constructor
  · intro hg
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hg
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp ha
    change Gate.thr ((cnotThreshold x x).map _) ∈ _
    rw [cnot_map]
    exact Finset.mem_map.mpr ⟨γ x, Finset.mem_univ _, rfl⟩
  · intro hg
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hg
    refine Finset.mem_map.mpr ⟨Gate.thr (cnotThreshold (γ.symm x) (γ.symm x)), ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨γ.symm x, Finset.mem_univ _, rfl⟩
    · change Gate.thr ((cnotThreshold (γ.symm x) (γ.symm x)).map _) = _
      rw [cnot_map, Equiv.apply_symm_apply]
      rfl
end Paper12
