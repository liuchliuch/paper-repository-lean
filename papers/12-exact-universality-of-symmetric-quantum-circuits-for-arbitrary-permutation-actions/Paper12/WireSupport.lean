import Paper12.CircuitExtension
import Paper12.CircuitRewire

noncomputable section
namespace Paper12
open Matrix Classical
open scoped Function
variable {J K : Type*} [Fintype J] [Fintype K]

theorem Gate.onLeft_map (e : J ≃ J) (f : K ≃ K) (g : Gate J) :
    Gate.map (e.sumCongr f) g.onLeft = (Gate.map e g).onLeft := by
  cases g with
  | one g => rfl
  | thr g =>
    simp only [Gate.map, Gate.onLeft, Threshold.onLeft, Threshold.map, Finset.map_map]
    congr 2

theorem Layer.onLeft_map (e : J ≃ J) (f : K ≃ K) (L : Layer J) :
    Layer.map (e.sumCongr f) L.onLeft = (Layer.map e L).onLeft := by
  apply Layer.ext
  simp only [Layer.map, Layer.onLeft, relabelGates, Finset.map_map]
  congr 1
  apply Function.Embedding.ext
  intro g
  exact Gate.onLeft_map e f g

theorem Circuit.preserved_onLeft {e : J ≃ J} (f : K ≃ K) {C : Circuit J}
    (hC : C.Preserved e) : (C.onLeft (K := K)).Preserved (e.sumCongr f) := by
  intro L hL
  obtain ⟨M, hM, rfl⟩ := List.mem_map.mp hL
  rw [Layer.onLeft_map, hC M hM]

def Circuit.onRight (C : Circuit K) : Circuit (J ⊕ K) :=
  (C.onLeft (K := J)).rewire (Equiv.sumComm K J)

theorem registerTensor_swap (A : Op K) (B : Op J) :
    rewireOp (Equiv.sumComm K J) (registerTensor A B) = registerTensor B A := by
  ext i j
  change A (i ∘ Sum.inr) (j ∘ Sum.inr) * B (i ∘ Sum.inl) (j ∘ Sum.inl) = _
  exact mul_comm _ _

theorem Circuit.onRight_unitary (C : Circuit K) :
    (C.onRight (J := J)).unitary = registerTensor 1 C.unitary := by
  rw [Circuit.onRight, Circuit.rewire_unitary, Circuit.onLeft_unitary]
  exact registerTensor_swap _ _

@[simp] theorem Circuit.onRight_size (C : Circuit K) : (C.onRight (J := J)).size = C.size := by
  simp [Circuit.onRight]

theorem Circuit.preserved_onRight (e : J ≃ J) {f : K ≃ K} {C : Circuit K}
    (hC : C.Preserved f) : (C.onRight (J := J)).Preserved (e.sumCongr f) := by
  apply Circuit.preserved_rewire (Equiv.sumComm K J) (Circuit.preserved_onLeft e hC)
  intro x
  cases x <;> rfl

theorem singleCircuit_preserved (e : J ≃ J) (g : Gate J) (hg : Gate.map e g = g) :
    (singleCircuit g).Preserved e := by
  intro L hL
  simp only [singleCircuit, List.mem_singleton] at hL
  subst L
  apply Layer.ext
  simp only [Layer.map, singletonLayer, relabelGates, Finset.map_singleton]
  exact congrArg (fun g : Gate J => ({g} : Finset (Gate J))) hg

def equalityCircuit (g : Threshold J) : Circuit J :=
  (singleCircuit (.thr g)).mul (singleCircuit (.thr (nextThreshold g)))

@[simp] theorem equalityCircuit_size (g : Threshold J) : (equalityCircuit g).size = 2 := by
  simp [equalityCircuit]

theorem equalityCircuit_unitary (g : Threshold J) :
    (equalityCircuit g).unitary =
      (fun i j : Basis J => if equalityAct g j = i then (1 : ℂ) else 0) := by
  simp only [equalityCircuit, Circuit.mul_unitary, singleCircuit_unitary]
  exact equality_unitary_expansion g

theorem equalityCircuit_preserved (e : J ≃ J) (g : Threshold J) (hg : g.map e = g) :
    (equalityCircuit g).Preserved e := by
  apply Circuit.preserved_mul
  · exact singleCircuit_preserved e (.thr g) (congrArg Gate.thr hg)
  · apply singleCircuit_preserved
    change Gate.thr (nextThreshold (g.map e)) = Gate.thr (nextThreshold g)
    rw [hg]
end Paper12
