import Paper37.CachedCoreWork
import Paper37.CachedBitBounds
import Paper37.BoundedLoopFlat

namespace Paper37.CachedCoreProgram
open Paper37.BoundedLoop Paper37.CachedDP Paper37.DP Paper37.ContinuationDP

lemma natArray_size_le {m : ℕ} (a : Vector ℕ m) (B : ℕ)
    (ha : ∀i : Fin m,(a[i.val]).size≤B) :
    (natArray a).representationSize≤m*(B+1)+2 := by
  simp only [natArray,Value.representationSize,List.map_map]
  have hh := list_sum_bound (List.range m)
    (fun i => (Value.nat (if hi : i<m then a[i] else 0)).representationSize) (B+1) (by
      intro i hi
      have hi' := List.mem_range.mp hi
      dsimp only
      rw [dif_pos hi',Value.representationSize]
      exact Nat.add_le_add_right (ha ⟨i,hi'⟩) 1)
  simp only [List.length_range] at hh
  exact Nat.add_le_add_right hh 2

def layerSizeBound (N B : ℕ) : ℕ := (N+1)*((N+1)*(2*B+4)+2)+2

lemma layerValue_size_le {N : ℕ} (old : Layer N) (B : ℕ)
    (ha : ∀k≤N,∀u≤N,(layerAt old k u).1.size≤B ∧ (layerAt old k u).2.size≤B) :
    (layerValue old).representationSize≤layerSizeBound N B := by
  simp only [layerValue,Value.representationSize,List.map_map]
  have ho := list_sum_bound (List.range (N+1))
    (fun k => (Value.array ((List.range (N+1)).map fun u =>
      Value.array [.nat (layerAt old k u).1,.nat (layerAt old k u).2])).representationSize)
    ((N+1)*(2*B+4)+2) (by
      intro k hk
      have hk' : k≤N := by have hh := List.mem_range.mp hk;omega
      simp only [Value.representationSize,List.map_map]
      have hi := list_sum_bound (List.range (N+1))
        (fun u => (Value.array [.nat (layerAt old k u).1,.nat (layerAt old k u).2]).representationSize)
        (2*B+4) (by
          intro u hu
          have hu' : u≤N := by have hh := List.mem_range.mp hu;omega
          have hb := ha k hk' u hu'
          simp only [Value.representationSize,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
          omega)
      simp only [List.length_range] at hi
      exact Nat.add_le_add_right hi 2)
  simp only [List.length_range] at ho
  exact Nat.add_le_add_right ho 2

def sourceWidth (N : ℕ) : ℕ := (4*N+1)*(2*N).size+1

lemma source_layer_size (N : ℕ) (z : List Bool) (A d : ℕ)
    (hN : 0<N) (hz : z.length≤N) (hd : d≤N) :
    (layerValue (cachedRun N (makeObservedCache N z) A d)).representationSize≤
      layerSizeBound N (sourceWidth N) := by
  apply layerValue_size_le
  intro k hk u hu
  have hh := Paper37.CachedBitBounds.cachedRun_binarySize_source N z A d ⟨k,by omega⟩ ⟨u,by omega⟩ hN hd hz
  simp only [layerAt,dif_pos (by omega : k<N+1),dif_pos (by omega : u<N+1)]
  unfold sourceWidth
  exact ⟨by nlinarith [hh.1],hh.2⟩

def chooseSizeBound (N : ℕ) : ℕ := (N+1)*((N+1)*(N+2)+2)+2

lemma source_choose_size (N : ℕ) (z : List Bool) :
    (chooseValue (makeObservedCache N z)).representationSize≤chooseSizeBound N := by
  simp only [chooseValue,Value.representationSize,List.map_map]
  have ho := list_sum_bound (List.range (N+1))
    (fun k => (Value.array ((List.range (N+1)).map fun b =>
      Value.nat (if hk : k<N+1 then chooseAt (makeObservedCache N z) ⟨k,hk⟩ b else 0))).representationSize)
    ((N+1)*(N+2)+2) (by
      intro k hk
      have hk' := List.mem_range.mp hk
      simp only [Value.representationSize,List.map_map]
      have hi := list_sum_bound (List.range (N+1))
        (fun b => (Value.nat (if hk : k<N+1 then chooseAt (makeObservedCache N z) ⟨k,hk⟩ b else 0)).representationSize)
        (N+2) (by
          intro b hb
          have hb' := List.mem_range.mp hb
          dsimp only
          rw [dif_pos hk',makeObservedCache_eq,chooseAt_correct N (observedCounts z) ⟨k,hk'⟩ b (by omega)]
          simp only [Value.representationSize]
          exact Nat.add_le_add_right (choose_binarySize N k b (by omega)) 1)
      simp only [List.length_range] at hi
      exact Nat.add_le_add_right hi 2)
  simp only [List.length_range] at ho
  exact Nat.add_le_add_right ho 2

lemma source_power_size (N : ℕ) (z : List Bool) :
    (powerValue (makeObservedCache N z)).representationSize≤
      (2*N+1)*(2*N*(2*N).size+2)+2 := by
  apply natArray_size_le
  intro i
  simp only [makeObservedCache_eq,makeCache,powerCache_correct]
  exact selfPower_binarySize (2*N) i.val (by omega)

lemma source_observed_size (N : ℕ) (z : List Bool) (hz : z.length≤N) :
    (observedValue (makeObservedCache N z)).representationSize≤(N+1)*(N.size+1)+2 := by
  apply natArray_size_le
  intro i
  simp only [makeObservedCache_eq,makeCache,Vector.getElem_ofFn]
  exact Nat.size_le_size (observedCounts_le_horizon N z hz i.val (by omega))

/-- A single explicit frame bound includes the complete cached arrays, a
materialized layer, and all scalar loop indices. -/
def sourceFrameBound (N : ℕ) : ℕ := layerSizeBound N (sourceWidth N)+chooseSizeBound N+
  ((2*N+1)*(2*N*(2*N).size+2)+2)+((N+1)*(N.size+1)+2)+(N+1)^2+20

lemma sourceFrame_contains (N : ℕ) :
    layerSizeBound N (sourceWidth N)≤sourceFrameBound N ∧
    chooseSizeBound N≤sourceFrameBound N ∧
    (2*N+1)*(2*N*(2*N).size+2)+2≤sourceFrameBound N ∧
    (N+1)*(N.size+1)+2≤sourceFrameBound N ∧
    N.size+1≤sourceFrameBound N ∧ sourceWidth N+1≤sourceFrameBound N ∧ 2≤sourceFrameBound N := by
  have hn : N.size+1≤(N+1)*(N.size+1)+2 := by nlinarith
  have hw : sourceWidth N+1≤layerSizeBound N (sourceWidth N) := by
    have ha : 2*sourceWidth N+4≤(N+1)*(2*sourceWidth N+4) := by
      simpa using Nat.mul_le_mul_right (2*sourceWidth N+4) (show 1≤N+1 by omega)
    have hb : (N+1)*(2*sourceWidth N+4)+2≤(N+1)*((N+1)*(2*sourceWidth N+4)+2) := by
      simpa using Nat.mul_le_mul_right ((N+1)*(2*sourceWidth N+4)+2) (show 1≤N+1 by omega)
    unfold layerSizeBound
    omega
  unfold sourceFrameBound
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  all_goals omega

lemma nat_sourceFrame_le (N m : ℕ) (hm : m≤N) :
    (Value.nat m).representationSize≤sourceFrameBound N := by
  simpa [Value.representationSize] using
    (Nat.add_le_add_right (Nat.size_le_size hm) 1).trans (sourceFrame_contains N).2.2.2.2.1

end Paper37.CachedCoreProgram
