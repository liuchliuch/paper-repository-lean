import Paper37.CachedValueSize
import Paper37.RefinedCoreWork

namespace Paper37.RefinedCoreProgram
open Paper37.BoundedLoop Paper37.CachedDP Paper37.DP Paper37.ContinuationDP
open Paper37.RefinedContinuation Paper37.CachedRefinedDP Paper37.AdaptiveDP
open Paper37.CachedCoreProgram (chooseValue powerValue observedValue sourceWidth source_choose_size
  source_power_size source_observed_size)

def layerSizeBound (N B : ℕ) : ℕ := (N+1)*((N+1)*((N+1)*(2*B+4)+2)+2)+2

lemma layerValue_size_le {N : ℕ} (old : RefinedLayer N) (B : ℕ)
    (ha:∀k≤N,∀u≤N,∀j≤N,(refinedLayerAt old k u j).1.size≤B ∧
      (refinedLayerAt old k u j).2.size≤B) :
    (layerValue old).representationSize≤layerSizeBound N B := by
  simp only [layerValue,Value.representationSize,List.map_map]
  have ho:=Paper37.CachedCoreProgram.list_sum_bound (List.range (N+1))
    (fun k=>(Value.array ((List.range (N+1)).map fun u=>
      Value.array ((List.range (N+1)).map fun j=>
        Value.array [.nat (refinedLayerAt old k u j).1,.nat (refinedLayerAt old k u j).2]))).representationSize)
    ((N+1)*((N+1)*(2*B+4)+2)+2) (by
      intro k hk
      have hk':k≤N := by have hh:=List.mem_range.mp hk;omega
      simp only [Value.representationSize,List.map_map]
      have hu:=Paper37.CachedCoreProgram.list_sum_bound (List.range (N+1))
        (fun u=>(Value.array ((List.range (N+1)).map fun j=>
          Value.array [.nat (refinedLayerAt old k u j).1,.nat (refinedLayerAt old k u j).2])).representationSize)
        ((N+1)*(2*B+4)+2) (by
          intro u hu
          have hu':u≤N := by have hh:=List.mem_range.mp hu;omega
          simp only [Value.representationSize,List.map_map]
          have hj:=Paper37.CachedCoreProgram.list_sum_bound (List.range (N+1))
            (fun j=>(Value.array [.nat (refinedLayerAt old k u j).1,.nat (refinedLayerAt old k u j).2]).representationSize)
            (2*B+4) (by
              intro j hj
              have hj':j≤N := by have hh:=List.mem_range.mp hj;omega
              have hb:=ha k hk' u hu' j hj'
              simp only [Value.representationSize,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
              omega)
          simp only [List.length_range] at hj
          exact Nat.add_le_add_right hj 2)
      simp only [List.length_range] at hu
      exact Nat.add_le_add_right hu 2)
  simp only [List.length_range] at ho
  exact Nat.add_le_add_right ho 2

lemma source_layer_size (N : ℕ) (z : List Bool) (A d : ℕ)
    (hN:0<N) (hz:z.length≤N) (hd:d≤N) :
    (layerValue (cachedRefinedRun N (makeObservedCache N z) A d)).representationSize≤
      layerSizeBound N (sourceWidth N) := by
  apply layerValue_size_le
  intro k hk u hu j hj
  have hh:=Paper37.CachedQueries.cachedRefined_binarySize N z A d
    ⟨k,by omega⟩ ⟨u,by omega⟩ ⟨j,by omega⟩ hN hd hz
  simp only [refinedLayerAt,dif_pos (by omega:k<N+1),dif_pos (by omega:u<N+1),dif_pos (by omega:j<N+1)]
  unfold Paper37.CachedCoreProgram.sourceWidth
  exact ⟨by nlinarith [hh.1],by nlinarith [hh.2]⟩

def sourceFrameBound (N : ℕ) : ℕ := layerSizeBound N (sourceWidth N)+Paper37.CachedCoreProgram.sourceFrameBound N

lemma sourceFrame_contains (N : ℕ) :
    layerSizeBound N (sourceWidth N)≤sourceFrameBound N ∧
    Paper37.CachedCoreProgram.chooseSizeBound N≤sourceFrameBound N ∧
    (2*N+1)*(2*N*(2*N).size+2)+2≤sourceFrameBound N ∧
    (N+1)*(N.size+1)+2≤sourceFrameBound N ∧
    N.size+1≤sourceFrameBound N ∧ sourceWidth N+1≤sourceFrameBound N ∧ 2≤sourceFrameBound N := by
  have hh:=Paper37.CachedCoreProgram.sourceFrame_contains N
  unfold sourceFrameBound
  omega

lemma nat_sourceFrame_le (N m : ℕ) (hm:m≤N) :
    (Value.nat m).representationSize≤sourceFrameBound N := by
  simpa [Value.representationSize] using
    (Nat.add_le_add_right (Nat.size_le_size hm) 1).trans (sourceFrame_contains N).2.2.2.2.1

end Paper37.RefinedCoreProgram
