import Paper37.AdaptiveQueryProgram
import Paper37.PredictorBatchPeak
import Paper37.CachedValueSize

namespace Paper37.AdaptiveMixPeak
open Finset Paper37.BoundedLoop Paper37.AdaptiveQueryProgram Paper37.AdaptiveIntegerOutput
open Paper37.WordProgram Paper37.CachedCoreProgram Paper37.IntegerOutput
open Paper37.PredictorBatchPeak (pairValue_size bind_peak_le)
set_option maxRecDepth 3000

def frame (N B : ℕ) : ℕ := (N+1)*(B+N+10)
def componentWidth (N B : ℕ) : ℕ := B+5*(N+1)+4

lemma weightWidth_le (N : ℕ) : weightBitBound N≤4*(N+1)+1 := by
  have hh := Paper37.DP.binarySize_le_self (2*(N+1))
  unfold weightBitBound
  omega

lemma component_size (N t B : ℕ) (masses norms : Vector ℕ (N+1))
    (hN : 0<N) (ht : t<N)
    (hm : ∀i : Fin (N+1),(masses[i.val]).size≤B)
    (hn : ∀i : Fin (N+1),(norms[i.val]).size≤B) :
    pairSize ((weightPair N (t+1)).1*lookupNumerator masses (t+1),
      (weightPair N (t+1)).2*(N+1)*lookupNumerator norms (t+1))≤componentWidth N B := by
  have hw := weightPair_binarySize N (t+1) hN (by omega)
  have hw1 := (le_max_left _ _).trans hw
  have hw2 := (le_max_right _ _).trans hw
  have hm' := hm ⟨min (t+1) N,by have hh := min_le_right (t+1) N;omega⟩
  have hn' := hn ⟨min (t+1) N,by have hh := min_le_right (t+1) N;omega⟩
  have hp1 := size_mul_le (weightPair N (t+1)).1 (lookupNumerator masses (t+1))
  have hp2 := size_mul_le (weightPair N (t+1)).2 (N+1)
  have hp3 := size_mul_le ((weightPair N (t+1)).2*(N+1)) (lookupNumerator norms (t+1))
  have hns := Paper37.DP.binarySize_le_self (N+1)
  have hws := weightWidth_le N
  unfold pairSize componentWidth
  dsimp only
  simp only [lookupNumerator] at *
  exact max_le (by omega) (by omega)

lemma weightProgram_flat : Flat weightProgram := by
  unfold weightProgram componentIndex
  apply Flat.ifLT
  · exact Flat.binary .add _ _ (Flat.var _) (Flat.lit _)
  · exact Flat.var _
  all_goals
    apply Flat.array
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    all_goals
      repeat
        first
        | exact Flat.lit _
        | exact Flat.var _
        | apply Flat.binary .add
        | apply Flat.binary .mul

lemma weightProgram_peak_le (ρ : Env) (N t : ℕ) (hN : ρ 0=.nat N)
    (ht : ρ 62=.nat t) (htN : t<N) :
    weightProgram.peak ρ≤4096*(N+2) := by
  have h0 : (Value.nat N).representationSize≤N+1 := by
    simp only [Value.representationSize]
    exact Nat.add_le_add_right (Paper37.DP.binarySize_le_self N) 1
  have h62 : (Value.nat t).representationSize≤N+1 := by
    simp only [Value.representationSize]
    have hh := Paper37.DP.binarySize_le_self t
    omega
  have hv : weightProgram.varsBound ρ (N+1) := by
    simp [weightProgram,componentIndex,Expr.varsBound,hN,ht,h0,h62]
  apply (flat_peak_le weightProgram_flat ρ (N+1) hv).trans
  simp [weightProgram,componentIndex,Expr.flatBudget]
  have hs2 := Paper37.DP.binarySize_le_self 2
  omega

def componentBody : Expr := .array [
  .mul (.get (.var 63) (.lit 0)) (.get (.var 60) (.min componentIndex (.var 0))),
  .mul (.mul (.get (.var 63) (.lit 1)) (.add (.var 0) (.lit 1)))
    (.get (.var 61) (.min componentIndex (.var 0)))]

lemma componentBody_flat : Flat componentBody := by
  unfold componentBody componentIndex
  apply Flat.array
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl
  all_goals
    repeat
      first
      | exact Flat.lit _
      | exact Flat.var _
      | apply Flat.get
      | apply Flat.binary .add
      | apply Flat.binary .min
      | apply Flat.binary .mul

lemma componentProgram_peak_le (ρ : Env) (N t B : ℕ) (masses norms : Vector ℕ (N+1))
    (hN : 0<N) (h0 : ρ 0=.nat N) (ht : ρ 62=.nat t) (htN : t<N)
    (hm : ρ 60=natArray masses) (hn : ρ 61=natArray norms)
    (hmB : ∀i : Fin (N+1),(masses[i.val]).size≤B)
    (hnB : ∀i : Fin (N+1),(norms[i.val]).size≤B) :
    componentProgram.peak ρ≤20000*frame N B := by
  let E := frame N B
  have hE : N+2≤E := by dsimp [E,frame];nlinarith
  have hmS : (natArray masses).representationSize≤4*E := by
    have hh := natArray_size_le masses B hmB
    dsimp [E,frame]
    nlinarith
  have hnS : (natArray norms).representationSize≤4*E := by
    have hh := natArray_size_le norms B hnB
    dsimp [E,frame]
    nlinarith
  have hw := weightPair_binarySize N (t+1) hN (by omega)
  have hwS : (pairValue (weightPair N (t+1))).representationSize≤4*E := by
    have hh := pairValue_size (weightPair N (t+1))
    have hb := weightWidth_le N
    dsimp [E,frame]
    nlinarith
  have h0S : (Value.nat N).representationSize≤4*E := by
    simp only [Value.representationSize]
    have hh := Paper37.DP.binarySize_le_self N
    omega
  have htS : (Value.nat t).representationSize≤4*E := by
    simp only [Value.representationSize]
    have hh := Paper37.DP.binarySize_le_self t
    omega
  let σ := Function.update ρ 63 (pairValue (weightPair N (t+1)))
  have hv : componentBody.varsBound σ (4*E) := by
    simp [componentBody,componentIndex,Expr.varsBound,σ,Function.update,h0,ht,hm,hn,hmS,hnS,hwS,h0S,htS]
  have hc : componentBody.peak σ≤20000*E := by
    apply (flat_peak_le componentBody_flat σ (4*E) hv).trans
    simp [componentBody,componentIndex,Expr.flatBudget]
    omega
  change (Expr.bind 63 weightProgram componentBody).peak ρ≤_
  apply (bind_peak_le ρ 63 weightProgram componentBody).trans
  rw [weightProgram_eval ρ N t h0 ht htN]
  apply max_le
  · exact (weightProgram_peak_le ρ N t h0 ht htN).trans (by omega)
  · exact hc

lemma mixBody_peak_le (ρ : Env) (N t B P : ℕ) (masses norms : Vector ℕ (N+1)) (p : ℕ×ℕ)
    (hN : 0<N) (h0 : ρ 0=.nat N) (ht : ρ 62=.nat t) (htN : t<N)
    (hm : ρ 60=natArray masses) (hn : ρ 61=natArray norms) (hp : ρ 64=pairValue p)
    (hpB : pairSize p≤P) (hmB : ∀i : Fin (N+1),(masses[i.val]).size≤B)
    (hnB : ∀i : Fin (N+1),(norms[i.val]).size≤B) :
    mixBody.peak ρ≤100000*(frame N B+P+componentWidth N B+10) := by
  let q := ((weightPair N (t+1)).1*lookupNumerator masses (t+1),
    (weightPair N (t+1)).2*(N+1)*lookupNumerator norms (t+1))
  let σ := Function.update ρ 53 (pairValue p)
  have hqB : pairSize q≤componentWidth N B := component_size N t B masses norms hN htN hmB hnB
  have hc := componentProgram_eval σ N t masses norms (by simpa [σ] using h0)
    (by simpa [σ] using ht) htN (by simpa [σ] using hm) (by simpa [σ] using hn)
  have hcP := componentProgram_peak_le σ N t B masses norms hN (by simpa [σ] using h0)
    (by simpa [σ] using ht) htN (by simpa [σ] using hm) (by simpa [σ] using hn) hmB hnB
  have hpS : (pairValue p).representationSize≤2*P+4 :=
    (pairValue_size p).trans (by omega)
  have hqS : (pairValue q).representationSize≤2*componentWidth N B+4 :=
    (pairValue_size q).trans (by omega)
  let τ := Function.update σ 54 (pairValue q)
  have hadd : Paper37.AdaptiveBatchProgram.pairAddProgram.peak τ≤
      128*((2*P+4)+(2*componentWidth N B+4)+1) := by
    apply Paper37.PredictorBatchPeak.pairAddProgram_peak
    · simpa [τ,σ] using hpS
    · simpa [τ] using hqS
  unfold mixBody
  apply (bind_peak_le ρ 53 (.var 64) _).trans
  simp only [Paper37.BoundedLoop.Expr.eval,hp]
  change max ((Expr.var 64).peak ρ)
    ((Expr.bind 54 componentProgram Paper37.AdaptiveBatchProgram.pairAddProgram).peak σ)≤_
  apply max_le
  · have hh : (Expr.var 64).peak ρ≤2*P+4 := by simpa [Expr.peak,Paper37.BoundedLoop.Expr.eval,hp] using hpS
    omega
  · apply (bind_peak_le σ 54 componentProgram Paper37.AdaptiveBatchProgram.pairAddProgram).trans
    rw [hc]
    change max (componentProgram.peak σ) (Paper37.AdaptiveBatchProgram.pairAddProgram.peak τ)≤_
    exact max_le (by omega) (by omega)

theorem mixProgram_peak_le (ρ : Env) (N B : ℕ) (masses norms : Vector ℕ (N+1))
    (hN : 0<N) (h0 : ρ 0=.nat N) (hm : ρ 60=natArray masses) (hn : ρ 61=natArray norms)
    (hmB : ∀i : Fin (N+1),(masses[i.val]).size≤B)
    (hnB : ∀i : Fin (N+1),(norms[i.val]).size≤B) :
    mixProgram.peak ρ≤10000000*(N+1)^2*(B+N+10) := by
  let E := frame N B
  let K := componentWidth N B
  let P := N*(K+4)+1
  let Q := 10000000*(N+1)^2*(B+N+10)
  have hE : 1≤E := by dsimp [E,frame];nlinarith
  have hNE : N+2≤E := by dsimp [E,frame];nlinarith
  have hP : P≤10*E := by dsimp [P,K,E,componentWidth,frame];nlinarith
  have hK : K+10≤10*E := by dsimp [K,E,componentWidth,frame];nlinarith
  have hQ : 100000*(E+P+K+10)≤Q := by
    have hEm : E≤(N+1)*E := by
      simpa using Nat.mul_le_mul_right E (show 1≤N+1 by omega)
    have hQeq : Q=10000000*(N+1)*E := by dsimp [Q,E,frame];ring
    rw [hQeq]
    nlinarith
  have hfold := Paper37.IntegerOutputPeak.range_foldl_peak_le N
    (fun vv t => mixBody.eval (Function.update (Function.update ρ 62 (.nat t)) 64 vv))
    (fun vv t => mixBody.peak (Function.update (Function.update ρ 62 (.nat t)) 64 vv))
    (fun j vv => ∃p : ℕ×ℕ,vv=pairValue p ∧ pairSize p≤j*(K+4)+1) Q (by
      intro t ht vv hv
      obtain ⟨p,rfl,hp⟩ := hv
      let q := ((weightPair N (t+1)).1*lookupNumerator masses (t+1),
        (weightPair N (t+1)).2*(N+1)*lookupNumerator norms (t+1))
      refine ⟨pairAdd p q,?_,?_⟩
      · dsimp only
        exact mixBody_eval _ N t masses norms p (by simpa using h0) (by simp) ht
          (by simpa using hm) (by simpa using hn) (by simp)
      · have hq := component_size N t B masses norms hN ht hmB hnB
        have hh := pairAdd_size p q
        dsimp only [K] at *
        nlinarith) (by
      intro t ht vv hv
      obtain ⟨p,rfl,hp⟩ := hv
      have htp : t*(K+4)+1≤P := by
        dsimp [P]
        exact Nat.add_le_add_right (Nat.mul_le_mul_right (K+4) (by omega)) 1
      have hh := mixBody_peak_le (Function.update (Function.update ρ 62 (.nat t)) 64 (pairValue p))
        N t B P masses norms p hN (by simpa using h0) (by simp) ht
        (by simpa using hm) (by simpa using hn) (by simp) (hp.trans htp) hmB hnB
      exact hh.trans hQ) (pairValue (0,1)) (by
        refine ⟨(0,1),rfl,?_⟩
        simp [pairSize]) 0 (by dsimp [Q];omega)
  have hout := hfold.1
  have hpeak := hfold.2
  unfold mixProgram
  rw [Expr.peak]
  apply max_le
  · have hval : (Expr.fold 62 64 (.var 0) (.array [.lit 0,.lit 1]) mixBody).eval ρ=
        ((List.range N).foldl
          (fun vv t => mixBody.eval (Function.update (Function.update ρ 62 (.nat t)) 64 vv))) (pairValue (0,1)) := by
      simp [Paper37.BoundedLoop.Expr.eval,h0,Value.natVal,pairValue]
    rw [hval]
    have heq : ((List.range N).foldl (fun vp t =>
      (mixBody.eval (Function.update (Function.update ρ 62 (.nat t)) 64 vp.1),
        max vp.2 (mixBody.peak (Function.update (Function.update ρ 62 (.nat t)) 64 vp.1))))
        (pairValue (0,1),0)).1=
        ((List.range N).foldl (fun vv t => mixBody.eval (Function.update (Function.update ρ 62 (.nat t)) 64 vv))) (pairValue (0,1)) := by
      generalize List.range N=xs
      generalize pairValue (0,1)=vv
      generalize (0:ℕ)=w
      induction xs generalizing vv w with
      | nil => rfl
      | cons t xs ih => simpa only [List.foldl_cons] using ih _ _
    rw [heq] at hout
    obtain ⟨p,hp,hps⟩ := hout
    rw [hp]
    have hh := pairValue_size p
    have hps' : pairSize p≤P := hps
    change (pairValue p).representationSize≤Q
    omega
  · change max ((Expr.var 0).peak ρ) (max ((Expr.array [.lit 0,.lit 1]).peak ρ) _)≤Q
    apply max_le
    · have hh := Paper37.DP.binarySize_le_self N
      simp only [Expr.peak,Paper37.BoundedLoop.Expr.eval,h0,Value.representationSize,max_eq_left (by omega : 0≤N.size+1)]
      omega
    · apply max_le
      · norm_num [Expr.peak,Paper37.BoundedLoop.Expr.eval,Value.representationSize]
        omega
      · simpa only [Paper37.BoundedLoop.Expr.eval,h0,Value.natVal,pairValue,List.map_cons,List.map_nil] using hpeak

end Paper37.AdaptiveMixPeak
