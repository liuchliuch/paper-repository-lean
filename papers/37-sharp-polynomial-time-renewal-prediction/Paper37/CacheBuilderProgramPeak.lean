import Paper37.CacheBuilderProgram
import Paper37.BoundedLoopFlat
import Paper37.IntegerOutputPeak
import Paper37.CachedBitBounds

namespace Paper37.CacheBuilderProgramPeak
open Paper37.BoundedLoop Paper37.CacheBuilderProgram Paper37.CachedDP
open Paper37.IntegerOutputPeak Paper37.DP

lemma encodeVector_size_le {m : ℕ} (a : Vector ℕ m) (B : ℕ)
    (h : ∀i:Fin m,(a[i.val]).size≤B) :
    (encodeVector a).representationSize≤m*(B+1)+2 := by
  simp only [encodeVector,Value.representationSize,List.map_map,Function.comp_apply]
  have hs := sum_map_bound (List.range m)
    (fun i => (Value.nat (if hi:i<m then a[i] else 0)).representationSize) (B+1)
    (by
      intro i hi
      have hi' := List.mem_range.mp hi
      simpa only [dif_pos hi',Value.representationSize] using Nat.add_le_add_right (h ⟨i,hi'⟩) 1)
  simpa only [List.length_range] using Nat.add_le_add_right hs 2

def rowSize (N : ℕ) : ℕ := (N+1)*(N+2)+2

lemma row_size_le (N k : ℕ) (hk : k≤N) :
    (encodeVector (pascalRow N k)).representationSize≤rowSize N := by
  apply encodeVector_size_le _ (N+1)
  intro i
  rw [pascalRow_correct]
  exact choose_binarySize N k i.val hk

lemma nat_index_size_le (i N : ℕ) (hi : i≤N) : (Value.nat i).representationSize≤N+1 := by
  have hh := (binarySize_le_self i).trans hi
  simpa only [Value.representationSize] using Nat.add_le_add_right hh 1

lemma tabulate_peak_le (ρ : Env) (i : ℕ) (bound body : Expr) (B : ℕ)
    (hout : ((Expr.tabulate i bound body).eval ρ).representationSize≤B)
    (hn : bound.peak ρ≤B)
    (hb : ∀j<(bound.eval ρ).natVal,body.peak (Function.update ρ i (.nat j))≤B) :
    (Expr.tabulate i bound body).peak ρ≤B := by
  rw [Expr.peak]
  apply max_le hout (max_le hn _)
  apply list_foldl_max_le _ _ _ (by omega)
  intro p hp
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
  exact hb j (List.mem_range.mp hj)

private def rowBody : Expr :=
  .add (.get (.var 22) (.var 23))
    (.ifLT (.lit 0) (.var 23) (.get (.var 22) (.sub (.var 23) (.lit 1))) (.lit 0))

private lemma rowBody_flat : Flat rowBody :=
  .binary .add _ _ (.get _ _ (.var 22) (.var 23))
    (.ifLT _ _ _ _ (.lit 0) (.var 23)
      (.get _ _ (.var 22) (.binary .sub _ _ (.var 23) (.lit 1))) (.lit 0))

lemma rowBody_peak (ρ : Env) (B : ℕ) (h22 : (ρ 22).representationSize≤B)
    (h23 : (ρ 23).representationSize≤B) (hB : 1≤B) : rowBody.peak ρ≤30*B+30 := by
  have hh := flat_peak_le rowBody_flat ρ B (by
    simp only [rowBody,Expr.varsBound]
    aesop)
  apply hh.trans
  simp only [rowBody,Expr.flatBudget,Nat.size_zero,Nat.size_one]
  omega

lemma bound_peak (ρ : Env) (N : ℕ) (hN : ρ 0=.nat N) :
    (Expr.add (.var 0) (.lit 1)).peak ρ≤4*N+12 := by
  have h0 : (Expr.var 0).peak ρ≤N+1 := by
    simpa [Expr.peak,Expr.eval,hN] using nat_index_size_le N N le_rfl
  have h1 : (Expr.lit 1).peak ρ≤2 := by simp [Expr.peak,Expr.eval,Value.representationSize,Nat.size_one]
  have hh := binary_peak_le .add (.var 0) (.lit 1) ρ _ _ h0 h1
  simpa only [Op.expr] using hh.trans (by omega)

lemma rowStep_peak (ρ : Env) (N k : ℕ) (hN : ρ 0=.nat N)
    (hr : ρ 22=encodeVector (pascalRow N k)) (hk : k<N) :
    rowStep.peak ρ≤100*(N+1)^2 := by
  have hs := row_size_le N k (by omega)
  have hout : (rowStep.eval ρ).representationSize≤rowSize N := by
    rw [rowStep_eval ρ N k hN hr]
    exact row_size_le N (k+1) (by omega)
  have hb := bound_peak ρ N hN
  change (Expr.tabulate 23 (.add (.var 0) (.lit 1)) rowBody).peak ρ≤_
  apply tabulate_peak_le
  · exact hout.trans (by unfold rowSize;nlinarith)
  · exact hb.trans (by nlinarith)
  · intro i hi
    have hi' : i≤N := by
      have hh : i<N+1 := by simpa [Expr.eval,hN,Value.natVal] using hi
      omega
    have hiB := nat_index_size_le i N hi'
    have hbody := rowBody_peak (Function.update ρ 23 (.nat i)) (rowSize N)
      (by simpa [hr] using hs) (by
        simpa using hiB.trans (show N+1≤rowSize N by unfold rowSize;nlinarith))
      (by unfold rowSize;omega)
    dsimp only [rowSize] at hbody
    nlinarith

lemma rowBase_peak (ρ : Env) (N : ℕ) (hN : ρ 0=.nat N) :
    rowBase.peak ρ≤100*(N+1)^2 := by
  have hout : (rowBase.eval ρ).representationSize≤rowSize N := by
    rw [rowBase_eval ρ N hN]
    exact row_size_le N 0 (by omega)
  have hn := bound_peak ρ N hN
  apply tabulate_peak_le
  · exact hout.trans (by unfold rowSize;nlinarith)
  · exact hn.trans (by nlinarith)
  · intro i hi
    have hi' : i≤N := by
      have hh : i<N+1 := by simpa [Expr.eval,hN,Value.natVal] using hi
      omega
    have hv : (Expr.var 23).peak (Function.update ρ 23 (.nat i))≤N+1 := by
      simpa [Expr.peak,Expr.eval] using nat_index_size_le i N hi'
    have hone : (Expr.lit 1).peak (Function.update ρ 23 (.nat i))≤2 := by
      simp [Expr.peak,Expr.eval,Value.representationSize,Nat.size_one]
    have hz : (Expr.lit 0).peak (Function.update ρ 23 (.nat i))≤1 := by
      simp [Expr.peak,Expr.eval,Value.representationSize,Nat.size_zero]
    have hh := if_peak_le (.var 23) (.lit 1) (.lit 1) (.lit 0)
      (Function.update ρ 23 (.nat i)) _ _ _ _ hv hone hone hz
    apply hh.trans
    simp only [max_le_iff]
    constructor
    · nlinarith
    constructor
    · nlinarith
    constructor <;> nlinarith

lemma rowProgram_peak (ρ : Env) (N k : ℕ) (hN : ρ 0=.nat N)
    (hk : ρ 20=.nat k) (hkN : k≤N) : rowProgram.peak ρ≤100*(N+1)^2 := by
  have hout : (rowProgram.eval ρ).representationSize≤rowSize N := by
    rw [rowProgram_eval ρ N k hN hk]
    exact row_size_le N k hkN
  have hbase := rowBase_peak ρ N hN
  let step := fun a i => rowStep.eval (Function.update (Function.update ρ 21 (.nat i)) 22 a)
  let cost := fun a i => rowStep.peak (Function.update (Function.update ρ 21 (.nat i)) 22 a)
  let I := fun j a => a=encodeVector (pascalRow N j)
  have hf := range_foldl_peak_le k step cost I (100*(N+1)^2)
    (by
      intro j hj a ha
      dsimp only [I] at ha ⊢
      subst a
      exact rowStep_eval _ N j (by simpa using hN) (by simp))
    (by
      intro j hj a ha
      dsimp only [I] at ha
      subst a
      exact rowStep_peak _ N j (by simpa using hN) (by simp) (by omega))
    (rowBase.eval ρ) (by dsimp [I];exact rowBase_eval ρ N hN) 0 (by omega)
  have hn : (Expr.var 20).peak ρ≤N+1 := by
    simpa [Expr.peak,Expr.eval,hk] using nat_index_size_le k N hkN
  change (Expr.fold 21 22 (.var 20) rowBase rowStep).peak ρ≤_
  rw [Expr.peak]
  apply max_le (hout.trans (by unfold rowSize;nlinarith))
  change max _ (max _ _)≤_
  apply max_le (hn.trans (by nlinarith)) (max_le hbase _)
  simpa only [rowProgram,Expr.eval,hk,Value.natVal,step,cost,I] using hf.2

theorem chooseProgram_peak (ρ : Env) (N : ℕ) (hN : ρ 0=.nat N) :
    chooseProgram.peak ρ≤200*(N+1)^3 := by
  have hcube : 0≤N^3 := Nat.zero_le _
  have hout : (chooseProgram.eval ρ).representationSize≤(N+1)*rowSize N+2 := by
    rw [chooseProgram_eval ρ N hN]
    simp only [Value.representationSize,List.map_map,Function.comp_apply]
    have hs := sum_map_bound (List.range (N+1))
      (fun k => (encodeVector (pascalRow N k)).representationSize) (rowSize N)
      (by intro k hk;exact row_size_le N k (by have hh:=List.mem_range.mp hk;omega))
    simpa only [List.length_range] using Nat.add_le_add_right hs 2
  have hn := bound_peak ρ N hN
  apply tabulate_peak_le
  · exact hout.trans (by unfold rowSize;nlinarith [hcube])
  · exact hn.trans (by nlinarith [hcube])
  · intro k hk
    have hk' : k≤N := by
      have hh : k<N+1 := by simpa [Expr.eval,hN,Value.natVal] using hk
      omega
    have hh := rowProgram_peak (Function.update ρ 20 (.nat k)) N k
      (by simpa using hN) (by simp) hk'
    nlinarith

lemma power_value_size (N c m : ℕ) (hm : m≤c) (hc : c≤2*N) :
    (Value.nat (linearPower c m)).representationSize≤4*N^2+3 := by
  have hh := Paper37.CachedBitBounds.linearPower_binarySize (2*N) c m hm hc
  have hs := binarySize_le_self (2*N)
  simp only [Value.representationSize]
  nlinarith

private def powerFold : Expr := .fold 25 26 (.var 24) (.lit 1) (.mul (.var 24) (.var 26))

lemma powerFold_peak (ρ : Env) (N c : ℕ) (hc : ρ 24=.nat c) (hcN : c≤2*N) :
    powerFold.peak ρ≤100*(N+1)^2 := by
  have hout : (powerFold.eval ρ).representationSize≤4*N^2+3 := by
    rw [powerFold,powerFold_eval ρ c hc]
    exact power_value_size N c c le_rfl hcN
  let step := fun (a : Value) (i : ℕ) =>
    (Expr.mul (.var 24) (.var 26)).eval (Function.update (Function.update ρ 25 (.nat i)) 26 a)
  let cost := fun (a : Value) (i : ℕ) =>
    (Expr.mul (.var 24) (.var 26)).peak (Function.update (Function.update ρ 25 (.nat i)) 26 a)
  let I := fun j a => a=Value.nat (linearPower c j)
  have hf := range_foldl_peak_le c step cost I (100*(N+1)^2)
    (by
      intro j hj a ha
      dsimp only [I] at ha ⊢
      subst a
      simp [step,Expr.eval,Function.update_apply,hc,Value.natVal,linearPower])
    (by
      intro j hj a ha
      dsimp only [I] at ha
      subst a
      have hcv := nat_index_size_le c (2*N) hcN
      have hav := power_value_size N c j (by omega) hcN
      have hx : (Expr.var 24).peak
          (Function.update (Function.update ρ 25 (.nat j)) 26 (.nat (linearPower c j)))≤2*N+1 := by
        simpa [Expr.peak,Expr.eval,Function.update_apply,hc] using hcv
      have hy : (Expr.var 26).peak
          (Function.update (Function.update ρ 25 (.nat j)) 26 (.nat (linearPower c j)))≤4*N^2+3 := by
        simpa [Expr.peak,Expr.eval] using hav
      have hh := binary_peak_le .mul (.var 24) (.var 26) _ _ _ hx hy
      exact hh.trans (by nlinarith))
    (.nat 1) (by rfl) 0 (by omega)
  have hn : (Expr.var 24).peak ρ≤2*N+1 := by
    simpa [Expr.peak,Expr.eval,hc] using nat_index_size_le c (2*N) hcN
  have hz : (Expr.lit 1).peak ρ≤2 := by
    simp [Expr.peak,Expr.eval,Value.representationSize,Nat.size_one]
  change (Expr.fold 25 26 (.var 24) (.lit 1) (.mul (.var 24) (.var 26))).peak ρ≤_
  rw [Expr.peak]
  apply max_le (hout.trans (by nlinarith))
  apply max_le (hn.trans (by nlinarith)) (max_le (hz.trans (by nlinarith)) _)
  simpa only [powerFold,Expr.eval,hc,Value.natVal,step,cost,I] using hf.2

theorem powerProgram_peak (ρ : Env) (N : ℕ) (hN : ρ 0=.nat N) :
    powerProgram.peak ρ≤1000*(N+1)^3 := by
  have hcube : 0≤N^3 := Nat.zero_le _
  have hout : (powerProgram.eval ρ).representationSize≤(2*N+1)*(4*N^2+3)+2 := by
    rw [powerProgram_eval ρ N hN]
    apply encodeVector_size_le _ (4*N^2+2)
    intro c
    have hh := power_value_size N c.val c.val le_rfl (by omega)
    simpa only [powerCache,Vector.getElem_ofFn] using
      (show (linearPower c.val c.val).size≤4*N^2+2 by
        simp only [Value.representationSize] at hh
        omega)
  have hvar : (Expr.var 0).peak ρ≤N+1 := by
    simpa [Expr.peak,Expr.eval,hN] using nat_index_size_le N N le_rfl
  have h2 : (Expr.lit 2).peak ρ≤3 := by
    simpa [Expr.peak,Expr.eval] using nat_index_size_le 2 2 le_rfl
  have h1 : (Expr.lit 1).peak ρ≤2 := by
    simp [Expr.peak,Expr.eval,Value.representationSize,Nat.size_one]
  have hm := binary_peak_le .mul (.lit 2) (.var 0) ρ _ _ h2 hvar
  have hn := binary_peak_le .add (.mul (.lit 2) (.var 0)) (.lit 1) ρ _ _ hm h1
  apply tabulate_peak_le
  · exact hout.trans (by nlinarith [hcube])
  · exact hn.trans (by nlinarith [hcube])
  · intro c hc
    have hcN : c≤2*N := by
      have hh : c<2*N+1 := by simpa [Expr.eval,hN,Value.natVal] using hc
      omega
    have hh := powerFold_peak (Function.update ρ 24 (.nat c)) N c (by simp) hcN
    exact hh.trans (by nlinarith [hcube])

end Paper37.CacheBuilderProgramPeak
