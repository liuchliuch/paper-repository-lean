import Paper37.BoundedLoop
import Paper37.CachedDP
import Paper37.CachedCoreProgram

namespace Paper37.CacheBuilderProgram
open Paper37.BoundedLoop Paper37.CachedDP
private abbrev v := Expr.var
private abbrev n := Expr.lit

def encodeVector {m : ℕ} (a : Vector ℕ m) : Value :=
  .array ((List.range m).map fun i => .nat (if hi:i<m then a[i] else 0))

lemma encodeVector_get {m : ℕ} (a : Vector ℕ m) (i : ℕ) (hi : i<m) :
    (encodeVector a).arrayVal[i]?.getD (.nat 0) = .nat (a[i]) := by
  simp [encodeVector,Value.arrayVal,List.getElem?_map,List.getElem?_range,hi]

def rowBase : Expr := .tabulate 23 (.add (v 0) (n 1))
  (.ifLT (v 23) (n 1) (n 1) (n 0))

def rowStep : Expr := .tabulate 23 (.add (v 0) (n 1))
  (.add (.get (v 22) (v 23))
    (.ifLT (n 0) (v 23) (.get (v 22) (.sub (v 23) (n 1))) (n 0)))

/-- Horizon in slot0, Pascal row index in slot20. Every loop body is finite
syntax, and its size is independent of both inputs. -/
def rowProgram : Expr := .fold 21 22 (v 20) rowBase rowStep

def chooseProgram : Expr := .tabulate 20 (.add (v 0) (n 1)) rowProgram

def powerProgram : Expr := .tabulate 24 (.add (.mul (n 2) (v 0)) (n 1))
  (.fold 25 26 (v 24) (n 1) (.mul (v 24) (v 26)))

lemma rowBase_eval (ρ : Env) (N : ℕ) (hN : ρ 0=.nat N) :
    rowBase.eval ρ=encodeVector (pascalRow N 0) := by
  simp only [rowBase,Expr.eval,hN,Value.natVal]
  apply congrArg Value.array
  apply List.map_congr_left
  intro i hi
  have hiN : i<N+1 := List.mem_range.mp hi
  simp only [Function.update_apply]
  by_cases hi0 : i=0 <;>
    simp [encodeVector,pascalRow,hiN,Vector.getElem_ofFn,hi0,show i<1 ↔ i=0 by omega]

lemma rowStep_eval (ρ : Env) (N k : ℕ) (hN : ρ 0=.nat N)
    (hrow : ρ 22=encodeVector (pascalRow N k)) :
    rowStep.eval ρ=encodeVector (pascalRow N (k+1)) := by
  simp only [rowStep,Expr.eval,hN,Value.natVal]
  unfold encodeVector
  apply congrArg Value.array
  apply List.map_congr_left
  intro i hi
  have hiN : i<N+1 := List.mem_range.mp hi
  simp only [Expr.eval,Function.update_apply,show (22:ℕ)≠23 by decide,
    if_false,if_true,hrow,Value.natVal]
  rw [encodeVector_get _ i hiN]
  by_cases hp : 0 < i
  case pos =>
    have hip : i-1<N+1 := by omega
    simp only [if_pos hp,Value.natVal]
    rw [encodeVector_get _ (i-1) hip]
    simp [hiN,pascalRow,Vector.getElem_ofFn,hp,show i≠0 by omega]
  case neg =>
    have hi0 : i=0 := by omega
    subst i
    simp [pascalRow,Vector.getElem_ofFn]

lemma rowProgram_eval (ρ : Env) (N k : ℕ) (hN : ρ 0=.nat N) (hk : ρ 20=.nat k) :
    rowProgram.eval ρ=encodeVector (pascalRow N k) := by
  simp only [rowProgram,Expr.eval,hk,Value.natVal,rowBase_eval ρ N hN]
  have hf : ∀m, (List.range m).foldl
      (fun a i => rowStep.eval (Function.update (Function.update ρ 21 (.nat i)) 22 a))
      (encodeVector (pascalRow N 0)) = encodeVector (pascalRow N m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [List.range_succ,List.foldl_append,ih]
      simp only [List.foldl_cons,List.foldl_nil]
      apply rowStep_eval _ N m
      · simpa using hN
      · simp
  exact hf k

theorem chooseProgram_eval (ρ : Env) (N : ℕ) (hN : ρ 0=.nat N) :
    chooseProgram.eval ρ = .array ((List.range (N+1)).map
      (fun k => encodeVector (pascalRow N k))) := by
  simp only [chooseProgram,Expr.eval,hN,Value.natVal]
  apply congrArg Value.array
  apply List.map_congr_left
  intro k hk
  exact rowProgram_eval _ N k (by simpa using hN) (by simp)

lemma powerFold_eval (ρ : Env) (c : ℕ) (hc : ρ 24=.nat c) :
    (Expr.fold 25 26 (v 24) (n 1) (.mul (v 24) (v 26))).eval ρ =
      .nat (linearPower c c) := by
  simp only [Expr.eval,hc,Value.natVal]
  have hf : ∀m, (List.range m).foldl
      (fun a i => Value.nat (c*a.natVal)) (.nat 1) = .nat (linearPower c m) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [List.range_succ,List.foldl_append,ih]
      rfl
  simpa [Function.update_apply,hc,Value.natVal] using hf c

theorem powerProgram_eval (ρ : Env) (N : ℕ) (hN : ρ 0=.nat N) :
    powerProgram.eval ρ=encodeVector (powerCache N) := by
  simp only [powerProgram,Expr.eval,hN,Value.natVal]
  unfold encodeVector
  apply congrArg Value.array
  apply List.map_congr_left
  intro c hc
  have hcN : c<2*N+1 := List.mem_range.mp hc
  have hp := powerFold_eval (Function.update ρ 24 (.nat c)) c (by simp)
  simpa only [Expr.eval,hcN,dif_pos, powerCache,Vector.getElem_ofFn] using hp

lemma fold_work_bound (xs : List ℕ) (f : Value → ℕ → Value × ℕ) (a : Value) (C : ℕ)
    (h : ∀v i,i∈xs → (f v i).2≤C) :
    (xs.foldl (fun vw i => let z:=f vw.1 i; (z.1,vw.2+z.2)) (a,0)).2≤xs.length*C := by
  have hf : ∀xs : List ℕ, ∀a j,
      (∀v i,i∈xs → (f v i).2≤C) →
      (xs.foldl (fun vw i => let z:=f vw.1 i; (z.1,vw.2+z.2)) (a,j)).2≤j+xs.length*C := by
    intro xs
    induction xs with
    | nil => intro a j h; simp
    | cons i xs ih =>
      intro a j h
      simp only [List.foldl_cons,List.length_cons]
      have hh := ih (f a i).1 (j+(f a i).2) (fun v q hq=>h v q (by simp [hq]))
      have hi := h a i (by simp)
      nlinarith
  simpa using hf xs a 0 h

lemma sum_map_bound (xs : List ℕ) (f : ℕ → ℕ) (C : ℕ)
    (h : ∀i∈xs,f i≤C) : (xs.map f).sum≤xs.length*C := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    have hi := h i (by simp)
    have ht := ih (fun j hj=>h j (by simp [hj]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

lemma rowBase_work_le (ρ : Env) (N : ℕ) (hN : ρ 0=.nat N) :
    rowBase.work ρ≤11*(N+1) := by
  simp [rowBase,Expr.work,Expr.eval,hN,Value.natVal]
  omega

lemma rowStep_work_le (ρ : Env) (N : ℕ) (hN : ρ 0=.nat N) :
    rowStep.work ρ≤20*(N+1) := by
  simp only [rowStep,Expr.work,Expr.eval,hN,Value.natVal]
  simp only [Function.update_apply,if_true,Value.natVal]
  have hs' : ((List.range (N+1)).map
      (fun i : ℕ => (1+1+1+(1+1+1+(if 0 < i then 1+(1+1+1)+1 else 1))+1+3 : ℕ))).sum≤16*(N+1) := by
    apply (sum_map_bound _ _ 16 _).trans_eq (by simp [Nat.mul_comm])
    intro i hi
    split_ifs <;> omega
  omega

lemma rowProgram_work_le (ρ : Env) (N k : ℕ) (hN : ρ 0=.nat N)
    (hk : ρ 20=.nat k) (hkN : k≤N) : rowProgram.work ρ≤40*(N+1)^2 := by
  have hb := rowBase_work_le ρ N hN
  let step := fun (a : Value) (i : ℕ) =>
    let ρ' := Function.update (Function.update ρ 21 (.nat i)) 22 a
    (rowStep.eval ρ',rowStep.work ρ'+4)
  have hf := fold_work_bound (List.range k) step (rowBase.eval ρ) (20*(N+1)+4)
    (by
      intro a i hi
      have hh := rowStep_work_le (Function.update (Function.update ρ 21 (.nat i)) 22 a) N
        (by simpa using hN)
      dsimp only [step]
      omega)
  simp only [List.length_range] at hf
  have hfold : ((List.range k).foldl
      (fun vw i => let ρ' := Function.update (Function.update ρ 21 (.nat i)) 22 vw.1
        (rowStep.eval ρ',vw.2+rowStep.work ρ'+4)) (rowBase.eval ρ,0)).2≤
      k*(20*(N+1)+4) := by simpa only [step,Nat.add_assoc] using hf
  simp only [rowProgram,Expr.work,Expr.eval,hk,Value.natVal]
  have hmono : k*(20*(N+1)+4)≤N*(20*(N+1)+4) := Nat.mul_le_mul_right _ hkN
  nlinarith

theorem chooseProgram_work_cubic (ρ : Env) (N : ℕ) (hN : ρ 0=.nat N) :
    chooseProgram.work ρ≤50*(N+1)^3 := by
  have hs := sum_map_bound (List.range (N+1))
    (fun k => rowProgram.work (Function.update ρ 20 (.nat k))+3) (40*(N+1)^2+3)
    (by
      intro k hk
      have hh := rowProgram_work_le (Function.update ρ 20 (.nat k)) N k
        (by simpa using hN) (by simp) (by have ht := List.mem_range.mp hk; omega)
      dsimp only
      omega)
  simp only [List.length_range] at hs
  simp only [chooseProgram,Expr.work,Expr.eval,hN,Value.natVal]
  nlinarith

lemma powerFold_work_le (ρ : Env) (c : ℕ) (hc : ρ 24=.nat c) :
    (Expr.fold 25 26 (v 24) (n 1) (.mul (v 24) (v 26))).work ρ≤3+7*c := by
  let step := fun (a : Value) (_i : ℕ) => (Value.nat (c*a.natVal),7)
  have hf := fold_work_bound (List.range c) step (.nat 1) 7 (by intros;exact le_rfl)
  simp only [List.length_range] at hf
  simp only [Expr.work,Expr.eval,hc,Value.natVal]
  have hh : ((List.range c).foldl
      (fun vw i => (Value.nat (c*vw.1.natVal),vw.2+3+4)) (Value.nat 1,0)).2≤c*7 := by
    simpa only [step,Nat.add_assoc] using hf
  simp only [Function.update_apply,show (24:ℕ)≠26 by decide,
    show (24:ℕ)≠25 by decide,if_false,if_true,hc,Value.natVal]
  simpa only [Value.natVal,Nat.mul_comm] using Nat.add_le_add_left hh 3

theorem powerProgram_work_quadratic (ρ : Env) (N : ℕ) (hN : ρ 0=.nat N) :
    powerProgram.work ρ≤60*(N+1)^2 := by
  have hs := sum_map_bound (List.range (2*N+1))
    (fun c => (Expr.fold 25 26 (v 24) (n 1) (.mul (v 24) (v 26))).work
      (Function.update ρ 24 (.nat c))+3) (6+14*N)
    (by
      intro c hc
      have hh := powerFold_work_le (Function.update ρ 24 (.nat c)) c (by simp)
      have hcN := List.mem_range.mp hc
      dsimp only
      omega)
  simp only [List.length_range] at hs
  have hs' : 6+((List.range (2*N+1)).map (fun c =>
      (Expr.fold 25 26 (v 24) (n 1) (.mul (v 24) (v 26))).work
        (Function.update ρ 24 (.nat c))+3)).sum≤60*(N+1)^2 := by nlinarith
  simpa only [powerProgram,Expr.work,Expr.eval,hN,Value.natVal] using hs'

theorem chooseProgram_source (ρ : Env) (H : ℕ) (z : List Bool) (hH : ρ 0=.nat H) :
    chooseProgram.eval ρ=Paper37.CachedCoreProgram.chooseValue (makeObservedCache H z) := by
  rw [chooseProgram_eval ρ H hH]
  unfold Paper37.CachedCoreProgram.chooseValue
  apply congrArg Value.array
  apply List.map_congr_left
  intro k hk
  have hkH : k<H+1 := List.mem_range.mp hk
  unfold encodeVector
  apply congrArg Value.array
  apply List.map_congr_left
  intro b hb
  have hbH : b<H+1 := List.mem_range.mp hb
  simp only [dif_pos hkH,dif_pos hbH,makeObservedCache_eq]
  rw [chooseAt_correct H (Paper37.ContinuationDP.observedCounts z) ⟨k,hkH⟩ b (by omega)]
  exact congrArg Value.nat (pascalRow_correct H k ⟨b,hbH⟩)

theorem powerProgram_source (ρ : Env) (H : ℕ) (z : List Bool) (hH : ρ 0=.nat H) :
    powerProgram.eval ρ=Paper37.CachedCoreProgram.powerValue (makeObservedCache H z) := by
  rw [powerProgram_eval ρ H hH]
  rfl

end Paper37.CacheBuilderProgram
