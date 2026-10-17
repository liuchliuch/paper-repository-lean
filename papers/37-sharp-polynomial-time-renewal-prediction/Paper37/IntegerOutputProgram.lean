import Paper37.CachedCoreProgram
import Paper37.CachedOutput

/-! A fixed, finite first-order bounded-loop program for the actual integer
continuation output pair. The inputs share the DP power/count caches and final
materialized layer; no rational normalization occurs in the program. -/
namespace Paper37.IntegerOutputProgram
open scoped BigOperators
open Paper37.BoundedLoop Paper37.CachedDP Paper37.CachedCoreProgram
open Paper37.CachedOutput Paper37.ContinuationDP Paper37.IntegerOutput
open Paper37.DP Paper37.Envelope

private abbrev v := BoundedLoop.Expr.var
private abbrev n := BoundedLoop.Expr.lit
private abbrev add := BoundedLoop.Expr.add
private abbrev mul := BoundedLoop.Expr.mul
private abbrev get := BoundedLoop.Expr.get

/-- Inputs 0=H,1=A,3=powers,4=observed counts,5=final layer,11=r,12=R.
Local bindings 13..20 are private scratch slots of this output program. -/
structure Inputs {H : ℕ} (ρ : Env) (c : Cache H) (A : ℕ) (table : Layer H) (r R : ℕ) : Prop where
  horizon : ρ 0=.nat H
  age : ρ 1=.nat A
  power : ρ 3=powerValue c
  observed : ρ 4=observedValue c
  layer : ρ 5=layerValue table
  count : ρ 11=.nat r
  remaining : ρ 12=.nat R

def outputEnv {H : ℕ} (c : Cache H) (A : ℕ) (table : Layer H) (r R : ℕ) : Env :=
  Function.update (Function.update (inputEnv c A table) 11 (.nat r)) 12 (.nat R)

lemma outputEnv_inputs {H : ℕ} (c : Cache H) (A : ℕ) (table : Layer H) (r R : ℕ) :
    Inputs (outputEnv c A table r R) c A table r R := by
  constructor <;> simp [outputEnv,inputEnv,Function.update_apply]

def totalFuture : BoundedLoop.Expr := add (v 1) (v 12)
def productIndex : BoundedLoop.Expr := add (v 19) (n 1)
def denominatorProgram : BoundedLoop.Expr :=
  .fold 19 20 (v 0) (n 1) (mul (v 20) (get (v 3) productIndex))
def initialProgram : BoundedLoop.Expr :=
  .fold 19 20 (v 0) (n 1) (mul (v 20) (get (v 3) (get (v 4) productIndex)))
def kIndex : BoundedLoop.Expr := add (v 15) (n 1)
def tableMarked : BoundedLoop.Expr := get (get (get (v 5) kIndex) (v 17)) (n 1)
def finalTerm : BoundedLoop.Expr :=
  mul (.div tableMarked kIndex) (.div (v 13) (get (v 3) (add (v 11) kIndex)))
def guardedTerm : BoundedLoop.Expr := .ifLT (v 17) kIndex (n 0) finalTerm

def innerSum : BoundedLoop.Expr :=
  .fold 17 18 (add totalFuture (n 1)) (n 0) (add (v 18) guardedTerm)
def outerSum : BoundedLoop.Expr :=
  .fold 15 16 totalFuture (n 0) (add (v 16) innerSum)
def outputArray : BoundedLoop.Expr := .array [
  add (mul (v 14) (.div (v 13) (get (v 3) (v 11)))) outerSum,v 13]

/-- A single syntax term for every horizon and every queried word. -/
def outputProgram : BoundedLoop.Expr :=
  .bind 13 denominatorProgram (.bind 14 initialProgram outputArray)

lemma fold_charge_le (is : List ℕ) (ρ : Env) (i a : ℕ) (body : BoundedLoop.Expr)
    (C : ℕ) (hc : ∀j∈is,∀x,body.work (Function.update (Function.update ρ i (.nat j)) a x)≤C)
    (x : Value) (cost : ℕ) :
    (is.foldl (fun vw j=>
      let ρ' := Function.update (Function.update ρ i (.nat j)) a vw.1
      (body.eval ρ',vw.2+body.work ρ'+4)) (x,cost)).2 ≤ cost+is.length*(C+4) := by
  induction is generalizing x cost with
  | nil => simp
  | cons j is ih =>
    simp only [List.foldl_cons,List.length_cons]
    have hj := hc j (by simp) x
    have hi := ih (fun t ht=>hc t (by simp [ht]))
      (body.eval (Function.update (Function.update ρ i (.nat j)) a x))
      (cost+body.work (Function.update (Function.update ρ i (.nat j)) a x)+4)
    dsimp only at hi ⊢
    nlinarith

lemma fold_work_le (ρ : Env) (i a : ℕ) (bound init body : BoundedLoop.Expr) (C : ℕ)
    (hc : ∀j<(bound.eval ρ).natVal,∀x,
      body.work (Function.update (Function.update ρ i (.nat j)) a x)≤C) :
    (BoundedLoop.Expr.fold i a bound init body).work ρ ≤
      bound.work ρ+init.work ρ+1+(bound.eval ρ).natVal*(C+4) := by
  rw [BoundedLoop.Expr.work]
  have h := fold_charge_le (List.range (bound.eval ρ).natVal) ρ i a body C
    (fun j hj=>hc j (List.mem_range.mp hj)) (init.eval ρ) 0
  simp only [List.length_range,zero_add] at h
  exact Nat.add_le_add_left h _

@[simp] lemma finalTerm_work (ρ : Env) : finalTerm.work ρ=23 := by
  simp [finalTerm,tableMarked,kIndex,BoundedLoop.Expr.work]
lemma guardedTerm_work (ρ : Env) : guardedTerm.work ρ≤28 := by
  unfold guardedTerm
  simp only [BoundedLoop.Expr.work,finalTerm_work,kIndex]
  split_ifs <;> simp [BoundedLoop.Expr.work]

lemma innerSum_work (ρ : Env) :
    innerSum.work ρ≤7+((totalFuture.eval ρ).natVal+1)*34 := by
  have h := fold_work_le ρ 17 18 (add totalFuture (n 1)) (n 0)
    (add (v 18) guardedTerm) 30 (by
      intro j hj x
      have hh := guardedTerm_work (Function.update (Function.update ρ 17 (.nat j)) 18 x)
      simp only [BoundedLoop.Expr.work]
      omega)
  simpa only [innerSum,BoundedLoop.Expr.work,BoundedLoop.Expr.eval,Value.natVal,totalFuture,
    Nat.reduceAdd] using h

lemma totalFuture_update (ρ : Env) (x : ℕ) (a : Value)
    (hx1 : x≠1) (hx12 : x≠12) :
    (totalFuture.eval (Function.update ρ x a)).natVal=(totalFuture.eval ρ).natVal := by
  simp [totalFuture,BoundedLoop.Expr.eval,Function.update_apply,Ne.symm hx1,Ne.symm hx12]

lemma outerSum_work (ρ : Env) :
    outerSum.work ρ≤5+(totalFuture.eval ρ).natVal*(13+34*((totalFuture.eval ρ).natVal+1)) := by
  have h := fold_work_le ρ 15 16 totalFuture (n 0) (add (v 16) innerSum)
    (9+34*((totalFuture.eval ρ).natVal+1)) (by
      intro j hj x
      have hh := innerSum_work (Function.update (Function.update ρ 15 (.nat j)) 16 x)
      rw [totalFuture_update _ 16 _ (by decide) (by decide),
        totalFuture_update _ 15 _ (by decide) (by decide)] at hh
      simp only [BoundedLoop.Expr.work]
      omega)
  have hcoeff (t : ℕ) : 9+34*(t+1)+4=13+34*(t+1) := by omega
  simp_rw [hcoeff] at h
  simpa only [outerSum,BoundedLoop.Expr.work,totalFuture,add,v,n,Nat.add_assoc,Nat.reduceAdd] using h

lemma denominatorProgram_work (ρ : Env) :
    denominatorProgram.work ρ≤3+(ρ 0).natVal*11 := by
  have h := fold_work_le ρ 19 20 (v 0) (n 1)
    (mul (v 20) (get (v 3) productIndex)) 7 (by intro j hj x; simp [BoundedLoop.Expr.work,productIndex])
  simpa only [denominatorProgram,BoundedLoop.Expr.work,BoundedLoop.Expr.eval,Nat.reduceAdd] using h

lemma initialProgram_work (ρ : Env) :
    initialProgram.work ρ≤3+(ρ 0).natVal*13 := by
  have h := fold_work_le ρ 19 20 (v 0) (n 1)
    (mul (v 20) (get (v 3) (get (v 4) productIndex))) 9 (by intro j hj x; simp [BoundedLoop.Expr.work,productIndex])
  simpa only [initialProgram,BoundedLoop.Expr.work,BoundedLoop.Expr.eval,Nat.reduceAdd] using h

lemma outputArray_work (ρ : Env) :
    outputArray.work ρ≤18+(totalFuture.eval ρ).natVal*(13+34*((totalFuture.eval ρ).natVal+1)) := by
  have h:=outerSum_work ρ
  simp only [outputArray,BoundedLoop.Expr.work,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  omega

/-- The work bound is obtained from the actual syntax evaluator, for arbitrary
input contents. It is not a freely supplied cost annotation. -/
lemma outputProgram_work (ρ : Env) :
    outputProgram.work ρ≤26+24*(ρ 0).natVal+
      (totalFuture.eval ρ).natVal*(13+34*((totalFuture.eval ρ).natVal+1)) := by
  have hD := denominatorProgram_work ρ
  let ρD := Function.update ρ 13 (denominatorProgram.eval ρ)
  have hI := initialProgram_work ρD
  let ρI := Function.update ρD 14 (initialProgram.eval ρD)
  have hA := outputArray_work ρI
  have h0 : ρD 0=ρ 0 := by simp [ρD,Function.update_apply]
  rw [h0] at hI
  have hT : (totalFuture.eval ρI).natVal=(totalFuture.eval ρ).natVal := by
    dsimp [ρI,ρD]
    rw [totalFuture_update _ 14 _ (by decide) (by decide),
      totalFuture_update _ 13 _ (by decide) (by decide)]
  rw [hT] at hA
  change outputProgram.work ρ≤_
  rw [outputProgram,BoundedLoop.Expr.work,BoundedLoop.Expr.work]
  change denominatorProgram.work ρ+1+(initialProgram.work ρD+1+outputArray.work ρI)≤_
  omega

lemma outputProgram_work_quadratic {H : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : Layer H}
    (hs : Inputs ρ c A table r R) (hT : A+R≤H) :
    outputProgram.work ρ≤200*(H+1)^2 := by
  have h:=outputProgram_work ρ
  have hF : (totalFuture.eval ρ).natVal=A+R := by
    simp [totalFuture,BoundedLoop.Expr.eval,hs.age,hs.remaining,Value.natVal]
  rw [hs.horizon,hF] at h
  change outputProgram.work ρ≤_
  simp only [Value.natVal] at h
  nlinarith [Nat.mul_self_le_mul_self hT]


lemma fold_mul_of (is : List ℕ) (f : ℕ → ℕ) (step : Value → ℕ → Value)
    (hs : ∀i∈is,∀a,step (.nat a) i=.nat (a*f i)) (a : ℕ) :
    is.foldl step (.nat a)=.nat (a*(is.map f).prod) := by
  induction is generalizing a with
  | nil => simp
  | cons i is ih =>
    rw [List.foldl_cons,hs i (by simp) a,ih (by
      intro j hj b
      exact hs j (by simp [hj]) b)]
    simp only [List.map_cons,List.prod_cons,Nat.mul_assoc]

lemma prod_range_succ (H : ℕ) (f : ℕ → ℕ) :
    (∏i∈Finset.range H,f (i+1))=∏i∈Finset.Icc 1 H,f i := by
  rw [← Finset.Ico_add_one_right_eq_Icc,Finset.prod_Ico_eq_prod_range]
  simp only [Nat.add_sub_cancel,Nat.add_comm]

lemma sum_range_succ (T : ℕ) (f : ℕ → ℕ) :
    (∑i∈Finset.range T,f (i+1))=∑i∈Finset.Icc 1 T,f i := by
  rw [← Finset.Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel,Nat.add_comm]

lemma denominatorProgram_eval {H : ℕ} (ρ : Env) (c : Cache H)
    (hH : ρ 0=.nat H) (hp : ρ 3=powerValue c) :
    denominatorProgram.eval ρ=.nat (denominator c) := by
  simp only [denominatorProgram,BoundedLoop.Expr.eval,hH,Value.natVal]
  rw [fold_mul_of _ (fun i=>powerAt c (i+1)) _ (by
    intro i hi a
    simp only [mul,get,v,productIndex,add,n,BoundedLoop.Expr.eval]
    simp [Function.update,hp,powerValue_get_total,Value.natVal])]
  congr 1
  simp only [one_mul]
  rw [← List.prod_toFinset _ List.nodup_range]
  simpa only [List.toFinset_range,denominator] using prod_range_succ H (powerAt c)

lemma observedValue_get {H : ℕ} (c : Cache H) (d : ℕ) (hd : d≤H) :
    (observedValue c).arrayVal[d]?.getD (.nat 0)=.nat (observedAt c d) := by
  rw [observedValue,natArray_get _ d (by omega)]
  simp only [observedAt,dif_pos (by omega : d<H+1)]

lemma initialProgram_eval {H : ℕ} (ρ : Env) (c : Cache H)
    (hH : ρ 0=.nat H) (hp : ρ 3=powerValue c) (hc : ρ 4=observedValue c) :
    initialProgram.eval ρ=.nat (initialNumerator c) := by
  simp only [initialProgram,BoundedLoop.Expr.eval,hH,Value.natVal]
  rw [fold_mul_of _ (fun i=>powerAt c (observedAt c (i+1))) _ (by
    intro i hi a
    have hiH : i+1≤H := by have hh:=List.mem_range.mp hi;omega
    simp only [mul,get,v,productIndex,add,n,BoundedLoop.Expr.eval]
    simp [Function.update,hp,hc,observedValue_get c (i+1) hiH,powerValue_get_total,Value.natVal])]
  congr 1
  simp only [one_mul]
  rw [← List.prod_toFinset _ List.nodup_range]
  simpa only [List.toFinset_range,initialNumerator,gapSet] using
    prod_range_succ H (fun d=>powerAt c (observedAt c d))


lemma Inputs.update_gt {H : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : Layer H}
    (hs : Inputs ρ c A table r R) {x : ℕ} (hx : 12<x) (a : Value) :
    Inputs (Function.update ρ x a) c A table r R := by
  constructor
  · simpa [Function.update,show (0:ℕ)≠x by omega] using hs.horizon
  · simpa [Function.update,show (1:ℕ)≠x by omega] using hs.age
  · simpa [Function.update,show (3:ℕ)≠x by omega] using hs.power
  · simpa [Function.update,show (4:ℕ)≠x by omega] using hs.observed
  · simpa [Function.update,show (5:ℕ)≠x by omega] using hs.layer
  · simpa [Function.update,show (11:ℕ)≠x by omega] using hs.count
  · simpa [Function.update,show (12:ℕ)≠x by omega] using hs.remaining

lemma finalTerm_eval {H : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : Layer H}
    (hs : Inputs ρ c A table r R) (D k0 u : ℕ)
    (hD : ρ 13=.nat D) (hk : ρ 15=.nat k0) (hu : ρ 17=.nat u)
    (hkH : k0+1≤H) (huH : u≤H) :
    finalTerm.eval ρ=.nat ((layerAt table (k0+1) u).2/(k0+1)*(D/powerAt c (r+(k0+1)))) := by
  simp only [finalTerm,tableMarked,kIndex,BoundedLoop.Expr.eval,hs.layer,hs.power,hs.count,
    hD,hk,hu,Value.natVal]
  rw [layerValue_get table (k0+1) u (by omega) (by omega)]
  simp only [Value.arrayVal,List.getElem?_cons_succ,List.getElem?_cons_zero,Option.getD_some,Value.natVal]
  change Value.nat ((layerAt table (k0+1) u).2/(k0+1)*
    (D/((powerValue c).arrayVal[r+(k0+1)]?.getD (.nat 0)).natVal))=_
  rw [powerValue_get_total]
  rfl

lemma guardedTerm_eval {H : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : Layer H}
    (hs : Inputs ρ c A table r R) (D k0 u : ℕ)
    (hD : ρ 13=.nat D) (hk : ρ 15=.nat k0) (hu : ρ 17=.nat u)
    (hkH : k0+1≤H) (huH : u≤H) :
    guardedTerm.eval ρ=.nat (if u<k0+1 then 0 else
      (layerAt table (k0+1) u).2/(k0+1)*(D/powerAt c (r+(k0+1)))) := by
  simp only [guardedTerm,BoundedLoop.Expr.eval,kIndex,hu,hk,Value.natVal]
  split_ifs with h
  · simp only [BoundedLoop.Expr.eval]
  · exact finalTerm_eval hs D k0 u hD hk hu hkH huH

lemma sum_range_guard (T k : ℕ) (f : ℕ → ℕ) :
    (∑u∈Finset.range (T+1),if u<k then 0 else f u)=∑u∈Finset.Icc k T,f u := by
  calc
    _ = ∑u∈(Finset.range (T+1)).filter (fun u=>k≤u),f u := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro u _
      by_cases h : u<k
      · simp [h,show ¬k≤u by omega]
      · simp [h,show k≤u by omega]
    _ = _ := by
      congr 1
      ext u
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Icc]
      omega

lemma innerSum_eval {H : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : Layer H}
    (hs : Inputs ρ c A table r R) (D k0 : ℕ)
    (hD : ρ 13=.nat D) (hk : ρ 15=.nat k0)
    (hkT : k0<A+R) (hT : A+R≤H) :
    innerSum.eval ρ=.nat (∑u∈Finset.Icc (k0+1) (A+R),
      (layerAt table (k0+1) u).2/(k0+1)*(D/powerAt c (r+(k0+1)))) := by
  have hbound : ((add totalFuture (n 1)).eval ρ).natVal=A+R+1 := by
    simp [totalFuture,BoundedLoop.Expr.eval,hs.age,hs.remaining,Value.natVal]
  rw [innerSum,BoundedLoop.Expr.eval,hbound]
  simp only [BoundedLoop.Expr.eval]
  rw [fold_add_of _ (fun u=>if u<k0+1 then 0 else
      (layerAt table (k0+1) u).2/(k0+1)*(D/powerAt c (r+(k0+1)))) _ (by
    intro u hu a
    have huH : u≤H := by have hh:=List.mem_range.mp hu;omega
    have hs' := (hs.update_gt (x:=17) (by decide) (.nat u)).update_gt (x:=18) (by decide) (.nat a)
    have hterm := guardedTerm_eval hs' D k0 u
      (by simp [Function.update,hD]) (by simp [Function.update,hk])
      (by simp [Function.update]) (by omega) huH
    simp only [add,v,BoundedLoop.Expr.eval]
    rw [hterm]
    simp [Function.update,Value.natVal])]
  simp only [zero_add]
  congr 1
  rw [← List.sum_toFinset _ List.nodup_range]
  simpa only [List.toFinset_range] using sum_range_guard (A+R) (k0+1)
    (fun u=>(layerAt table (k0+1) u).2/(k0+1)*(D/powerAt c (r+(k0+1))))

lemma outerSum_eval {H : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : Layer H}
    (hs : Inputs ρ c A table r R) (D : ℕ) (hD : ρ 13=.nat D) (hT : A+R≤H) :
    outerSum.eval ρ=.nat (∑k∈Finset.Icc 1 (A+R),∑u∈Finset.Icc k (A+R),
      (layerAt table k u).2/k*(D/powerAt c (r+k))) := by
  have hbound : (totalFuture.eval ρ).natVal=A+R := by
    simp [totalFuture,BoundedLoop.Expr.eval,hs.age,hs.remaining,Value.natVal]
  simp only [outerSum,BoundedLoop.Expr.eval,hbound]
  rw [fold_add_of _ (fun k0=>∑u∈Finset.Icc (k0+1) (A+R),
      (layerAt table (k0+1) u).2/(k0+1)*(D/powerAt c (r+(k0+1)))) _ (by
    intro k0 hk a
    have hs' := (hs.update_gt (x:=15) (by decide) (.nat k0)).update_gt (x:=16) (by decide) (.nat a)
    have hinner := innerSum_eval hs' D k0 (by simp [Function.update,hD])
      (by simp [Function.update]) (List.mem_range.mp hk) hT
    simp only [add,v,BoundedLoop.Expr.eval]
    rw [hinner]
    simp [Function.update,Value.natVal])]
  simp only [zero_add]
  congr 1
  rw [← List.sum_toFinset _ List.nodup_range]
  simpa only [List.toFinset_range] using sum_range_succ (A+R)
    (fun k=>∑u∈Finset.Icc k (A+R),(layerAt table k u).2/k*(D/powerAt c (r+k)))

/-- The pair computed from the shared materialized cache and final layer. -/
def outputPair {H : ℕ} (c : Cache H) (A : ℕ) (table : Layer H) (r R : ℕ) : ℕ×ℕ :=
  (initialNumerator c*(denominator c/powerAt c r)+
    ∑k∈Finset.Icc 1 (A+R),∑u∈Finset.Icc k (A+R),
      (layerAt table k u).2/k*(denominator c/powerAt c (r+k)),denominator c)

/-- Compositional semantic interface: arbitrary surrounding environments may
contain the parser, suffix loops and batch accumulators in other slots. -/
theorem outputProgram_eval_inputs {H : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : Layer H}
    (hs : Inputs ρ c A table r R) (hT : A+R≤H) :
    outputProgram.eval ρ=.array [.nat (outputPair c A table r R).1,.nat (outputPair c A table r R).2] := by
  have hD:=denominatorProgram_eval ρ c hs.horizon hs.power
  let ρD:=Function.update ρ 13 (.nat (denominator c))
  have hsD : Inputs ρD c A table r R := hs.update_gt (by decide) _
  have hI:=initialProgram_eval ρD c hsD.horizon hsD.power hsD.observed
  let ρI:=Function.update ρD 14 (.nat (initialNumerator c))
  have hsI : Inputs ρI c A table r R := hsD.update_gt (by decide) _
  have houter:=outerSum_eval hsI (denominator c) (by simp [ρI,ρD,Function.update]) hT
  rw [outputProgram,BoundedLoop.Expr.eval,hD]
  change (BoundedLoop.Expr.bind 14 initialProgram outputArray).eval ρD=_
  rw [BoundedLoop.Expr.eval,hI]
  change outputArray.eval ρI=_
  simp only [outputArray,BoundedLoop.Expr.eval,List.map_cons,List.map_nil]
  rw [houter]
  simp only [BoundedLoop.Expr.eval,hsI.power,hsI.count]
  simp only [ρI,ρD,Function.update]
  simp only [dif_pos rfl,dif_neg (by decide : (13:ℕ)≠14)]
  rw [powerValue_get_total]
  rfl

/-- This is exactly the integer-only C.8 output, with its real cached inputs. -/
theorem outputPair_source (H : ℕ) (z : List Bool) (R : ℕ) :
    outputPair (makeObservedCache H z) (parseAge 0 z)
      (cachedRun H (makeObservedCache H z) (parseAge 0 z) H)
      (parseGaps 0 z).length R=Paper37.CachedOutput.evaluatePair H z R := rfl

/-- One fixed program computes the actual exact integer output pair. -/
theorem outputProgram_evaluatePair (H : ℕ) (z : List Bool) (R : ℕ)
    (hz : z.length+R≤H) :
    let c:=makeObservedCache H z
    let table:=cachedRun H c (parseAge 0 z) H
    outputProgram.eval (outputEnv c (parseAge 0 z) table (parseGaps 0 z).length R)=
      .array [.nat (Paper37.CachedOutput.evaluatePair H z R).1,
        .nat (Paper37.CachedOutput.evaluatePair H z R).2] := by
  dsimp only
  rw [← outputPair_source]
  exact outputProgram_eval_inputs (outputEnv_inputs _ _ _ _ _)
    (by have hh:=age_le_length z;omega)


/-- Uniformity certificate for the output stage: the existential syntax term
is chosen before the horizon, observed word and query length. The work is the
charge of that same term on those same shared cached inputs. -/
theorem uniform_output_program :
    ∃p : BoundedLoop.Expr, ∀(H : ℕ)(z : List Bool)(R : ℕ),z.length+R≤H →
      let c:=makeObservedCache H z
      let table:=cachedRun H c (parseAge 0 z) H
      let ρ:=outputEnv c (parseAge 0 z) table (parseGaps 0 z).length R
      p.eval ρ=.array [.nat (Paper37.CachedOutput.evaluatePair H z R).1,
        .nat (Paper37.CachedOutput.evaluatePair H z R).2] ∧
        p.work ρ≤200*(H+1)^2 := by
  refine ⟨outputProgram,?_⟩
  intro H z R hz
  dsimp only
  constructor
  · exact outputProgram_evaluatePair H z R hz
  · exact outputProgram_work_quadratic (outputEnv_inputs _ _ _ _ _)
      (by have hh:=age_le_length z;omega)

end Paper37.IntegerOutputProgram

