import Paper37.RefinedCoreProgram
import Paper37.IntegerOutputProgram
import Paper37.AdaptiveIntegerOutput

/-! Fixed finite syntax for extracting every occupied-type restriction from
one materialized table with a common integer denominator. -/
namespace Paper37.RefinedOutputProgram
open Finset Paper37.BoundedLoop Paper37.CachedDP Paper37.CachedOutput
open Paper37.DP Paper37.Envelope Paper37.ContinuationDP Paper37.RefinedContinuation
open Paper37.AdaptiveDP Paper37.AdaptiveIntegerOutput Paper37.CachedRefinedDP
open Paper37.CachedCoreProgram (natArray powerValue observedValue powerValue_get_total fold_add_of)
open Paper37.IntegerOutputProgram (denominatorProgram initialProgram denominatorProgram_eval
  initialProgram_eval observedValue_get sum_range_guard sum_range_succ)
private abbrev v := Expr.var
private abbrev n := Expr.lit
private abbrev add := Expr.add
private abbrev mul := Expr.mul
private abbrev get := Expr.get

structure Inputs {H : ℕ} (ρ : Env) (c : Cache H) (A : ℕ) (table : RefinedLayer H) (r R : ℕ) : Prop where
  horizon : ρ 0=.nat H
  age : ρ 1=.nat A
  power : ρ 3=powerValue c
  observed : ρ 4=observedValue c
  layer : ρ 5=RefinedCoreProgram.layerValue table
  count : ρ 11=.nat r
  remaining : ρ 12=.nat R

lemma Inputs.update_gt {H : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : RefinedLayer H}
    (hs : Inputs ρ c A table r R) {x : ℕ} (hx : 12<x) (a : Value) :
    Inputs (Function.update ρ x a) c A table r R := by
  cases hs
  constructor <;> rw [Function.update_of_ne (by omega)] <;> assumption

def totalFuture : Expr := add (v 1) (v 12)
def observedTypes {H : ℕ} (c : Cache H) : ℕ :=
  ∑ d ∈ gapSet H, if 0<observedAt c d then 1 else 0

def observedTypesProgram : Expr := .fold 19 20 (v 0) (n 0)
  (add (v 20) (.ifLT (n 0) (get (v 4) (add (v 19) (n 1))) (n 1) (n 0)))
def kIndex : Expr := add (v 15) (n 1)
def tableMarked : Expr := get (get (get (get (v 5) kIndex) (v 17)) (v 29)) (n 1)
def prefixSum : Expr := .fold 29 30 (add (v 28) (n 1)) (n 0) (add (v 30) tableMarked)
def finalTerm : Expr := mul (.div prefixSum kIndex)
  (.div (v 13) (get (v 3) (add (v 11) kIndex)))
def guardedTerm : Expr := .ifLT (v 17) kIndex (n 0) finalTerm

def innerSum : Expr := .fold 17 18 (add totalFuture (n 1)) (n 0) (add (v 18) guardedTerm)
def outerSum : Expr := .fold 15 16 totalFuture (n 0) (add (v 16) innerSum)
def numeratorProgram : Expr := add
  (.ifLT (v 28) (v 31) (n 0) (mul (v 14) (.div (v 13) (get (v 3) (v 11))))) outerSum

def outputProgram : Expr := .bind 13 denominatorProgram (.bind 14 initialProgram
  (.bind 31 observedTypesProgram (.tabulate 28 (add (v 0) (n 1)) numeratorProgram)))

def outputValues {H : ℕ} (c : Cache H) (A : ℕ) (table : RefinedLayer H) (r R : ℕ) : Vector ℕ (H+1) :=
  Vector.ofFn fun t =>
    (if observedTypes c≤t.val then initialNumerator c*(denominator c/powerAt c r) else 0)+
      ∑k∈Icc 1 (A+R),∑u∈Icc k (A+R),
        (∑j∈range (t.val+1),(refinedLayerAt table k u j).2)/k*(denominator c/powerAt c (r+k))

lemma observedTypesProgram_eval {H : ℕ} (ρ : Env) (c : Cache H)
    (hH : ρ 0=.nat H) (hc : ρ 4=observedValue c) :
    observedTypesProgram.eval ρ=.nat (observedTypes c) := by
  simp only [observedTypesProgram,Expr.eval,hH,Value.natVal]
  rw [fold_add_of _ (fun i=>if 0<observedAt c (i+1) then 1 else 0) _ (by
    intro i hi a
    have hiH : i+1≤H := by have hh:=List.mem_range.mp hi;omega
    simp only [add,v,Expr.eval]
    simp [Function.update,hc,observedValue_get c (i+1) hiH,Value.natVal]
    split_ifs <;> rfl)]
  simp only [zero_add]
  congr 1
  rw [← List.sum_toFinset _ List.nodup_range]
  simpa only [List.toFinset_range,observedTypes,gapSet] using
    sum_range_succ H (fun d=>if 0<observedAt c d then 1 else 0)

lemma prefixSum_eval {H : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : RefinedLayer H}
    (hs : Inputs ρ c A table r R) (k0 u t : ℕ)
    (hk : ρ 15=.nat k0) (hu : ρ 17=.nat u) (ht : ρ 28=.nat t)
    (hkH : k0+1≤H) (huH : u≤H) (htH : t≤H) :
    prefixSum.eval ρ=.nat (∑j∈range (t+1),(refinedLayerAt table (k0+1) u j).2) := by
  simp only [prefixSum,Expr.eval,ht,Value.natVal]
  rw [fold_add_of _ (fun j=>(refinedLayerAt table (k0+1) u j).2) _ (by
    intro j hj a
    have hjH : j<H+1 := by have hh := List.mem_range.mp hj;omega
    simp only [add,v,Expr.eval]
    have hread : tableMarked.eval (Function.update (Function.update ρ 29 (.nat j)) 30 (.nat a))=
        .nat (refinedLayerAt table (k0+1) u j).2 := by
      simp only [tableMarked,kIndex,Expr.eval]
      simp only [Function.update_of_ne (by decide : (5:ℕ)≠30),Function.update_of_ne (by decide : (5:ℕ)≠29),
        Function.update_of_ne (by decide : (15:ℕ)≠30),Function.update_of_ne (by decide : (15:ℕ)≠29),
        Function.update_of_ne (by decide : (17:ℕ)≠30),Function.update_of_ne (by decide : (17:ℕ)≠29),
        Function.update_of_ne (by decide : (29:ℕ)≠30),Function.update_self,hs.layer,hk,hu,Value.natVal]
      rw [RefinedCoreProgram.layerValue_get table (k0+1) u j (by omega) (by omega) hjH]
      rfl
    rw [hread]
    simp [Function.update,Value.natVal])]
  simp only [zero_add]
  congr 1

lemma finalTerm_eval {H : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : RefinedLayer H}
    (hs : Inputs ρ c A table r R) (D k0 u t : ℕ)
    (hD : ρ 13=.nat D) (hk : ρ 15=.nat k0) (hu : ρ 17=.nat u) (ht : ρ 28=.nat t)
    (hkH : k0+1≤H) (huH : u≤H) (htH : t≤H) :
    finalTerm.eval ρ=.nat ((∑j∈range (t+1),(refinedLayerAt table (k0+1) u j).2)/(k0+1)*
      (D/powerAt c (r+(k0+1)))) := by
  simp only [finalTerm,Expr.eval]
  rw [prefixSum_eval hs k0 u t hk hu ht hkH huH htH]
  simp only [kIndex,Expr.eval,hs.power,hs.count,hD,hk,Value.natVal]
  rw [powerValue_get_total]

lemma guardedTerm_eval {H : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : RefinedLayer H}
    (hs : Inputs ρ c A table r R) (D k0 u t : ℕ)
    (hD : ρ 13=.nat D) (hk : ρ 15=.nat k0) (hu : ρ 17=.nat u) (ht : ρ 28=.nat t)
    (hkH : k0+1≤H) (huH : u≤H) (htH : t≤H) :
    guardedTerm.eval ρ=.nat (if u<k0+1 then 0 else
      (∑j∈range (t+1),(refinedLayerAt table (k0+1) u j).2)/(k0+1)*(D/powerAt c (r+(k0+1)))) := by
  simp only [guardedTerm,Expr.eval,kIndex,hu,hk,Value.natVal]
  split_ifs
  · rfl
  · exact finalTerm_eval hs D k0 u t hD hk hu ht hkH huH htH

lemma innerSum_eval {H : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : RefinedLayer H}
    (hs : Inputs ρ c A table r R) (D k0 t : ℕ)
    (hD : ρ 13=.nat D) (hk : ρ 15=.nat k0) (ht : ρ 28=.nat t)
    (hkT : k0<A+R) (hT : A+R≤H) (htH : t≤H) :
    innerSum.eval ρ=.nat (∑u∈Icc (k0+1) (A+R),
      (∑j∈range (t+1),(refinedLayerAt table (k0+1) u j).2)/(k0+1)*(D/powerAt c (r+(k0+1)))) := by
  have hbound : (totalFuture.eval ρ).natVal=A+R := by
    simp [totalFuture,Expr.eval,hs.age,hs.remaining,Value.natVal]
  simp only [innerSum,Expr.eval]
  change (List.range ((totalFuture.eval ρ).natVal+1)).foldl _ (Value.nat 0)=_
  rw [hbound]
  rw [fold_add_of _ (fun u=>if u<k0+1 then 0 else
      (∑j∈range (t+1),(refinedLayerAt table (k0+1) u j).2)/(k0+1)*(D/powerAt c (r+(k0+1)))) _ (by
    intro u hu a
    have huH : u≤H := by have hh:=List.mem_range.mp hu;omega
    have hs' := (hs.update_gt (x:=17) (by decide) (.nat u)).update_gt (x:=18) (by decide) (.nat a)
    have hterm := guardedTerm_eval hs' D k0 u t
      (by simp [Function.update,hD]) (by simp [Function.update,hk]) (by simp [Function.update])
      (by simp [Function.update,ht]) (by omega) huH htH
    simp only [add,v,Expr.eval]
    rw [hterm]
    simp [Function.update,Value.natVal])]
  simp only [zero_add]
  congr 1
  rw [← List.sum_toFinset _ List.nodup_range]
  simpa only [List.toFinset_range] using sum_range_guard (A+R) (k0+1)
    (fun u=>(∑j∈range (t+1),(refinedLayerAt table (k0+1) u j).2)/(k0+1)*(D/powerAt c (r+(k0+1))))

lemma outerSum_eval {H : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : RefinedLayer H}
    (hs : Inputs ρ c A table r R) (D t : ℕ) (hD : ρ 13=.nat D) (ht : ρ 28=.nat t)
    (hT : A+R≤H) (htH : t≤H) :
    outerSum.eval ρ=.nat (∑k∈Icc 1 (A+R),∑u∈Icc k (A+R),
      (∑j∈range (t+1),(refinedLayerAt table k u j).2)/k*(D/powerAt c (r+k))) := by
  have hbound : (totalFuture.eval ρ).natVal=A+R := by
    simp [totalFuture,Expr.eval,hs.age,hs.remaining,Value.natVal]
  simp only [outerSum,Expr.eval,hbound]
  rw [fold_add_of _ (fun k0=>∑u∈Icc (k0+1) (A+R),
      (∑j∈range (t+1),(refinedLayerAt table (k0+1) u j).2)/(k0+1)*(D/powerAt c (r+(k0+1)))) _ (by
    intro k0 hk a
    have hs' := (hs.update_gt (x:=15) (by decide) (.nat k0)).update_gt (x:=16) (by decide) (.nat a)
    have hinner := innerSum_eval hs' D k0 t (by simp [Function.update,hD])
      (by simp [Function.update]) (by simp [Function.update,ht]) (List.mem_range.mp hk) hT htH
    simp only [add,v,Expr.eval]
    rw [hinner]
    simp [Function.update,Value.natVal])]
  simp only [zero_add]
  congr 1
  rw [← List.sum_toFinset _ List.nodup_range]
  simpa only [List.toFinset_range] using sum_range_succ (A+R)
    (fun k=>∑u∈Icc k (A+R),(∑j∈range (t+1),(refinedLayerAt table k u j).2)/k*(D/powerAt c (r+k)))

theorem outputProgram_eval_inputs {H : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : RefinedLayer H}
    (hs : Inputs ρ c A table r R) (hT : A+R≤H) :
    outputProgram.eval ρ=natArray (outputValues c A table r R) := by
  have hD:=denominatorProgram_eval ρ c hs.horizon hs.power
  let ρD:=Function.update ρ 13 (.nat (denominator c))
  have hsD : Inputs ρD c A table r R := hs.update_gt (by decide) _
  have hI:=initialProgram_eval ρD c hsD.horizon hsD.power hsD.observed
  let ρI:=Function.update ρD 14 (.nat (initialNumerator c))
  have hsI : Inputs ρI c A table r R := hsD.update_gt (by decide) _
  have hO:=observedTypesProgram_eval ρI c hsI.horizon hsI.observed
  let ρO:=Function.update ρI 31 (.nat (observedTypes c))
  have hsO : Inputs ρO c A table r R := hsI.update_gt (by decide) _
  rw [outputProgram,Expr.eval,hD]
  change (Expr.bind 14 initialProgram _).eval ρD=_
  rw [Expr.eval,hI]
  change (Expr.bind 31 observedTypesProgram _).eval ρI=_
  rw [Expr.eval,hO]
  change (Expr.tabulate 28 (add (v 0) (n 1)) numeratorProgram).eval ρO=_
  simp only [Expr.eval,hsO.horizon,Value.natVal,natArray,outputValues]
  congr 1
  apply List.map_congr_left
  intro t ht
  have htH : t<H+1 := List.mem_range.mp ht
  let ρt:=Function.update ρO 28 (.nat t)
  have hst : Inputs ρt c A table r R := hsO.update_gt (by decide) _
  have houter:=outerSum_eval hst (denominator c) t (by simp [ρt,ρO,ρI,ρD,Function.update])
    (by simp [ρt]) hT (by omega)
  have ht28 : ρt 28=.nat t := by simp [ρt]
  have ht31 : ρt 31=.nat (observedTypes c) := by simp [ρt,ρO]
  have ht14 : ρt 14=.nat (initialNumerator c) := by simp [ρt,ρO,ρI]
  have ht13 : ρt 13=.nat (denominator c) := by simp [ρt,ρO,ρI,ρD]
  change numeratorProgram.eval ρt=_
  simp only [numeratorProgram,Expr.eval,houter,ht28,ht31,ht14,ht13,hst.power,hst.count,
    Value.natVal,Vector.getElem_ofFn,dif_pos htH]
  rw [powerValue_get_total]
  by_cases ho:observedTypes c≤t <;> simp [ho,show (t<observedTypes c)↔¬observedTypes c≤t by omega]

lemma observedTypes_source (H : ℕ) (z : List Bool) (hz : z.length≤H) :
    observedTypes (makeObservedCache H z)=Paper37.Adaptive.nu z := by
  rw [← Paper37.AdaptiveContinuation.occupied_observed_zero H z hz]
  unfold observedTypes occupied
  rw [card_eq_sum_ones,sum_filter]
  apply sum_congr rfl
  intro d hd
  rw [observedAt_source H z d (mem_Icc.mp hd).2]
  simp

theorem outputValues_source (H : ℕ) (z : List Bool) (R : ℕ) (hz : z.length≤H) :
    outputValues (makeObservedCache H z) (parseAge 0 z)
      (cachedRefinedRun H (makeObservedCache H z) (parseAge 0 z) H)
      (parseGaps 0 z).length R=allNumerators H z R := by
  unfold outputValues allNumerators
  dsimp only
  rw [observedTypes_source H z hz]
  rfl

end Paper37.RefinedOutputProgram
