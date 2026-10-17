import Paper37.IntegerOutputProgram
import Paper37.BoundedLoopSize
import Paper37.BoundedLoopFlat

/-! Dynamic intermediate-size bounds for the fixed integer output program.
The range-loop invariant follows the actual running accumulator at every
visited index; no execution trace or cost is supplied as an assumption. -/
namespace Paper37.IntegerOutputPeak
open scoped BigOperators
open Paper37.BoundedLoop Paper37.IntegerOutputProgram Paper37.CachedDP
open Paper37.CachedCoreProgram Paper37.CachedOutput Paper37.IntegerOutput
open Paper37.DP Paper37.ContinuationDP Paper37.Envelope

/-- Indexed invariant and maximum-cost bound for an actual increasing range
fold. The cost may depend on the current value, not merely on the index. -/
lemma range_foldl_peak_le (n : ℕ) (step : Value → ℕ → Value) (cost : Value → ℕ → ℕ)
    (I : ℕ → Value → Prop) (B : ℕ)
    (hstep : ∀j<n,∀v,I j v → I (j+1) (step v j))
    (hcost : ∀j<n,∀v,I j v → cost v j≤B)
    (v : Value) (hv : I 0 v) (p : ℕ) (hp : p≤B) :
    let out:=(List.range n).foldl (fun vp j=>(step vp.1 j,max vp.2 (cost vp.1 j))) (v,p)
    I n out.1 ∧ out.2≤B := by
  induction n with
  | zero => simpa using And.intro hv hp
  | succ n ih =>
    have hh:=ih (fun j hj=>hstep j (by omega)) (fun j hj=>hcost j (by omega))
    simp only [List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
    exact ⟨hstep n (by omega) _ hh.1,max_le hh.2 (hcost n (by omega) _ hh.1)⟩

/-- A natural cap for every scalar in the output stage, polynomial in the
input magnitude B at exponent O(H). Its binary length is polynomial in H and
in the binary length of B. -/
def scalarCap (H B : ℕ) : ℕ := (H+1)^2*B^(2*H+2)

def CacheBound {H : ℕ} (c : Cache H) (table : Layer H) (B : ℕ) : Prop :=
  (∀i,powerAt c i≤B) ∧
    (∀i≤H,observedAt c i≤B) ∧
    (∀k≤H,∀u≤H,(layerAt table k u).2≤B)

lemma product_prefix_le (H j : ℕ) (c : Cache H) (B : ℕ)
    (hpow : ∀i,powerAt c i≤B) :
    (∏i∈Finset.range j,powerAt c (i+1))≤B^j := by
  calc
    _ ≤ ∏_i∈Finset.range j,B := Finset.prod_le_prod' (fun i _=>hpow (i+1))
    _ = _ := by simp

lemma initial_prefix_le (H j : ℕ) (c : Cache H) (B : ℕ)
    (hpow : ∀i,powerAt c i≤B) :
    (∏i∈Finset.range j,powerAt c (observedAt c (i+1)))≤B^j := by
  calc
    _ ≤ ∏_i∈Finset.range j,B := Finset.prod_le_prod' (fun i _=>hpow (observedAt c (i+1)))
    _ = _ := by simp

lemma denominator_le {H B : ℕ} (c : Cache H) (hpow : ∀i,powerAt c i≤B) :
    denominator c≤B^H := by
  rw [denominator,← prod_range_succ]
  exact product_prefix_le H H c B hpow

lemma initial_le {H B : ℕ} (c : Cache H) (hpow : ∀i,powerAt c i≤B) :
    initialNumerator c≤B^H := by
  rw [initialNumerator,gapSet,← prod_range_succ]
  exact initial_prefix_le H H c B hpow

lemma scaled_term_le {H B : ℕ} (c : Cache H) (table : Layer H) (r k u D : ℕ)
    (hD : D≤B^H) (hS : (layerAt table k u).2≤B) :
    (layerAt table k u).2/k*(D/powerAt c (r+k))≤B^(H+1) := by
  calc
    _ ≤ B*B^H := Nat.mul_le_mul ((Nat.div_le_self _ _).trans hS)
      ((Nat.div_le_self _ _).trans hD)
    _ = _ := by rw [pow_succ];ring

lemma scalarCap_mono_power {H B e : ℕ} (hB : 1≤B) (he : e≤2*H+2) :
    B^e≤scalarCap H B := by
  exact (Nat.pow_le_pow_right hB he).trans
    (Nat.le_mul_of_pos_left _ (by positivity))

lemma scalarCap_ge_base {H B : ℕ} (hB : 1≤B) : B≤scalarCap H B := by
  simpa only [pow_one] using scalarCap_mono_power (H:=H) hB (e:=1) (by omega)

lemma scalarCap_binarySize (H B : ℕ) :
    (scalarCap H B).size≤2*(H+1).size+(2*H+2)*B.size+3 := by
  unfold scalarCap
  have hm:=size_mul_le ((H+1)^2) (B^(2*H+2))
  have h1:=binarySize_le_of_le_pow ((H+1)^2) (H+1) 2 le_rfl
  have h2:=binarySize_le_of_le_pow (B^(2*H+2)) B (2*H+2) le_rfl
  omega

/-- Polynomial scalar-bit bound once the materialized input integers have a
polynomial bit bound. This bounds intermediate values, not just final output. -/
lemma scalarCap_binarySize_polynomial (H B L : ℕ) (hB : B.size≤L) :
    (scalarCap H B).size≤2*(H+1)+(2*H+2)*L+3 := by
  have h:=scalarCap_binarySize H B
  have hs:=binarySize_le_self (H+1)
  have hp:=Nat.mul_le_mul_left (2*H+2) hB
  omega


/-- Uniform scalar magnitude of all actual source cache/table entries. -/
def baseCap (H : ℕ) : ℕ := (2*H)^(4*H+2)
def baseBits (H : ℕ) : ℕ := (4*H+2)*(2*H).size+1

lemma baseCap_binarySize (H : ℕ) : (baseCap H).size≤baseBits H :=
  binarySize_le_of_le_pow _ _ _ le_rfl

lemma baseCap_ge {H : ℕ} (hH : 0<H) : 2*H+1≤baseCap H := by
  calc
    _ ≤ (2*H)^2 := by nlinarith
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

lemma source_power_bound (H : ℕ) (z : List Bool) (hH : 0<H) (i : ℕ) :
    powerAt (makeObservedCache H z) i≤baseCap H := by
  by_cases hi : i≤2*H
  · rw [makeObservedCache_eq,powerAt_correct H _ i hi]
    calc
      _ ≤ (2*H)^i := Nat.pow_le_pow_left hi _
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  · simp [powerAt,show ¬i<2*H+1 by omega]

lemma source_observed_bound (H : ℕ) (z : List Bool) (hz : z.length≤H) (i : ℕ) (hi : i≤H) :
    observedAt (makeObservedCache H z) i≤H := by
  rw [observedAt_source H z i hi]
  exact observedCounts_le_horizon H z hz i hi

lemma source_marked_bound (H : ℕ) (z : List Bool) (A : ℕ) (hH : 0<H)
    (hz : z.length≤H) (k u : ℕ) (hk : k≤H) (hu : u≤H) :
    (layerAt (cachedRun H (makeObservedCache H z) A H) k u).2≤baseCap H := by
  rw [makeObservedCache_eq,cachedRun_correct H _ A H le_rfl (observedCounts_le_horizon H z hz),
    layerAt_run H _ A H k u hk hu]
  change S (observedCounts z) (gapSet H) A k u≤baseCap H
  have hs : (gapSet H).sum (observedCounts z)+k≤2*H := by
    rw [observed_sum H z hz]
    have hh:=count_add_age_le z
    omega
  have hc : (gapSet H).card≤2*H := by simp [gapSet,Nat.card_Icc];omega
  exact (S_le_power _ _ _ _ _ (2*H) (by omega) hc hs).trans
    (Nat.pow_le_pow_right (by omega) (by omega))

lemma source_cacheBound (H : ℕ) (z : List Bool) (A : ℕ) (hH : 0<H) (hz : z.length≤H) :
    CacheBound (makeObservedCache H z)
      (cachedRun H (makeObservedCache H z) A H) (baseCap H) := by
  refine ⟨source_power_bound H z hH,?_,fun k hk u hu=>source_marked_bound H z A hH hz k u hk hu⟩
  intro i hi
  exact (source_observed_bound H z hz i hi).trans (by have hh:=baseCap_ge hH;omega)

lemma sum_map_le {α : Type*} (xs : List α) (f : α → ℕ) (M : ℕ)
    (hf : ∀x∈xs,f x≤M) : (xs.map f).sum≤xs.length*M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx:=hf x (by simp)
    have hh:=ih (fun y hy=>hf y (by simp [hy]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

lemma natArray_representation {m L : ℕ} (a : Vector ℕ m)
    (ha : ∀i : Fin m,(a[i.val]).size≤L) :
    (natArray a).representationSize≤m*(L+1)+2 := by
  simp only [natArray,Value.representationSize,List.map_map]
  apply Nat.add_le_add_right
  have hh:=sum_map_le (List.range m)
    (fun i=>(Value.nat (if hi:i<m then a[i] else 0)).representationSize) (L+1) (by
      intro i hi
      have him:=List.mem_range.mp hi
      simp only [dif_pos him,Value.representationSize]
      exact Nat.add_le_add_right (ha ⟨i,him⟩) 1)
  simpa only [List.length_range] using hh

lemma source_power_representation (H : ℕ) (z : List Bool) (hH : 0<H) :
    (powerValue (makeObservedCache H z)).representationSize≤(2*H+1)*(baseBits H+1)+2 := by
  apply natArray_representation
  intro i
  have hi : i.val≤2*H := by omega
  have he : (makeObservedCache H z).power[i.val]=powerAt (makeObservedCache H z) i.val := by
    simp only [powerAt,dif_pos (show i.val<2*H+1 from i.isLt)]
  rw [he]
  exact (Nat.size_le_size (source_power_bound H z hH i.val)).trans (baseCap_binarySize H)

lemma source_observed_representation (H : ℕ) (z : List Bool) (hz : z.length≤H) :
    (observedValue (makeObservedCache H z)).representationSize≤(H+1)*(H+1)+2 := by
  apply natArray_representation
  intro i
  have hi : i.val≤H := by omega
  have he : (makeObservedCache H z).observed[i.val]=observedAt (makeObservedCache H z) i.val := by
    simp only [observedAt,dif_pos (show i.val<H+1 from i.isLt)]
  rw [he]
  exact (binarySize_le_self _).trans (source_observed_bound H z hz i.val hi)

lemma source_layer_representation (H : ℕ) (z : List Bool) (A : ℕ)
    (hH : 0<H) (hz : z.length≤H) :
    (layerValue (cachedRun H (makeObservedCache H z) A H)).representationSize≤
      (H+1)*((H+1)*(2*baseBits H+4)+2)+2 := by
  let table:=cachedRun H (makeObservedCache H z) A H
  have hentry (k u : ℕ) (hk : k≤H) (hu : u≤H) :
      (layerAt table k u).1.size≤baseBits H ∧ (layerAt table k u).2.size≤baseBits H := by
    have hh:=cachedRun_binarySize H z A H ⟨k,by omega⟩ ⟨u,by omega⟩ hH le_rfl hz
      (by rw [observed_sum H z hz];have hh:=count_add_age_le z;omega)
    have he : layerAt table k u=table[k][u] := by simp [layerAt,show k<H+1 by omega,show u<H+1 by omega]
    rw [he]
    dsimp [baseBits]
    constructor
    · exact hh.1.trans (by nlinarith)
    · exact hh.2.trans (by nlinarith)
  simp only [layerValue,Value.representationSize,List.map_map]
  apply Nat.add_le_add_right
  have hrow (k : ℕ) (hk : k<H+1) :
      (Value.array ((List.range (H+1)).map fun u=>
        Value.array [.nat (layerAt table k u).1,.nat (layerAt table k u).2])).representationSize≤
          (H+1)*(2*baseBits H+4)+2 := by
    simp only [Value.representationSize,List.map_map]
    apply Nat.add_le_add_right
    have hh:=sum_map_le (List.range (H+1))
      (fun u=>(Value.array [.nat (layerAt table k u).1,.nat (layerAt table k u).2]).representationSize)
      (2*baseBits H+4) (by
        intro u hu
        have he:=hentry k u (by omega) (by have hh:=List.mem_range.mp hu;omega)
        simp only [Value.representationSize,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
        omega)
    simpa only [List.length_range] using hh
  have hh:=sum_map_le (List.range (H+1))
    (fun k=>(Value.array ((List.range (H+1)).map fun u=>
      Value.array [.nat (layerAt table k u).1,.nat (layerAt table k u).2])).representationSize)
    ((H+1)*(2*baseBits H+4)+2) (fun k hk=>hrow k (List.mem_range.mp hk))
  simpa only [List.length_range] using hh


lemma pair_fold_fst (xs : List ℕ) (step : Value → ℕ → Value)
    (cost : Value → ℕ → ℕ) (v : Value) (p : ℕ) :
    (xs.foldl (fun vp j=>(step vp.1 j,max vp.2 (cost vp.1 j))) (v,p)).1=xs.foldl step v := by
  induction xs generalizing v p with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons];exact ih _ _

/-- A peak rule for the actual range fold with an indexed value invariant. -/
lemma fold_peak_bound (ρ : Env) (i a : ℕ) (bound init body : BoundedLoop.Expr)
    (n P : ℕ) (I : ℕ → Value → Prop)
    (hn : (bound.eval ρ).natVal=n) (hb : bound.peak ρ≤P) (hi : init.peak ρ≤P)
    (hstart : I 0 (init.eval ρ))
    (hstep : ∀j<n,∀v,I j v → I (j+1)
      (body.eval (Function.update (Function.update ρ i (.nat j)) a v)))
    (hbody : ∀j<n,∀v,I j v → body.peak (Function.update (Function.update ρ i (.nat j)) a v)≤P)
    (hend : ∀v,I n v → v.representationSize≤P) :
    (BoundedLoop.Expr.fold i a bound init body).peak ρ≤P := by
  let step:=fun v j=>body.eval (Function.update (Function.update ρ i (.nat j)) a v)
  let cost:=fun v j=>body.peak (Function.update (Function.update ρ i (.nat j)) a v)
  have hh:=range_foldl_peak_le n step cost I P hstep hbody (init.eval ρ) hstart 0 (by omega)
  have hval : ((List.range n).foldl step (init.eval ρ)).representationSize≤P := by
    have hh':=hend _ hh.1
    rw [pair_fold_fst] at hh'
    exact hh'
  rw [BoundedLoop.Expr.peak]
  apply max_le
  · simpa only [BoundedLoop.Expr.eval,hn] using hval
  · exact max_le hb (max_le hi (by simpa only [hn] using hh.2))

lemma bind_peak_bound (ρ : Env) (x : ℕ) (a b : BoundedLoop.Expr) (P : ℕ)
    (ha : a.peak ρ≤P) (hb : b.peak (Function.update ρ x (a.eval ρ))≤P) :
    (BoundedLoop.Expr.bind x a b).peak ρ≤P := by
  have hr:=representationSize_le_peak b (Function.update ρ x (a.eval ρ))
  rw [BoundedLoop.Expr.peak,BoundedLoop.Expr.eval]
  exact max_le (hr.trans hb) (max_le ha hb)

lemma nat_rep_le {H B P x : ℕ} (hP : (scalarCap H B).size+1≤P) (hx : x≤scalarCap H B) :
    (Value.nat x).representationSize≤P := by
  simpa only [Value.representationSize] using (Nat.add_le_add_right (Nat.size_le_size hx) 1).trans hP

lemma nat_control_rep {H B P x : ℕ} (hB : 2*H+1≤B)
    (hP : (scalarCap H B).size+1≤P) (hx : x≤2*H+1) :
    (Value.nat x).representationSize≤P :=
  nat_rep_le hP ((hx.trans hB).trans (scalarCap_ge_base (by omega)))

lemma prefix_rep {H B P j x : ℕ} (hB : 1≤B)
    (hP : (scalarCap H B).size+1≤P) (hj : j≤H) (hx : x≤B^j) :
    (Value.nat x).representationSize≤P :=
  nat_rep_le hP (hx.trans (scalarCap_mono_power hB (by omega)))

lemma sum_acc_le_cap {H B j x : ℕ} (hB : 1≤B) (hj : j≤H+1)
    (hx : x≤j*B^(H+1)) : x≤scalarCap H B := by
  calc
    _ ≤ (H+1)*B^(H+1) := hx.trans (Nat.mul_le_mul_right _ hj)
    _ ≤ (H+1)^2*B^(H+1) := Nat.mul_le_mul_right _ (by nlinarith)
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB (by omega))

lemma outer_acc_le_cap {H B j x : ℕ} (hB : 1≤B) (hj : j≤H+1)
    (hx : x≤j*(H+1)*B^(H+1)) : x≤scalarCap H B := by
  calc
    _ ≤ (H+1)*(H+1)*B^(H+1) := hx.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hj))
    _ = (H+1)^2*B^(H+1) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hB (by omega))

private def dBody : BoundedLoop.Expr :=
  .mul (.var 20) (.get (.var 3) productIndex)
private def iBody : BoundedLoop.Expr :=
  .mul (.var 20) (.get (.var 3) (.get (.var 4) productIndex))
private def sumBody : BoundedLoop.Expr := .add (.var 18) guardedTerm

private lemma dBody_flat : Flat dBody := by
  unfold dBody productIndex
  repeat' first | apply Flat.binary .mul | apply Flat.binary .add | apply Flat.get | apply Flat.var | apply Flat.lit
private lemma iBody_flat : Flat iBody := by
  unfold iBody productIndex
  repeat' first | apply Flat.binary .mul | apply Flat.binary .add | apply Flat.get | apply Flat.var | apply Flat.lit
private lemma sumBody_flat : Flat sumBody := by
  unfold sumBody guardedTerm finalTerm tableMarked kIndex
  repeat' first | apply Flat.binary .mul | apply Flat.binary .add | apply Flat.binary .div |
    apply Flat.get | apply Flat.ifLT | apply Flat.var | apply Flat.lit

lemma dBody_peak (ρ : Env) (P : ℕ) (hv : dBody.varsBound ρ P) : dBody.peak ρ≤4000*(P+1) := by
  have h:=flat_peak_le dBody_flat ρ P hv
  apply h.trans
  norm_num [dBody,productIndex,BoundedLoop.Expr.flatBudget]
  omega
lemma iBody_peak (ρ : Env) (P : ℕ) (hv : iBody.varsBound ρ P) : iBody.peak ρ≤4000*(P+1) := by
  have h:=flat_peak_le iBody_flat ρ P hv
  apply h.trans
  norm_num [iBody,productIndex,BoundedLoop.Expr.flatBudget]
  omega
lemma sumBody_peak (ρ : Env) (P : ℕ) (hv : sumBody.varsBound ρ P) : sumBody.peak ρ≤4000*(P+1) := by
  have h:=flat_peak_le sumBody_flat ρ P hv
  apply h.trans
  norm_num [sumBody,guardedTerm,finalTerm,tableMarked,kIndex,BoundedLoop.Expr.flatBudget]
  omega


lemma denominator_peak {H B P : ℕ} (ρ : Env) (c : Cache H)
    (hH : ρ 0=.nat H) (hp : ρ 3=powerValue c)
    (hpow : ∀i,powerAt c i≤B) (hpr : (powerValue c).representationSize≤P)
    (hB : 2*H+1≤B) (hP : (scalarCap H B).size+1≤P) :
    denominatorProgram.peak ρ≤4000*(P+1) := by
  have hB1 : 1≤B := by omega
  rw [denominatorProgram]
  apply fold_peak_bound ρ 19 20 (.var 0) (.lit 1) dBody H (4000*(P+1))
    (fun j v=>∃a,v=.nat a ∧ a≤B^j)
  · simp [BoundedLoop.Expr.eval,hH,Value.natVal]
  · have hh:=nat_control_rep hB hP (x:=H) (by omega)
    simp only [BoundedLoop.Expr.peak,BoundedLoop.Expr.eval,hH,Nat.max_zero]
    omega
  · have hh:=nat_control_rep hB hP (x:=1) (by omega)
    simp only [BoundedLoop.Expr.peak,BoundedLoop.Expr.eval,Nat.max_zero]
    omega
  · simp [BoundedLoop.Expr.eval]
  · intro j hj v hv
    obtain ⟨a,rfl,ha⟩:=hv
    refine ⟨a*powerAt c (j+1),?_,?_⟩
    · simp [dBody,productIndex,BoundedLoop.Expr.eval,Function.update,hp,powerValue_get_total,Value.natVal]
    · exact (Nat.mul_le_mul ha (hpow (j+1))).trans_eq (by rw [pow_succ])
  · intro j hj v hv
    obtain ⟨a,rfl,ha⟩:=hv
    have hacc:=prefix_rep hB1 hP (by omega : j≤H) ha
    have hidx:=nat_control_rep hB hP (x:=j) (by omega)
    apply dBody_peak
    simp [dBody,productIndex,BoundedLoop.Expr.varsBound,Function.update,hp,hacc,hidx,hpr]
  · intro v hv
    obtain ⟨a,rfl,ha⟩:=hv
    exact (prefix_rep hB1 hP (j:=H) le_rfl ha).trans (by omega)

lemma initial_peak {H B P : ℕ} (ρ : Env) (c : Cache H)
    (hH : ρ 0=.nat H) (hp : ρ 3=powerValue c) (hc : ρ 4=observedValue c)
    (hpow : ∀i,powerAt c i≤B) (hpr : (powerValue c).representationSize≤P)
    (hcr : (observedValue c).representationSize≤P)
    (hB : 2*H+1≤B) (hP : (scalarCap H B).size+1≤P) :
    initialProgram.peak ρ≤4000*(P+1) := by
  have hB1 : 1≤B := by omega
  rw [initialProgram]
  apply fold_peak_bound ρ 19 20 (.var 0) (.lit 1) iBody H (4000*(P+1))
    (fun j v=>∃a,v=.nat a ∧ a≤B^j)
  · simp [BoundedLoop.Expr.eval,hH,Value.natVal]
  · have hh:=nat_control_rep hB hP (x:=H) (by omega)
    simp only [BoundedLoop.Expr.peak,BoundedLoop.Expr.eval,hH,Nat.max_zero]
    omega
  · have hh:=nat_control_rep hB hP (x:=1) (by omega)
    simp only [BoundedLoop.Expr.peak,BoundedLoop.Expr.eval,Nat.max_zero]
    omega
  · simp [BoundedLoop.Expr.eval]
  · intro j hj v hv
    obtain ⟨a,rfl,ha⟩:=hv
    refine ⟨a*powerAt c (observedAt c (j+1)),?_,?_⟩
    · simp [iBody,productIndex,BoundedLoop.Expr.eval,Function.update,hp,hc,
        observedValue_get c (j+1) (by omega),powerValue_get_total,Value.natVal]
    · exact (Nat.mul_le_mul ha (hpow _)).trans_eq (by rw [pow_succ])
  · intro j hj v hv
    obtain ⟨a,rfl,ha⟩:=hv
    have hacc:=prefix_rep hB1 hP (by omega : j≤H) ha
    have hidx:=nat_control_rep hB hP (x:=j) (by omega)
    apply iBody_peak
    simp [iBody,productIndex,BoundedLoop.Expr.varsBound,Function.update,hp,hc,hacc,hidx,hpr,hcr]
  · intro v hv
    obtain ⟨a,rfl,ha⟩:=hv
    exact (prefix_rep hB1 hP (j:=H) le_rfl ha).trans (by omega)


lemma var_peak_of_rep (ρ : Env) (x P : ℕ) (h : (ρ x).representationSize≤P) :
    (BoundedLoop.Expr.var x).peak ρ≤P := by
  simpa only [BoundedLoop.Expr.peak,BoundedLoop.Expr.eval,Nat.max_zero] using h
lemma lit_peak_of_rep (ρ : Env) (x P : ℕ) (h : (Value.nat x).representationSize≤P) :
    (BoundedLoop.Expr.lit x).peak ρ≤P := by
  simpa only [BoundedLoop.Expr.peak,BoundedLoop.Expr.eval,Nat.max_zero] using h

lemma future_peak {H B P : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : Layer H}
    (hs : Inputs ρ c A table r R) (hT : A+R≤H) (hB : 2*H+1≤B)
    (hP : (scalarCap H B).size+1≤P) : totalFuture.peak ρ≤4000*(P+1) := by
  have ha:=nat_control_rep hB hP (x:=A) (by omega)
  have hr:=nat_control_rep hB hP (x:=R) (by omega)
  have h:=binary_peak_le .add (.var 1) (.var 12) ρ P P
    (var_peak_of_rep ρ 1 P (by rw [hs.age];exact ha))
    (var_peak_of_rep ρ 12 P (by rw [hs.remaining];exact hr))
  exact h.trans (by omega)

lemma inner_bound_peak {H B P : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : Layer H}
    (hs : Inputs ρ c A table r R) (hT : A+R≤H) (hB : 2*H+1≤B)
    (hP : (scalarCap H B).size+1≤P) :
    (BoundedLoop.Expr.add totalFuture (.lit 1)).peak ρ≤4000*(P+1) := by
  have ha:=nat_control_rep hB hP (x:=A) (by omega)
  have hr:=nat_control_rep hB hP (x:=R) (by omega)
  have he : Flat (BoundedLoop.Expr.add totalFuture (.lit 1)) := by
    unfold totalFuture
    repeat' first | apply Flat.binary .add | apply Flat.var | apply Flat.lit
  have h:=flat_peak_le he ρ P (by
    simp [totalFuture,BoundedLoop.Expr.varsBound,hs.age,hs.remaining,ha,hr])
  apply h.trans
  norm_num [totalFuture,BoundedLoop.Expr.flatBudget]
  omega

lemma inner_peak {H B P : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : Layer H}
    (hs : Inputs ρ c A table r R) (D k0 : ℕ)
    (hD : ρ 13=.nat D) (hk : ρ 15=.nat k0) (hDs : D≤B^H)
    (hT : A+R≤H) (hkT : k0<A+R) (hr : r≤H)
    (hmarked : ∀k≤H,∀u≤H,(layerAt table k u).2≤B)
    (hpr : (powerValue c).representationSize≤P) (htr : (layerValue table).representationSize≤P)
    (hB : 2*H+1≤B) (hP : (scalarCap H B).size+1≤P) :
    innerSum.peak ρ≤4000*(P+1) := by
  have hB1 : 1≤B := by omega
  have hDr:=prefix_rep hB1 hP (j:=H) le_rfl hDs
  have hkr:=nat_control_rep hB hP (x:=k0) (by omega)
  have hrr:=nat_control_rep hB hP (x:=r) (by omega)
  rw [innerSum]
  apply fold_peak_bound ρ 17 18 (.add totalFuture (.lit 1)) (.lit 0) sumBody (A+R+1)
    (4000*(P+1)) (fun j v=>∃a,v=.nat a ∧ a≤j*B^(H+1))
  · simp [totalFuture,BoundedLoop.Expr.eval,hs.age,hs.remaining,Value.natVal]
  · exact inner_bound_peak hs hT hB hP
  · exact (lit_peak_of_rep ρ 0 P (nat_control_rep hB hP (by omega))).trans (by omega)
  · simp [BoundedLoop.Expr.eval]
  · intro j hj v hv
    obtain ⟨a,rfl,ha⟩:=hv
    let t:=if j<k0+1 then 0 else (layerAt table (k0+1) j).2/(k0+1)*(D/powerAt c (r+(k0+1)))
    have ht : t≤B^(H+1) := by
      dsimp [t]
      split_ifs
      · exact Nat.zero_le _
      · exact scaled_term_le c table r (k0+1) j D hDs (hmarked _ (by omega) _ (by omega))
    have hs' := (hs.update_gt (x:=17) (by decide) (.nat j)).update_gt (x:=18) (by decide) (.nat a)
    have he:=guardedTerm_eval hs' D k0 j (by simp [Function.update,hD])
      (by simp [Function.update,hk]) (by simp [Function.update]) (by omega) (by omega)
    refine ⟨a+t,?_,by nlinarith⟩
    simp only [sumBody,BoundedLoop.Expr.eval]
    rw [he]
    simp [t,Function.update,Value.natVal]
  · intro j hj v hv
    obtain ⟨a,rfl,ha⟩:=hv
    have hacc:=nat_rep_le hP (sum_acc_le_cap hB1 (by omega : j≤H+1) ha)
    have hidx:=nat_control_rep hB hP (x:=j) (by omega)
    apply sumBody_peak
    simp [sumBody,guardedTerm,finalTerm,tableMarked,kIndex,BoundedLoop.Expr.varsBound,
      Function.update,hs.power,hs.layer,hs.count,hD,hk,hDr,hkr,hrr,hacc,hidx,hpr,htr]
  · intro v hv
    obtain ⟨a,rfl,ha⟩:=hv
    exact (nat_rep_le hP (sum_acc_le_cap hB1 (by omega : A+R+1≤H+1) ha)).trans (by omega)

lemma inner_value_le {H B : ℕ} (c : Cache H) (table : Layer H) (r D k T : ℕ)
    (hD : D≤B^H) (hk : k≤H) (hT : T≤H)
    (hmarked : ∀k≤H,∀u≤H,(layerAt table k u).2≤B) :
    (∑u∈Finset.Icc k T,(layerAt table k u).2/k*(D/powerAt c (r+k)))≤(H+1)*B^(H+1) := by
  calc
    _ ≤ (Finset.Icc k T).card*B^(H+1) := Finset.sum_le_card_nsmul _ _ _ (by
      intro u hu
      exact scaled_term_le c table r k u D hD (hmarked _ hk _ ((Finset.mem_Icc.mp hu).2.trans hT)))
    _ ≤ _ := Nat.mul_le_mul_right _ (by simp only [Nat.card_Icc];omega)

lemma outer_peak {H B P : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : Layer H}
    (hs : Inputs ρ c A table r R) (D : ℕ) (hD : ρ 13=.nat D) (hDs : D≤B^H)
    (hT : A+R≤H) (hr : r≤H)
    (hmarked : ∀k≤H,∀u≤H,(layerAt table k u).2≤B)
    (hpr : (powerValue c).representationSize≤P) (htr : (layerValue table).representationSize≤P)
    (hB : 2*H+1≤B) (hP : (scalarCap H B).size+1≤P) :
    outerSum.peak ρ≤10000*(P+1) := by
  have hB1 : 1≤B := by omega
  rw [outerSum]
  apply fold_peak_bound ρ 15 16 totalFuture (.lit 0) (.add (.var 16) innerSum) (A+R)
    (10000*(P+1)) (fun j v=>∃a,v=.nat a ∧ a≤j*(H+1)*B^(H+1))
  · simp [totalFuture,BoundedLoop.Expr.eval,hs.age,hs.remaining,Value.natVal]
  · exact (future_peak hs hT hB hP).trans (by omega)
  · exact (lit_peak_of_rep ρ 0 P (nat_control_rep hB hP (by omega))).trans (by omega)
  · simp [BoundedLoop.Expr.eval]
  · intro j hj v hv
    obtain ⟨a,rfl,ha⟩:=hv
    have hs' := (hs.update_gt (x:=15) (by decide) (.nat j)).update_gt (x:=16) (by decide) (.nat a)
    have he:=innerSum_eval hs' D j (by simp [Function.update,hD]) (by simp [Function.update]) hj hT
    have hv:=inner_value_le c table r D (j+1) (A+R) hDs (by omega) hT hmarked
    refine ⟨a+∑u∈Finset.Icc (j+1) (A+R),
      (layerAt table (j+1) u).2/(j+1)*(D/powerAt c (r+(j+1))),?_,by nlinarith⟩
    simp only [BoundedLoop.Expr.eval]
    rw [he]
    simp [Function.update,Value.natVal]
  · intro j hj v hv
    obtain ⟨a,rfl,ha⟩:=hv
    let ρ':=Function.update (Function.update ρ 15 (.nat j)) 16 (.nat a)
    have hs' : Inputs ρ' c A table r R := (hs.update_gt (by decide) _).update_gt (by decide) _
    have hi:=inner_peak hs' D j (by simp [ρ',Function.update,hD])
      (by simp [ρ',Function.update]) hDs hT hj hr hmarked hpr htr hB hP
    have ha':=(nat_rep_le hP (outer_acc_le_cap hB1 (by omega : j≤H+1) ha))
    have hp:=var_peak_of_rep ρ' 16 P (by simpa [ρ',Function.update] using ha')
    exact (binary_peak_le .add (.var 16) innerSum ρ' P (4000*(P+1)) hp hi).trans (by omega)
  · intro v hv
    obtain ⟨a,rfl,ha⟩:=hv
    exact (nat_rep_le hP (outer_acc_le_cap hB1 (by omega : A+R≤H+1) ha)).trans (by omega)


private def initialScaled : BoundedLoop.Expr :=
  .mul (.var 14) (.div (.var 13) (.get (.var 3) (.var 11)))
private lemma initialScaled_flat : Flat initialScaled := by
  unfold initialScaled
  repeat' first | apply Flat.binary .mul | apply Flat.binary .div | apply Flat.get | apply Flat.var

lemma outputArray_peak {H B P : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : Layer H}
    (hs : Inputs ρ c A table r R) (D I : ℕ)
    (hD : ρ 13=.nat D) (hI : ρ 14=.nat I) (hDs : D≤B^H) (hIs : I≤B^H)
    (hT : A+R≤H) (hr : r≤H)
    (hmarked : ∀k≤H,∀u≤H,(layerAt table k u).2≤B)
    (hpr : (powerValue c).representationSize≤P) (htr : (layerValue table).representationSize≤P)
    (hB : 2*H+1≤B) (hP : (scalarCap H B).size+1≤P) :
    outputArray.peak ρ≤100000*(P+1) := by
  have hB1 : 1≤B := by omega
  have hDr:=prefix_rep hB1 hP (j:=H) le_rfl hDs
  have hIr:=prefix_rep hB1 hP (j:=H) le_rfl hIs
  have hrr:=nat_control_rep hB hP (x:=r) (by omega)
  have hscaled : initialScaled.peak ρ≤4000*(P+1) := by
    have hh:=flat_peak_le initialScaled_flat ρ P (by
      simp [initialScaled,BoundedLoop.Expr.varsBound,hD,hI,hs.power,hs.count,hDr,hIr,hrr,hpr])
    apply hh.trans
    norm_num [initialScaled,BoundedLoop.Expr.flatBudget]
    omega
  have hout:=outer_peak hs D hD hDs hT hr hmarked hpr htr hB hP
  have hnum : (BoundedLoop.Expr.add initialScaled outerSum).peak ρ≤30000*(P+1) :=
    (binary_peak_le .add initialScaled outerSum ρ _ _ hscaled hout).trans (by omega)
  have hden : (BoundedLoop.Expr.var 13).peak ρ≤30000*(P+1) :=
    (var_peak_of_rep ρ 13 P (by rw [hD];exact hDr)).trans (by omega)
  change (BoundedLoop.Expr.array [.add initialScaled outerSum,.var 13]).peak ρ≤_
  have hh:=array_peak_le [.add initialScaled outerSum,.var 13] ρ (fun _=>30000*(P+1)) (by
    intro e he
    simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl|rfl
    · exact hnum
    · exact hden)
  exact hh.trans (by simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil];omega)

/-- Actual dynamic peak for the fixed syntax, under magnitude and encoded
array bounds on its shared input cache. Unused surrounding slots are arbitrary. -/
theorem outputProgram_peak_inputs {H B P : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : Layer H}
    (hs : Inputs ρ c A table r R) (hT : A+R≤H) (hr : r≤H)
    (hcb : CacheBound c table B)
    (hpr : (powerValue c).representationSize≤P) (hcr : (observedValue c).representationSize≤P)
    (htr : (layerValue table).representationSize≤P)
    (hB : 2*H+1≤B) (hP : (scalarCap H B).size+1≤P) :
    outputProgram.peak ρ≤100000*(P+1) := by
  have hDe:=denominatorProgram_eval ρ c hs.horizon hs.power
  let ρD:=Function.update ρ 13 (.nat (denominator c))
  have hsD : Inputs ρD c A table r R:=hs.update_gt (by decide) _
  have hIe:=initialProgram_eval ρD c hsD.horizon hsD.power hsD.observed
  let ρI:=Function.update ρD 14 (.nat (initialNumerator c))
  have hsI : Inputs ρI c A table r R:=hsD.update_gt (by decide) _
  have hA:=outputArray_peak hsI (denominator c) (initialNumerator c)
    (by simp [ρI,ρD,Function.update]) (by simp [ρI,Function.update])
    (denominator_le c hcb.1) (initial_le c hcb.1) hT hr hcb.2.2 hpr htr hB hP
  rw [outputProgram]
  apply bind_peak_bound
  · exact (denominator_peak ρ c hs.horizon hs.power hcb.1 hpr hB hP).trans (by omega)
  · rw [hDe]
    change (BoundedLoop.Expr.bind 14 initialProgram outputArray).peak ρD≤_
    apply bind_peak_bound
    · exact (initial_peak ρD c hsD.horizon hsD.power hsD.observed hcb.1 hpr hcr hB hP).trans (by omega)
    · rw [hIe]
      exact hA

/-- Total encoded-size reserve for all source arrays and scalar accumulators.
The array delimiters are included in each displayed summand. -/
def storageBound (H : ℕ) : ℕ :=
  (scalarCap H (baseCap H)).size+1+
  ((2*H+1)*(baseBits H+1)+2)+((H+1)*(H+1)+2)+
  ((H+1)*((H+1)*(2*baseBits H+4)+2)+2)

lemma storageBound_polynomial (H : ℕ) : storageBound H≤1000*(H+1)^4 := by
  have hb:=baseCap_binarySize H
  have hs:=scalarCap_binarySize_polynomial H (baseCap H) (baseBits H) hb
  have h2:=binarySize_le_self (2*H)
  have hb' : baseBits H≤(4*H+2)*(2*H)+1 := by unfold baseBits;nlinarith
  have hm:=Nat.mul_le_mul_left (2*H+2) hb'
  have hp:=Nat.mul_le_mul_left (2*H+1) hb'
  have hl:=Nat.mul_le_mul_left ((H+1)*(H+1)*2) hb'
  unfold storageBound
  nlinarith

/-- The true evaluator peak is polynomial for every actual source cache and
final DP layer. This applies unchanged inside the enclosing suffix/batch code. -/
theorem outputProgram_source_peak {H : ℕ} (hH : 0<H) (z : List Bool) (hz : z.length≤H)
    {ρ : Env} {A r R : ℕ}
    (hs : Inputs ρ (makeObservedCache H z) A
      (cachedRun H (makeObservedCache H z) A H) r R)
    (hT : A+R≤H) (hr : r≤H) :
    outputProgram.peak ρ≤200000000*(H+1)^4 := by
  have hp:=source_power_representation H z hH
  have hc:=source_observed_representation H z hz
  have ht:=source_layer_representation H z A hH hz
  have hb:=outputProgram_peak_inputs (P:=storageBound H) hs hT hr (source_cacheBound H z A hH hz)
    (by unfold storageBound;omega) (by unfold storageBound;omega)
    (by unfold storageBound;omega) (baseCap_ge hH) (by unfold storageBound;omega)
  have hpoly:=storageBound_polynomial H
  have hpow : 1≤(H+1)^4 := by
    have hh : 0<(H+1)^4 := by positivity
    omega
  nlinarith [hpow]

/-- Specialization to the exact actual input environment of the output query. -/
theorem outputProgram_evaluatePair_peak (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : 0<H) (hz : z.length+R≤H) :
    let c:=makeObservedCache H z
    let table:=cachedRun H c (parseAge 0 z) H
    outputProgram.peak (outputEnv c (parseAge 0 z) table (parseGaps 0 z).length R)≤
      200000000*(H+1)^4 := by
  dsimp only
  exact outputProgram_source_peak hH z (by omega) (outputEnv_inputs _ _ _ _ _)
    (by have hh:=age_le_length z;omega) (by have hh:=count_add_age_le z;omega)

end Paper37.IntegerOutputPeak
