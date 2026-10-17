import Paper37.RefinedOutputProgram
import Paper37.RefinedValueSize
import Paper37.IntegerOutputPeak
import Paper37.CachedFramePolynomial
import Paper37.BoundedLoopTabulate

/-! Actual dynamic intermediate-size bounds for the fixed occupied-type output
program. Prefix sums, observed-type counts and every running output accumulator
are bounded along their actual executions. -/
namespace Paper37.RefinedOutputPeak
open scoped BigOperators
open Paper37.BoundedLoop Paper37.RefinedOutputProgram Paper37.RefinedCoreProgram
open Paper37.CachedDP Paper37.CachedRefinedDP Paper37.AdaptiveDP
open Paper37.DP Paper37.ContinuationDP Paper37.RefinedContinuation Paper37.Envelope
open Paper37.CachedOutput
open Paper37.CachedCoreProgram (powerValue observedValue powerValue_get_total)
open Paper37.IntegerOutputPeak (scalarCap baseCap baseBits nat_rep_le nat_control_rep prefix_rep
  scalarCap_mono_power scalarCap_ge_base fold_peak_bound bind_peak_bound
  var_peak_of_rep lit_peak_of_rep denominator_peak initial_peak denominator_le initial_le)
open Paper37.IntegerOutputProgram (denominatorProgram initialProgram denominatorProgram_eval initialProgram_eval observedValue_get)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

lemma small_sum_cap {H B j a : ℕ} (hB : 2*H+1≤B) (hj : j≤H+1) (ha : a≤j*B) :
    a≤scalarCap H B := by
  calc
    _ ≤ (H+1)*B := ha.trans (Nat.mul_le_mul_right _ hj)
    _ ≤ B*B := Nat.mul_le_mul_right _ (by omega)
    _ = B^2 := by ring
    _ ≤ _ := scalarCap_mono_power (by omega) (by omega)

lemma outer_sum_cap {H B j a : ℕ} (hB : 2*H+1≤B) (hj : j≤H+1)
    (ha : a≤j*(H+1)^2*B^(H+1)) : a≤scalarCap H B := by
  calc
    _ ≤ B*(H+1)^2*B^(H+1) := ha.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega)))
    _ = (H+1)^2*B^(H+2) := by rw [pow_succ];ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

private def pBody : Expr := .add (.var 30) tableMarked
private lemma pBody_flat : Flat pBody := by
  unfold pBody tableMarked kIndex
  repeat' first | apply Flat.binary .add | apply Flat.get | apply Flat.var | apply Flat.lit

lemma tableMarked_eval {H : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : RefinedLayer H}
    (hs : Inputs ρ c A table r R) (k0 u j : ℕ)
    (hk : ρ 15=.nat k0) (hu : ρ 17=.nat u) (hj : ρ 29=.nat j)
    (hkH : k0+1≤H) (huH : u≤H) (hjH : j≤H) :
    tableMarked.eval ρ=.nat (refinedLayerAt table (k0+1) u j).2 := by
  simp only [tableMarked,kIndex,Expr.eval,hs.layer,hk,hu,hj,Value.natVal]
  rw [Paper37.RefinedCoreProgram.layerValue_get table (k0+1) u j (by omega) (by omega) (by omega)]
  rfl

lemma prefix_peak {H B P : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : RefinedLayer H}
    (hs : Inputs ρ c A table r R) (k0 u t : ℕ)
    (hk : ρ 15=.nat k0) (hu : ρ 17=.nat u) (ht : ρ 28=.nat t)
    (hkH : k0+1≤H) (huH : u≤H) (htH : t≤H)
    (hmarked : ∀k≤H,∀u≤H,∀j≤H,(refinedLayerAt table k u j).2≤B)
    (htr : (Paper37.RefinedCoreProgram.layerValue table).representationSize≤P)
    (hB : 2*H+1≤B) (hP : (scalarCap H B).size+1≤P) : prefixSum.peak ρ≤4000*(P+1) := by
  have hkr:=nat_control_rep hB hP (x:=k0) (by omega)
  have hur:=nat_control_rep hB hP (x:=u) (by omega)
  have htrt:=nat_control_rep hB hP (x:=t) (by omega)
  have hbound : (Expr.add (.var 28) (.lit 1)).peak ρ≤4000*(P+1) := by
    have hv:=var_peak_of_rep ρ 28 P (by rw [ht];exact htrt)
    have hl:=lit_peak_of_rep ρ 1 P (nat_control_rep hB hP (by omega))
    exact (binary_peak_le .add _ _ ρ P P hv hl).trans (by omega)
  rw [prefixSum]
  apply fold_peak_bound ρ 29 30 (.add (.var 28) (.lit 1)) (.lit 0) pBody (t+1) (4000*(P+1))
    (fun j v=>∃a,v=.nat a ∧ a≤j*B)
  · simp [Expr.eval,ht,Value.natVal]
  · exact hbound
  · exact (lit_peak_of_rep ρ 0 P (nat_control_rep hB hP (by omega))).trans (by omega)
  · simp [Expr.eval]
  · intro j hj v hv
    obtain ⟨a,rfl,ha⟩:=hv
    have hs':=(hs.update_gt (x:=29) (by decide) (.nat j)).update_gt (x:=30) (by decide) (.nat a)
    have he:=tableMarked_eval hs' k0 u j (by simp [Function.update,hk])
      (by simp [Function.update,hu]) (by simp [Function.update]) hkH huH (by omega)
    refine ⟨a+(refinedLayerAt table (k0+1) u j).2,?_,?_⟩
    · simp only [pBody,Expr.eval]
      rw [he]
      simp [Function.update,Value.natVal]
    · have hh:=hmarked _ hkH _ huH j (by omega)
      nlinarith
  · intro j hj v hv
    obtain ⟨a,rfl,ha⟩:=hv
    have har:=nat_rep_le hP (small_sum_cap hB (by omega : j≤H+1) ha)
    have hjr:=nat_control_rep hB hP (x:=j) (by omega)
    have hh:=flat_peak_le pBody_flat (Function.update (Function.update ρ 29 (.nat j)) 30 (.nat a)) P (by
      simp [pBody,tableMarked,kIndex,Expr.varsBound,Function.update,hs.layer,hk,hu,htr,hkr,hur,hjr,har])
    apply hh.trans
    norm_num [pBody,tableMarked,kIndex,Expr.flatBudget]
    omega
  · intro v hv
    obtain ⟨a,rfl,ha⟩:=hv
    exact (nat_rep_le hP (small_sum_cap hB (by omega : t+1≤H+1) ha)).trans (by omega)

lemma prefix_value_le {H B : ℕ} (table : RefinedLayer H) (k u t : ℕ)
    (hk : k≤H) (hu : u≤H) (ht : t≤H)
    (hm : ∀k≤H,∀u≤H,∀j≤H,(refinedLayerAt table k u j).2≤B) :
    (∑j∈Finset.range (t+1),(refinedLayerAt table k u j).2)≤(H+1)*B := by
  calc
    _ ≤ (t+1)*B := by
      simpa using Finset.sum_le_card_nsmul (Finset.range (t+1))
        (fun j=>(refinedLayerAt table k u j).2) B (by
          intro j hj
          exact hm _ hk _ hu j (by have hh:=Finset.mem_range.mp hj;omega))
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

lemma scaled_term_le {H B : ℕ} (c : Cache H) (table : RefinedLayer H) (r D k u t : ℕ)
    (hD : D≤B^H) (hk : k≤H) (hu : u≤H) (ht : t≤H)
    (hm : ∀k≤H,∀u≤H,∀j≤H,(refinedLayerAt table k u j).2≤B) :
    (∑j∈Finset.range (t+1),(refinedLayerAt table k u j).2)/k*(D/powerAt c (r+k))≤(H+1)*B^(H+1) := by
  calc
    _ ≤ ((H+1)*B)*B^H := Nat.mul_le_mul
      ((Nat.div_le_self _ _).trans (prefix_value_le table k u t hk hu ht hm))
      ((Nat.div_le_self _ _).trans hD)
    _ = _ := by rw [pow_succ];ring

private def ratio : Expr := .div (.var 13) (.get (.var 3) (.add (.var 11) kIndex))
private lemma ratio_flat : Flat ratio := by
  unfold ratio kIndex
  repeat' first | apply Flat.binary .add | apply Flat.binary .div | apply Flat.get | apply Flat.var | apply Flat.lit

lemma finalTerm_peak {H B P : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : RefinedLayer H}
    (hs : Inputs ρ c A table r R) (D k0 u t : ℕ)
    (hD : ρ 13=.nat D) (hk : ρ 15=.nat k0) (hu : ρ 17=.nat u) (ht : ρ 28=.nat t)
    (hDs : D≤B^H) (hkH : k0+1≤H) (huH : u≤H) (htH : t≤H) (hrH : r≤H)
    (hm : ∀k≤H,∀u≤H,∀j≤H,(refinedLayerAt table k u j).2≤B)
    (hpr : (powerValue c).representationSize≤P)
    (htr : (Paper37.RefinedCoreProgram.layerValue table).representationSize≤P)
    (hB : 2*H+1≤B) (hP : (scalarCap H B).size+1≤P) : finalTerm.peak ρ≤50000*(P+1) := by
  have hprefix:=prefix_peak hs k0 u t hk hu ht hkH huH htH hm htr hB hP
  have hDr:=prefix_rep (by omega : 1≤B) hP (j:=H) le_rfl hDs
  have hkr:=nat_control_rep hB hP (x:=k0) (by omega)
  have hrr:=nat_control_rep hB hP (x:=r) (by omega)
  have hratio : ratio.peak ρ≤4000*(P+1) := by
    have hh:=flat_peak_le ratio_flat ρ P (by simp [ratio,kIndex,Expr.varsBound,hD,hs.power,hs.count,hk,hDr,hkr,hrr,hpr])
    apply hh.trans
    norm_num [ratio,kIndex,Expr.flatBudget]
    omega
  have hindex : kIndex.peak ρ≤4000*(P+1) := by
    have hv:=var_peak_of_rep ρ 15 P (by rw [hk];exact hkr)
    have hl:=lit_peak_of_rep ρ 1 P (nat_control_rep hB hP (by omega))
    exact (binary_peak_le .add _ _ ρ P P hv hl).trans (by omega)
  have hdiv : (Expr.div prefixSum kIndex).peak ρ≤20000*(P+1) :=
    (binary_peak_le .div _ _ ρ _ _ hprefix hindex).trans (by omega)
  exact (binary_peak_le .mul _ _ ρ _ _ hdiv hratio).trans (by omega)

lemma guardedTerm_peak {H B P : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : RefinedLayer H}
    (hs : Inputs ρ c A table r R) (D k0 u t : ℕ)
    (hD : ρ 13=.nat D) (hk : ρ 15=.nat k0) (hu : ρ 17=.nat u) (ht : ρ 28=.nat t)
    (hDs : D≤B^H) (hkH : k0+1≤H) (huH : u≤H) (htH : t≤H) (hrH : r≤H)
    (hm : ∀k≤H,∀u≤H,∀j≤H,(refinedLayerAt table k u j).2≤B)
    (hpr : (powerValue c).representationSize≤P)
    (htr : (Paper37.RefinedCoreProgram.layerValue table).representationSize≤P)
    (hB : 2*H+1≤B) (hP : (scalarCap H B).size+1≤P) : guardedTerm.peak ρ≤50000*(P+1) := by
  have hf:=finalTerm_peak hs D k0 u t hD hk hu ht hDs hkH huH htH hrH hm hpr htr hB hP
  have hkr:=nat_control_rep hB hP (x:=k0) (by omega)
  have hur:=nat_control_rep hB hP (x:=u) (by omega)
  have hkpeak : kIndex.peak ρ≤50000*(P+1) := by
    have hv:=var_peak_of_rep ρ 15 P (by rw [hk];exact hkr)
    have hl:=lit_peak_of_rep ρ 1 P (nat_control_rep hB hP (by omega))
    exact (binary_peak_le .add _ _ ρ P P hv hl).trans (by omega)
  have hupeak : (Expr.var 17).peak ρ≤50000*(P+1) :=
    (var_peak_of_rep ρ 17 P (by rw [hu];exact hur)).trans (by omega)
  have hz : (Expr.lit 0).peak ρ≤50000*(P+1) :=
    (lit_peak_of_rep ρ 0 P (nat_control_rep hB hP (by omega))).trans (by omega)
  have hh:=if_peak_le (.var 17) kIndex (.lit 0) finalTerm ρ _ _ _ _ hupeak hkpeak hz hf
  simpa only [max_self,guardedTerm] using hh


lemma future_peak (ρ : Env) (P : ℕ) (ha : (ρ 1).representationSize≤P)
    (hr : (ρ 12).representationSize≤P) : totalFuture.peak ρ≤4000*(P+1) :=
  (binary_peak_le .add _ _ ρ P P (var_peak_of_rep ρ 1 P ha) (var_peak_of_rep ρ 12 P hr)).trans (by omega)

lemma inner_peak {H B P : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : RefinedLayer H}
    (hs : Inputs ρ c A table r R) (D k0 t : ℕ)
    (hD : ρ 13=.nat D) (hk : ρ 15=.nat k0) (ht : ρ 28=.nat t) (hDs : D≤B^H)
    (hkT : k0<A+R) (hT : A+R≤H) (htH : t≤H) (hrH : r≤H)
    (hm : ∀k≤H,∀u≤H,∀j≤H,(refinedLayerAt table k u j).2≤B)
    (hpr : (powerValue c).representationSize≤P)
    (htr : (Paper37.RefinedCoreProgram.layerValue table).representationSize≤P)
    (hB : 2*H+1≤B) (hP : (scalarCap H B).size+1≤P) : innerSum.peak ρ≤110000*(P+1) := by
  have hB1 : 1≤B := by omega
  have ha:=nat_control_rep hB hP (x:=A) (by omega)
  have hr:=nat_control_rep hB hP (x:=R) (by omega)
  have hf:=future_peak ρ P (by rw [hs.age];exact ha) (by rw [hs.remaining];exact hr)
  have hl:=lit_peak_of_rep ρ 1 P (nat_control_rep hB hP (by omega))
  rw [innerSum]
  apply fold_peak_bound ρ 17 18 (.add totalFuture (.lit 1)) (.lit 0) (.add (.var 18) guardedTerm)
    (A+R+1) (110000*(P+1)) (fun j v=>∃a,v=.nat a ∧ a≤j*(H+1)*B^(H+1))
  · simp [totalFuture,Expr.eval,hs.age,hs.remaining,Value.natVal]
  · exact (binary_peak_le .add _ _ ρ _ _ hf hl).trans (by omega)
  · exact (lit_peak_of_rep ρ 0 P (nat_control_rep hB hP (by omega))).trans (by omega)
  · simp [Expr.eval]
  · intro u hu v hv
    obtain ⟨a,rfl,ha⟩:=hv
    let T:=if u<k0+1 then 0 else (∑j∈Finset.range (t+1),(refinedLayerAt table (k0+1) u j).2)/
      (k0+1)*(D/powerAt c (r+(k0+1)))
    have hTerm : T≤(H+1)*B^(H+1) := by
      dsimp [T]
      split_ifs
      · exact Nat.zero_le _
      · exact scaled_term_le c table r D (k0+1) u t hDs (by omega) (by omega) htH hm
    have hs':=(hs.update_gt (x:=17) (by decide) (.nat u)).update_gt (x:=18) (by decide) (.nat a)
    have he:=guardedTerm_eval hs' D k0 u t (by simp [Function.update,hD])
      (by simp [Function.update,hk]) (by simp [Function.update]) (by simp [Function.update,ht])
      (by omega) (by omega) htH
    refine ⟨a+T,?_,by nlinarith⟩
    simp only [Expr.eval]
    rw [he]
    simp [T,Function.update,Value.natVal]
  · intro u hu v hv
    obtain ⟨a,rfl,ha⟩:=hv
    let σ:=Function.update (Function.update ρ 17 (.nat u)) 18 (.nat a)
    have hs' : Inputs σ c A table r R:=(hs.update_gt (by decide) _).update_gt (by decide) _
    have hg:=guardedTerm_peak hs' D k0 u t (by simp [σ,Function.update,hD])
      (by simp [σ,Function.update,hk]) (by simp [σ,Function.update]) (by simp [σ,Function.update,ht])
      hDs (by omega) (by omega) htH hrH hm hpr htr hB hP
    have har:=nat_rep_le hP (Paper37.IntegerOutputPeak.outer_acc_le_cap hB1 (by omega : u≤H+1) ha)
    have hv:=var_peak_of_rep σ 18 P (by simpa [σ,Function.update] using har)
    exact (binary_peak_le .add _ _ σ _ _ hv hg).trans (by omega)
  · intro v hv
    obtain ⟨a,rfl,ha⟩:=hv
    exact (nat_rep_le hP (Paper37.IntegerOutputPeak.outer_acc_le_cap hB1 (by omega : A+R+1≤H+1) ha)).trans (by omega)

lemma inner_value_le {H B : ℕ} (c : Cache H) (table : RefinedLayer H) (r D k T t : ℕ)
    (hD : D≤B^H) (hk : k≤H) (hT : T≤H) (ht : t≤H)
    (hm : ∀k≤H,∀u≤H,∀j≤H,(refinedLayerAt table k u j).2≤B) :
    (∑u∈Finset.Icc k T,(∑j∈Finset.range (t+1),(refinedLayerAt table k u j).2)/k*
      (D/powerAt c (r+k)))≤(H+1)^2*B^(H+1) := by
  calc
    _ ≤ (Finset.Icc k T).card*((H+1)*B^(H+1)) := Finset.sum_le_card_nsmul _ _ _ (by
      intro u hu
      exact scaled_term_le c table r D k u t hD hk ((Finset.mem_Icc.mp hu).2.trans hT) ht hm)
    _ ≤ (H+1)*((H+1)*B^(H+1)) := Nat.mul_le_mul_right _ (by simp only [Nat.card_Icc];omega)
    _ = _ := by ring

lemma outer_peak {H B P : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : RefinedLayer H}
    (hs : Inputs ρ c A table r R) (D t : ℕ) (hD : ρ 13=.nat D) (ht : ρ 28=.nat t)
    (hDs : D≤B^H) (hT : A+R≤H) (htH : t≤H) (hrH : r≤H)
    (hm : ∀k≤H,∀u≤H,∀j≤H,(refinedLayerAt table k u j).2≤B)
    (hpr : (powerValue c).representationSize≤P)
    (htr : (Paper37.RefinedCoreProgram.layerValue table).representationSize≤P)
    (hB : 2*H+1≤B) (hP : (scalarCap H B).size+1≤P) : outerSum.peak ρ≤230000*(P+1) := by
  have ha:=nat_control_rep hB hP (x:=A) (by omega)
  have hr:=nat_control_rep hB hP (x:=R) (by omega)
  rw [outerSum]
  apply fold_peak_bound ρ 15 16 totalFuture (.lit 0) (.add (.var 16) innerSum)
    (A+R) (230000*(P+1)) (fun j v=>∃a,v=.nat a ∧ a≤j*(H+1)^2*B^(H+1))
  · simp [totalFuture,Expr.eval,hs.age,hs.remaining,Value.natVal]
  · exact (future_peak ρ P (by rw [hs.age];exact ha) (by rw [hs.remaining];exact hr)).trans (by omega)
  · exact (lit_peak_of_rep ρ 0 P (nat_control_rep hB hP (by omega))).trans (by omega)
  · simp [Expr.eval]
  · intro k0 hk v hv
    obtain ⟨a,rfl,ha⟩:=hv
    have hs':=(hs.update_gt (x:=15) (by decide) (.nat k0)).update_gt (x:=16) (by decide) (.nat a)
    have he:=innerSum_eval hs' D k0 t (by simp [Function.update,hD]) (by simp [Function.update])
      (by simp [Function.update,ht]) hk hT htH
    have hval:=inner_value_le c table r D (k0+1) (A+R) t hDs (by omega) hT htH hm
    refine ⟨a+∑u∈Finset.Icc (k0+1) (A+R),(∑j∈Finset.range (t+1),
      (refinedLayerAt table (k0+1) u j).2)/(k0+1)*(D/powerAt c (r+(k0+1))),?_,by nlinarith⟩
    simp only [Expr.eval]
    rw [he]
    simp [Function.update,Value.natVal]
  · intro k0 hk v hv
    obtain ⟨a,rfl,ha⟩:=hv
    let σ:=Function.update (Function.update ρ 15 (.nat k0)) 16 (.nat a)
    have hs' : Inputs σ c A table r R:=(hs.update_gt (by decide) _).update_gt (by decide) _
    have hi:=inner_peak hs' D k0 t (by simp [σ,Function.update,hD]) (by simp [σ,Function.update])
      (by simp [σ,Function.update,ht]) hDs hk hT htH hrH hm hpr htr hB hP
    have har:=nat_rep_le hP (outer_sum_cap hB (by omega : k0≤H+1) ha)
    have hv:=var_peak_of_rep σ 16 P (by simpa [σ,Function.update] using har)
    exact (binary_peak_le .add _ _ σ _ _ hv hi).trans (by omega)
  · intro v hv
    obtain ⟨a,rfl,ha⟩:=hv
    exact (nat_rep_le hP (outer_sum_cap hB (by omega : A+R≤H+1) ha)).trans (by omega)


private def oBody : Expr := .add (.var 20)
  (.ifLT (.lit 0) (.get (.var 4) (.add (.var 19) (.lit 1))) (.lit 1) (.lit 0))
private lemma oBody_flat : Flat oBody := by
  unfold oBody
  repeat' first | apply Flat.binary .add | apply Flat.get | apply Flat.ifLT | apply Flat.var | apply Flat.lit

lemma observedTypes_le {H : ℕ} (c : Cache H) : observedTypes c≤H := by
  unfold observedTypes
  have hh:=Finset.sum_le_card_nsmul (gapSet H) (fun d=>if 0<observedAt c d then 1 else 0) 1 (by
    intro d hd
    dsimp only
    split_ifs <;> omega)
  simpa [gapSet,Nat.card_Icc] using hh

lemma observedTypes_peak {H B P : ℕ} (ρ : Env) (c : Cache H)
    (hH : ρ 0=.nat H) (hc : ρ 4=observedValue c) (hcr : (observedValue c).representationSize≤P)
    (hB : 2*H+1≤B) (hP : (scalarCap H B).size+1≤P) :
    observedTypesProgram.peak ρ≤4000*(P+1) := by
  rw [observedTypesProgram]
  apply fold_peak_bound ρ 19 20 (.var 0) (.lit 0) oBody H (4000*(P+1)) (fun j v=>∃a,v=.nat a ∧ a≤j)
  · simp [Expr.eval,hH,Value.natVal]
  · exact (var_peak_of_rep ρ 0 P (by rw [hH];exact nat_control_rep hB hP (by omega))).trans (by omega)
  · exact (lit_peak_of_rep ρ 0 P (nat_control_rep hB hP (by omega))).trans (by omega)
  · simp [Expr.eval]
  · intro j hj v hv
    obtain ⟨a,rfl,ha⟩:=hv
    refine ⟨a+(if 0<observedAt c (j+1) then 1 else 0),?_,?_⟩
    · simp [oBody,Expr.eval,Function.update,hc,observedValue_get c (j+1) (by omega),Value.natVal]
      split_ifs <;> rfl
    · split_ifs <;> omega
  · intro j hj v hv
    obtain ⟨a,rfl,ha⟩:=hv
    have har:=nat_control_rep hB hP (x:=a) (by omega)
    have hjr:=nat_control_rep hB hP (x:=j) (by omega)
    have hh:=flat_peak_le oBody_flat (Function.update (Function.update ρ 19 (.nat j)) 20 (.nat a)) P
      (by simp [oBody,Expr.varsBound,Function.update,hc,hcr,har,hjr])
    apply hh.trans
    norm_num [oBody,Expr.flatBudget]
    omega
  · intro v hv
    obtain ⟨a,rfl,ha⟩:=hv
    exact (nat_control_rep hB hP (x:=a) (by omega)).trans (by omega)

private def initialGate : Expr := .ifLT (.var 28) (.var 31) (.lit 0)
  (.mul (.var 14) (.div (.var 13) (.get (.var 3) (.var 11))))
private lemma initialGate_flat : Flat initialGate := by
  unfold initialGate
  repeat' first | apply Flat.ifLT | apply Flat.binary .mul | apply Flat.binary .div | apply Flat.get | apply Flat.var | apply Flat.lit

lemma numerator_peak {H B P : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : RefinedLayer H}
    (hs : Inputs ρ c A table r R) (D I t ν : ℕ)
    (hD : ρ 13=.nat D) (hI : ρ 14=.nat I) (ht : ρ 28=.nat t) (hν : ρ 31=.nat ν)
    (hDs : D≤B^H) (hIs : I≤B^H) (hT : A+R≤H) (htH : t≤H) (hνH : ν≤H) (hrH : r≤H)
    (hm : ∀k≤H,∀u≤H,∀j≤H,(refinedLayerAt table k u j).2≤B)
    (hpr : (powerValue c).representationSize≤P)
    (htr : (Paper37.RefinedCoreProgram.layerValue table).representationSize≤P)
    (hB : 2*H+1≤B) (hP : (scalarCap H B).size+1≤P) : numeratorProgram.peak ρ≤500000*(P+1) := by
  have hDr:=prefix_rep (by omega : 1≤B) hP (j:=H) le_rfl hDs
  have hIr:=prefix_rep (by omega : 1≤B) hP (j:=H) le_rfl hIs
  have hrr:=nat_control_rep hB hP (x:=r) (by omega)
  have htrt:=nat_control_rep hB hP (x:=t) (by omega)
  have hνr:=nat_control_rep hB hP (x:=ν) (by omega)
  have hi : initialGate.peak ρ≤4000*(P+1) := by
    have hh:=flat_peak_le initialGate_flat ρ P (by
      simp [initialGate,Expr.varsBound,hD,hI,ht,hν,hs.power,hs.count,hDr,hIr,hrr,htrt,hνr,hpr])
    apply hh.trans
    norm_num [initialGate,Expr.flatBudget]
    omega
  have ho:=outer_peak hs D t hD ht hDs hT htH hrH hm hpr htr hB hP
  exact (binary_peak_le .add initialGate outerSum ρ _ _ hi ho).trans (by omega)

/-- Dynamic peak for the actual output AST; all loops use the current real
accumulators, including occupied-type count and every j-prefix sum. -/
theorem outputProgram_peak_inputs {H B P : ℕ} {ρ : Env} {c : Cache H} {A r R : ℕ} {table : RefinedLayer H}
    (hs : Inputs ρ c A table r R) (hT : A+R≤H) (hrH : r≤H)
    (hpow : ∀i,powerAt c i≤B)
    (hm : ∀k≤H,∀u≤H,∀j≤H,(refinedLayerAt table k u j).2≤B)
    (hpr : (powerValue c).representationSize≤P) (hcr : (observedValue c).representationSize≤P)
    (htr : (Paper37.RefinedCoreProgram.layerValue table).representationSize≤P)
    (hB : 2*H+1≤B) (hP : (scalarCap H B).size+1≤P) :
    outputProgram.peak ρ≤1000000*(H+2)*(P+1) := by
  have hDe:=denominatorProgram_eval ρ c hs.horizon hs.power
  let ρD:=Function.update ρ 13 (.nat (denominator c))
  have hsD : Inputs ρD c A table r R:=hs.update_gt (by decide) _
  have hIe:=initialProgram_eval ρD c hsD.horizon hsD.power hsD.observed
  let ρI:=Function.update ρD 14 (.nat (initialNumerator c))
  have hsI : Inputs ρI c A table r R:=hsD.update_gt (by decide) _
  have hOe:=observedTypesProgram_eval ρI c hsI.horizon hsI.observed
  let ρO:=Function.update ρI 31 (.nat (observedTypes c))
  have hsO : Inputs ρO c A table r R:=hsI.update_gt (by decide) _
  have hb : (Expr.add (.var 0) (.lit 1)).peak ρO≤4000*(P+1) := by
    have hv:=var_peak_of_rep ρO 0 P (by rw [hsO.horizon];exact nat_control_rep hB hP (by omega))
    have hl:=lit_peak_of_rep ρO 1 P (nat_control_rep hB hP (by omega))
    exact (binary_peak_le .add _ _ ρO P P hv hl).trans (by omega)
  have htab:=Paper37.BoundedLoop.tabulate_peak_le 28 (.add (.var 0) (.lit 1)) numeratorProgram ρO
    (H+1) (4000*(P+1)) (500000*(P+1)) (by simp [Expr.eval,hsO.horizon,Value.natVal]) hb (by
      intro t ht
      let σ:=Function.update ρO 28 (.nat t)
      have hs' : Inputs σ c A table r R:=hsO.update_gt (by decide) _
      exact numerator_peak hs' (denominator c) (initialNumerator c) t (observedTypes c)
        (by simp [σ,ρO,ρI,ρD]) (by simp [σ,ρO,ρI]) (by simp [σ]) (by simp [σ,ρO])
        (denominator_le c hpow) (initial_le c hpow) hT (by omega) (observedTypes_le c) hrH hm hpr htr hB hP)
  have htab' : (Expr.tabulate 28 (.add (.var 0) (.lit 1)) numeratorProgram).peak ρO≤1000000*(H+2)*(P+1) :=
    htab.trans (by nlinarith)
  rw [outputProgram]
  apply bind_peak_bound
  · exact (denominator_peak ρ c hs.horizon hs.power hpow hpr hB hP).trans (by nlinarith)
  · rw [hDe]
    change (Expr.bind 14 initialProgram (.bind 31 observedTypesProgram _)).peak ρD≤_
    apply bind_peak_bound
    · exact (initial_peak ρD c hsD.horizon hsD.power hsD.observed hpow hpr hcr hB hP).trans (by nlinarith)
    · rw [hIe]
      change (Expr.bind 31 observedTypesProgram _).peak ρI≤_
      apply bind_peak_bound
      · exact (observedTypes_peak ρI c hsI.horizon hsI.observed hcr hB hP).trans (by nlinarith)
      · rw [hOe]
        exact htab'

lemma source_marked_bound (H : ℕ) (z : List Bool) (A : ℕ) (hH : 0<H) (hz : z.length≤H)
    (k u j : ℕ) (hk : k≤H) (hu : u≤H) (hj : j≤H) :
    (refinedLayerAt (cachedRefinedRun H (makeObservedCache H z) A H) k u j).2≤baseCap H := by
  rw [makeObservedCache_eq,cachedRefinedRun_correct H _ A H le_rfl (observedCounts_le_horizon H z hz),
    refinedLayerAt_run H _ A H k u j hk hu hj]
  change refinedS (observedCounts z) (gapSet H) A k u j≤baseCap H
  have ho:=Paper37.IntegerOutputPeak.source_marked_bound H z A hH hz k u hk hu
  rw [makeObservedCache_eq,cachedRun_correct H _ A H le_rfl (observedCounts_le_horizon H z hz),
    layerAt_run H _ A H k u hk hu] at ho
  exact (refinedS_le_S _ _ _ _ _ _).trans ho

def sourceReserve (H : ℕ) : ℕ := sourceFrameBound H+(scalarCap H (baseCap H)).size+1

lemma sourceFrame_polynomial (H : ℕ) : sourceFrameBound H≤200*(H+2)^5 := by
  have hf:=Paper37.CachedCoreProgram.sourceFrameBound_polynomial H
  have hl : layerSizeBound H (Paper37.CachedCoreProgram.sourceWidth H)=
      (H+1)*Paper37.CachedCoreProgram.layerSizeBound H (Paper37.CachedCoreProgram.sourceWidth H)+2 := rfl
  have hc:=(Paper37.CachedCoreProgram.sourceFrame_contains H).1
  have hm:=Nat.mul_le_mul_left (H+1) hc
  have hp:=Nat.mul_le_mul_left (H+2) hf
  have hmono : (H+2)*(H+1)^4≤(H+2)^5 := by
    calc _ ≤(H+2)*(H+2)^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 4)
         _ =_ := by ring
  have hp5 : 1≤(H+2)^5 := one_le_pow₀ (by omega)
  unfold sourceFrameBound
  rw [hl]
  nlinarith

lemma sourceReserve_polynomial (H : ℕ) : sourceReserve H≤1000*(H+2)^5 := by
  have hf:=sourceFrame_polynomial H
  have hs:=Paper37.IntegerOutputPeak.scalarCap_binarySize_polynomial H (baseCap H) (baseBits H)
    (Paper37.IntegerOutputPeak.baseCap_binarySize H)
  have hbits : baseBits H≤(4*H+2)*(2*H)+1 := by
    have hh:=binarySize_le_self (2*H)
    unfold baseBits
    nlinarith
  have hm:=Nat.mul_le_mul_left (2*H+2) hbits
  unfold sourceReserve
  nlinarith

/-- A source-level polynomial bound, with every actual cached input and
running value discharged. No trace, value or peak estimate is assumed. -/
theorem outputProgram_source_peak (H : ℕ) (z : List Bool) (R : ℕ) (ρ : Env)
    (hH : 0<H) (hz : z.length+R≤H)
    (hs : Inputs ρ (makeObservedCache H z) (parseAge 0 z)
      (cachedRefinedRun H (makeObservedCache H z) (parseAge 0 z) H) (parseGaps 0 z).length R) :
    outputProgram.peak ρ≤1000000000000000*(H+2)^12 := by
  have hf:=sourceFrame_contains H
  have hp:=Paper37.CachedCoreProgram.source_power_size H z
  have hc:=Paper37.CachedCoreProgram.source_observed_size H z (by omega)
  have ht:=source_layer_size H z (parseAge 0 z) H hH (by omega) le_rfl
  have hh:=outputProgram_peak_inputs (P:=sourceReserve H) hs
    (by have hh:=age_le_length z;omega)
    (by have hh:=Paper37.IntegerOutput.count_add_age_le z;omega)
    (Paper37.IntegerOutputPeak.source_power_bound H z hH)
    (fun k hk u hu j hj=>source_marked_bound H z (parseAge 0 z) hH (by omega) k u j hk hu hj)
    (by unfold sourceReserve;omega) (by unfold sourceReserve;omega) (by unfold sourceReserve;omega)
    (Paper37.IntegerOutputPeak.baseCap_ge hH) (by unfold sourceReserve;omega)
  have hres:=sourceReserve_polynomial H
  have hp5 : 1≤(H+2)^5 := one_le_pow₀ (by omega)
  have hres' : sourceReserve H+1≤1001*(H+2)^5 := by omega
  calc
    _ ≤1000000*(H+2)*(sourceReserve H+1) := hh
    _ ≤1000000*(H+2)*(1001*(H+2)^5) := Nat.mul_le_mul_left _ hres'
    _ =1001000000*(H+2)^6 := by ring
    _ ≤_ := Nat.mul_le_mul (by norm_num) (Nat.pow_le_pow_right (by omega) (by norm_num))

end Paper37.RefinedOutputPeak
