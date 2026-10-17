import Paper20.HilbertSeriesSemantics
import Paper20.Elimination
import Paper20.PartitionFinite

namespace Paper20
open Finset
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

lemma nuOf_replicate_one (r : ℕ) : nuOf (List.replicate r 1) = Nat.choose r 2 := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [List.replicate_succ,nuOf_cons,ih]
    simp only [List.sum_replicate,nsmul_eq_mul,Nat.mul_one]
    have hc := Nat.choose_succ_succ r 1
    simpa only [Nat.choose_one_right,Nat.add_comm] using hc.symm

lemma Part.ones_of_transpose_nu_zero (p : Part r) (hz : nuOf p.transpose.parts=0) :
    ∀ a ∈ p.parts, a=1 := by
  intro a ha
  obtain ⟨i,hi,hai⟩ := List.mem_iff_getElem.mp ha
  have hpos := p.pos a ha
  by_contra hne
  have htwo : 1 < a := by omega
  have hbox : (i,1) ∈ boxesOf p.parts := by
    apply (mem_boxesOf p.parts i 1).2
    refine ⟨hi,?_⟩
    rw [hai]
    exact htwo
  have hm : 1 ∈ (boxesOf p.parts).map Prod.snd := List.mem_map.mpr ⟨(i,1),hbox,rfl⟩
  have hle := List.single_le_sum (fun b hb => Nat.zero_le b) 1 hm
  rw [← p.nuOf_transpose_boxes,hz] at hle
  omega

lemma Part.parts_eq_column_of_shift_zero (p : Part r) (k : ℕ) (hk : 1 ≤ k)
    (hz : shiftE p.parts k (deg r k)=0) : p.parts=List.replicate r 1 := by
  rw [p.shiftE_eq] at hz
  have hnat : k*(Nat.choose r 2-nuOf p.parts)+(k+1)*nuOf p.transpose.parts=0 := by
    exact_mod_cast hz
  have hnu : nuOf p.transpose.parts=0 := by nlinarith
  have hp := List.eq_replicate_of_mem (p.ones_of_transpose_nu_zero hnu)
  have hs : r = p.parts.length := by
    have he := congrArg (fun xs : List ℕ => xs.sum) hp
    change p.parts.sum = (List.replicate p.parts.length 1).sum at he
    simpa only [p.sum_eq,List.sum_replicate,nsmul_eq_mul,Nat.cast_id,mul_one] using he
  rw [← hs] at hp
  exact hp

lemma Part.transpose_nu_zero_of_ones (p : Part r) (hones : ∀ a ∈ p.parts, a=1) :
    nuOf p.transpose.parts=0 := by
  rw [p.nuOf_transpose_boxes]
  apply List.sum_eq_zero
  intro j hj
  obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hj
  obtain ⟨hi,hj⟩ := (mem_boxesOf p.parts c.1 c.2).mp hc
  have he := hones p.parts[c.1] (List.getElem_mem hi)
  omega

def columnPart (r : ℕ) : Part r where
  parts := List.replicate r 1
  sorted := by simp
  pos := by
    intro a ha
    rw [(List.mem_replicate.mp ha).2]
    decide
  sum_eq := by simp

lemma shiftE_column (r k : ℕ) : shiftE (List.replicate r 1) k (deg r k)=0 := by
  have ht := (columnPart r).transpose_nu_zero_of_ones
    (by intro a ha; exact (List.mem_replicate.mp ha).2)
  have he := (columnPart r).shiftE_eq k
  change shiftE (List.replicate r 1) k (deg r k) = _ at he
  rw [he,ht]
  change ((k*(Nat.choose r 2-nuOf (List.replicate r 1))+(k+1)*0:ℕ):ℤ)=0
  rw [nuOf_replicate_one]
  simp

namespace HilbertSeriesProof

lemma hookInverse_constant (a : ℕ) (ha : 0 < a) :
    PowerSeries.constantCoeff (hookInverse a)=1 := by
  rw [hookInverse,PowerSeries.constantCoeff_inv,hook_constant a ha,inv_one]

lemma hooks_product_constant (hs : List ℕ) (hh : ∀ a ∈ hs, 0 < a) :
    PowerSeries.constantCoeff (hs.map hookInverse).prod=1 := by
  induction hs with
  | nil => simp
  | cons a hs ih =>
    rw [List.map_cons,List.prod_cons,map_mul,hookInverse_constant a (hh a (by simp)),
      ih (fun b hb => hh b (by simp [hb])),mul_one]

lemma partitionSummand_constant (p : Part r) (k : ℕ) (hk : 1 ≤ k) :
    PowerSeries.constantCoeff (partitionSummand r k p.parts)=
      if p=columnPart r then 1 else 0 := by
  classical
  unfold partitionSummand
  rw [map_mul,PowerSeries.constantCoeff_C,map_mul,
    hooks_product_constant _ (hooksOf_positive_of_mem_partitionsOf p.mem_partitionsOf),mul_one]
  by_cases hp : p=columnPart r
  · rw [if_pos hp,hp]
    change (dimOf r (List.replicate r 1):ℚ)*
      PowerSeries.constantCoeff (PowerSeries.X^(shiftE (List.replicate r 1) k (deg r k)).toNat)=1
    rw [dimOf_replicate_one,shiftE_column]
    simp
  · rw [if_neg hp]
    have hE : shiftE p.parts k (deg r k) ≠ 0 := by
      intro h
      exact hp (Part.ext_parts (p.parts_eq_column_of_shift_zero k hk h))
    have he : (shiftE p.parts k (deg r k)).toNat ≠ 0 := by
      intro h
      have hz := Int.toNat_of_nonneg (p.shiftE_nonnegative k)
      rw [h] at hz
      exact hE (by simpa using hz.symm)
    rw [map_pow,PowerSeries.constantCoeff_X,zero_pow he,mul_zero]

/-- The constant coefficient of the actual full Hilbert partition sum is
one: only the one-column partition has zero shift. -/
theorem partitionHilbertSeries_constant (r k : ℕ) (hk : 1 ≤ k) :
    PowerSeries.constantCoeff (partitionHilbertSeries r k)=1 := by
  classical
  rw [partitionHilbertSeries,← Part.sum_over_partitions r (partitionSummand r k),map_sum]
  simp only [partitionSummand_constant _ k hk]
  simp

/-- The original array program has the geometric constant coefficient one. -/
theorem hilbertArray_zero (r k : ℕ) (hk : 1 ≤ k) :
    (hilbertArray r k).getD 0 0=1 := by
  have he := hilbertArray_coeff r k 0 (Nat.zero_le _)
  rw [PowerSeries.coeff_zero_eq_constantCoeff,partitionHilbertSeries_constant r k hk] at he
  exact_mod_cast he

/-- The top BPS coefficient of the actual extraction program is one. -/
theorem bpsCoeff_top (r k : ℕ) (hk : 1 ≤ k) : bpsCoeff r k (deg r k)=1 := by
  rw [Elimination.bpsCoeff_eq_toNat r k _ le_rfl]
  have he := Elimination.bpsFromHilbert_recurrence r k (deg r k) le_rfl
  simp only [Semantics.recurrence25,Nat.sub_self,Finset.Ico_self,
    Finset.sum_empty,sub_zero] at he
  rw [ArraySemantics.fArray_correct r k 0 (Nat.zero_le _)] at he
  simp only [Semantics.hilbertResidual,Finset.sum_range_succ,Finset.sum_range_zero,
    zero_add,pow_zero,Nat.choose_zero_right,Nat.cast_one,one_mul,Nat.sub_zero] at he
  rw [hilbertArray_zero r k hk] at he
  rw [he]
  rfl

end HilbertSeriesProof


end
end Paper20
