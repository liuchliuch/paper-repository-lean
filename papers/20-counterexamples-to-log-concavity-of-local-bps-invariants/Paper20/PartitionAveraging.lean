import Paper20.PartitionFinite
import Paper20.ConjugateContent

namespace Paper20
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

theorem Part.sum_transpose {M : Type*} [AddCommMonoid M] (r : ℕ) (f : Part r → M) :
    (∑ p : Part r, f p.transpose) = ∑ p : Part r, f p := by
  classical
  exact Fintype.sum_equiv (Part.transposeEquiv r) _ _ (by intro p; rfl)

variable {K : Type*} [Field K] [CharZero K]

def quantumInteger (a : ℕ) (v : K) : K := (v^a-(v⁻¹)^a)/(v-v⁻¹)

def quantumDenominator (ps : List ℕ) (v : K) : K :=
  ((hooksOf ps).map (fun a => quantumInteger a v)).prod

theorem Part.quantumDenominator_transpose (p : Part r) (v : K) :
    quantumDenominator p.transpose.parts v = quantumDenominator p.parts v :=
  (p.hooks_transpose_perm.map (fun a => quantumInteger a v)).prod_eq

def quantumTerm (r k : ℕ) (v : K) (p : Part r) : K :=
  (dimOf r p.parts:K)*v^(((2*k+1:ℕ):ℤ)*contentOf p.parts)/quantumDenominator p.parts v

def quantumPartitionTrace (r k : ℕ) (v : K) : K := ∑ p : Part r, quantumTerm r k v p

lemma symmetric_zpow_natAbs (v : K) (c : ℤ) :
    v^c+v^(-c) = v^c.natAbs+(v⁻¹)^c.natAbs := by
  cases c with
  | ofNat n => simp [zpow_natCast, inv_pow]
  | negSucc n =>
    change v^(-((n+1:ℕ):ℤ))+v^(-(-((n+1:ℕ):ℤ))) = v^(n+1)+(v⁻¹)^(n+1)
    simp only [neg_neg, zpow_neg, zpow_natCast, inv_pow, add_comm]

theorem paired_quantumTerm (r k : ℕ) (v : K) (p : Part r) :
    (quantumTerm r k v p+quantumTerm r k v p.transpose)/2 =
      (dimOf r p.parts:K)*
        (v^((2*k+1)*(contentOf p.parts).natAbs)+
          (v⁻¹)^((2*k+1)*(contentOf p.parts).natAbs))/
        (2*quantumDenominator p.parts v) := by
  unfold quantumTerm
  rw [p.dimOf_transpose, p.contentOf_transpose, p.quantumDenominator_transpose]
  have he : ((2*k+1:ℕ):ℤ)*(-contentOf p.parts) =
      -(((2*k+1:ℕ):ℤ)*contentOf p.parts) := by ring
  rw [he]
  have hs := symmetric_zpow_natAbs v (((2*k+1:ℕ):ℤ)*contentOf p.parts)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hs
  calc
    _ = (dimOf r p.parts:K)*
        (v^(((2*k+1:ℕ):ℤ)*contentOf p.parts)+
          v^(-(((2*k+1:ℕ):ℤ)*contentOf p.parts)))/(2*quantumDenominator p.parts v) := by ring
    _ = _ := by rw [hs]

/-- The partition-conjugation averaging step in (21), over the actual
complete enumeration via its proved equivalence with all partitions. -/
theorem quantumPartitionTrace_averaged (r k : ℕ) (v : K) :
    quantumPartitionTrace r k v =
      ∑ p : Part r, (dimOf r p.parts:K)*
        (v^((2*k+1)*(contentOf p.parts).natAbs)+
          (v⁻¹)^((2*k+1)*(contentOf p.parts).natAbs))/
        (2*quantumDenominator p.parts v) := by
  classical
  have ht := Part.sum_transpose r (quantumTerm r k v)
  have htwo : (2:K) ≠ 0 := by norm_num
  unfold quantumPartitionTrace
  calc
    _ = ((∑ p : Part r, quantumTerm r k v p)+
        (∑ p : Part r, quantumTerm r k v p.transpose))/2 := by rw [ht]; field_simp; ring
    _ = ∑ p : Part r, (quantumTerm r k v p+quantumTerm r k v p.transpose)/2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      exact paired_quantumTerm r k v p

end
end Paper20
