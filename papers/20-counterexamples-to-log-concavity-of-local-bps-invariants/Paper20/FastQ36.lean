import Paper20.FastR36
import Paper20.IntegerPolynomial
import Paper20.PolynomialLink

namespace Paper20.FastQ36
open Paper20.Cert.QuantumCache36 Paper20.IntegerPolynomial
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def denominatorR (j : ℕ) : ℕ := Cert.QuantumCache36.scale^j*j.factorial
def denominator (h : ℕ) : ℕ := denominatorA h*denominatorR h
def cofactor (h j : ℕ) : ℕ := denominator h/(denominatorA j*denominatorR (h-j))

theorem denominator_dvd (h j : ℕ) (hj : j ≤ h) :
    denominatorA j*denominatorR (h-j) ∣ denominator h := by
  apply Nat.mul_dvd_mul
  · exact Nat.mul_dvd_mul (pow_dvd_pow 4 hj)
      (Nat.factorial_dvd_factorial (by omega))
  · exact Nat.mul_dvd_mul (pow_dvd_pow Cert.QuantumCache36.scale (Nat.sub_le h j))
      (Nat.factorial_dvd_factorial (Nat.sub_le h j))

theorem denominator_pos (h : ℕ) : 0 < denominator h := by
  have ha := denominatorA_pos h
  have hL := scale_pos
  unfold denominator denominatorR
  positivity

theorem cofactor_correct (h j : ℕ) (hj : j ≤ h) :
    (cofactor h j:ℚ)*(denominatorA j:ℚ)*(denominatorR (h-j):ℚ) = (denominator h:ℚ) := by
  have he := Nat.div_mul_cancel (denominator_dvd h j hj)
  have hc := congrArg (fun n : ℕ => (n:ℚ)) he
  simpa only [cofactor,Nat.cast_mul,mul_assoc] using hc

def partNumerator (h i : ℕ) (ps : List ℕ) : ℤ :=
  let c := contentOf ps
  let ev := decide (c%2=0)
  let R := FastR36.values (hooksOf ps) (partsEvenHooks ps) 22
  (((dimOf 36 ps)^2:ℕ):ℤ)*((List.range (h+1)).map (fun j =>
    R.getD (h-j) 0*(numeratorA (c*c) ev j).getD i 0*(cofactor h j:ℤ))).sum

theorem values22_scaled {ps : List ℕ} (hp : ps ∈ partitionsOf 36) (h j : ℕ)
    (hH : h ≤ 22) (hj : j ≤ h) :
    ((FastR36.values (hooksOf ps) (partsEvenHooks ps) 22).getD (h-j) 0:ℚ) =
      (denominatorR (h-j):ℚ)*(Rseries (hooksOf ps) (partsEvenHooks ps) h).getD (h-j) 0 := by
  have hv := FastR36.values_coeff (hooksOf ps) (partsEvenHooks ps) 22 (h-j)
    (hooksOf_positive_of_mem_partitionsOf hp) (hooksOf_le_of_mem_partitionsOf hp)
    (by decide) (by omega)
  rw [← LogSeries.Rseries_correct (hooksOf ps) (partsEvenHooks ps) h (h-j)
    (hooksOf_positive_of_mem_partitionsOf hp) (by omega)] at hv
  simpa only [denominatorR,Nat.cast_mul,Nat.cast_pow,mul_assoc] using hv

theorem partNumerator_scaled {ps : List ℕ} (hp : ps ∈ partitionsOf 36)
    (h i : ℕ) (hH : h ≤ 22) :
    (partNumerator h i ps:ℚ) = (denominator h:ℚ)*cget (partQ 36 h ps) i := by
  have hs : (((List.range (h+1)).map (fun j =>
      (FastR36.values (hooksOf ps) (partsEvenHooks ps) 22).getD (h-j) 0*
        (numeratorA (contentOf ps*contentOf ps) (decide (contentOf ps%2=0)) j).getD i 0*
          (cofactor h j:ℤ))).sum:ℚ) =
      (denominator h:ℚ)*((List.range (h+1)).map (fun j =>
        (Rseries (hooksOf ps) (partsEvenHooks ps) h).getD (h-j) 0*
          cget (Apoly (contentOf ps*contentOf ps) (decide (contentOf ps%2=0)) j) i)).sum := by
    rw [Int.cast_list_sum,List.map_map]
    simp only [Function.comp_def,Int.cast_mul,Int.cast_natCast]
    rw [ScaledIntegration.sum_map_range_rat,LogSeries.sum_map_range,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjh : j ≤ h := by have := Finset.mem_range.mp hj; omega
    rw [values22_scaled hp h j hH hjh,numeratorA_coeff]
    calc
      _ = ((cofactor h j:ℚ)*(denominatorA j:ℚ)*(denominatorR (h-j):ℚ))*
          ((Rseries (hooksOf ps) (partsEvenHooks ps) h).getD (h-j) 0*
            cget (Apoly (contentOf ps*contentOf ps) (decide (contentOf ps%2=0)) j) i) := by ring
      _ = _ := by rw [cofactor_correct h j hjh]
  dsimp only [partNumerator,partQ]
  rw [Int.cast_mul,Int.cast_natCast,hs,cget_psmul,cget_innerSum]
  simp only [partsDim_eq_dimOf,partsHooks_eq_hooksOf,partsContent_eq_contentOf,pow_two]
  ring

def totalNumerator (h i : ℕ) : ℤ :=
  ((partitionsOf 36).map (partNumerator h i)).sum

/-- The integer optimized complete sum is linked to the very same Qcoeff
as the required paper statements; no numerical certificate equality is an input. -/
theorem totalNumerator_scaled (h i : ℕ) (hH : h ≤ 22) :
    (totalNumerator h i:ℚ) =
      (denominator h:ℚ)*((36:ℕ).factorial:ℚ)*cget (Qcoeff 36 h) i := by
  rw [totalNumerator,Int.cast_list_sum,List.map_map,cget_Qcoeff]
  have hs : ((partitionsOf 36).map (fun ps => (partNumerator h i ps:ℚ))).sum =
      (denominator h:ℚ)*((partitionsOf 36).map (fun ps => cget (partQ 36 h ps) i)).sum := by
    have aux : ∀ xs : List (List ℕ), (∀ q ∈ xs, q ∈ partitionsOf 36) →
          (xs.map (fun q => (partNumerator h i q:ℚ))).sum =
            (denominator h:ℚ)*(xs.map (fun q => cget (partQ 36 h q) i)).sum := by
      intro xs hx
      induction xs with
      | nil => simp
      | cons q qs ih =>
        simp only [List.map_cons,List.sum_cons]
        rw [partNumerator_scaled (hx q (by simp)) h i hH,ih (fun u hu => hx u (by simp [hu]))]
        ring
    exact aux _ (fun q hq => hq)
  dsimp only [Function.comp_def]
  rw [hs]
  have hf : ((36:ℕ).factorial:ℚ) ≠ 0 := by positivity
  field_simp

end
end Paper20.FastQ36
