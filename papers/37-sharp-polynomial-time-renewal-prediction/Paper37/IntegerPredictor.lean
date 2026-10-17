import Paper37.CachedOutput
import Paper37.AssignmentConditionals

namespace Paper37.IntegerPredictor
open Finset Paper37.DP Paper37.ContinuationDP Paper37.CachedOutput
open Paper37.IntegerOutput Paper37.Envelope Paper37.Prediction Paper37.EnvelopeBridge

def visiblePair (H L : ℕ) (z : List Bool) : ℕ × ℕ :=
  let x := evaluatePair H (z++[false]) (L-(z.length+1))
  let y := evaluatePair H (z++[true]) (L-(z.length+1))
  (y.1,x.1+y.1)

lemma childPair_exact (H L : ℕ) (z : List Bool) (b : Bool)
    (hL : L≤H) (hz : z.length<L) :
    let x := evaluatePair H (z++[b]) (L-(z.length+1))
    (x.1:ℚ)/(commonDenominator H:ℚ) = continuationMass L (z++[b]) := by
  have hc : (z++[b]).length+(L-(z.length+1))=L := by simp; omega
  have h := evaluatePair_correct H (z++[b]) (L-(z.length+1)) (by rw [hc];exact hL)
  rw [hc] at h
  rw [evaluatePair_eq H _ _ (by rw [hc];exact hL)] at h ⊢
  exact h

lemma childPair_positive (H L : ℕ) (z : List Bool) (b : Bool)
    (hL : L≤H) (hz : z.length<L) :
    0<(evaluatePair H (z++[b]) (L-(z.length+1))).1 := by
  have he := childPair_exact H L z b hL hz
  have hp := continuationMass_pos L (z++[b])
  dsimp only at he
  by_contra hh
  have h0 : (evaluatePair H (z++[b]) (L-(z.length+1))).1=0 := by omega
  rw [h0] at he
  simp only [Nat.cast_zero,zero_div] at he
  linarith

theorem visiblePair_exact (H L : ℕ) (z : List Bool) (hL : L≤H) (hz : z.length<L) :
    ((visiblePair H L z).1:ℚ)/(visiblePair H L z).2 =
      continuationMass L (z++[true]) /
        (continuationMass L (z++[false])+continuationMass L (z++[true])) := by
  have h0 := childPair_exact H L z false hL hz
  have h1 := childPair_exact H L z true hL hz
  have hD : (commonDenominator H:ℚ)≠0 := by exact_mod_cast (commonDenominator_pos H).ne'
  dsimp only at h0 h1
  rw [← h0,← h1]
  simp only [visiblePair,Nat.cast_add]
  field_simp

def conditionalPair (N : ℕ) (y : List Bool) : ℕ × ℕ :=
  match firstSuffix y with
  | none => (1,N-y.length+1)
  | some z => visiblePair N (N-y.length+z.length) z

theorem conditionalPair_exact (N : ℕ) (y : List Bool) (hy : y.length<N) :
    ((conditionalPair N y).1:ℚ)/(conditionalPair N y).2 = blockConditional N y := by
  unfold conditionalPair
  cases hs : firstSuffix y with
  | none =>
    have hz := firstSuffix_none_iff y |>.mp hs
    rw [hz,blockConditional_zeros N y.length hy]
    simp
  | some z =>
    dsimp only
    obtain ⟨j,hj⟩ := firstSuffix_some_decomposition y z hs
    have hlen : y.length=j+1+z.length := by simp [hj];omega
    have hL : N-y.length+z.length=N-(j+1) := by omega
    rw [hL,visiblePair_exact N _ z (by omega) (by omega),hj,
      blockConditional_firstRenewal N j z (by omega)]

theorem conditionalPair_denominator_pos (N : ℕ) (y : List Bool) (hy : y.length<N) :
    0<(conditionalPair N y).2 := by
  unfold conditionalPair
  cases hs : firstSuffix y with
  | none => simp
  | some z =>
    obtain ⟨j,hj⟩ := firstSuffix_some_decomposition y z hs
    have hlen : y.length=j+1+z.length := by simp [hj];omega
    have hp := childPair_positive N (N-y.length+z.length) z true (by omega) (by omega)
    change 0<_+_
    omega

def suffixPairs (n : ℕ) (x : List Bool) : List (ℕ × ℕ) :=
  List.ofFn (fun t : Fin n => conditionalPair (n+1) (x.drop (n-(t.val+1))))

def predictorPair (n : ℕ) (x : List Bool) : ℕ × ℕ :=
  let p := pairSum (suffixPairs n x)
  (p.1,p.2*n)

theorem predictorPair_exact (n : ℕ) (x : List Bool) (hx : x.length=n) :
    ((predictorPair n x).1:ℚ)/(predictorPair n x).2 = predict n x := by
  have hp : ∀ p∈suffixPairs n x,0<p.2 := by
    intro p hp
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hp
    apply conditionalPair_denominator_pos
    simp only [List.length_drop,hx]
    omega
  unfold predictorPair
  dsimp only
  rw [Nat.cast_mul,← div_div,pairSum_exact (suffixPairs n x) hp]
  unfold suffixPairs predict
  rw [List.map_ofFn,List.sum_ofFn]
  dsimp only [Function.comp_apply]
  rw [Fin.sum_univ_eq_sum_range (fun t : ℕ =>
    ((conditionalPair (n+1) (x.drop (n-(t+1)))).1:ℚ)/
      (conditionalPair (n+1) (x.drop (n-(t+1)))).2) n]
  congr 1
  apply sum_bij (fun t _ => t+1)
  · intro t ht
    have hh := mem_range.mp ht
    exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro i hi j hj he
    omega
  · intro t ht
    have hh := mem_Icc.mp ht
    exact ⟨t-1,mem_range.mpr (by omega),by omega⟩
  · intro t ht
    apply conditionalPair_exact
    have hh := mem_range.mp ht
    simp only [List.length_drop,hx]
    omega

def outputBitBound (H : ℕ) : ℕ :=
  2*(H+1).size+(4*H+1)*(2*H).size+(H*(H+1)/2)*H.size+5

def queryBitBound (H : ℕ) : ℕ := outputBitBound H+(H+1).size+3

theorem visiblePair_binarySize (H L : ℕ) (z : List Bool)
    (hH : 0<H) (hL : L≤H) (hz : z.length<L) :
    pairSize (visiblePair H L z) ≤ outputBitBound H+2 := by
  have hb (b : Bool) : (z++[b]).length+(L-(z.length+1))≤H := by simp;omega
  have h0 := evaluatePair_binarySize H (z++[false]) (L-(z.length+1)) hH (hb false)
  have h1 := evaluatePair_binarySize H (z++[true]) (L-(z.length+1)) hH (hb true)
  have hs := size_add_le
    (evaluatePair H (z++[false]) (L-(z.length+1))).1
    (evaluatePair H (z++[true]) (L-(z.length+1))).1
  have ha0 := le_trans (le_max_left _ _) h0
  have ha1 := le_trans (le_max_left _ _) h1
  unfold pairSize visiblePair
  dsimp only
  change max _ _ ≤ _
  apply max_le (by dsimp [outputBitBound] at *;omega)
  apply hs.trans
  have hm := max_le ha0 ha1
  dsimp [outputBitBound] at *
  omega

theorem conditionalPair_binarySize (N : ℕ) (y : List Bool) (hN : 0<N) (hy : y.length<N) :
    pairSize (conditionalPair N y) ≤ queryBitBound N := by
  unfold conditionalPair
  cases hs : firstSuffix y with
  | none =>
    dsimp only
    have hd : N-y.length+1≤N+1 := by omega
    have hd' := Nat.size_le_size hd
    have hone : (1:ℕ).size=1 := by simpa using Nat.size_pow 0
    change max (1:ℕ).size (N-y.length+1).size ≤ _
    rw [hone]
    unfold queryBitBound
    omega
  | some z =>
    dsimp only
    obtain ⟨j,hj⟩ := firstSuffix_some_decomposition y z hs
    have hlen : y.length=j+1+z.length := by simp [hj];omega
    have hb := visiblePair_binarySize N (N-y.length+z.length) z hN (by omega) (by omega)
    unfold queryBitBound
    omega

/-- The final exact compression average has polynomial bit length even when
fractions are kept unreduced throughout the whole requested suffix batch. -/
theorem predictorPair_binarySize (n : ℕ) (x : List Bool) (hx : x.length=n) :
    pairSize (predictorPair n x) ≤ n*(queryBitBound (n+1)+4)+n.size+2 := by
  have hp : ∀ p∈suffixPairs n x,pairSize p≤queryBitBound (n+1) := by
    intro p hp
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hp
    apply conditionalPair_binarySize _ _ (by omega)
    simp only [List.length_drop,hx]
    omega
  have hb := pairSum_binarySize (suffixPairs n x) (queryBitBound (n+1)) hp
  have hl : (suffixPairs n x).length=n := by simp [suffixPairs]
  rw [hl] at hb
  have h1 := le_trans (le_max_left _ _) hb
  have h2 := le_trans (le_max_right _ _) hb
  have hm := size_mul_le (pairSum (suffixPairs n x)).2 n
  change max (pairSum (suffixPairs n x)).1.size ((pairSum (suffixPairs n x)).2*n).size ≤ _
  apply max_le <;> omega

end Paper37.IntegerPredictor
