import Paper37.CachedQueries
import Paper37.CachedOutput
import Paper37.IntegerPredictor

/-! Integer-only output and mixture arithmetic for the actual occupied-type
refinement table. Every restriction shares one cache and one rolling table. -/
namespace Paper37.AdaptiveIntegerOutput
open Finset Paper37.DP Paper37.Envelope Paper37.Prediction Paper37.Adaptive
open Paper37.ContinuationDP Paper37.RefinedContinuation Paper37.AdaptiveDP
open Paper37.CachedDP Paper37.CachedRefinedDP Paper37.CachedOutput Paper37.IntegerOutput

/-- All numerators use the same positive denominator D_H. The refinement
recurrence and coefficient cache are constructed once for this whole vector. -/
def allNumerators (H : ℕ) (z : List Bool) (R : ℕ) : Vector ℕ (H+1) :=
  let c := makeObservedCache H z
  let D := denominator c
  let r := (parseGaps 0 z).length
  let A := parseAge 0 z
  let table := cachedRefinedRun H c A H
  let initial := initialNumerator c * (D/powerAt c r)
  Vector.ofFn fun t => (if nu z≤t.val then initial else 0) +
    ∑ k ∈ Icc 1 (A+R), ∑ u ∈ Icc k (A+R),
      scaledKernel.eval ![∑ j ∈ range (t.val+1), (refinedLayerAt table k u j).2,
        k,D,powerAt c (r+k)]

theorem allNumerators_source (H : ℕ) (z : List Bool) (R : ℕ)
    (hz : z.length+R≤H) (t : Fin (H+1)) :
    (allNumerators H z R)[t.val] =
      (if nu z≤t.val then scaledNumerator H (weight (observedCounts z) (gapSet H) 0)
        (parseGaps 0 z).length else 0) +
      ∑ k ∈ Icc 1 (parseAge 0 z+R), ∑ u ∈ Icc k (parseAge 0 z+R),
        scaledNumerator H
          ((∑ j ∈ range (t.val+1), refinedSd (observedCounts z) (parseAge 0 z) H k u j)/k)
          ((parseGaps 0 z).length+k) := by
  unfold allNumerators
  dsimp only
  simp only [Vector.getElem_ofFn]
  rw [denominator_source,initialNumerator_source H z (by omega),makeObservedCache_eq,
    cachedRefinedRun_correct H (observedCounts z) (parseAge 0 z) H le_rfl
      (observedCounts_le_horizon H z (by omega)),
    powerAt_correct H (observedCounts z) _ (by
      have hh := count_add_age_le z; omega)]
  change (if _ then scaledNumerator _ _ _ else 0)+_=_
  congr 1
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro u hu
  rw [powerAt_correct H (observedCounts z) _ (by
    have hc := count_add_age_le z
    have hkt := (mem_Icc.mp hk).2; omega),scaledKernel_source]
  congr 2
  apply sum_congr rfl
  intro j hj
  have hT : parseAge 0 z+R≤H := by have hh := age_le_length z;omega
  rw [refinedLayerAt_run H (observedCounts z) (parseAge 0 z) H k u j
    ((mem_Icc.mp hk).2.trans hT) ((mem_Icc.mp hu).2.trans hT) (by
      have hh := mem_range.mp hj; have ht := t.isLt;omega)]

theorem allNumerators_exact (H : ℕ) (z : List Bool) (R : ℕ)
    (hz : z.length+R≤H) (t : Fin (H+1)) :
    ((allNumerators H z R)[t.val]:ℚ)/(commonDenominator H:ℚ) =
      restrictedContinuation (z.length+R) t.val z := by
  rw [allNumerators_source H z R hz t,restrictedContinuation_eq_integerDP H t.val z R hz,
    Nat.cast_add,add_div]
  have hr : (parseGaps 0 z).length≤H := by have hh := count_add_age_le z;omega
  have hi := scaledNumerator_exact H (weight (observedCounts z) (gapSet H) 0) _ hr
  have hw := histogramMass_zero H z (by omega)
  have hi' : (scaledNumerator H (weight (observedCounts z) (gapSet H) 0)
      (parseGaps 0 z).length:ℚ)/(commonDenominator H:ℚ) = wordEnvelope z := by
    rw [hi]
    simpa [histogramMass] using hw
  have hn : ((if nu z≤t.val then scaledNumerator H (weight (observedCounts z) (gapSet H) 0)
      (parseGaps 0 z).length else 0:ℕ):ℚ)/(commonDenominator H:ℚ)=restrictedEnvelope t.val z := by
    by_cases ht : nu z≤t.val
    · simpa only [ht,if_true,restrictedEnvelope] using hi'
    · simp [ht,restrictedEnvelope]
  rw [hn,Nat.cast_sum,sum_div]
  refine congrArg (fun q:ℚ => restrictedEnvelope t.val z+q) ?_
  apply sum_congr rfl
  intro k hk
  rw [Nat.cast_sum,sum_div]
  apply sum_congr rfl
  intro u hu
  rw [scaledNumerator_exact H _ _ (by
    have hh := count_add_age_le z
    have hk' := (mem_Icc.mp hk).2;omega),Nat.cast_pow]

lemma restrictedContinuation_le (L t : ℕ) (z : List Bool) :
    restrictedContinuation L t z ≤ continuationMass L z := by
  unfold restrictedContinuation continuationMass
  apply sum_le_sum
  intro v hv
  unfold restrictedEnvelope
  split_ifs
  · exact le_rfl
  · exact (wordEnvelope_pos _).le

/-- The actual integer numerator for every restriction is bounded by the
ordinary continuation numerator with exactly the same common denominator. -/
theorem allNumerators_le (H : ℕ) (z : List Bool) (R : ℕ)
    (hz : z.length+R≤H) (t : Fin (H+1)) :
    (allNumerators H z R)[t.val] ≤ numerator H z R := by
  have he := allNumerators_exact H z R hz t
  have ho := numerator_exact H z R hz
  have hp : (0:ℚ)<commonDenominator H := by exact_mod_cast commonDenominator_pos H
  have hq := restrictedContinuation_le (z.length+R) t.val z
  rw [←he,←ho] at hq
  exact_mod_cast (div_le_div_iff_of_pos_right hp).mp hq

theorem allNumerators_binarySize (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : 0<H) (hz : z.length+R≤H) (t : Fin (H+1)) :
    ((allNumerators H z R)[t.val]).size ≤ Paper37.IntegerPredictor.outputBitBound H := by
  exact (Nat.size_le_size (allNumerators_le H z R hz t)).trans
    (numerator_binarySize H z R hH hz)

/-- An arbitrary component index is capped at H after the shared vector has
been computed; all source words have at most H occupied types. -/
def lookupNumerator {H : ℕ} (values : Vector ℕ (H+1)) (t : ℕ) : ℕ :=
  values[min t H]'(by have hh := min_le_right t H;omega)

theorem lookupNumerator_exact (H t : ℕ) (z : List Bool) (R : ℕ)
    (hz : z.length+R≤H) :
    (lookupNumerator (allNumerators H z R) t:ℚ)/(commonDenominator H:ℚ) =
      restrictedContinuation (z.length+R) t z := by
  unfold lookupNumerator
  rw [allNumerators_exact H z R hz ⟨min t H,by have hh := min_le_right t H;omega⟩]
  exact (restrictedContinuation_cap H t z R hz).symm

/-- Exact E.3 mixture weight, kept as an unreduced natural pair. -/
def weightPair (N t : ℕ) : ℕ×ℕ :=
  if t=N then (N+1,2*N) else (1,2*t*(t+1))

theorem weightPair_exact (N t : ℕ) (hN : 0<N) (ht : 0<t) :
    ((weightPair N t).1:ℚ)/(weightPair N t).2=omegaWeight N t := by
  unfold weightPair omegaWeight
  by_cases h:t=N
  · subst t
    simp only [if_true,Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat]
    have hq : (N:ℚ)≠0 := by exact_mod_cast hN.ne'
    field_simp
  · simp [h]

theorem weightPair_denominator_pos (N t : ℕ) (hN : 0<N) (ht : 0<t) :
    0<(weightPair N t).2 := by
  unfold weightPair
  split_ifs <;> dsimp only <;> positivity

lemma lookupNumerator_pos (H t : ℕ) (L : ℕ) (hL : L≤H) :
    0<lookupNumerator (allNumerators H [] L) t := by
  have he := lookupNumerator_exact H t [] L (by simpa using hL)
  simp only [List.length_nil,zero_add,restrictedContinuation_nil] at he
  have hp := restrictedNormalizer_pos L t
  by_contra hh
  have hz : lookupNumerator (allNumerators H [] L) t=0 := by omega
  rw [hz] at he
  simp only [Nat.cast_zero,zero_div] at he
  linarith

/-- All mixture components read the same already-computed numerator vectors.
The empirical denominator D_H cancels between mass and normalizer. -/
def componentPairs (N : ℕ) (masses normalizers : Vector ℕ (N+1)) : List (ℕ×ℕ) :=
  List.ofFn fun t : Fin N =>
    let s := t.val+1
    let w := weightPair N s
    (w.1*lookupNumerator masses s,w.2*(N+1)*lookupNumerator normalizers s)

/-- The source adaptive prefix is evaluated using integer pairs only. At a
visible first renewal it builds two shared all-restriction tables and then
adds the finite mixture by exact cross multiplication. -/
def prefixPair (N : ℕ) (y : List Bool) : ℕ×ℕ :=
  match firstSuffix y with
  | none => (N-y.length+1,N+1)
  | some z =>
    let L := N-y.length+z.length
    let masses := allNumerators N z (L-z.length)
    let normalizers := allNumerators N [] L
    pairSum (componentPairs N masses normalizers)

lemma componentPairs_positive (N L : ℕ) (z : List Bool) (hN : 0<N) (hL : L≤N) :
    ∀ p∈componentPairs N (allNumerators N z (L-z.length)) (allNumerators N [] L),0<p.2 := by
  intro p hp
  obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hp
  dsimp only
  exact Nat.mul_pos (Nat.mul_pos (weightPair_denominator_pos N (t.val+1) hN (by omega))
    (by omega)) (lookupNumerator_pos N (t.val+1) L hL)

lemma componentPairs_exact (N L : ℕ) (z : List Bool) (hN : 0<N) (hL : L≤N) (hz : z.length≤L) :
    ((pairSum (componentPairs N (allNumerators N z (L-z.length))
      (allNumerators N [] L))).1:ℚ)/
      (pairSum (componentPairs N (allNumerators N z (L-z.length)) (allNumerators N [] L))).2 =
    ∑ t ∈ Icc 1 N, omegaWeight N t *
      (restrictedContinuation L t z/((N+1:ℚ)*restrictedNormalizer L t)) := by
  rw [pairSum_exact _ (componentPairs_positive N L z hN hL)]
  unfold componentPairs
  rw [List.map_ofFn,List.sum_ofFn]
  dsimp only [Function.comp_apply]
  rw [Fin.sum_univ_eq_sum_range (fun t:ℕ =>
    (((weightPair N (t+1)).1*lookupNumerator (allNumerators N z (L-z.length)) (t+1):ℕ):ℚ)/
      (((weightPair N (t+1)).2*(N+1)*lookupNumerator (allNumerators N [] L) (t+1):ℕ):ℚ)) N]
  apply sum_bij (fun t _ => t+1)
  · intro t ht; have hh := mem_range.mp ht;exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro i hi j hj he;omega
  · intro t ht;have hh := mem_Icc.mp ht;exact ⟨t-1,mem_range.mpr (by omega),by omega⟩
  · intro t ht
    have hm := lookupNumerator_exact N (t+1) z (L-z.length) (by omega)
    have hn := lookupNumerator_exact N (t+1) [] L (by simpa using hL)
    rw [Nat.add_sub_of_le hz] at hm
    simp only [List.length_nil,zero_add,restrictedContinuation_nil] at hn
    rw [←hm,←hn,←weightPair_exact N (t+1) hN (by omega)]
    have hD : (commonDenominator N:ℚ)≠0 := by exact_mod_cast (commonDenominator_pos N).ne'
    simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    field_simp

theorem prefixPair_exact (N : ℕ) (y : List Bool) (hN : 0<N) (hy : y.length≤N) :
    ((prefixPair N y).1:ℚ)/(prefixPair N y).2=adaptivePrefix N y := by
  unfold prefixPair
  cases hs:firstSuffix y with
  | none =>
    dsimp only
    rw [adaptivePrefix_eq_mix N y hy]
    have hz := (Paper37.EnvelopeBridge.firstSuffix_none_iff y).mp hs
    have hp (t:ℕ) : restrictedPrefix N t y=((N-y.length+1:ℕ):ℚ)/(N+1:ℚ) := by
      conv_lhs => rw [hz,restrictedPrefix_zeros N t y.length hy]
    simp_rw [hp]
    rw [←sum_mul,omegaWeight_sum (by omega),one_mul]
    simp
  | some z =>
    dsimp only
    obtain ⟨j,hj⟩ := Paper37.EnvelopeBridge.firstSuffix_some_decomposition y z hs
    have hl : y.length=j+1+z.length := by simp [hj];omega
    have hL : N-y.length+z.length=N-(j+1) := by omega
    rw [hL,componentPairs_exact N _ z hN (by omega) (by omega),adaptivePrefix_eq_mix N y hy]
    apply sum_congr rfl
    intro t ht
    rw [hj,restrictedPrefix_firstRenewal N t j z (by omega)]

theorem prefixPair_denominator_pos (N : ℕ) (y : List Bool) (hN : 0<N) (hy : y.length≤N) :
    0<(prefixPair N y).2 := by
  unfold prefixPair
  cases hs:firstSuffix y with
  | none => dsimp only;omega
  | some z =>
    dsimp only
    apply pairSum_denominator_pos
    apply componentPairs_positive N _ z hN
    obtain ⟨j,hj⟩ := Paper37.EnvelopeBridge.firstSuffix_some_decomposition y z hs
    have hl : y.length=j+1+z.length := by simp [hj];omega
    omega

theorem prefixPair_numerator_pos (N : ℕ) (y : List Bool) (hN : 0<N) (hy : y.length≤N) :
    0<(prefixPair N y).1 := by
  have he := prefixPair_exact N y hN hy
  have hp := adaptivePrefix_pos (by omega : 1≤N) y hy
  by_contra hh
  have hz : (prefixPair N y).1=0 := by omega
  rw [hz] at he
  simp only [Nat.cast_zero,zero_div] at he
  linarith

/-- Exact integer division of two mixed prefix masses, after E.3 mixing. -/
def conditionalPair (N : ℕ) (y : List Bool) : ℕ×ℕ :=
  let c := prefixPair N (y++[true])
  let p := prefixPair N y
  (c.1*p.2,c.2*p.1)

theorem conditionalPair_exact (N : ℕ) (y : List Bool) (hy : y.length<N) :
    ((conditionalPair N y).1:ℚ)/(conditionalPair N y).2=adaptiveConditional N y := by
  unfold conditionalPair adaptiveConditional
  dsimp only
  rw [←prefixPair_exact N (y++[true]) (by omega) (by simp;omega),
    ←prefixPair_exact N y (by omega) hy.le]
  simp only [Nat.cast_mul]
  field_simp

theorem conditionalPair_denominator_pos (N : ℕ) (y : List Bool) (hy : y.length<N) :
    0<(conditionalPair N y).2 := by
  exact Nat.mul_pos (prefixPair_denominator_pos N (y++[true]) (by omega) (by simp;omega))
    (prefixPair_numerator_pos N y (by omega) hy.le)

def suffixPairs (n : ℕ) (x : List Bool) : List (ℕ×ℕ) :=
  List.ofFn fun t:Fin n => conditionalPair (n+1) (x.drop (n-(t.val+1)))

def predictorPair (n : ℕ) (x : List Bool) : ℕ×ℕ :=
  let p := pairSum (suffixPairs n x)
  (p.1,p.2*n)

theorem predictorPair_exact (n : ℕ) (x : List Bool) (hx : x.length=n) :
    ((predictorPair n x).1:ℚ)/(predictorPair n x).2=adaptivePredict n x := by
  have hp : ∀ p∈suffixPairs n x,0<p.2 := by
    intro p hp
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hp
    apply conditionalPair_denominator_pos
    simp only [List.length_drop,hx];omega
  unfold predictorPair
  dsimp only
  rw [Nat.cast_mul,←div_div,pairSum_exact _ hp]
  unfold suffixPairs adaptivePredict
  rw [List.map_ofFn,List.sum_ofFn]
  dsimp only [Function.comp_apply]
  rw [Fin.sum_univ_eq_sum_range (fun t:ℕ =>
    ((conditionalPair (n+1) (x.drop (n-(t+1)))).1:ℚ)/
      (conditionalPair (n+1) (x.drop (n-(t+1)))).2) n]
  congr 1
  apply sum_bij (fun t _ => t+1)
  · intro t ht;have hh := mem_range.mp ht;exact mem_Icc.mpr ⟨by omega,by omega⟩
  · intro i hi j hj he;omega
  · intro t ht;have hh := mem_Icc.mp ht;exact ⟨t-1,mem_range.mpr (by omega),by omega⟩
  · intro t ht
    apply conditionalPair_exact
    have hh := mem_range.mp ht
    simp only [List.length_drop,hx];omega

def weightBitBound (N : ℕ) : ℕ := 2*(2*(N+1)).size+1

theorem weightPair_binarySize (N t : ℕ) (hN : 0<N) (ht : t≤N) :
    pairSize (weightPair N t)≤weightBitBound N := by
  have hnum : (weightPair N t).1≤(2*(N+1))^2 := by
    unfold weightPair
    split_ifs <;> dsimp only <;> nlinarith
  have hden : (weightPair N t).2≤(2*(N+1))^2 := by
    unfold weightPair
    split_ifs
    · dsimp only;nlinarith
    · dsimp only
      have hm := Nat.mul_le_mul ht (show t+1≤N+1 by omega)
      nlinarith
  exact max_le (binarySize_le_of_le_pow _ _ _ hnum) (binarySize_le_of_le_pow _ _ _ hden)

lemma lookupNumerator_binarySize (H t : ℕ) (z : List Bool) (R : ℕ)
    (hH : 0<H) (hz : z.length+R≤H) :
    (lookupNumerator (allNumerators H z R) t).size≤Paper37.IntegerPredictor.outputBitBound H := by
  unfold lookupNumerator
  exact allNumerators_binarySize H z R hH hz ⟨min t H,by have hh := min_le_right t H;omega⟩

def componentBitBound (N : ℕ) : ℕ := weightBitBound N+
  Paper37.IntegerPredictor.outputBitBound N+(N+1).size+2

lemma componentPairs_binarySize (N L : ℕ) (z : List Bool)
    (hN : 0<N) (hL : L≤N) (hz : z.length≤L) :
    ∀ p∈componentPairs N (allNumerators N z (L-z.length)) (allNumerators N [] L),
      pairSize p≤componentBitBound N := by
  intro p hp
  obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hp
  dsimp only
  have hw := weightPair_binarySize N (t.val+1) hN (by have hh := t.isLt;omega)
  have hm := lookupNumerator_binarySize N (t.val+1) z (L-z.length) hN (by omega)
  have hn := lookupNumerator_binarySize N (t.val+1) [] L hN (by simpa using hL)
  have hw1 := (le_max_left _ _).trans hw
  have hw2 := (le_max_right _ _).trans hw
  have hmul1 := size_mul_le (weightPair N (t.val+1)).1
    (lookupNumerator (allNumerators N z (L-z.length)) (t.val+1))
  have hmul2 := size_mul_le (weightPair N (t.val+1)).2 (N+1)
  have hmul3 := size_mul_le ((weightPair N (t.val+1)).2*(N+1))
    (lookupNumerator (allNumerators N [] L) (t.val+1))
  unfold pairSize
  dsimp only
  apply max_le <;> unfold componentBitBound <;> omega

def prefixBitBound (N : ℕ) : ℕ := N*(componentBitBound N+4)+(N+1).size+3

theorem prefixPair_binarySize (N : ℕ) (y : List Bool) (hN : 0<N) (hy : y.length≤N) :
    pairSize (prefixPair N y)≤prefixBitBound N := by
  unfold prefixPair
  cases hs:firstSuffix y with
  | none =>
    dsimp only
    have hn : N-y.length+1≤N+1 := by omega
    have hb := Nat.size_le_size hn
    unfold pairSize prefixBitBound
    dsimp only
    exact max_le (by omega) (by omega)
  | some z =>
    dsimp only
    obtain ⟨j,hj⟩ := Paper37.EnvelopeBridge.firstSuffix_some_decomposition y z hs
    have hl : y.length=j+1+z.length := by simp [hj];omega
    have hp := pairSum_binarySize _ (componentBitBound N)
      (componentPairs_binarySize N (N-y.length+z.length) z hN (by omega) (by omega))
    have hlen : (componentPairs N (allNumerators N z (N-y.length+z.length-z.length))
        (allNumerators N [] (N-y.length+z.length))).length=N := by simp [componentPairs]
    rw [hlen] at hp
    unfold prefixBitBound
    omega

def conditionalBitBound (N : ℕ) : ℕ := 2*prefixBitBound N+1

theorem conditionalPair_binarySize (N : ℕ) (y : List Bool) (hy : y.length<N) :
    pairSize (conditionalPair N y)≤conditionalBitBound N := by
  have hc := prefixPair_binarySize N (y++[true]) (by omega) (by simp;omega)
  have hp := prefixPair_binarySize N y (by omega) hy.le
  have hc1 := (le_max_left _ _).trans hc
  have hc2 := (le_max_right _ _).trans hc
  have hp1 := (le_max_left _ _).trans hp
  have hp2 := (le_max_right _ _).trans hp
  have hm1 := size_mul_le (prefixPair N (y++[true])).1 (prefixPair N y).2
  have hm2 := size_mul_le (prefixPair N (y++[true])).2 (prefixPair N y).1
  unfold pairSize conditionalPair conditionalBitBound
  dsimp only
  apply max_le <;> omega

theorem predictorPair_binarySize (n : ℕ) (x : List Bool) (hx : x.length=n) :
    pairSize (predictorPair n x)≤n*(conditionalBitBound (n+1)+4)+n.size+2 := by
  have hp : ∀ p∈suffixPairs n x,pairSize p≤conditionalBitBound (n+1) := by
    intro p hp
    obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hp
    apply conditionalPair_binarySize
    simp only [List.length_drop,hx];omega
  have hs := pairSum_binarySize (suffixPairs n x) (conditionalBitBound (n+1)) hp
  have hn := size_mul_le (pairSum (suffixPairs n x)).2 n
  have ha := (le_max_left _ _).trans hs
  have hb := (le_max_right _ _).trans hs
  have hlen : (suffixPairs n x).length=n := by simp [suffixPairs]
  rw [hlen] at hs ha hb
  unfold pairSize predictorPair
  dsimp only
  apply max_le <;> omega

/-- This is the actual extraction-loop schedule: each restriction scans the
same finite k,u states and sums its occupied-coordinate prefix. -/
def extractionWork (N : ℕ) (z : List Bool) (R : ℕ) : ℕ :=
  8*N+12 + ∑ t ∈ range (N+1), (4+∑ k ∈ Icc 1 (parseAge 0 z+R),
    ∑ _u ∈ Icc k (parseAge 0 z+R), (16+3*(t+1)))

theorem extractionWork_quartic (N : ℕ) (z : List Bool) (R : ℕ)
    (hz : z.length+R≤N) : extractionWork N z R≤40*(N+1)^4 := by
  have hT : parseAge 0 z+R≤N := by have hh := age_le_length z;omega
  have hi (t:ℕ) (ht:t<N+1) :
      (∑ k ∈ Icc 1 (parseAge 0 z+R),∑ _u ∈ Icc k (parseAge 0 z+R),
        (16+3*(t+1))) ≤N*N*(19+3*N) := by
    calc
      _ ≤ ∑ _k ∈ Icc 1 (parseAge 0 z+R), N*(19+3*N) := by
        apply sum_le_sum
        intro k hk
        simp only [sum_const,Nat.card_Icc,smul_eq_mul]
        have hk1 := (mem_Icc.mp hk).1
        apply Nat.mul_le_mul (by omega) (by omega)
      _ ≤ N*N*(19+3*N) := by
        simp only [sum_const,Nat.card_Icc,smul_eq_mul,Nat.add_sub_cancel]
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (N*(19+3*N)) hT
  have hs : (∑ t ∈ range (N+1),(4+∑ k ∈ Icc 1 (parseAge 0 z+R),
      ∑ _u ∈ Icc k (parseAge 0 z+R),(16+3*(t+1))))≤
      (N+1)*(4+N*N*(19+3*N)) := by
    calc
      _ ≤ ∑ _t ∈ range (N+1),(4+N*N*(19+3*N)) := by
        apply sum_le_sum;intro t ht;exact Nat.add_le_add_left (hi t (mem_range.mp ht)) 4
      _ = _ := by simp
  unfold extractionWork
  nlinarith [sq_nonneg (N*N),sq_nonneg N]

end Paper37.AdaptiveIntegerOutput
