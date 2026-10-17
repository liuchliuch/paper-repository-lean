import Paper37.DPBounds
import Paper37.ContinuationDP

/-! The actual C.8 continuation as an unreduced pair of natural integers.
The denominator D_H is shared by every term, so rational normalization is not
performed inside the DP or its output sum. -/
namespace Paper37.IntegerOutput
open Finset Paper37.DP Paper37.ContinuationDP Paper37.Envelope Paper37.Prediction

def numerator (H : ℕ) (z : List Bool) (R : ℕ) : ℕ :=
  let A := parseAge 0 z
  let r := (parseGaps 0 z).length
  let table := run H (observedCounts z) A H
  scaledNumerator H (weight (observedCounts z) (gapSet H) 0) r +
    ∑ k ∈ Icc 1 (A+R), ∑ u ∈ Icc k (A+R),
      scaledNumerator H ((layerAt table k u).2/k) (r+k)

lemma observed_sum (H : ℕ) (z : List Bool) (hz : z.length ≤ H) :
    (gapSet H).sum (observedCounts z) = (parseGaps 0 z).length := by
  simpa only [observedCounts,List.length_map] using
    sum_count_of_support ((parseGaps 0 z).map Nat.succ) (gapSet H) (observed_support z H hz)

lemma count_add_age_le (z : List Bool) :
    (parseGaps 0 z).length + parseAge 0 z ≤ z.length := by
  have hlist : ∀ g : List ℕ, g.length ≤ (g.map (fun d => d+1)).sum := by
    intro g
    induction g with
    | nil => simp
    | cons d g ih => simp only [List.length_cons,List.map_cons,List.sum_cons]; omega
  have hw := hlist (parseGaps 0 z)
  have he := parse_weight_age 0 z
  omega

/-- This pair represents exactly the source continuation, including empty
histograms and the no-future-renewal term. -/
theorem numerator_exact (H : ℕ) (z : List Bool) (R : ℕ) (hH : z.length+R≤H) :
    (numerator H z R : ℚ)/(commonDenominator H : ℚ) =
      continuationMass (z.length+R) z := by
  rw [← evaluateContinuation_correct H z R hH]
  unfold numerator evaluateContinuation
  dsimp only
  rw [Nat.cast_add,add_div,scaledNumerator_exact H _ _
    ((Nat.le_add_right _ _).trans ((count_add_age_le z).trans (by omega)))]
  congr 1
  · simp [histogramMass]
  rw [Nat.cast_sum,sum_div]
  apply sum_congr rfl
  intro k hk
  rw [Nat.cast_sum,sum_div]
  apply sum_congr rfl
  intro u hu
  rw [scaledNumerator_exact H _ _ (by
    have hh := count_add_age_le z
    have hkt := (mem_Icc.mp hk).2
    omega), Nat.cast_pow]

def valueEnvelope (H : ℕ) : ℕ := (2*H)^(4*H+1)
def outputEnvelope (H : ℕ) : ℕ := (H+1)^2 * valueEnvelope H * commonDenominator H

lemma initial_weight_le (H : ℕ) (z : List Bool) (hH : 0<H) (hz : z.length≤H) :
    weight (observedCounts z) (gapSet H) 0 ≤ valueEnvelope H := by
  have hc := count_add_age_le z
  have hs : ∑ d ∈ gapSet H, (observedCounts z d + (0:ℕ)) ≤ 2*H := by
    simpa only [add_zero,observed_sum H z hz] using (show (parseGaps 0 z).length≤2*H by omega)
  exact (weight_le_pow _ _ _ (2*H) (by omega) hs).trans
    (Nat.pow_le_pow_right (by omega) (by omega))

lemma final_entry_le (H : ℕ) (z : List Bool) (R k u : ℕ)
    (hH : 0<H) (hz : z.length+R≤H) (hk : k≤parseAge 0 z+R)
    (hu : u≤parseAge 0 z+R) :
    (layerAt (run H (observedCounts z) (parseAge 0 z) H) k u).2/k ≤ valueEnvelope H := by
  have hbudget := age_le_length z
  rw [layerAt_run _ _ _ _ _ _ (by omega) (by omega)]
  apply (Nat.div_le_self _ _).trans
  change S (observedCounts z) (gapSet H) (parseAge 0 z) k u ≤ (2*H)^(4*H+1)
  convert S_le_power (observedCounts z) (gapSet H) (parseAge 0 z) k u (2*H)
    (by omega) ?_ ?_ using 1 <;> try congr 2 <;> try omega
  · simp only [gapSet,Nat.card_Icc]; omega
  · rw [observed_sum H z (by omega)]
    have hc := count_add_age_le z
    omega

/-- Every partial output sum is bounded by the same polynomial-bit envelope;
all summands are nonnegative natural integers. -/
theorem numerator_le (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : 0<H) (hz : z.length+R≤H) : numerator H z R ≤ outputEnvelope H := by
  let T := parseAge 0 z+R
  let B := valueEnvelope H * commonDenominator H
  have hT : T≤H := by have hh := age_le_length z; dsimp [T]; omega
  have hi : scaledNumerator H (weight (observedCounts z) (gapSet H) 0)
      (parseGaps 0 z).length ≤ B :=
    (scaledNumerator_le _ _ _).trans (Nat.mul_le_mul_right _ (initial_weight_le H z hH (by omega)))
  have hs : (∑ k ∈ Icc 1 T, ∑ u ∈ Icc k T,
      scaledNumerator H
        ((layerAt (run H (observedCounts z) (parseAge 0 z) H) k u).2/k)
        ((parseGaps 0 z).length+k)) ≤ T*T*B := by
    calc
      _ ≤ ∑ _k ∈ Icc 1 T, T*B := by
        apply sum_le_sum
        intro k hk
        calc
          _ ≤ (Icc k T).card*B := by
            apply sum_le_card_nsmul
            intro u hu
            exact (scaledNumerator_le _ _ _).trans
              (Nat.mul_le_mul_right _ (final_entry_le H z R k u hH hz
                (mem_Icc.mp hk).2 (mem_Icc.mp hu).2))
          _ ≤ T*B := by
            apply Nat.mul_le_mul_right
            simp only [Nat.card_Icc]
            have := (mem_Icc.mp hk).1
            omega
      _ = _ := by simp [Nat.card_Icc,Nat.mul_assoc]
  change _ + _ ≤ _
  calc
    _ ≤ B+T*T*B := Nat.add_le_add hi hs
    _ ≤ B+H*H*B := Nat.add_le_add_left (Nat.mul_le_mul_right B (Nat.mul_self_le_mul_self hT)) B
    _ ≤ (H+1)^2*B := by nlinarith
    _ = _ := by simp only [outputEnvelope,B,Nat.mul_assoc]

lemma size_mul_le (x y : ℕ) : (x*y).size ≤ x.size+y.size+1 := by
  have hx : x≤2^x.size := (Nat.lt_size_self x).le
  have hy : y≤2^y.size := (Nat.lt_size_self y).le
  have hxy : x*y≤2^(x.size+y.size) := by rw [pow_add]; exact Nat.mul_le_mul hx hy
  exact (Nat.size_le_size hxy).trans_eq (by rw [Nat.size_pow])

/-- The output pair has an explicit polynomial bound on its actual binary
encoding. Its D_H component uses O(H² log H) bits. -/
theorem numerator_binarySize (H : ℕ) (z : List Bool) (R : ℕ)
    (hH : 0<H) (hz : z.length+R≤H) :
    (numerator H z R).size ≤
      2*(H+1).size+(4*H+1)*(2*H).size+
        (H*(H+1)/2)*H.size+5 := by
  apply (Nat.size_le_size (numerator_le H z R hH hz)).trans
  unfold outputEnvelope valueEnvelope
  have h1 := size_mul_le ((H+1)^2 * (2*H)^(4*H+1)) (commonDenominator H)
  have h2 := size_mul_le ((H+1)^2) ((2*H)^(4*H+1))
  have h3 := binarySize_le_of_le_pow ((H+1)^2) (H+1) 2 le_rfl
  have h4 := binarySize_le_of_le_pow ((2*H)^(4*H+1)) (2*H) (4*H+1) le_rfl
  have h5 := commonDenominator_binarySize H
  omega

/-- A fixed arithmetic expression uses an indexed run-time input vector. Each
input access and integer primitive has unit RAM charge. -/
inductive Expr (m : ℕ) where
  | input : Fin m → Expr m
  | add : Expr m → Expr m → Expr m
  | mul : Expr m → Expr m → Expr m
  | div : Expr m → Expr m → Expr m

def Expr.eval {m : ℕ} (v : Fin m → ℕ) : Expr m → ℕ
  | .input i => v i
  | .add x y => x.eval v+y.eval v
  | .mul x y => x.eval v*y.eval v
  | .div x y => x.eval v/y.eval v

def Expr.work {m : ℕ} : Expr m → ℕ
  | .input _ => 1
  | .add x y | .mul x y | .div x y => x.work+y.work+1

/-- Inputs: S, k, shared denominator, cached (r+k)^(r+k). -/
def scaledKernel : Expr 4 :=
  .mul (.div (.input 0) (.input 1)) (.div (.input 2) (.input 3))

theorem scaledKernel_eval (S k D p : ℕ) :
    scaledKernel.eval ![S,k,D,p] = (S/k)*(D/p) := rfl

@[simp] theorem scaledKernel_work : scaledKernel.work = 7 := rfl

/-- The instruction kernel produces the exact term used in numerator. -/
theorem scaledKernel_source (H S k r : ℕ) :
    scaledKernel.eval ![S,k,commonDenominator H,(r+k)^(r+k)] =
      scaledNumerator H (S/k) (r+k) := rfl

/-- C.8 output work charges one interpreted kernel, accumulation, table and
power-cache address arithmetic, and loop control per actual pair. The initial
weight and D_H are products of H cached values. -/
def outputWork (H : ℕ) (z : List Bool) (R : ℕ) : ℕ :=
  6*H+8 + ∑ k ∈ Icc 1 (parseAge 0 z+R),
    ∑ _u ∈ Icc k (parseAge 0 z+R), (scaledKernel.work+8)

theorem outputWork_quadratic (H : ℕ) (z : List Bool) (R : ℕ)
    (hz : z.length+R≤H) : outputWork H z R ≤ 30*(H+1)^2 := by
  have hT : parseAge 0 z+R≤H := by have hh := age_le_length z; omega
  have hs : (∑ k ∈ Icc 1 (parseAge 0 z+R),
      ∑ _u ∈ Icc k (parseAge 0 z+R), (scaledKernel.work+8)) ≤ 15*H*H := by
    calc
      _ ≤ ∑ _k ∈ Icc 1 (parseAge 0 z+R), 15*H := by
        apply sum_le_sum
        intro k hk
        simp only [scaledKernel_work,sum_const,Nat.card_Icc,smul_eq_mul]
        have h1 := (mem_Icc.mp hk).1
        have hc : parseAge 0 z+R+1-k≤H := by omega
        norm_num
        nlinarith
      _ ≤ 15*H*H := by
        simp only [sum_const,Nat.card_Icc,smul_eq_mul,Nat.add_sub_cancel]
        nlinarith
  unfold outputWork
  nlinarith

/-- An exact addition algorithm on unreduced integer pairs. It is used to
average any requested finite batch without hidden rational gcd calls. -/
def pairAdd (x y : ℕ × ℕ) : ℕ × ℕ := (x.1*y.2+y.1*x.2,x.2*y.2)

theorem pairAdd_exact (x y : ℕ × ℕ) (hx : 0<x.2) (hy : 0<y.2) :
    ((pairAdd x y).1 : ℚ)/(pairAdd x y).2 = (x.1:ℚ)/x.2+(y.1:ℚ)/y.2 := by
  have hx0 : (x.2:ℚ)≠0 := by exact_mod_cast hx.ne'
  have hy0 : (y.2:ℚ)≠0 := by exact_mod_cast hy.ne'
  simp only [pairAdd,Nat.cast_add,Nat.cast_mul]
  field_simp

/-- Cross multiplication adds binary lengths. Thus unreduced batch fractions
remain polynomial in the batch size and in the input-pair bit bound. -/
theorem pairAdd_binarySize (x y : ℕ × ℕ) :
    (pairAdd x y).2.size ≤ x.2.size+y.2.size+1 := size_mul_le _ _

lemma size_add_le (x y : ℕ) : (x+y).size ≤ max x.size y.size+2 := by
  let M := max x.size y.size
  have hx : x≤2^M := (Nat.lt_size_self x).le.trans
    (Nat.pow_le_pow_right (by omega) (le_max_left _ _))
  have hy : y≤2^M := (Nat.lt_size_self y).le.trans
    (Nat.pow_le_pow_right (by omega) (le_max_right _ _))
  have hs : x+y≤2^(M+1) := by rw [pow_succ]; omega
  exact (Nat.size_le_size hs).trans_eq (by rw [Nat.size_pow])

def pairSize (x : ℕ × ℕ) : ℕ := max x.1.size x.2.size

theorem pairAdd_size (x y : ℕ × ℕ) :
    pairSize (pairAdd x y) ≤ pairSize x+pairSize y+4 := by
  have h1 := size_mul_le x.1 y.2
  have h2 := size_mul_le y.1 x.2
  have h3 := size_add_le (x.1*y.2) (y.1*x.2)
  have h4 := size_mul_le x.2 y.2
  have hx1 : x.1.size≤pairSize x := le_max_left _ _
  have hx2 : x.2.size≤pairSize x := le_max_right _ _
  have hy1 : y.1.size≤pairSize y := le_max_left _ _
  have hy2 : y.2.size≤pairSize y := le_max_right _ _
  change max (x.1*y.2+y.1*x.2).size (x.2*y.2).size ≤ _
  apply max_le
  · apply h3.trans
    have hm : max (x.1*y.2).size (y.1*x.2).size ≤ pairSize x+pairSize y+1 :=
      max_le (by omega) (by omega)
    omega
  · omega

def pairSum : List (ℕ × ℕ) → ℕ × ℕ
  | [] => (0,1)
  | x::xs => pairAdd x (pairSum xs)

theorem pairSum_denominator_pos (xs : List (ℕ × ℕ))
    (h : ∀ x∈xs,0<x.2) : 0<(pairSum xs).2 := by
  induction xs with
  | nil => norm_num [pairSum]
  | cons x xs ih =>
    exact Nat.mul_pos (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem pairSum_exact (xs : List (ℕ × ℕ)) (h : ∀ x∈xs,0<x.2) :
    ((pairSum xs).1:ℚ)/(pairSum xs).2 =
      (xs.map (fun x => (x.1:ℚ)/x.2)).sum := by
  induction xs with
  | nil => norm_num [pairSum]
  | cons x xs ih =>
    have ht : ∀ y∈xs,0<y.2 := fun y hy => h y (by simp [hy])
    rw [pairSum,pairAdd_exact x (pairSum xs) (h x (by simp))
      (pairSum_denominator_pos xs ht),ih ht]
    rfl

/-- Both integer components of an unreduced batch sum grow only linearly in
the number of input fractions and their bit bounds. -/
theorem pairSum_binarySize (xs : List (ℕ × ℕ)) (B : ℕ)
    (h : ∀ x∈xs,pairSize x≤B) :
    pairSize (pairSum xs) ≤ xs.length*(B+4)+1 := by
  induction xs with
  | nil => norm_num [pairSum,pairSize]
  | cons x xs ih =>
    have ht : ∀ y∈xs,pairSize y≤B := fun y hy => h y (by simp [hy])
    have hx := h x (by simp)
    have hs := ih ht
    have ha := pairAdd_size x (pairSum xs)
    change pairSize (pairAdd x (pairSum xs)) ≤ _
    simp only [List.length_cons]
    nlinarith

end Paper37.IntegerOutput
