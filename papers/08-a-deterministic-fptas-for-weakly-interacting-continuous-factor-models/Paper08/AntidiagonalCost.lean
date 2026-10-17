import Paper08.LowDegreeDiscreteCost
import Paper08.Connected
import Paper08.TupleCount
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! # Source work of recursive antidiagonal generation

The recursion below follows the actual `finAntidiagonal` and
`List.Nat.antidiagonalTuple` sources. It counts recursive calls, including
empty terminal branches, every antidiagonal split, and every copied tuple.
The bounds use the sum of coordinates and never enumerate a coordinate box.
-/
open scoped BigOperators
namespace Paper08.AntidiagonalCost
open LowDegreeDiscreteCost

def tupleKey {k : ℕ} (ν : Fin k → ℕ) : List ℕ := List.ofFn ν

lemma size_le_succ (a : ℕ) : a.size ≤ a+1 :=
  (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)

lemma tupleKey_bits {k n : ℕ} (ν : Fin k → ℕ) (hν : ∑ i, ν i ≤ n) :
    keyBits (tupleKey ν) ≤ k*(n+2)+1 := by
  apply keyBits_ofFn_le
  intro i
  have hi : ν i ≤ n := (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans hν
  have hh := size_le_succ (ν i)
  omega

lemma card_finAntidiagonal_le (k n : ℕ) :
    (Finset.finAntidiagonal k n).card ≤ 2^(n+k) := by
  have hsub : Finset.finAntidiagonal k n ⊆ TupleCount.boundedTuples k n := by
    intro ν hν
    rw [TupleCount.mem_boundedTuples]
    exact (Finset.mem_finAntidiagonal.mp hν).le
  exact (Finset.card_le_card hsub).trans (by
    rw [TupleCount.card_boundedTuples]
    exact Nat.choose_le_two_pow _ _)

/-- Both existing recursive tuple implementations enumerate the same source. -/
theorem finAntidiagonal_eq_tuple (k n : ℕ) :
    Finset.finAntidiagonal k n = Finset.Nat.antidiagonalTuple k n := by
  ext ν
  rw [Finset.mem_finAntidiagonal, Finset.Nat.mem_antidiagonalTuple]

/-- Every recursive call is counted, even when dimension zero has positive
remaining sum and returns no tuple. -/
def calls : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k+1, n => 1+∑ ij ∈ Finset.antidiagonal n, calls k ij.2

lemma sum_pow_snd (k n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal n, 4^(k+ij.2+1)) =
      4^(k+1)*(∑ i ∈ Finset.range (n+1), 4^i) := by
  have hswap := Finset.Nat.sum_antidiagonal_swap (n := n) (f := fun ij => 4^(k+ij.1+1))
  change (∑ ij ∈ Finset.antidiagonal n, 4^(k+ij.2+1)) =
    (∑ ij ∈ Finset.antidiagonal n, 4^(k+ij.1+1)) at hswap
  rw [hswap]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [Prod.swap]
  rw [← pow_add]
  congr 1
  omega

/-- A uniform exponential bound for the real recursive call tree. -/
theorem calls_le (k n : ℕ) : calls k n ≤ 4^(k+n+1) := by
  induction k generalizing n with
  | zero =>
    simp only [calls, Nat.zero_add]
    exact Nat.one_le_pow _ _ (by decide)
  | succ k ih =>
    have hs := Finset.sum_le_sum (s := Finset.antidiagonal n) (fun ij _ => ih ij.2)
    rw [sum_pow_snd] at hs
    have hg := Connected.two_mul_sum_range_pow_le 4 (n+1) (by decide)
    have hm := Nat.mul_le_mul_left (4^(k+1)) hg
    have hpos : 1 ≤ 4^(k+1)*(∑ i ∈ Finset.range (n+1), 4^i) := by
      have hsum : 1 ≤ ∑ i ∈ Finset.range (n+1), 4^i := by
        simpa using (Finset.single_le_sum (fun i _ => Nat.zero_le (4^i))
          (show 0 ∈ Finset.range (n+1) by simp))
      exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by omega))
    have he : 4^(k+1)*4^(n+1) = 4^(k+1+n+1) := by rw [← pow_add]; congr 1 <;> omega
    rw [calls]
    rw [he] at hm
    nlinarith

/-- Source scans and actual tuple copies in one nonterminal generation call. -/
def nodeWork (k n : ℕ) : ℕ :=
  (∑ ij ∈ Finset.antidiagonal n,
    (2*(n+1)+ij.1.size+ij.2.size+1+
      ∑ ν ∈ Finset.finAntidiagonal k ij.2,
        (keyBits (tupleKey ν)+ij.1.size+2)))+1

/-- The complete recursive source trace, following the same split sources as
both actual tuple implementations. -/
def work : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k+1, n => (∑ ij ∈ Finset.antidiagonal n, work k ij.2)+nodeWork k n

def nodeBound (K N : ℕ) : ℕ :=
  (N+1)*(4*(N+2)+2^(N+K)*(K*(N+2)+1+N+3))+1

lemma nodeWork_le {k n K N : ℕ} (hk : k ≤ K) (hn : n ≤ N) :
    nodeWork k n ≤ nodeBound K N := by
  unfold nodeWork nodeBound
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _ij ∈ Finset.antidiagonal n,
        (4*(N+2)+2^(N+K)*(K*(N+2)+1+N+3)) := by
      apply Finset.sum_le_sum
      intro ij hij
      have hij' := Finset.mem_antidiagonal.mp hij
      have hi := size_le_succ ij.1; have hj := size_le_succ ij.2
      have hcopy : (∑ ν ∈ Finset.finAntidiagonal k ij.2,
          (keyBits (tupleKey ν)+ij.1.size+2)) ≤
          2^(N+K)*(K*(N+2)+1+N+3) := by
        calc
          _ ≤ ∑ _ν ∈ Finset.finAntidiagonal k ij.2, (K*(N+2)+1+N+3) := by
            apply Finset.sum_le_sum
            intro ν hν
            have hν' : ∑ i, ν i ≤ N := (Finset.mem_finAntidiagonal.mp hν).le.trans (by omega)
            have hb := tupleKey_bits ν hν'
            have hh := Nat.mul_le_mul_right (N+2) hk
            omega
          _ = (Finset.finAntidiagonal k ij.2).card*(K*(N+2)+1+N+3) := by simp
          _ ≤ _ := Nat.mul_le_mul_right _ ((card_finAntidiagonal_le _ _).trans
            (Nat.pow_le_pow_right (by decide) (by omega)))
      omega
    _ = (n+1)*(4*(N+2)+2^(N+K)*(K*(N+2)+1+N+3)) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

/-- Each recursive node's local source work is bounded at the original
ambient dimension and coordinate-sum budget. -/
theorem work_le_calls {k n K N : ℕ} (hk : k ≤ K) (hn : n ≤ N) :
    work k n ≤ calls k n*nodeBound K N := by
  induction k generalizing n with
  | zero =>
    simp only [work, calls, Nat.one_mul]
    unfold nodeBound
    omega
  | succ k ih =>
    have hs : (∑ ij ∈ Finset.antidiagonal n, work k ij.2) ≤
        (∑ ij ∈ Finset.antidiagonal n, calls k ij.2)*nodeBound K N := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro ij hij
      have hij' := Finset.mem_antidiagonal.mp hij
      exact ih (by omega) (by omega)
    have hl := nodeWork_le (show k ≤ K by omega) hn
    rw [work, calls]
    nlinarith

def bound (K N : ℕ) : ℕ := 4^(K+N+1)*nodeBound K N

theorem work_le {k n K N : ℕ} (hk : k ≤ K) (hn : n ≤ N) : work k n ≤ bound K N := by
  apply (work_le_calls hk hn).trans
  apply Nat.mul_le_mul_right
  exact (calls_le k n).trans (Nat.pow_le_pow_right (by decide) (by omega))

/-- Generation plus the actual `Fin.tail` map and duplicate-key comparisons
used by the bounded total-level enumeration. -/
def boundedWork (t J : ℕ) : ℕ :=
  let S := Finset.finAntidiagonal (t+1) J
  work (t+1) J+(∑ ν ∈ S, (keyBits (tupleKey ν)+t+2))+
    ∑ ν ∈ S, ∑ μ ∈ S, (keyBits (tupleKey ν)+keyBits (tupleKey μ)+1)

def boundedBound (s J : ℕ) : ℕ :=
  let Q := 2^(J+s+1)
  let D := (s+1)*(J+2)+1
  bound (s+1) J+Q*(D+s+2)+Q^2*(2*D+1)

lemma boundedWork_le {t s J : ℕ} (ht : t ≤ s) : boundedWork t J ≤ boundedBound s J := by
  let S := Finset.finAntidiagonal (t+1) J
  let Q := 2^(J+s+1)
  let D := (s+1)*(J+2)+1
  have hcard : S.card ≤ Q := (card_finAntidiagonal_le _ _).trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hkey : ∀ ν ∈ S, keyBits (tupleKey ν) ≤ D := by
    intro ν hν
    have hh := tupleKey_bits ν (Finset.mem_finAntidiagonal.mp hν).le
    exact hh.trans (by dsimp [D]; nlinarith)
  have hmap : (∑ ν ∈ S, (keyBits (tupleKey ν)+t+2)) ≤ Q*(D+s+2) := by
    calc
      _ ≤ ∑ _ν ∈ S, (D+s+2) := Finset.sum_le_sum (fun ν hν => by have hh := hkey ν hν; omega)
      _ = S.card*(D+s+2) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hcard
  have hdup : (∑ ν ∈ S, ∑ μ ∈ S, (keyBits (tupleKey ν)+keyBits (tupleKey μ)+1)) ≤ Q^2*(2*D+1) := by
    calc
      _ ≤ ∑ _ν ∈ S, ∑ _μ ∈ S, (2*D+1) := by
        apply Finset.sum_le_sum
        intro ν hν
        exact Finset.sum_le_sum (fun μ hμ => by have hh := hkey ν hν; have hg := hkey μ hμ; omega)
      _ = S.card^2*(2*D+1) := by simp; ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hcard 2)
  exact Nat.add_le_add (Nat.add_le_add (work_le (show t+1 ≤ s+1 by omega) le_rfl) hmap) hdup

/-- Finite-support output construction charges each tuple's actual list,
all ordered-support lookups and the support filter, in addition to generation. -/
def exponentWork {m : ℕ} (B : Finset (Fin m)) (j : ℕ) : ℕ :=
  work B.card j+sortCharge B indexKey+
    ∑ ν ∈ Finset.finAntidiagonal B.card j,
      (keyBits (tupleKey ν)+m*(B.card+1)*(j.size+2)+1)

def exponentBound (m s : ℕ) : ℕ :=
  bound s s+s^2*(2*s*(m+2)+6)+4^s*(s*(s+2)+1+m*(s+1)*(s+3)+1)

lemma exponentWork_le {m s j : ℕ} (B : Finset (Fin m)) (hB : B.card ≤ s) (hj : j ≤ s) :
    exponentWork B j ≤ exponentBound m s := by
  have hsort : sortCharge B indexKey ≤ s^2*(2*s*(m+2)+6) := by
    apply (sortCharge_le _ _ (fun e _ => indexKey_bits_le e)).trans
    exact Nat.mul_le_mul (Nat.pow_le_pow_left hB 2) (by nlinarith)
  have hcard : (Finset.finAntidiagonal B.card j).card ≤ 4^s := by
    apply (card_finAntidiagonal_le _ _).trans
    calc
      _ ≤ 2^(s+s) := Nat.pow_le_pow_right (by decide) (by omega)
      _ = _ := by rw [pow_add, ← mul_pow]; norm_num
  have hcopy : (∑ ν ∈ Finset.finAntidiagonal B.card j,
      (keyBits (tupleKey ν)+m*(B.card+1)*(j.size+2)+1)) ≤
      4^s*(s*(s+2)+1+m*(s+1)*(s+3)+1) := by
    calc
      _ ≤ ∑ _ν ∈ Finset.finAntidiagonal B.card j,
          (s*(s+2)+1+m*(s+1)*(s+3)+1) := by
        apply Finset.sum_le_sum
        intro ν hν
        have hh := tupleKey_bits ν ((Finset.mem_finAntidiagonal.mp hν).le.trans hj)
        have hm := Nat.mul_le_mul_right (s+2) hB
        have hb := size_le_succ j
        have hp := Nat.mul_le_mul (Nat.mul_le_mul_left m (Nat.add_le_add_right hB 1))
          (show j.size+2 ≤ s+3 by omega)
        omega
      _ = (Finset.finAntidiagonal B.card j).card*(s*(s+2)+1+m*(s+1)*(s+3)+1) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hcard
  exact Nat.add_le_add (Nat.add_le_add (work_le hB hj) hsort) hcopy

/-- This is the actual split/map source equation of `finAntidiagonal`. -/
theorem finAntidiagonal_source (k n : ℕ) :
    Finset.finAntidiagonal (k+1) n = (Finset.antidiagonal n).biUnion (fun ij =>
      (Finset.finAntidiagonal k ij.2).image (Fin.cons ij.1)) := by
  ext ν
  constructor
  · intro hν
    have hs := Finset.mem_finAntidiagonal.mp hν
    apply Finset.mem_biUnion.mpr
    refine ⟨(ν 0, ∑ i : Fin k, ν i.succ), Finset.mem_antidiagonal.mpr ?_, ?_⟩
    · simpa only [Fin.sum_univ_succ] using hs
    · apply Finset.mem_image.mpr
      refine ⟨Fin.tail ν, ?_, Fin.cons_self_tail ν⟩
      rw [Finset.mem_finAntidiagonal]
      rfl
  · intro hν
    obtain ⟨ij, hij, hν'⟩ := Finset.mem_biUnion.mp hν
    obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hν'
    rw [Finset.mem_finAntidiagonal]
    have hij' := Finset.mem_antidiagonal.mp hij
    have hμ' := Finset.mem_finAntidiagonal.mp hμ
    simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hμ'] using hij'

theorem boundedTuples_source (t J : ℕ) :
    TupleCount.boundedTuples t J = (Finset.finAntidiagonal (t+1) J).image Fin.tail := by
  rw [finAntidiagonal_eq_tuple]
  rfl

/-- Computable ordered-support transfer of a generated tuple to a sparse
exponent vector. All membership and lookup scans are included in `exponentWork`. -/
def exponentOfTuple {m : ℕ} (B : Finset (Fin m)) (ν : Fin B.card → ℕ) : Fin m →₀ ℕ :=
  let f : Fin m → ℕ := fun e => if he : e ∈ B then
    ν ((B.orderIsoOfFin rfl).symm ⟨e,he⟩) else 0
  { support := B.filter (fun e => f e ≠ 0)
    toFun := f
    mem_support_toFun := by
      intro e
      by_cases he : e ∈ B <;> simp [he, f] }

@[simp] lemma exponentOfTuple_order {m : ℕ} (B : Finset (Fin m)) (ν : Fin B.card → ℕ)
    (i : Fin B.card) : exponentOfTuple B ν (B.orderEmbOfFin rfl i) = ν i := by
  change (if he : B.orderEmbOfFin rfl i ∈ B then
    ν ((B.orderIsoOfFin rfl).symm ⟨B.orderEmbOfFin rfl i,he⟩) else 0) = ν i
  rw [dif_pos (Finset.orderEmbOfFin_mem B rfl i)]
  change ν ((B.orderIsoOfFin rfl).symm ((B.orderIsoOfFin rfl) i)) = ν i
  simp

lemma exponentOfTuple_support {m : ℕ} (B : Finset (Fin m)) (ν : Fin B.card → ℕ) :
    (exponentOfTuple B ν).support ⊆ B := by
  intro e he
  by_contra hB
  have hz : exponentOfTuple B ν e=0 := by simp [exponentOfTuple, hB]
  exact (Finsupp.mem_support_iff.mp he) hz

/-- The actual ordered tuple generator computes exactly the finite-support
source consumed by every moment expression. -/
theorem finsuppAntidiag_source {m : ℕ} (B : Finset (Fin m)) (j : ℕ) :
    Finset.finsuppAntidiag B j = (Finset.finAntidiagonal B.card j).image (exponentOfTuple B) := by
  ext d
  constructor
  · intro hd
    have hh := Finset.mem_finsuppAntidiag.mp hd
    let ν : Fin B.card → ℕ := fun i => d (B.orderEmbOfFin rfl i)
    apply Finset.mem_image.mpr
    refine ⟨ν, ?_, ?_⟩
    · rw [Finset.mem_finAntidiagonal, TupleCount.sum_ordered]
      exact hh.1
    · apply Finsupp.ext
      intro e
      by_cases he : e ∈ B
      · obtain ⟨i, hi⟩ := (B.orderIsoOfFin rfl).surjective ⟨e,he⟩
        have hi' : B.orderEmbOfFin rfl i=e := congrArg Subtype.val hi
        rw [← hi', exponentOfTuple_order]
      · have hd0 : d e=0 := Finsupp.notMem_support_iff.mp (fun h => he (hh.2 h))
        simp [exponentOfTuple, he, hd0]
  · intro hd
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hd
    rw [Finset.mem_finsuppAntidiag]
    refine ⟨?_, exponentOfTuple_support B ν⟩
    rw [← TupleCount.sum_ordered]
    simpa only [exponentOfTuple_order] using Finset.mem_finAntidiagonal.mp hν

end Paper08.AntidiagonalCost
