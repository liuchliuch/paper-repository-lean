import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic

/-!
# Finite-field sparse recovery

The algebraic and checksum ingredients of Lemma A.1. Coordinates use the
indices `1, ..., d`, represented by `Fin d` with one added to the value.
-/

noncomputable section

namespace Paper02.SparseRecovery

open scoped BigOperators
open Finset Polynomial

variable {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]

/-- The support of a vector over a field. -/
def support (v : ι → F) : Finset ι := by
  classical
  exact univ.filter (fun i => v i ≠ 0)

@[simp] theorem mem_support {v : ι → F} {i : ι} : i ∈ support v ↔ v i ≠ 0 := by
  classical
  simp [support]

/-- A power moment of a vector, with arbitrary distinct field nodes. -/
def powerMoment (nodes v : ι → F) (t : ℕ) : F := ∑ i, v i * nodes i ^ t

theorem powerMoment_add (nodes u v : ι → F) (t : ℕ) :
    powerMoment nodes (u + v) t = powerMoment nodes u t + powerMoment nodes v t := by
  simp [powerMoment, add_mul, Finset.sum_add_distrib]

theorem powerMoment_sub (nodes u v : ι → F) (t : ℕ) :
    powerMoment nodes (u - v) t = powerMoment nodes u t - powerMoment nodes v t := by
  simp [powerMoment, sub_mul, Finset.sum_sub_distrib]

/-- The first `s.card` moments determine any vector supported on `s`.
This is the Vandermonde step; the support is enumerated only in the proof. -/
theorem eq_zero_of_moments_eq_zero (nodes v : ι → F)
    (hnodes : Function.Injective nodes) (s : Finset ι)
    (hs : support v ⊆ s) (hm : ∀ t < s.card, powerMoment nodes v t = 0) : v = 0 := by
  classical
  let e : Fin s.card ≃ s := s.equivFin.symm
  have hinj : Function.Injective (fun j : Fin s.card => nodes (e j)) :=
    hnodes.comp (Subtype.val_injective.comp e.injective)
  have hz : (fun j : Fin s.card => v (e j)) = 0 := by
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hinj
    intro t
    calc
      ∑ j : Fin s.card, v (e j) * nodes (e j) ^ t.val =
          ∑ j : s, v j * nodes j ^ t.val :=
        e.sum_comp (fun j : s => v j * nodes j ^ t.val)
      _ = ∑ j ∈ s, v j * nodes j ^ t.val := by
        exact Finset.sum_coe_sort s (fun j => v j * nodes j ^ t.val)
      _ = powerMoment nodes v t.val := by
        apply Finset.sum_subset (Finset.subset_univ s)
        intro j _ hj
        have hv : v j = 0 := by
          by_contra h
          exact hj (hs (mem_support.mpr h))
        simp [hv]
      _ = 0 := hm t.val t.isLt
  funext i
  by_cases hi : i ∈ s
  · have h := congrFun hz (e.symm ⟨i, hi⟩)
    simpa using h
  · have hv : v i = 0 := by
      by_contra h
      exact hi (hs (mem_support.mpr h))
    exact hv

/-- The `2K` moments are injective on the set of `K`-sparse field vectors. -/
theorem sparse_moments_injective (nodes u v : ι → F)
    (hnodes : Function.Injective nodes) {K : ℕ}
    (hu : (support u).card ≤ K) (hv : (support v).card ≤ K)
    (hm : ∀ t < 2 * K, powerMoment nodes u t = powerMoment nodes v t) : u = v := by
  classical
  have hs : support (u - v) ⊆ support u ∪ support v := by
    intro i hi
    simp only [mem_support, Pi.sub_apply, mem_union] at hi ⊢
    by_contra h
    push_neg at h
    exact hi (by simp [h.1, h.2])
  have hcard : (support u ∪ support v).card ≤ 2 * K :=
    (card_union_le _ _).trans (by omega)
  have hz := eq_zero_of_moments_eq_zero nodes (u - v) hnodes
    (support u ∪ support v) hs (fun t ht => by
      rw [powerMoment_sub, hm t (lt_of_lt_of_le ht hcard), sub_self])
  exact sub_eq_zero.mp hz

/-- The checksum is the evaluation of a degree-at-most-`d` polynomial. -/
def checksumPolynomial {d : ℕ} (v : Fin d → F) : F[X] :=
  ∑ i, monomial (i.val + 1) (v i)

def checksum {d : ℕ} (v : Fin d → F) (z : F) : F :=
  ∑ i, v i * z ^ (i.val + 1)

theorem eval_checksumPolynomial {d : ℕ} (v : Fin d → F) (z : F) :
    (checksumPolynomial v).eval z = checksum v z := by
  simp [checksumPolynomial, checksum, eval_finset_sum, eval_monomial]

@[simp] theorem coeff_checksumPolynomial {d : ℕ} (v : Fin d → F) (i : Fin d) :
    (checksumPolynomial v).coeff (i.val + 1) = v i := by
  classical
  simp only [checksumPolynomial, finset_sum_coeff, coeff_monomial]
  rw [sum_eq_single i]
  · simp
  · intro j _ hji
    have h : j.val + 1 ≠ i.val + 1 := fun h => hji (Fin.ext (by omega))
    exact if_neg h
  · simp

theorem checksumPolynomial_injective {d : ℕ} :
    Function.Injective (checksumPolynomial : (Fin d → F) → F[X]) := by
  intro u v h
  funext i
  have hi := congrArg (fun p : F[X] => p.coeff (i.val + 1)) h
  simpa using hi

theorem checksumPolynomial_ne_zero {d : ℕ} {v : Fin d → F} (hv : v ≠ 0) :
    checksumPolynomial v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hi := congrArg (fun p : F[X] => p.coeff (i.val + 1)) h
  simpa using hi

theorem natDegree_checksumPolynomial_le {d : ℕ} (v : Fin d → F) :
    (checksumPolynomial v).natDegree ≤ d := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  classical
  simp only [checksumPolynomial, finset_sum_coeff, coeff_monomial]
  apply sum_eq_zero
  intro i _
  have hi : i.val + 1 ≠ n := by omega
  simp [hi]

theorem checksum_add {d : ℕ} (u v : Fin d → F) (z : F) :
    checksum (u + v) z = checksum u z + checksum v z := by
  simp [checksum, add_mul, sum_add_distrib]

theorem checksum_sub {d : ℕ} (u v : Fin d → F) (z : F) :
    checksum (u - v) z = checksum u z - checksum v z := by
  simp [checksum, sub_mul, sum_sub_distrib]

/-- The number of seeds falsely identifying two different vectors is at most
the dimension. This applies to a candidate selected without the checksum seed. -/
theorem checksum_collision_count_le [Fintype F] [DecidableEq F]
    {d : ℕ} (u v : Fin d → F) (hne : u ≠ v) :
    (univ.filter (fun z => checksum u z = checksum v z)).card ≤ d := by
  have hp : checksumPolynomial (u - v) ≠ 0 :=
    checksumPolynomial_ne_zero (sub_ne_zero.mpr hne)
  apply (Polynomial.card_le_degree_of_subset_roots ?_).trans
    (natDegree_checksumPolynomial_le (u - v))
  intro z hz
  change z ∈ univ.filter (fun z => checksum u z = checksum v z) at hz
  have hz' := (mem_filter.mp hz).2
  apply (Polynomial.mem_roots hp).mpr
  change (checksumPolynomial (u - v)).eval z = 0
  rw [eval_checksumPolynomial, checksum_sub, hz', sub_self]

/-- The finite uniform probability formulation of the checksum bound. -/
theorem checksum_collision_probability_le [Fintype F] [DecidableEq F]
    {d : ℕ} (u v : Fin d → F) (hne : u ≠ v) :
    ((univ.filter (fun z => checksum u z = checksum v z)).card : ℝ) /
        Fintype.card F ≤ (d : ℝ) / Fintype.card F := by
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast checksum_collision_count_le u v hne) (by positivity)

/-- Integer representatives in `[-U,U]` remain distinct whenever `2U < q`. -/
theorem bounded_intCast_injective {q U : ℕ} (hq : 2 * U < q)
    {a b : ℤ} (ha : -(U : ℤ) ≤ a ∧ a ≤ U) (hb : -(U : ℤ) ≤ b ∧ b ≤ U)
    (he : (a : ZMod q) = (b : ZMod q)) : a = b := by
  have hd : (q : ℤ) ∣ b - a := (ZMod.intCast_eq_intCast_iff_dvd_sub a b q).mp he
  have hq' : (2 * U : ℤ) < q := by exact_mod_cast hq
  have hlt : (b - a).natAbs < (q : ℤ).natAbs := by
    rw [Int.natAbs_lt_iff_sq_lt]
    have h1 : -(q : ℤ) < b - a := by omega
    have h2 : b - a < q := by omega
    nlinarith
  exact (sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hlt)).symm

/-- The coordinate labels `1,...,d` are distinct modulo `q`. -/
theorem coordinate_nodes_injective {d q : ℕ} (hdq : d < q) :
    Function.Injective (fun i : Fin d => ((i.val + 1 : ℕ) : ZMod q)) := by
  intro i j h
  have hmod := (ZMod.natCast_eq_natCast_iff' (i.val + 1) (j.val + 1) q).mp h
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
  exact Fin.ext (by omega)

def integerSupport {d : ℕ} (v : Fin d → ℤ) : Finset (Fin d) :=
  univ.filter (fun i => v i ≠ 0)

theorem support_intCast {d q U : ℕ} [Fact q.Prime] (hUq : 2 * U < q)
    (v : Fin d → ℤ) (hv : ∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U) :
    support (fun i => (v i : ZMod q)) = integerSupport v := by
  classical
  ext i
  simp only [mem_support, integerSupport, mem_filter, mem_univ, true_and]
  constructor
  · intro h hz
    exact h (by simp [hz])
  · intro h hz
    apply h
    exact bounded_intCast_injective hUq (hv i) (by omega) (by simpa using hz)

/-- Sparse integer uniqueness, including the essential `2U < q` hypothesis. -/
theorem sparse_integer_moments_injective {d q U K : ℕ} [Fact q.Prime]
    (hdq : d < q) (hUq : 2 * U < q) (u v : Fin d → ℤ)
    (huBound : ∀ i, -(U : ℤ) ≤ u i ∧ u i ≤ U)
    (hvBound : ∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U)
    (hu : (integerSupport u).card ≤ K) (hv : (integerSupport v).card ≤ K)
    (hm : ∀ t < 2 * K,
      powerMoment (fun i : Fin d => ((i.val + 1 : ℕ) : ZMod q))
        (fun i => (u i : ZMod q)) t =
      powerMoment (fun i : Fin d => ((i.val + 1 : ℕ) : ZMod q))
        (fun i => (v i : ZMod q)) t) : u = v := by
  have he := sparse_moments_injective
    (fun i : Fin d => ((i.val + 1 : ℕ) : ZMod q))
    (fun i => (u i : ZMod q)) (fun i => (v i : ZMod q))
    (coordinate_nodes_injective hdq)
    (by simpa only [support_intCast hUq u huBound] using hu)
    (by simpa only [support_intCast hUq v hvBound] using hv) hm
  funext i
  exact bounded_intCast_injective hUq (huBound i) (hvBound i) (congrFun he i)

/-- The deterministic part of the sparse decoder checks only the power moments,
never the checksum or its seed. -/
def IntegerCandidate {d q : ℕ} [Fact q.Prime] (U K : ℕ)
    (M : Fin (2 * K) → ZMod q) (v : Fin d → ℤ) : Prop :=
  (∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U) ∧ (integerSupport v).card ≤ K ∧
    ∀ t, powerMoment (fun i : Fin d => ((i.val + 1 : ℕ) : ZMod q))
      (fun i => (v i : ZMod q)) t.val = M t

/-- A mathematical specification of candidate selection. Efficient realization
by the Hankel and Vandermonde operations is developed below. -/
def momentCandidate {d q : ℕ} [Fact q.Prime] (U K : ℕ)
    (M : Fin (2 * K) → ZMod q) : Option (Fin d → ℤ) := by
  classical
  exact if h : ∃ v, IntegerCandidate U K M v then some h.choose else none

theorem momentCandidate_spec {d q U K : ℕ} [Fact q.Prime]
    {M : Fin (2 * K) → ZMod q} {v : Fin d → ℤ}
    (h : momentCandidate U K M = some v) : IntegerCandidate U K M v := by
  unfold momentCandidate at h
  split_ifs at h with hex
  · cases Option.some.inj h
    exact hex.choose_spec

theorem integerCandidate_unique {d q U K : ℕ} [Fact q.Prime]
    (hdq : d < q) (hUq : 2 * U < q) {M : Fin (2 * K) → ZMod q}
    {u v : Fin d → ℤ} (hu : IntegerCandidate U K M u)
    (hv : IntegerCandidate U K M v) : u = v := by
  apply sparse_integer_moments_injective hdq hUq u v hu.1 hv.1 hu.2.1 hv.2.1
  intro t ht
  exact (hu.2.2 ⟨t, ht⟩).trans (hv.2.2 ⟨t, ht⟩).symm

theorem momentCandidate_eq_some {d q U K : ℕ} [Fact q.Prime]
    (hdq : d < q) (hUq : 2 * U < q) {M : Fin (2 * K) → ZMod q}
    {v : Fin d → ℤ} (hv : IntegerCandidate U K M v) :
    momentCandidate U K M = some v := by
  unfold momentCandidate
  split_ifs with hex
  · congr 1
    exact integerCandidate_unique hdq hUq hex.choose_spec hv
  · exact False.elim (hex ⟨v, hv⟩)

/-- The finite state consists of `2K` field moments and one checksum. -/
abbrev Summary (K : ℕ) (F : Type*) := (Fin (2 * K) → F) × F

def fieldSummary {d : ℕ} (K : ℕ) (z : F) (v : Fin d → F) : Summary K F :=
  (fun t => powerMoment (fun i => (i.val + 1 : F)) v t.val, checksum v z)

def integerMoments {d q : ℕ} [Fact q.Prime] (K : ℕ)
    (v : Fin d → ℤ) : Fin (2 * K) → ZMod q :=
  fun t => powerMoment (fun i : Fin d => ((i.val + 1 : ℕ) : ZMod q))
    (fun i => (v i : ZMod q)) t.val

def integerSummary {d q : ℕ} [Fact q.Prime] (K : ℕ) (z : ZMod q)
    (v : Fin d → ℤ) : Summary K (ZMod q) :=
  (integerMoments K v, checksum (fun i => (v i : ZMod q)) z)

theorem integerSummary_eq_fieldSummary {d q : ℕ} [Fact q.Prime]
    (K : ℕ) (z : ZMod q) (v : Fin d → ℤ) :
    integerSummary K z v = fieldSummary K z (fun i => (v i : ZMod q)) := by
  apply Prod.ext
  · funext t
    change powerMoment (fun i : Fin d => ((i.val + 1 : ℕ) : ZMod q))
      (fun i => (v i : ZMod q)) t.val =
      powerMoment (fun i : Fin d => (i.val + 1 : ZMod q))
        (fun i => (v i : ZMod q)) t.val
    simp only [Nat.cast_add, Nat.cast_one]
  · rfl

/-- The decoder performs the independent checksum test after candidate selection. -/
def decodeSummary {d q : ℕ} [Fact q.Prime] (U K : ℕ) (z : ZMod q)
    (s : Summary K (ZMod q)) : Option (Fin d → ℤ) :=
  match momentCandidate U K s.1 with
  | none => none
  | some y => if checksum (fun i => (y i : ZMod q)) z = s.2 then some y else none

/-- Every sparse bounded vector is returned exactly, for every seed. -/
theorem decodeSummary_sparse {d q U K : ℕ} [Fact q.Prime]
    (hdq : d < q) (hUq : 2 * U < q) (v : Fin d → ℤ)
    (hbound : ∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U)
    (hsparse : (integerSupport v).card ≤ K) (z : ZMod q) :
    decodeSummary U K z (integerSummary K z v) = some v := by
  have hc : IntegerCandidate U K (integerMoments (q := q) K v) v :=
    ⟨hbound, hsparse, fun _ => rfl⟩
  have h := momentCandidate_eq_some hdq hUq hc
  simp [decodeSummary, integerSummary, h]

/-- For a fixed dense vector, at most `d` uniformly sampled checksum seeds
allow any output. The deterministic candidate is selected without this seed. -/
theorem decodeSummary_dense_count_le {d q U K : ℕ} [Fact q.Prime]
    (hUq : 2 * U < q) (v : Fin d → ℤ)
    (hbound : ∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U)
    (hdense : K < (integerSupport v).card) :
    (univ.filter (fun z : ZMod q =>
      decodeSummary (d := d) U K z (integerSummary K z v) ≠ none)).card ≤ d := by
  classical
  cases hc : momentCandidate (d := d) U K (integerMoments (q := q) K v) with
  | none => simp [decodeSummary, integerSummary, hc]
  | some y =>
    have hy := momentCandidate_spec hc
    have hne : (fun i => (y i : ZMod q)) ≠ (fun i => (v i : ZMod q)) := by
      intro he
      have hxy : y = v := by
        funext i
        exact bounded_intCast_injective hUq (hy.1 i) (hbound i) (congrFun he i)
      rw [hxy] at hy
      exact (not_le_of_gt hdense) hy.2.1
    simpa [decodeSummary, integerSummary, hc] using
      checksum_collision_count_le (fun i => (y i : ZMod q)) (fun i => (v i : ZMod q)) hne

theorem decodeSummary_dense_probability_le {d q U K : ℕ} [Fact q.Prime]
    (hUq : 2 * U < q) (v : Fin d → ℤ)
    (hbound : ∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U)
    (hdense : K < (integerSupport v).card) :
    ((univ.filter (fun z : ZMod q =>
      decodeSummary (d := d) U K z (integerSummary K z v) ≠ none)).card : ℝ) / q ≤ (d : ℝ) / q := by
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast decodeSummary_dense_count_le hUq v hbound hdense) (by positivity)

theorem fieldSummary_add {d : ℕ} (K : ℕ) (z : F) (u v : Fin d → F) :
    fieldSummary K z (u + v) = fieldSummary K z u + fieldSummary K z v := by
  apply Prod.ext
  · funext t
    exact powerMoment_add (fun i : Fin d => (i.val + 1 : F)) u v t.val
  · exact checksum_add u v z

@[simp] theorem fieldSummary_zero {d : ℕ} (K : ℕ) (z : F) :
    fieldSummary K z (0 : Fin d → F) = 0 := by
  ext t <;> simp [fieldSummary, powerMoment, checksum]

theorem fieldSummary_single {d : ℕ} (K : ℕ) (z : F) (i : Fin d) (a : F) :
    fieldSummary K z (Pi.single i a) =
      (fun t => a * (i.val + 1 : F) ^ t.val, a * z ^ (i.val + 1)) := by
  classical
  ext t <;> simp [fieldSummary, powerMoment, checksum, Pi.single_apply]

/-- A real update changes the state by these explicit field operations. -/
def updateSummary {d : ℕ} (K : ℕ) (z : F)
    (s : Summary K F) (i : Fin d) (a : F) : Summary K F :=
  s + (fun t => a * (i.val + 1 : F) ^ t.val, a * z ^ (i.val + 1))

theorem updateSummary_correct {d : ℕ} (K : ℕ) (z : F)
    (v : Fin d → F) (i : Fin d) (a : F) :
    updateSummary K z (fieldSummary K z v) i a =
      fieldSummary K z (v + Pi.single i a) := by
  rw [fieldSummary_add, fieldSummary_single]
  rfl

@[simp] theorem integerSummary_zero {d q : ℕ} [Fact q.Prime]
    (K : ℕ) (z : ZMod q) : integerSummary K z (0 : Fin d → ℤ) = 0 := by
  ext t <;> simp [integerSummary, integerMoments, checksum, powerMoment]

theorem integerSummary_update {d q : ℕ} [Fact q.Prime]
    (K : ℕ) (z : ZMod q) (v : Fin d → ℤ) (i : Fin d) (a : ℤ) :
    integerSummary K z (v + Pi.single i a) =
      updateSummary K z (integerSummary K z v) i (a : ZMod q) := by
  rw [integerSummary_eq_fieldSummary, integerSummary_eq_fieldSummary, updateSummary_correct]
  congr 1
  classical
  funext j
  by_cases hj : j = i <;> simp [hj, Pi.single_apply]

/-- Integer turnstile updates, with no restriction on the increments. -/
abbrev Update (d : ℕ) := Fin d × ℤ

def finalVector {d : ℕ} (stream : List (Update d)) : Fin d → ℤ :=
  stream.foldl (fun v u => v + Pi.single u.1 u.2) 0

def streamSummary {d q : ℕ} [Fact q.Prime] (K : ℕ) (z : ZMod q)
    (stream : List (Update d)) : Summary K (ZMod q) :=
  stream.foldl (fun s u => updateSummary K z s u.1 (u.2 : ZMod q)) 0

/-- The maintained state depends only on the final vector. In particular no
bound on intermediate frequencies appears in its invariant. -/
theorem streamSummary_finalVector {d q : ℕ} [Fact q.Prime]
    (K : ℕ) (z : ZMod q) (stream : List (Update d)) :
    streamSummary K z stream =
      fieldSummary K z (fun i => ((finalVector stream i : ℤ) : ZMod q)) := by
  have aux : ∀ (stream : List (Update d)) (v : Fin d → ℤ),
      stream.foldl (fun s u => updateSummary K z s u.1 (u.2 : ZMod q))
          (fieldSummary K z (fun i => (v i : ZMod q))) =
        fieldSummary K z (fun i =>
          ((stream.foldl (fun w u => w + Pi.single u.1 u.2) v) i : ZMod q)) := by
    intro stream
    induction stream with
    | nil => intro v; rfl
    | cons u us ih =>
      intro v
      simp only [List.foldl_cons]
      rw [updateSummary_correct]
      have he : (fun i => (v i : ZMod q)) + Pi.single u.1 (u.2 : ZMod q) =
          (fun i => (((v + (Pi.single u.1 u.2 : Fin d → ℤ)) i : ℤ) : ZMod q)) := by
        classical
        funext i
        by_cases hi : i = u.1 <;> simp [hi, Pi.single_apply]
      rw [he]
      exact ih _
  simpa [streamSummary, finalVector, fieldSummary, powerMoment, checksum] using aux stream 0

/-- The Hankel matrix formed from `2r-1` consecutive moments. -/
def hankel {r : ℕ} (nodes weights : Fin r → F) : Matrix (Fin r) (Fin r) F :=
  fun t j => powerMoment nodes weights (t.val + j.val)

/-- The factorization used in the efficient decoder. -/
theorem hankel_factorization {r : ℕ} (nodes weights : Fin r → F) :
    hankel nodes weights = (Matrix.vandermonde nodes).transpose *
      Matrix.diagonal weights * Matrix.vandermonde nodes := by
  classical
  ext t j
  simp only [hankel, powerMoment, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.vandermonde_apply, Matrix.diagonal_apply]
  simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
  apply sum_congr rfl
  intro a _
  rw [pow_add]
  ring

/-- Distinct support indices and nonzero frequencies make the Hankel system
invertible; the decoder therefore reaches the true sparse support size. -/
theorem det_hankel_ne_zero {r : ℕ} (nodes weights : Fin r → F)
    (hnodes : Function.Injective nodes) (hw : ∀ i, weights i ≠ 0) :
    (hankel nodes weights).det ≠ 0 := by
  classical
  rw [hankel_factorization, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, Matrix.det_diagonal]
  exact mul_ne_zero
    (mul_ne_zero (Matrix.det_vandermonde_ne_zero_iff.mpr hnodes)
      (prod_ne_zero_iff.mpr (by simpa using hw)))
    (Matrix.det_vandermonde_ne_zero_iff.mpr hnodes)

/-- The monic polynomial whose roots are exactly the retained coordinate labels. -/
def supportPolynomial {r : ℕ} (nodes : Fin r → F) : F[X] :=
  ∏ i, (X - C (nodes i))

theorem eval_supportPolynomial {r : ℕ} (nodes : Fin r → F) (z : F) :
    (supportPolynomial nodes).eval z = ∏ i, (z - nodes i) := by
  simp [supportPolynomial, eval_prod]

theorem supportPolynomial_root_iff {r : ℕ} (nodes : Fin r → F) (z : F) :
    (supportPolynomial nodes).eval z = 0 ↔ ∃ i, z = nodes i := by
  classical
  rw [eval_supportPolynomial, prod_eq_zero_iff]
  simp only [mem_univ, true_and, sub_eq_zero]

theorem supportPolynomial_monic {r : ℕ} (nodes : Fin r → F) :
    (supportPolynomial nodes).Monic := by
  exact monic_prod_X_sub_C nodes univ

theorem natDegree_supportPolynomial {r : ℕ} (nodes : Fin r → F) :
    (supportPolynomial nodes).natDegree = r := by
  simp [supportPolynomial]

/-- The trial polynomial built after solving the Hankel system. -/
def recurrencePolynomial {r : ℕ} (c : Fin r → F) : F[X] :=
  X ^ r + ∑ j, monomial j.val (c j)

theorem eval_recurrencePolynomial {r : ℕ} (c : Fin r → F) (z : F) :
    (recurrencePolynomial c).eval z = z ^ r + ∑ j, c j * z ^ j.val := by
  simp [recurrencePolynomial, eval_finset_sum, eval_monomial]

/-- The coefficients of the support polynomial give a trial polynomial. -/
theorem recurrencePolynomial_support_coeff {r : ℕ} (nodes : Fin r → F) :
    recurrencePolynomial (fun j : Fin r => (supportPolynomial nodes).coeff j.val) =
      supportPolynomial nodes := by
  have hp := (supportPolynomial nodes).as_sum_range
  rw [natDegree_supportPolynomial, sum_range_succ] at hp
  have hc : (supportPolynomial nodes).coeff r = 1 := by
    simpa only [natDegree_supportPolynomial] using
      (supportPolynomial_monic nodes).coeff_natDegree
  rw [hc] at hp
  unfold recurrencePolynomial
  dsimp only
  rw [Fin.sum_univ_eq_sum_range
    (fun n : ℕ => monomial n ((supportPolynomial nodes).coeff n)) r]
  simpa only [← C_mul_X_pow_eq_monomial, C_1, one_mul, add_comm] using hp.symm

/-- Any monic polynomial vanishing on the support supplies the moment recurrence. -/
theorem moment_recurrence {r : ℕ} (nodes weights c : Fin r → F)
    (hc : ∀ a, (recurrencePolynomial c).eval (nodes a) = 0) (t : ℕ) :
    (∑ j, c j * powerMoment nodes weights (t + j.val)) =
      -powerMoment nodes weights (t + r) := by
  classical
  apply eq_neg_iff_add_eq_zero.mpr
  simp only [powerMoment, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply sum_eq_zero
  intro a _
  have ha := hc a
  rw [eval_recurrencePolynomial] at ha
  calc
    (∑ j, c j * (weights a * nodes a ^ (t + j.val))) +
          weights a * nodes a ^ (t + r) =
        (weights a * nodes a ^ t) * ((∑ j, c j * nodes a ^ j.val) + nodes a ^ r) := by
      simp only [pow_add, mul_add, Finset.mul_sum]
      congr 1
      · apply sum_congr rfl
        intro j _
        ring
      · ring
    _ = 0 := by rw [add_comm, ha, mul_zero]

/-- The true support polynomial solves the system at the support size. -/
theorem support_coeff_solves_hankel {r : ℕ} (nodes weights : Fin r → F) :
    ∀ t : Fin r,
      (∑ j : Fin r, hankel nodes weights t j *
        (supportPolynomial nodes).coeff j.val) =
      -powerMoment nodes weights (t.val + r) := by
  intro t
  have h := moment_recurrence nodes weights
    (fun j : Fin r => (supportPolynomial nodes).coeff j.val) (by
      intro a
      rw [recurrencePolynomial_support_coeff]
      exact (supportPolynomial_root_iff nodes (nodes a)).mpr ⟨a, rfl⟩) t.val
  simpa only [hankel, mul_comm] using h

/-- The Hankel solve returns exactly the true support polynomial. -/
theorem recurrencePolynomial_eq_supportPolynomial {r : ℕ}
    (nodes weights c : Fin r → F) (hnodes : Function.Injective nodes)
    (hw : ∀ a, weights a ≠ 0)
    (hc : ∀ t : Fin r, (∑ j, hankel nodes weights t j * c j) =
      -powerMoment nodes weights (t.val + r)) :
    recurrencePolynomial c = supportPolynomial nodes := by
  classical
  have hz : (fun j : Fin r => c j - (supportPolynomial nodes).coeff j.val) = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero (det_hankel_ne_zero nodes weights hnodes hw)
    funext t
    change (∑ j, hankel nodes weights t j *
      (c j - (supportPolynomial nodes).coeff j.val)) = 0
    simp only [mul_sub, sum_sub_distrib, hc t, support_coeff_solves_hankel nodes weights t,
      sub_self, Pi.zero_apply]
  have he : c = fun j : Fin r => (supportPolynomial nodes).coeff j.val := by
    funext j
    have h := congrFun hz j
    exact sub_eq_zero.mp h
  rw [he, recurrencePolynomial_support_coeff]

/-- The matrix actually constructed by a decoder from its stored moments. -/
def momentHankel (r : ℕ) (M : ℕ → F) : Matrix (Fin r) (Fin r) F :=
  fun t j => M (t.val + j.val)

/-- Gaussian elimination may compute this unique linear-system solution. -/
def solveCoefficients (r : ℕ) (M : ℕ → F) : Fin r → F :=
  Matrix.mulVec (momentHankel r M)⁻¹ (fun t => -M (t.val + r))

theorem solveCoefficients_correct (r : ℕ) (M : ℕ → F)
    (hdet : (momentHankel r M).det ≠ 0) (t : Fin r) :
    (∑ j, M (t.val + j.val) * solveCoefficients r M j) = -M (t.val + r) := by
  have h : Matrix.mulVec (momentHankel r M) (solveCoefficients r M) =
      (fun t : Fin r => -M (t.val + r)) := by
    unfold solveCoefficients
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  exact congrFun h t

def trialPolynomial (r : ℕ) (M : ℕ → F) : F[X] :=
  recurrencePolynomial (solveCoefficients r M)

/-- At the true support size, the actual matrix inverse produces precisely
the polynomial whose roots are the support labels. -/
theorem trialPolynomial_correct {r : ℕ} (nodes weights : Fin r → F)
    (hnodes : Function.Injective nodes) (hw : ∀ a, weights a ≠ 0) :
    trialPolynomial r (powerMoment nodes weights) = supportPolynomial nodes := by
  apply recurrencePolynomial_eq_supportPolynomial nodes weights _ hnodes hw
  intro t
  apply solveCoefficients_correct r (powerMoment nodes weights)
  exact det_hankel_ne_zero nodes weights hnodes hw

/-- Scanning the coordinate labels for roots finds exactly the support. -/
theorem trialPolynomial_roots {r : ℕ} (nodes weights : Fin r → F)
    (hnodes : Function.Injective nodes) (hw : ∀ a, weights a ≠ 0) (z : F) :
    (trialPolynomial r (powerMoment nodes weights)).eval z = 0 ↔ ∃ a, z = nodes a := by
  rw [trialPolynomial_correct nodes weights hnodes hw, supportPolynomial_root_iff]

/-- The value-recovery step solves the Vandermonde system on the roots. -/
def recoverValues {r : ℕ} (nodes : Fin r → F) (M : ℕ → F) : Fin r → F :=
  Matrix.mulVec (Matrix.vandermonde nodes).transpose⁻¹ (fun t => M t.val)

theorem recoverValues_correct {r : ℕ} (nodes weights : Fin r → F)
    (hnodes : Function.Injective nodes) :
    recoverValues nodes (powerMoment nodes weights) = weights := by
  have hM : (fun t : Fin r => powerMoment nodes weights t.val) =
      Matrix.mulVec (Matrix.vandermonde nodes).transpose weights := by
    funext t
    simp only [powerMoment, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Matrix.vandermonde_apply]
    apply sum_congr rfl
    intro a _
    exact mul_comm _ _
  unfold recoverValues
  rw [hM, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ?_, Matrix.one_mulVec]
  rw [Matrix.det_transpose]
  exact isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hnodes)

def enumeratedNodes (nodes : ι → F) (s : Finset ι) : Fin s.card → F :=
  fun a => nodes (s.equivFin.symm a)

def enumeratedWeights (v : ι → F) (s : Finset ι) : Fin s.card → F :=
  fun a => v (s.equivFin.symm a)

theorem enumeratedNodes_injective (nodes : ι → F) (hnodes : Function.Injective nodes)
    (s : Finset ι) : Function.Injective (enumeratedNodes nodes s) :=
  hnodes.comp (Subtype.val_injective.comp s.equivFin.symm.injective)

theorem powerMoment_enumerated (nodes v : ι → F) (s : Finset ι)
    (hs : support v ⊆ s) (t : ℕ) :
    powerMoment (enumeratedNodes nodes s) (enumeratedWeights v s) t =
      powerMoment nodes v t := by
  classical
  calc
    powerMoment (enumeratedNodes nodes s) (enumeratedWeights v s) t =
        ∑ a : s, v a * nodes a ^ t :=
      s.equivFin.symm.sum_comp (fun a : s => v a * nodes a ^ t)
    _ = ∑ a ∈ s, v a * nodes a ^ t := sum_coe_sort s (fun a => v a * nodes a ^ t)
    _ = powerMoment nodes v t := by
      apply sum_subset (subset_univ s)
      intro a _ ha
      have hz : v a = 0 := by
        by_contra h
        exact ha (hs (mem_support.mpr h))
      simp [hz]

/-- A sparse list of indexed values, viewed extensionally as a vector. -/
def assemble (s : Finset ι) (values : Fin s.card → F) : ι → F := by
  classical
  exact fun i => if hi : i ∈ s then values (s.equivFin ⟨i, hi⟩) else 0

theorem support_assemble_subset (s : Finset ι) (values : Fin s.card → F) :
    support (assemble s values) ⊆ s := by
  classical
  intro i hi
  by_contra h
  exact (mem_support.mp hi) (by simp [assemble, h])

theorem assemble_enumeratedWeights (v : ι → F) (s : Finset ι)
    (hs : support v ⊆ s) : assemble s (enumeratedWeights v s) = v := by
  classical
  funext i
  by_cases hi : i ∈ s
  · simp [assemble, enumeratedWeights, hi]
  · have hz : v i = 0 := by
      by_contra h
      exact hi (hs (mem_support.mpr h))
    simp [assemble, hi, hz]

/-- The root scan used by a single Hankel trial. -/
def hankelTrialRoots (nodes : ι → F) (r : ℕ) (M : ℕ → F) : Finset ι := by
  classical
  exact univ.filter (fun i => (trialPolynomial r M).eval (nodes i) = 0)

theorem hankelTrialRoots_correct (nodes v : ι → F) (hnodes : Function.Injective nodes) :
    hankelTrialRoots nodes (support v).card (powerMoment nodes v) = support v := by
  classical
  have hM : powerMoment nodes v =
      powerMoment (enumeratedNodes nodes (support v)) (enumeratedWeights v (support v)) := by
    funext t
    exact (powerMoment_enumerated nodes v (support v) (subset_refl _) t).symm
  have hw : ∀ a, enumeratedWeights v (support v) a ≠ 0 := by
    intro a
    change v ((support v).equivFin.symm a) ≠ 0
    exact mem_support.mp ((support v).equivFin.symm a).property
  ext i
  simp only [hankelTrialRoots, mem_filter, mem_univ, true_and]
  rw [hM, trialPolynomial_roots _ _ (enumeratedNodes_injective nodes hnodes _) hw]
  constructor
  · rintro ⟨a, ha⟩
    have he : i = ((support v).equivFin.symm a).val := hnodes ha
    exact he ▸ ((support v).equivFin.symm a).property
  · intro hi
    refine ⟨(support v).equivFin ⟨i, hi⟩, ?_⟩
    simp [enumeratedNodes]

/-- The values returned by a trial are stored only at its scanned roots. -/
def hankelTrialVector (nodes : ι → F) (r : ℕ) (M : ℕ → F) : ι → F :=
  let roots := hankelTrialRoots nodes r M
  assemble roots (recoverValues (enumeratedNodes nodes roots) M)

/-- A trial at the true support size recovers the entire vector by the actual
Hankel solve, root scan, and Vandermonde solve. -/
theorem hankelTrialVector_correct (nodes v : ι → F) (hnodes : Function.Injective nodes) :
    hankelTrialVector nodes (support v).card (powerMoment nodes v) = v := by
  classical
  unfold hankelTrialVector
  rw [hankelTrialRoots_correct nodes v hnodes]
  dsimp only
  have hM : powerMoment nodes v =
      powerMoment (enumeratedNodes nodes (support v)) (enumeratedWeights v (support v)) := by
    funext t
    exact (powerMoment_enumerated nodes v (support v) (subset_refl _) t).symm
  rw [hM, recoverValues_correct _ _ (enumeratedNodes_injective nodes hnodes _)]
  exact assemble_enumeratedWeights v (support v) (subset_refl _)

def ValidHankelTrial (nodes : ι → F) (K r : ℕ) (M : ℕ → F) : Prop :=
  (momentHankel r M).det ≠ 0 ∧ (hankelTrialRoots nodes r M).card = r ∧
    ∀ t < 2 * K, powerMoment nodes (hankelTrialVector nodes r M) t = M t

/-- One actual trial: solve the Hankel system, scan roots, solve the values,
and check all the stored moments before accepting. -/
def hankelTrial (nodes : ι → F) (K r : ℕ) (M : ℕ → F) : Option (ι → F) := by
  classical
  exact if ValidHankelTrial nodes K r M then some (hankelTrialVector nodes r M) else none

theorem hankelTrial_spec (nodes : ι → F) {K r : ℕ} {M : ℕ → F} {y : ι → F}
    (hr : r ≤ K) (hy : hankelTrial nodes K r M = some y) :
    (support y).card ≤ K ∧ ∀ t < 2 * K, powerMoment nodes y t = M t := by
  classical
  unfold hankelTrial at hy
  split_ifs at hy with hvalid
  cases Option.some.inj hy
  refine ⟨?_, hvalid.2.2⟩
  exact (card_le_card (support_assemble_subset _ _)).trans
    (by rw [hvalid.2.1]; exact hr)

theorem hankelTrial_true (nodes v : ι → F) (hnodes : Function.Injective nodes) (K : ℕ) :
    hankelTrial nodes K (support v).card (powerMoment nodes v) = some v := by
  classical
  have hvalid : ValidHankelTrial nodes K (support v).card (powerMoment nodes v) := by
    refine ⟨?_, ?_, ?_⟩
    · have hM : powerMoment nodes v =
          powerMoment (enumeratedNodes nodes (support v)) (enumeratedWeights v (support v)) := by
        funext t
        exact (powerMoment_enumerated nodes v (support v) (subset_refl _) t).symm
      rw [hM]
      apply det_hankel_ne_zero _ _ (enumeratedNodes_injective nodes hnodes _)
      intro a
      change v ((support v).equivFin.symm a) ≠ 0
      exact mem_support.mp ((support v).equivFin.symm a).property
    · rw [hankelTrialRoots_correct nodes v hnodes]
    · intro t _
      rw [hankelTrialVector_correct nodes v hnodes]
  simp only [hankelTrial, if_pos hvalid, hankelTrialVector_correct nodes v hnodes]

/-- Search the trial sizes in order. Only a single trial and its sparse result
need to be retained during this search. -/
def searchHankelTrials (nodes : ι → F) (K : ℕ) (M : ℕ → F) : ℕ → Option (ι → F)
  | 0 => hankelTrial nodes K 0 M
  | r + 1 => match searchHankelTrials nodes K M r with
    | some y => some y
    | none => hankelTrial nodes K (r + 1) M

theorem searchHankelTrials_spec (nodes : ι → F) {K r : ℕ} {M : ℕ → F} {y : ι → F}
    (hr : r ≤ K) (hy : searchHankelTrials nodes K M r = some y) :
    (support y).card ≤ K ∧ ∀ t < 2 * K, powerMoment nodes y t = M t := by
  induction r with
  | zero => exact hankelTrial_spec nodes (by omega) hy
  | succ r ih =>
    simp only [searchHankelTrials] at hy
    cases he : searchHankelTrials nodes K M r with
    | none =>
      rw [he] at hy
      exact hankelTrial_spec nodes hr hy
    | some z =>
      rw [he] at hy
      cases Option.some.inj hy
      exact ih (by omega) he

/-- The actual finite search returns every `K`-sparse input exactly. -/
theorem searchHankelTrials_correct (nodes v : ι → F) (hnodes : Function.Injective nodes)
    {K r : ℕ} (hv : (support v).card ≤ r) (hr : r ≤ K) :
    searchHankelTrials nodes K (powerMoment nodes v) r = some v := by
  classical
  have uniqueness : ∀ j ≤ K, ∀ y, searchHankelTrials nodes K (powerMoment nodes v) j = some y →
      y = v := by
    intro j hj y hy
    have hs := searchHankelTrials_spec nodes hj hy
    exact sparse_moments_injective nodes y v hnodes hs.1 (hv.trans hr) hs.2
  induction r with
  | zero =>
    have hz : (support v).card = 0 := by omega
    simpa only [searchHankelTrials, hz] using hankelTrial_true nodes v hnodes K
  | succ r ih =>
    simp only [searchHankelTrials]
    cases he : searchHankelTrials nodes K (powerMoment nodes v) r with
    | some y => rw [uniqueness r (by omega) y he]
    | none =>
      have hs : (support v).card = r + 1 := by
        by_contra h
        have hlt : (support v).card ≤ r := by omega
        have heq := ih hlt (by omega)
        rw [he] at heq
        contradiction
      rw [← hs]
      exact hankelTrial_true nodes v hnodes K

/-- A trial of size at most `K` reads only the stored `2K` moments. -/
theorem hankelTrial_congr (nodes : ι → F) {K r : ℕ} (hr : r ≤ K)
    {M N : ℕ → F} (hm : ∀ t < 2 * K, M t = N t) :
    hankelTrial nodes K r M = hankelTrial nodes K r N := by
  classical
  have hH : momentHankel r M = momentHankel r N := by
    ext i j
    exact hm _ (by omega)
  have hC : solveCoefficients r M = solveCoefficients r N := by
    unfold solveCoefficients
    rw [hH]
    congr 1
    funext t
    rw [hm (t.val + r) (by omega)]
  have hP : trialPolynomial r M = trialPolynomial r N := congrArg recurrencePolynomial hC
  have hR : hankelTrialRoots nodes r M = hankelTrialRoots nodes r N := by
    ext i
    simp only [hankelTrialRoots, hP]
  by_cases hc : (hankelTrialRoots nodes r M).card = r
  · have hV : hankelTrialVector nodes r M = hankelTrialVector nodes r N := by
      unfold hankelTrialVector
      rw [← hR]
      dsimp only
      apply congrArg (assemble (hankelTrialRoots nodes r M))
      unfold recoverValues
      apply congrArg (Matrix.mulVec
        (Matrix.vandermonde (enumeratedNodes nodes (hankelTrialRoots nodes r M))).transpose⁻¹)
      funext t
      exact hm t.val (by have ht := lt_of_lt_of_le t.isLt (le_of_eq hc); omega)
    have hvalid : ValidHankelTrial nodes K r M ↔ ValidHankelTrial nodes K r N := by
      constructor
      · rintro ⟨hd, hcard, hcheck⟩
        refine ⟨by rwa [← hH], by rwa [← hR], ?_⟩
        intro t ht
        rw [← hV, hcheck t ht, hm t ht]
      · rintro ⟨hd, hcard, hcheck⟩
        refine ⟨by rwa [hH], by rwa [hR], ?_⟩
        intro t ht
        rw [hV, hcheck t ht, hm t ht]
    simp only [hankelTrial, hvalid, hV]
  · have hbadM : ¬ ValidHankelTrial nodes K r M := fun h => hc h.2.1
    have hbadN : ¬ ValidHankelTrial nodes K r N := by
      intro h
      apply hc
      rw [hR]
      exact h.2.1
    simp only [hankelTrial, if_neg hbadM, if_neg hbadN]

theorem searchHankelTrials_congr (nodes : ι → F) {K r : ℕ} (hr : r ≤ K)
    {M N : ℕ → F} (hm : ∀ t < 2 * K, M t = N t) :
    searchHankelTrials nodes K M r = searchHankelTrials nodes K N r := by
  induction r with
  | zero => exact hankelTrial_congr nodes (by omega) hm
  | succ r ih =>
    simp only [searchHankelTrials]
    rw [ih (by omega), hankelTrial_congr nodes hr hm]

/-- Extend the stored array by zero; the dependency theorem above guarantees
that no trial in the search uses those extra entries. -/
def extendMoments {q K : ℕ} (M : Fin (2 * K) → ZMod q) (t : ℕ) : ZMod q :=
  if ht : t < 2 * K then M ⟨t, ht⟩ else 0

/-- Convert a residue to its only possible representative in `[-U,U]`.
The caller checks the bound before retaining it. -/
def boundedLift {q : ℕ} (U : ℕ) (a : ZMod q) : ℤ :=
  if (a.val : ℤ) ≤ U then (a.val : ℤ) else (a.val : ℤ) - q

theorem boundedLift_intCast {q U : ℕ} [Fact q.Prime] (hUq : 2 * U < q)
    (a : ℤ) (ha : -(U : ℤ) ≤ a ∧ a ≤ U) : boundedLift U (a : ZMod q) = a := by
  have hq : (2 * U : ℤ) < q := by exact_mod_cast hUq
  have hval : ((a : ZMod q).val : ℤ) = a % q := ZMod.val_intCast a
  unfold boundedLift
  by_cases hnonneg : 0 ≤ a
  · have hv : ((a : ZMod q).val : ℤ) = a :=
      hval.trans (Int.emod_eq_of_lt hnonneg (by omega))
    rw [hv, if_pos ha.2]
  · have hmod : (a + q) % q = a % q := by simp [Int.add_emod]
    have hv : ((a : ZMod q).val : ℤ) = a + q :=
      hval.trans (hmod.symm.trans (Int.emod_eq_of_lt (by omega) (by omega)))
    have hb : ¬ ((a : ZMod q).val : ℤ) ≤ U := by omega
    rw [if_neg hb, hv]
    omega

/-- Actual integer candidate selection: the finite Hankel search is followed
by arithmetic residue lifting and verification of the original bounds. -/
def hankelIntegerCandidate {d q : ℕ} [Fact q.Prime] (U K : ℕ)
    (M : Fin (2 * K) → ZMod q) : Option (Fin d → ℤ) := by
  classical
  exact match searchHankelTrials
      (fun i : Fin d => ((i.val + 1 : ℕ) : ZMod q)) K (extendMoments M) K with
    | none => none
    | some y =>
      let v := fun i => boundedLift U (y i)
      if IntegerCandidate U K M v then some v else none

theorem hankelIntegerCandidate_spec {d q U K : ℕ} [Fact q.Prime]
    {M : Fin (2 * K) → ZMod q} {v : Fin d → ℤ}
    (h : hankelIntegerCandidate U K M = some v) : IntegerCandidate U K M v := by
  classical
  unfold hankelIntegerCandidate at h
  split at h
  · contradiction
  · dsimp only at h
    split_ifs at h with hv
    cases Option.some.inj h
    exact hv

theorem hankelIntegerCandidate_of_candidate {d q U K : ℕ} [Fact q.Prime]
    (hdq : d < q) (hUq : 2 * U < q) {M : Fin (2 * K) → ZMod q}
    {v : Fin d → ℤ} (hv : IntegerCandidate U K M v) :
    hankelIntegerCandidate U K M = some v := by
  classical
  let nodes : Fin d → ZMod q := fun i => ((i.val + 1 : ℕ) : ZMod q)
  let vf : Fin d → ZMod q := fun i => (v i : ZMod q)
  have hsparse : (support vf).card ≤ K := by
    simpa only [vf, support_intCast hUq v hv.1] using hv.2.1
  have hm : ∀ t < 2 * K, extendMoments M t = powerMoment nodes vf t := by
    intro t ht
    rw [extendMoments, dif_pos ht]
    exact (hv.2.2 ⟨t, ht⟩).symm
  have hsearch : searchHankelTrials nodes K (extendMoments M) K = some vf := by
    rw [searchHankelTrials_congr nodes (le_refl K) hm]
    exact searchHankelTrials_correct nodes vf (coordinate_nodes_injective hdq) hsparse (le_refl K)
  have hlift : (fun i => boundedLift U (vf i)) = v := by
    funext i
    exact boundedLift_intCast hUq (v i) (hv.1 i)
  change (match searchHankelTrials nodes K (extendMoments M) K with
    | none => none
    | some y => if IntegerCandidate U K M (fun i => boundedLift U (y i)) then
        some (fun i => boundedLift U (y i)) else none) = some v
  simp only [hsearch]
  rw [hlift, if_pos hv]

/-- The actual finite-field decoder realizes the earlier seed-independent
candidate specification on every stored moment array, including dense inputs. -/
theorem hankelIntegerCandidate_eq_momentCandidate {d q U K : ℕ} [Fact q.Prime]
    (hdq : d < q) (hUq : 2 * U < q) (M : Fin (2 * K) → ZMod q) :
    hankelIntegerCandidate (d := d) U K M = momentCandidate U K M := by
  classical
  cases hc : momentCandidate (d := d) U K M with
  | none =>
    cases ha : hankelIntegerCandidate (d := d) U K M with
    | none => rfl
    | some v =>
      have h := momentCandidate_eq_some hdq hUq (hankelIntegerCandidate_spec ha)
      rw [hc] at h
      contradiction
  | some v => exact hankelIntegerCandidate_of_candidate hdq hUq (momentCandidate_spec hc)

/-- The actual decoder may replace the specification in the streaming sketch. -/
def decodeHankelSummary {d q : ℕ} [Fact q.Prime] (U K : ℕ) (z : ZMod q)
    (s : Summary K (ZMod q)) : Option (Fin d → ℤ) :=
  match hankelIntegerCandidate U K s.1 with
  | none => none
  | some y => if checksum (fun i => (y i : ZMod q)) z = s.2 then some y else none

theorem decodeHankelSummary_eq_decodeSummary {d q U K : ℕ} [Fact q.Prime]
    (hdq : d < q) (hUq : 2 * U < q) (z : ZMod q) (s : Summary K (ZMod q)) :
    decodeHankelSummary (d := d) U K z s = decodeSummary U K z s := by
  unfold decodeHankelSummary decodeSummary
  rw [hankelIntegerCandidate_eq_momentCandidate hdq hUq]

end Paper02.SparseRecovery
