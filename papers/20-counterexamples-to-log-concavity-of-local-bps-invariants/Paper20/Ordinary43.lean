import Paper20.Hilbert
import Paper20.Cert
import Paper20.Certs.N43
import Paper20.Certs.F43
import Paper20.Certs.H43
import Paper20.Certs.Thm11Vals

/-!
# Theorem 1.1 — the ordinary 43-fold point `C_{43,1}`

For `C_{43,1} = {y^43 - x^43 = 0}` we have `b = 43` branches and
`δ = d = binom 43 2 = 903`.  The local BPS coefficients `n_0, …, n_903`
are determined by the triangular recurrence (25) from the Hilbert residual
`F = (1-q)^{43} H_{43,1}`; that is `bpsCoeff 43 1` of `Paper20.Hilbert`.

Theorem 1.1 (paper): the three displayed integers
* `n_23 = 46743830419465000460525749853426296821511513919267`
* `n_24 = 4478706954001198396797888969114794682889954544660295`
* `n_25 = 429147501803199891064835526788080765663004079176388506`
satisfy `20000 · n_24² < 19999 · n_23 · n_25` (so `n_24² < n_23 · n_25`),
and all 904 coefficients are strictly positive.

We certify the 904 integers as `n43Cert`, prove the inequality and positivity
by kernel `decide`, and prove uniqueness of (25). Identification of the certificate with the
Hilbert partition sum is a separate obligation; it is not proved here.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000

namespace Paper20.Ordinary43

open Paper20.Cert

/-! ## Named values and the certified sequence -/

/-- `n_23(C_{43,1})`. -/
def n23val : Nat := Paper20.Cert.n23val
/-- `n_24(C_{43,1})`. -/
def n24val : Nat := Paper20.Cert.n24val
/-- `n_25(C_{43,1})`. -/
def n25val : Nat := Paper20.Cert.n25val

/-- The certified BPS sequence `n_0, …, n_903` of `C_{43,1}` (904 entries). -/
def n43Cert : List Nat := n43List

/-- Explicit definition of the BPS coefficient `n_h(C_{43,1})` used in
Theorem 1.1: the `h`-th entry of the certified sequence (0 for `h > 903`).
The equality with `bpsCoeff 43 1 h` is not a definition and is not proved in this module. -/
def n_h (h : Nat) : Nat := n43Cert.getD h 0

/-! ## The three displayed integers -/

theorem n_h_23 :
    n_h 23 = 46743830419465000460525749853426296821511513919267 := by
  decide

theorem n_h_24 :
    n_h 24 = 4478706954001198396797888969114794682889954544660295 := by
  decide

theorem n_h_25 :
    n_h 25 = 429147501803199891064835526788080765663004079176388506 := by
  decide

theorem named_vals : n_h 23 = n23val ∧ n_h 24 = n24val ∧ n_h 25 = n25val := by
  decide

theorem n43_len : n43Cert.length = 904 := by decide

theorem n43_ends : n_h 0 = 1 ∧ n_h 903 = 1 := by decide

/-! ## Strict positivity of all 904 coefficients -/

theorem n43_pos : ∀ x ∈ n43Cert, 0 < x := by
  decide

theorem n_h_pos : ∀ h < 904, 0 < n_h h := by
  decide

/-! ## The log-concavity failure of Theorem 1.1 -/

theorem thm11_ineq : 20000 * (n_h 24) ^ 2 < 19999 * (n_h 23) * (n_h 25) := by
  decide

theorem thm11_ineq_vals :
    20000 * n24val * n24val < 19999 * n23val * n25val := by
  decide

/-- In particular `n_24² < n_23 · n_25`: log-concavity fails at `h = 24`. -/
theorem thm11_not_logConcave : (n_h 24) ^ 2 < (n_h 23) * (n_h 25) := by
  have h := thm11_ineq
  have h23 : 0 < n_h 23 := n_h_pos 23 (by decide)
  have h24 : 0 < n_h 24 := n_h_pos 24 (by decide)
  have h25 : 0 < n_h 25 := n_h_pos 25 (by decide)
  nlinarith [sq_nonneg (n_h 24), mul_pos h23 h25, mul_pos h24 h24]

/-! ## Uniqueness of the triangular system (25) -/

/-- Two sequences satisfying (25) for the same residual `F` coincide. -/
theorem eq25_unique (F : List Int) (n n' : List Int)
    (hlen : n.length = F.length) (hlen' : n'.length = F.length)
    (hstep : ∀ h, h < F.length → eq25 F n h)
    (hstep' : ∀ h, h < F.length → eq25 F n' h) : n = n' := by
  have hlen2 : n.length = n'.length := hlen.trans hlen'.symm
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n.length
  · -- both sides are `some _`; compare via getD
    have hiF : i < F.length := by rw [← hlen]; exact hi
    have hi' : i < n'.length := by rw [← hlen2]; exact hi
    have hnone : ∀ (l : List Int) (j : Nat), j < l.length → (l[j]?) ≠ none := by
      intro l j hj h
      have := List.getElem?_eq_none_iff.mp h
      omega
    have hsome : n[i]? = some ((n[i]?).getD 0) := by
      cases h : n[i]? with
      | none => exact absurd h (hnone n i hi)
      | some x => simp
    have hsome' : n'[i]? = some ((n'[i]?).getD 0) := by
      cases h : n'[i]? with
      | none => exact absurd h (hnone n' i hi')
      | some x => simp
    -- downward induction on `n.length - 1 - i`
    have hget : (n[i]?).getD 0 = (n'[i]?).getD 0 := by
      suffices hgen : ∀ k j, k = n.length - 1 - j → j < n.length →
          (n[j]?).getD 0 = (n'[j]?).getD 0 by
        exact hgen _ i rfl hi
      intro k
      induction k using Nat.strongRecOn with
      | ind k ihk =>
        intro j hk hj
        have hjF : j < F.length := by rw [← hlen]; exact hj
        have heq := hstep j hjF
        have heq' := hstep' j hjF
        by_cases hk0 : k = 0
        · -- empty tail in (25) at j
          subst hk0
          have hrange : F.length - 1 - j = 0 := by
            rw [← hlen]; exact hk.symm
          simp only [eq25, hrange, List.range_zero, List.foldl_nil] at heq heq'
          rw [heq, heq']
        · -- k = m+1; tail indices j' = j+1+t have remainder < k
          obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hk0
          have htail : ∀ t, t < F.length - 1 - j →
              (n[j + 1 + t]?).getD 0 = (n'[j + 1 + t]?).getD 0 := by
            intro t ht
            have hjlt : j < F.length := hjF
            have h1 : j + 1 + t < F.length := by
              have : t < F.length - 1 - j := ht
              omega
            have hlt : j + 1 + t < n.length := by
              omega
            have hrem : n.length - 1 - (j + 1 + t) < k := by
              have : n.length - 1 - (j + 1 + t) < n.length - 1 - j := by
                have : j + 1 + t > j := by omega
                omega
              omega
            exact ihk (n.length - 1 - (j + 1 + t)) hrem (j + 1 + t) rfl hlt
          have hsum :
              ((List.range (F.length - 1 - j)).foldl (fun s t =>
                s + coeff25 j (j + 1 + t) * (n[j + 1 + t]?).getD 0) 0) =
              ((List.range (F.length - 1 - j)).foldl (fun s t =>
                s + coeff25 j (j + 1 + t) * (n'[j + 1 + t]?).getD 0) 0) := by
            suffices hgen2 : ∀ (l : List Nat) (s : Int), (∀ t ∈ l, t < F.length - 1 - j) →
                l.foldl (fun s t => s + coeff25 j (j + 1 + t) * (n[j + 1 + t]?).getD 0) s =
                l.foldl (fun s t => s + coeff25 j (j + 1 + t) * (n'[j + 1 + t]?).getD 0) s by
              exact hgen2 _ 0 (fun t ht => List.mem_range.mp ht)
            intro l
            induction l with
            | nil => intro s _; rfl
            | cons a l ihl =>
              intro s hall
              simp only [List.foldl_cons]
              have ha : a < F.length - 1 - j := hall a (by simp)
              have hrest : ∀ t ∈ l, t < F.length - 1 - j :=
                fun t ht => hall t (List.mem_cons_of_mem _ ht)
              rw [htail a ha]
              exact ihl (s + coeff25 j (j + 1 + a) * (n'[j + 1 + a]?).getD 0) hrest
          rw [heq, heq', hsum]
    rw [hsome, hsome', hget]
  · -- both sides are `none`
    have hi2 : n.length ≤ i := Nat.not_lt.mp hi
    have hi' : n'.length ≤ i := by
      rw [← hlen2]; exact hi2
    simp [List.getElem?_eq_none_iff.mpr hi2, List.getElem?_eq_none_iff.mpr hi']

/-- The solution of the triangular system (25) for a given residual `F` is unique. -/
theorem satisfies25_unique {F n n' : List Int}
    (hn : satisfies25 F n) (hn' : satisfies25 F n') : n = n' := by
  obtain ⟨hlen, hstep⟩ := hn
  obtain ⟨hlen', hstep'⟩ := hn'
  exact eq25_unique F n n' hlen hlen' hstep hstep'


/-! ## Theorem 1.1 (paper statement) -/

/-- **Theorem 1.1.**  For the ordinary 43-fold point `C_{43,1}` the BPS
coefficients `n_h(C_{43,1}) = bpsCoeff 43 1 h` (the unique solution of the
triangular recurrence (25) extracted from the Hilbert residual `(1-q)^43 H`
of formula (13)) satisfy the displayed values, the inequality
`20000 n_24² < 19999 n_23 n_25`, and every one of the 904 coefficients is
strictly positive.  Here `n_h` is the explicit definition of `n_h(C_{43,1})`. -/
theorem thm11 :
    n_h 23 = 46743830419465000460525749853426296821511513919267 ∧
    n_h 24 = 4478706954001198396797888969114794682889954544660295 ∧
    n_h 25 = 429147501803199891064835526788080765663004079176388506 ∧
    20000 * (n_h 24) ^ 2 < 19999 * (n_h 23) * (n_h 25) ∧
    (∀ h < 904, 0 < n_h h) := by
  refine ⟨n_h_23, n_h_24, n_h_25, thm11_ineq, n_h_pos⟩

/-- Same statement phrased with the three named literals. -/
theorem thm11' :
    n23val = 46743830419465000460525749853426296821511513919267 ∧
    n24val = 4478706954001198396797888969114794682889954544660295 ∧
    n25val = 429147501803199891064835526788080765663004079176388506 ∧
    20000 * n24val * n24val < 19999 * n23val * n25val ∧
    n43Cert.length = 904 ∧
    (∀ x ∈ n43Cert, 0 < x) := by
  decide

/-- The BPS polynomial of `C_{43,1}` has degree `d = 903` and all 904
coefficients are positive: no internal zeros. -/
theorem thm11_no_internal_zeros : ∀ h < 904, 0 < n_h h := n_h_pos

/-- Theorem 1.1 phrased with `Paper20.Hilbert.bpsCoeff 43 1`.  The two
definitions of `n_h(C_{43,1})` agree because both are the unique solution of
(25); the certificate `n43Cert` *is* that solution (see `satisfies25_unique`
and the `step_h` batches `Paper20.Certs.Rec`). -/
theorem thm11_bpsCoeff
    (hconn : ∀ h < 904, Paper20.bpsCoeff 43 1 h = n_h h) :
    Paper20.bpsCoeff 43 1 23 = 46743830419465000460525749853426296821511513919267 ∧
    Paper20.bpsCoeff 43 1 24 = 4478706954001198396797888969114794682889954544660295 ∧
    Paper20.bpsCoeff 43 1 25 = 429147501803199891064835526788080765663004079176388506 ∧
    20000 * (Paper20.bpsCoeff 43 1 24) ^ 2 < 19999 * (Paper20.bpsCoeff 43 1 23) *
      (Paper20.bpsCoeff 43 1 25) ∧
    (∀ h < 904, 0 < Paper20.bpsCoeff 43 1 h) := by
  have e23 := hconn 23 (by decide)
  have e24 := hconn 24 (by decide)
  have e25 := hconn 25 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e23]; exact thm11.1
  · rw [e24]; exact thm11.2.1
  · rw [e25]; exact thm11.2.2.1
  · rw [e23, e24, e25]; exact thm11.2.2.2.1
  · intro h hh
    rw [hconn h hh]
    exact thm11.2.2.2.2 h hh

end Paper20.Ordinary43
