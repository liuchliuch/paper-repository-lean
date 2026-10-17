import Paper20.Ordinary43
import Paper20.PolynomialLink
import Paper20.BraidWalk
import Paper20.Node
import Paper20.Appendix
import Paper20.Certs.CheckedRec.All
import Paper20.Certs.CheckedHilbert43

/-! Supporting results only. This is not a whole-paper completion contract. -/
namespace P20Verified
open BigOperators

theorem ordinary_certificate  :
    Paper20.Ordinary43.n_h 23 = 46743830419465000460525749853426296821511513919267 ∧
    Paper20.Ordinary43.n_h 24 = 4478706954001198396797888969114794682889954544660295 ∧
    Paper20.Ordinary43.n_h 25 = 429147501803199891064835526788080765663004079176388506 ∧
    20000*(Paper20.Ordinary43.n_h 24)^2 < 19999*Paper20.Ordinary43.n_h 23*Paper20.Ordinary43.n_h 25 ∧
    (∀ h < 904, 0 < Paper20.Ordinary43.n_h h) :=
  Paper20.Ordinary43.thm11

theorem defining_series (b d : ℕ) (H n : ℕ → ℤ) :
    Paper20.Semantics.localBPSExpansion b d H n ↔
    (1-PowerSeries.X)^b * Paper20.Semantics.hilbertSeries H = Paper20.Semantics.bpsSeries d n :=
  Paper20.Semantics.localBPSExpansion_iff_series b d H n

theorem defining_extraction {b d : ℕ} {H n : ℕ → ℤ} (hn : Paper20.Semantics.localBPSExpansion b d H n) :
    ∀ h, h ≤ d → n h = Paper20.Semantics.extracted d (Paper20.Semantics.hilbertResidual b H) h :=
  Paper20.Semantics.localBPSExpansion_eq_extracted hn

theorem partition_enumeration (n : ℕ) (ps : List ℕ) :
    ps ∈ Paper20.partitionsOf n ↔ Paper20.ValidPartition n n ps :=
  Paper20.mem_partitionsOf n ps

theorem partition_no_duplicates (n : ℕ) :
    (Paper20.partitionsOf n).Nodup :=
  Paper20.nodup_partitionsOf n

theorem concrete_walk_bounds (r k h : ℕ) (hh : h ≤ Paper20.deg r k) :
    1 ≤ Paper20.BraidWalk.walkCount r k h ∧
    Paper20.BraidWalk.walkCount r k h ≤ Nat.choose (2*Paper20.deg r k) (2*h) :=
  Paper20.BraidWalk.walk_bounds r k h hh

theorem concrete_walk_endpoints (r k : ℕ) :
    Paper20.BraidWalk.walkCount r k 0 = 1 ∧
    Paper20.BraidWalk.walkCount r k (Paper20.deg r k) = 1 :=
  Paper20.BraidWalk.walk_endpoints r k

theorem Q_degree (r h i : ℕ) (hi : h < i) :
    Paper20.cget (Paper20.Qcoeff r h) i = 0 :=
  Paper20.Qcoeff_degree r h i hi

theorem Q_leading_spectral (r h : ℕ) :
    Paper20.cget (Paper20.Qcoeff r h) h =
    Paper20.transpositionMoment r h / ((2*h).factorial : ℚ) :=
  Paper20.prop_3_2 r h

theorem uniform_polynomial_inequality (k : ℕ) (hk : 10 ≤ k) :
    (Paper20.Uniform36.Q21.eval ((k:ℚ)*(k+1)))^2 <
    Paper20.Uniform36.Q20.eval ((k:ℚ)*(k+1))*Paper20.Uniform36.Q22.eval ((k:ℚ)*(k+1)) :=
  Paper20.Uniform36.thm12_Q k hk

theorem shift_identity (x : ℚ) :
    Paper20.Uniform36.G.eval (110+x) = -(1/(Paper20.Uniform36.Dval:ℚ)) *
    ∑ j ∈ Finset.range 43, (Paper20.Uniform36.bOf j : ℚ)*x^j :=
  Paper20.Uniform36.G_shift x

theorem table1  :
    ∀ j < 43, let de := Paper20.Uniform36.tableBounds.getD j (0,0)
    (de.1:ℤ)*10^de.2 ≤ Paper20.Uniform36.bOf j ∧
    Paper20.Uniform36.bOf j < (de.1+1:ℤ)*10^de.2 :=
  Paper20.Uniform36.table1_verified

theorem node {m : ℕ → ℤ} (hm : Paper20.Semantics.localBPSExpansion 2 1 Paper20.Node.H m) :
    m 0 = 1 ∧ m 1 = 1 :=
  Paper20.Node.node_BPS hm

theorem certified_recurrence  :
    Paper20.Semantics.recurrence25 903
    (fun ℓ => Paper20.Cert.f43List.getD ℓ 0)
    (fun h => Paper20.Cert.Checked43.integers.getD h 0) :=
  Paper20.Cert.Checked43.certificate_recurrence

theorem certified_residual (ℓ : ℕ) (hℓ : ℓ ≤ 903) :
    Paper20.Semantics.hilbertResidual 43 (fun i => Paper20.Cert.Hilbert43.H.getD i 0) ℓ =
    Paper20.Cert.f43List.getD ℓ 0 :=
  Paper20.Cert.Hilbert43.residual_eq ℓ hℓ

end P20Verified
