import Paper20.Actual43Bridge
import Paper20.Certs.HilbertParts.All

/-! The ordinary 43-fold counterexample against the actual executable BPS
coefficients. The full partition-sum certificate supplies the input to the
already checked Hilbert-to-program bridge. -/
namespace Paper20.Counterexample43

theorem coefficient (h : ℕ) (hh : h ≤ 903) : bpsCoeff 43 1 h = Ordinary43.n_h h :=
  Actual43Bridge.coefficient Cert.HilbertParts.Tree.h43_partition_sum h hh

theorem theorem1_1 :
    bpsCoeff 43 1 23 = 46743830419465000460525749853426296821511513919267 ∧
    bpsCoeff 43 1 24 = 4478706954001198396797888969114794682889954544660295 ∧
    bpsCoeff 43 1 25 = 429147501803199891064835526788080765663004079176388506 ∧
    20000*(bpsCoeff 43 1 24)^2 < 19999*bpsCoeff 43 1 23*bpsCoeff 43 1 25 ∧
    (∀ h ≤ 903, 0 < bpsCoeff 43 1 h) :=
  Actual43Bridge.theorem1_1 Cert.HilbertParts.Tree.h43_partition_sum

end Paper20.Counterexample43
