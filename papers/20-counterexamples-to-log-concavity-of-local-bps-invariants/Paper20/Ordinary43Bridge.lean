import Paper20.Ordinary43
import Paper20.Certs.CheckedRec.All
import Paper20.Certs.CheckedHilbert43
import Paper20.PowerSeriesBPS

/-!
Connection of the original defining expansion to the ordinary-point
certificate. The only remaining input to `from_hilbert_prefix` is a statement
about the Hilbert coefficients, not a statement about the BPS conclusion.
Checking that prefix against the partition sum (13), and the geometric
identification, remain separate required obligations.
-/
namespace Paper20.Ordinary43Bridge
open Paper20.Semantics

/-- Recovering the certificate from any genuine local BPS expansion with
the independently specified Hilbert prefix. -/
theorem from_hilbert_prefix {H n : ℕ → ℤ}
    (hn : localBPSExpansion 43 903 H n)
    (hH : ∀ ℓ, ℓ ≤ 903 → H ℓ = Cert.Hilbert43.H.getD ℓ 0) :
    ∀ h, h ≤ 903 → n h = Cert.Checked43.integers.getD h 0 := by
  apply recurrence25_unique (F := fun ℓ => Cert.f43List.getD ℓ 0)
    (n := n) (m := fun h => Cert.Checked43.integers.getD h 0)
    ?_ Cert.Checked43.certificate_recurrence
  intro h hh
  have hF : hilbertResidual 43 H (903-h) = Cert.f43List.getD (903-h) 0 := by
    calc
      _ = hilbertResidual 43 (fun i => Cert.Hilbert43.H.getD i 0) (903-h) := by
        unfold hilbertResidual
        apply Finset.sum_congr rfl
        intro i hi
        rw [hH (903-h-i) (by omega)]
      _ = _ := Cert.Hilbert43.residual_eq _ (by omega)
  have hrec := localBPSExpansion_recurrence hn h hh
  rwa [hF] at hrec

lemma integers_get (h : ℕ) :
    Cert.Checked43.integers.getD h 0 = (Ordinary43.n_h h : ℤ) := by
  unfold Cert.Checked43.integers Ordinary43.n_h Ordinary43.n43Cert
  simp only [List.getD_eq_getD_getElem?, List.getElem?_map]
  cases he : Cert.n43List[h]? <;> simp [he]

/-- The full ordinary-point conclusion follows from the original BPS
expansion and the Hilbert prefix; none of its displayed BPS values is an input. -/
theorem theorem11_of_hilbert_prefix {H n : ℕ → ℤ}
    (hn : localBPSExpansion 43 903 H n)
    (hH : ∀ ℓ, ℓ ≤ 903 → H ℓ = Cert.Hilbert43.H.getD ℓ 0) :
    n 23 = 46743830419465000460525749853426296821511513919267 ∧
    n 24 = 4478706954001198396797888969114794682889954544660295 ∧
    n 25 = 429147501803199891064835526788080765663004079176388506 ∧
    20000*(n 24)^2 < 19999*n 23*n 25 ∧ (∀ h ≤ 903, 0 < n h) := by
  have he : ∀ h, h ≤ 903 → n h = (Ordinary43.n_h h : ℤ) :=
    fun h hh => (from_hilbert_prefix hn hH h hh).trans (integers_get h)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [he 23 (by decide), Ordinary43.n_h_23]
    norm_num
  · rw [he 24 (by decide), Ordinary43.n_h_24]
    norm_num
  · rw [he 25 (by decide), Ordinary43.n_h_25]
    norm_num
  · rw [he 24 (by decide), he 23 (by decide), he 25 (by decide)]
    exact_mod_cast Ordinary43.thm11_ineq
  · intro h hh
    rw [he h hh]
    exact_mod_cast Ordinary43.n_h_pos h (by omega)

end Paper20.Ordinary43Bridge
