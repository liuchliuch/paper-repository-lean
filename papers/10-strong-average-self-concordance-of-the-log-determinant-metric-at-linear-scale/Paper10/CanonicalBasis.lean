import Paper10.StandardBasis

noncomputable section
open Matrix
namespace Paper10

/-- Reindexing preserves a complete Frobenius orthonormal basis. -/
theorem orthonormalFrob_reindex {q : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ι → Matrix (Fin q) (Fin q) ℝ) (hF : OrthonormalFrob F) (e : κ ≃ ι) :
    OrthonormalFrob (fun a => F (e a)) := by
  classical
  refine ⟨fun a => hF.1 (e a), ?_, ?_⟩
  · intro a b
    by_cases hab : a = b
    · subst b
      simpa using hF.2.1 (e a) (e a)
    · have he : e a ≠ e b := fun hh => hab (e.injective hh)
      simpa [hab, he] using hF.2.1 (e a) (e b)
  · intro U hU
    obtain ⟨v, hv⟩ := hF.2.2 U hU
    refine ⟨fun a => v (e a), ?_⟩
    exact hv.trans (e.sum_comp (fun a => v a • F a)).symm

/-- The standard symmetric coordinate basis has the actual ambient dimension n=q(q+1)/2. -/
theorem standard_basis_card (q : ℕ) : Fintype.card (Fin q ⊕ Upper q) = n q := by
  have hh := parseval_trace_sq (standardF q) (standardF_orthonormal q)
  have hs : ∀ a : Fin q ⊕ Upper q, Matrix.trace (standardF q a * standardF q a) = 1 := by
    intro a
    simpa only [if_pos rfl, frob] using standardF_inner q a a
  simp_rw [hs] at hh
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hh
  exact_mod_cast hh

/-- A fixed explicit Frobenius basis indexed by Fin n, with n equal to the ambient dimension. -/
def canonicalF (q : ℕ) : Fin (n q) → Matrix (Fin q) (Fin q) ℝ :=
  fun a => standardF q ((Fintype.equivOfCardEq (by simpa using (standard_basis_card q).symm)) a)

theorem canonicalF_orthonormal (q : ℕ) : OrthonormalFrob (canonicalF q) :=
  orthonormalFrob_reindex (standardF q) (standardF_orthonormal q) _

end Paper10
