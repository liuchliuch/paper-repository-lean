import Paper13.CompleteDimension
import Paper13.InvariantGap
import Paper13.PositiveDimension
noncomputable section
namespace Paper13
attribute [local instance] Classical.propDecidable

lemma GkOrdinal_connected (k : ℕ) (hk : 7 ≤ k) : (GkOrdinal k).Connected :=
  (Gk_connected k hk).map (GkOrdinalIso k).symm.toHom (GkOrdinalIso k).symm.surjective

/-- The natural algebra's exact dimension follows from the actual triangle in each gadget. -/
theorem Gk_natural_dimension (k : ℕ) (hk : 7 ≤ k) :
    Module.finrank ℝ (graphNat (GkOrdinal k))=2^(14*k-1)-2 := by
  rw [GkOrdinal_nat_eq_ma k hk]
  let v : Fin k := ⟨0,by omega⟩
  let a : Fin (k*7) := finProdFinEquiv (v,(1 : Fin 7))
  let b : Fin (k*7) := finProdFinEquiv (v,(2 : Fin 7))
  let c : Fin (k*7) := finProdFinEquiv (v,(5 : Fin 7))
  have hab : (GkOrdinal k).Adj a b := by
    change (Gk k).Adj (finProdFinEquiv.symm (finProdFinEquiv (v,1))) (finProdFinEquiv.symm (finProdFinEquiv (v,2)))
    simp only [Equiv.symm_apply_apply]
    exact Or.inl ⟨rfl,by change H.Adj (1 : Fin 7) 2; decide⟩
  have hac : (GkOrdinal k).Adj a c := by
    change (Gk k).Adj (finProdFinEquiv.symm (finProdFinEquiv (v,1))) (finProdFinEquiv.symm (finProdFinEquiv (v,5)))
    simp only [Equiv.symm_apply_apply]
    exact Or.inl ⟨rfl,by change H.Adj (1 : Fin 7) 5; decide⟩
  have hbc : (GkOrdinal k).Adj b c := by
    change (Gk k).Adj (finProdFinEquiv.symm (finProdFinEquiv (v,2))) (finProdFinEquiv.symm (finProdFinEquiv (v,5)))
    simp only [Equiv.symm_apply_apply]
    exact Or.inl ⟨rfl,by change H.Adj (2 : Fin 7) 5; decide⟩
  have hd := graphMa_dimension_of_triangle (by omega : 2 ≤ k*7) (GkOrdinal k) (GkOrdinal_connected k hk) a b c hab hac hbc
  simpa only [show 2*(k*7)=14*k by omega] using hd

/-- Full actual finite-dimensional algebra conclusion of Theorem 1. -/
theorem theorem1_actual_algebras (k : ℕ) (hk : 7 ≤ k) : Theorem1AlgebraClaim k :=
  ⟨Gk_std_dimension k (by omega),Gk_natural_dimension k hk⟩
end Paper13
