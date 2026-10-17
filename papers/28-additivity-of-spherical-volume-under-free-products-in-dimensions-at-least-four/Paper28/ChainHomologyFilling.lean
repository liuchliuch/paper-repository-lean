import Paper28.ComparisonHomologyInjection

/-! The exact native chain-boundary consequence of injectivity on homology.
Positive chain degree is written as k+1, matching the source's k>=1. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory
universe v

theorem prescribed_chain_filling_of_homology_mono
    {P C : ChainComplex AddCommGrpCat.{v} ℕ} (integration : P ⟶ C) (k : ℕ)
    [Mono (HomologicalComplex.homologyMap integration (k+1))]
    (z : P.X (k+1)) (hz : P.d (k+1) k z = 0)
    (hBounds : ∃ D : C.X (k+2), C.d (k+2) (k+1) D = integration.f (k+1) z) :
    ∃ Q : P.X (k+2), P.d (k+2) (k+1) Q = z := by
  have hp : (ComplexShape.down ℕ).prev (k+1) = k+2 :=
    (ComplexShape.down ℕ).prev_eq' rfl
  have hn : (ComplexShape.down ℕ).next (k+1) = k :=
    (ComplexShape.down ℕ).next_eq' rfl
  let φ := (HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.down ℕ) (k+1)).map integration
  have hInjective : Function.Injective (ShortComplex.homologyMap φ) :=
    (AddCommGrpCat.mono_iff_injective (HomologicalComplex.homologyMap integration (k+1))).mp inferInstance
  have hz' : (P.sc (k+1)).g z = 0 := by
    change P.d (k+1) ((ComplexShape.down ℕ).next (k+1)) z = 0
    rw [hn]
    exact hz
  have hB : ∃ D : (C.sc (k+1)).X₁, (C.sc (k+1)).f D = φ.τ₂ z := by
    change ∃ D : C.X ((ComplexShape.down ℕ).prev (k+1)),
      C.d ((ComplexShape.down ℕ).prev (k+1)) (k+1) D = integration.f (k+1) z
    rw [hp]
    exact hBounds
  have hQ := prescribed_filling_of_homology_injective φ hInjective z hz' hB
  change ∃ Q : P.X ((ComplexShape.down ℕ).prev (k+1)),
    P.d ((ComplexShape.down ℕ).prev (k+1)) (k+1) Q = z at hQ
  rw [hp] at hQ
  exact hQ

end Paper28
