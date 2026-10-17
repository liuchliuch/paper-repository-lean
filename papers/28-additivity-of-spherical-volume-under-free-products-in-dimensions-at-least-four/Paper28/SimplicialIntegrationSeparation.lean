import Paper28.NondegenerateSimplicialChains
import Mathlib.Algebra.FreeAbelianGroup.Finsupp

/-! Standard Euclidean test-current separation is kept as a local
evaluation input, with real-valued evaluations. Actual strict simplicial
integration is injective by a native finite coefficient argument. No
homology comparison or prescribed filling is an input here. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical

structure EuclideanSimplexSeparationInput {d : ℕ}
    (I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance)
    (S : EuclideanSimplexIntegrationInput d I) : Prop where
  separation : ∀ (K : FiniteEuclideanComplex (EuclideanAmbient d)) (k : ℕ)
    (σ : NondegenerateComplexSimplex K k), ∃ ev : I.Current k →+ ℝ,
      ∀ τ : NondegenerateComplexSimplex K k,
        ev (S.integration k (orderedSimplexVertices τ.val)) = if σ = τ then 1 else 0

theorem finiteSimplicialIntegration_of {d k : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    {I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance}
    (S : EuclideanSimplexIntegrationInput d I) (σ : NondegenerateComplexSimplex K k) :
    finiteSimplicialIntegration S k (FreeAbelianGroup.of σ) = S.integration k (orderedSimplexVertices σ.val) := by
  simp only [finiteSimplicialIntegration,AddMonoidHom.comp_apply,nondegenerateChainInclusion,
    FreeAbelianGroup.map_of_apply,orderedIntegration,FreeAbelianGroup.lift_apply_of]

theorem finiteSimplicialIntegration_injective {d : ℕ}
    (I : CompactIntegralCurrentAlgebraInput.{0,0} (EuclideanAmbient d) inferInstance)
    (S : EuclideanSimplexIntegrationInput d I) (Sep : EuclideanSimplexSeparationInput I S)
    (K : FiniteEuclideanComplex (EuclideanAmbient d)) (k : ℕ) :
    Function.Injective (finiteSimplicialIntegration (K := K) S k) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  apply (FreeAbelianGroup.equivFinsupp (NondegenerateComplexSimplex K k)).injective
  change FreeAbelianGroup.toFinsupp z = FreeAbelianGroup.toFinsupp 0
  rw [map_zero]
  apply Finsupp.ext
  intro σ
  obtain ⟨ev,hev⟩ := Sep.separation K k σ
  have he : ev.comp (finiteSimplicialIntegration S k) =
      (Int.castAddHom ℝ).comp (FreeAbelianGroup.coeff σ) := by
    apply FreeAbelianGroup.lift_ext
    intro τ
    simp only [AddMonoidHom.comp_apply,finiteSimplicialIntegration_of,hev]
    by_cases he : σ = τ
    · subst τ
      simp [FreeAbelianGroup.coeff]
    · simp [FreeAbelianGroup.coeff,he]
  have hzero := congrArg ev hz
  rw [map_zero] at hzero
  have hc : ((FreeAbelianGroup.coeff σ z : ℤ) : ℝ) = 0 :=
    (DFunLike.congr_fun he z).symm.trans hzero
  exact Int.cast_eq_zero.mp hc

end Paper28
