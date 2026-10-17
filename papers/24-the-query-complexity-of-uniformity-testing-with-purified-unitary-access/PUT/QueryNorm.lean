import PUT.FourierModel
import PUT.OperatorBridge
import PUT.NormBound

/-!
# Finite Fourier-sector assembly in the actual Hilbert norm

The actual adversary has finite Fourier support. Consequently the query
difference can be assembled from finitely many whole radial sectors. This
module proves the Hilbert-space assembly theorem (including complements)
and the last step from the two difference blocks to the printed bound.
-/
noncomputable section
namespace PUT.QueryNorm
open scoped InnerProduct

section OrthogonalSectors
variable {ι H E K F : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Bessel's inequality for full mutually orthogonal Hilbert subspaces,
proved using their actual adjoints. The radial dimension need not be finite. -/
theorem sector_bessel (J : ι → H →ₗᵢ[ℂ] E)
    (hJ : OrthogonalFamily ℂ (fun _ : ι => H) J) (s : Finset ι) (x : E) :
    ∑ i ∈ s, ‖(J i).toContinuousLinearMap.adjoint x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  let y : ι → H := fun i => (J i).toContinuousLinearMap.adjoint x
  let v : E := ∑ i ∈ s, J i (y i)
  have hv : ‖v‖ ^ 2 = ∑ i ∈ s, ‖y i‖ ^ 2 := hJ.norm_sum y s
  have hi : (inner ℂ v x).re = ∑ i ∈ s, ‖y i‖ ^ 2 := by
    simp only [v, sum_inner, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change (inner ℂ ((J i).toContinuousLinearMap (y i)) x).re = _
    rw [← (J i).toContinuousLinearMap.adjoint_inner_right]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (y i)
  have hcs := re_inner_le_norm (𝕜 := ℂ) v x
  change (inner ℂ v x).re ≤ ‖v‖ * ‖x‖ at hcs
  rw [hi, ← hv] at hcs
  have hn : ‖v‖ ≤ ‖x‖ := by nlinarith [norm_nonneg v, norm_nonneg x]
  change (∑ i ∈ s, ‖y i‖ ^ 2) ≤ ‖x‖ ^ 2
  rw [← hv]
  exact pow_le_pow_left₀ (norm_nonneg v) hn 2

/-- A finite operator diagonal between orthogonal families of entire
Hilbert subspaces. Its domain and codomain can be infinite dimensional. -/
def sectorOperator (s : Finset ι) (J : ι → H →ₗᵢ[ℂ] E)
    (L : ι → K →ₗᵢ[ℂ] F) (D : ι → H →L[ℂ] K) : E →L[ℂ] F :=
  ∑ i ∈ s, (L i).toContinuousLinearMap ∘L D i ∘L (J i).toContinuousLinearMap.adjoint

@[simp] theorem sectorOperator_apply (s : Finset ι) (J : ι → H →ₗᵢ[ℂ] E)
    (L : ι → K →ₗᵢ[ℂ] F) (D : ι → H →L[ℂ] K) (x : E) :
    sectorOperator s J L D x = ∑ i ∈ s, L i (D i ((J i).toContinuousLinearMap.adjoint x)) := by
  simp [sectorOperator]

/-- Disjoint column or row blocks control the genuine operator norm by the
largest whole-sector norm. No premise here presumes a query norm bound. -/
theorem sectorOperator_norm_le (s : Finset ι) (J : ι → H →ₗᵢ[ℂ] E)
    (L : ι → K →ₗᵢ[ℂ] F) (D : ι → H →L[ℂ] K)
    (hJ : OrthogonalFamily ℂ (fun _ : ι => H) J)
    (hL : OrthogonalFamily ℂ (fun _ : ι => K) L)
    (C : ℝ) (hC : 0 ≤ C) (hD : ∀ i ∈ s, ‖D i‖ ≤ C) :
    ‖sectorOperator s J L D‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro x
  have hsq : ‖sectorOperator s J L D x‖ ^ 2 ≤ C ^ 2 * ‖x‖ ^ 2 := by
    rw [sectorOperator_apply, hL.norm_sum]
    calc
      (∑ i ∈ s, ‖D i ((J i).toContinuousLinearMap.adjoint x)‖ ^ 2)
          ≤ ∑ i ∈ s, C ^ 2 * ‖(J i).toContinuousLinearMap.adjoint x‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hb : ‖D i ((J i).toContinuousLinearMap.adjoint x)‖ ≤
            C * ‖(J i).toContinuousLinearMap.adjoint x‖ :=
          ((D i).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hD i hi) (norm_nonneg _))
        simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = C ^ 2 * ∑ i ∈ s, ‖(J i).toContinuousLinearMap.adjoint x‖ ^ 2 :=
        (Finset.mul_sum ..).symm
      _ ≤ C ^ 2 * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (sector_bessel J hJ s x) (sq_nonneg C)
  nlinarith [norm_nonneg (sectorOperator s J L D x),
    mul_nonneg hC (norm_nonneg x)]

/-- The Fourier sectors constructed on the actual prior are mutually
orthogonal, including every unselected radial direction. -/
theorem actual_fourier_orthogonal {d M : ℕ} {a : ℝ} (ha : 0 < a) :
    OrthogonalFamily ℂ (fun _ : PhaseIndex d M => FourierModel.RadialL2 d a)
      (FourierModel.sector ha) := by
  intro n m hnm h g
  exact FourierModel.sector_orthogonal ha hnm h g

end OrthogonalSectors

end PUT.QueryNorm
