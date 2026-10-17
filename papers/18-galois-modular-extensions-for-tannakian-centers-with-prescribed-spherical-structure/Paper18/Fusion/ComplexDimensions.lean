import Paper18.Fusion.Pivotal

/-! # Conjugation and nonzero global dimension

The transpose relation from actual rigid reciprocity makes every complex
dimension character preserve the based involution. In particular, squared
norm dimensions are positive and their sum cannot vanish.
-/
noncomputable section
open Classical
open scoped BigOperators ComplexConjugate
universe u
namespace Paper18.PivotalData
variable {ι : Type u} [Fintype ι] {B : FusionBasis ι} (J : PivotalData B)

/-- Rigid duality acts as complex conjugation on any complex dimension
character. This follows by pairing a common eigenvector against itself. -/
theorem jdim_dual_eq_conj (x : ι) : J.jdim (B.dual x) = conj (J.jdim x) := by
  let Q : ℂ := ∑ i, conj (J.jdim i) * J.jdim i
  have hQ : Q = ((∑ i, Complex.normSq (J.jdim i) : ℝ) : ℂ) := by
    simp only [Q, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  have hp : 0 < ∑ i, Complex.normSq (J.jdim i) :=
    Finset.sum_pos' (fun i _ => Complex.normSq_nonneg _)
      ⟨B.one, Finset.mem_univ _, by simp [J.jdim_one]⟩
  have hn : Q ≠ 0 := by
    rw [hQ]
    exact_mod_cast ne_of_gt hp
  apply mul_right_cancel₀ hn
  calc
    J.jdim (B.dual x) * Q = ∑ y, conj (J.jdim y) *
        (J.jdim (B.dual x) * J.jdim y) := by
      simp only [Q, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = ∑ y, conj (J.jdim y) *
        (∑ z, (B.N (B.dual x) y z : ℂ) * J.jdim z) := by
      simp_rw [J.jdim_tensor]
    _ = ∑ z, conj (∑ y, (B.N x z y : ℂ) * J.jdim y) * J.jdim z := by
      simp only [Finset.mul_sum, map_sum, map_mul, map_natCast, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      apply Finset.sum_congr rfl
      intro y _
      rw [← B.N_dual x z y]
      ring
    _ = ∑ z, conj (J.jdim x * J.jdim z) * J.jdim z := by
      simp_rw [← J.jdim_tensor]
    _ = conj (J.jdim x) * Q := by
      simp only [Q, map_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring

theorem ndim_eq_normSq (x : ι) : J.ndim x = (Complex.normSq (J.jdim x) : ℂ) := by
  rw [ndim, J.jdim_dual_eq_conj, Complex.mul_conj]

theorem ndim_re_pos (x : ι) : 0 < (J.ndim x).re := by
  rw [J.ndim_eq_normSq]
  exact Complex.normSq_pos.mpr (J.jdim_ne_zero x)

/-- Global categorical dimension, computed from the actual simple norms
after applying the proved categorical bridge. -/
def globalDimension : ℂ := ∑ x, J.ndim x

theorem globalDimension_re_pos : 0 < J.globalDimension.re := by
  change 0 < Complex.reAddGroupHom (∑ x, J.ndim x)
  rw [map_sum]
  exact Finset.sum_pos' (fun i _ => (J.ndim_re_pos i).le)
    ⟨B.one, Finset.mem_univ _, J.ndim_re_pos B.one⟩

theorem globalDimension_ne_zero : J.globalDimension ≠ 0 := by
  intro h
  have hp := J.globalDimension_re_pos
  rw [h] at hp
  simp at hp

end Paper18.PivotalData
