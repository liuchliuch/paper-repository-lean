import Paper06.Model
import Paper06.MatchingFull
import Paper06.IncidenceFull

open Real Set BigOperators
open scoped Classical

namespace Paper06

/-- The fixed uniform-input constraint written with the paper's finite vector target. -/
noncomputable def uniformInputLinear (R : Type*) [Fintype R] :
    ((R × R) → ℝ) →ₗ[ℝ] (Fin (Fintype.card R) → ℝ) where
  toFun q x := ∑ a, q ((Fintype.equivFin R).symm x, a)
  map_add' q q' := by funext x; simp [Finset.sum_add_distrib]
  map_smul' c q := by funext x; simp [Finset.mul_sum]

noncomputable def uniformInputTarget (R : Type*) [Fintype R] :
    Fin (Fintype.card R) → ℝ := fun _ => (Fintype.card R : ℝ)⁻¹

theorem uniformInput_affineSlice (R : Type*) [Fintype R] :
    Posterior.AffineSlice (uniformInputLinear R) (uniformInputTarget R) =
      {q : FinProb (R × R) | UniformInput q} := by
  ext q
  constructor
  · intro h x
    have hh := congrFun h ((Fintype.equivFin R) x)
    simpa [uniformInputLinear, uniformInputTarget, one_div] using hh
  · intro h
    funext x
    simpa [uniformInputLinear, uniformInputTarget, one_div] using h ((Fintype.equivFin R).symm x)

/-- The explicit matching law is admissible in the original finite-vector model. -/
noncomputable def matchingAdmissible (R : Type*) [Fintype R] [CommRing R] [Nontrivial R]
    (n : ℕ) (hn : Even n) : Admissible (R × R) n where
  t := Fintype.card R
  Γ := uniformInputLinear R
  η := uniformInputTarget R
  law := Matching.matchingLawFin n hn
  exchangeable := Matching.matchingLawFin_exchangeable n hn
  cp i z := by
    funext x
    exact Matching.matchingLawFin_fixedInput n hn z i ((Fintype.equivFin R).symm x)

@[simp] theorem matchingAdmissible_slice (R : Type*) [Fintype R] [CommRing R] [Nontrivial R]
    (n : ℕ) (hn : Even n) :
    (matchingAdmissible R n hn).slice = {q : FinProb (R × R) | UniformInput q} :=
  uniformInput_affineSlice R

end Paper06
