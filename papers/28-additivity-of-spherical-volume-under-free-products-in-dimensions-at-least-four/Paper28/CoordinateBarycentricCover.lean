import Paper28.PositiveChainExpansion
import Paper28.SignedFaceGeometry

/-! Every actual unit vector in a finite coordinate sphere lies in the
relative interior of an actual signed barycentric face-chain cell. The
finite positive-coordinate layer construction gives the cell explicitly. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G]

theorem coordinate_sign_recovers_vector (F : Finset G) (u : CoordinateHilbert G)
    (hu : u ∈ coordinateSupportSubspace F) (g : G) :
    coordinateSign (F.filter (fun g => 0 < u g)) g*|u g| = u g := by
  by_cases hg : g ∈ F
  · by_cases hp : 0 < u g
    · simp [coordinateSign,hg,hp,abs_of_pos hp]
    · simp [coordinateSign,hg,hp,abs_of_nonpos (not_lt.mp hp)]
  · have hz := hu g hg
    simp [coordinateSign,hg,hz]

theorem signedChainRaw_scaled_norms_apply (A : Finset G) (C : Finset (Finset G))
    (hFaces : ∀ F ∈ C, F.Nonempty) (w : Finset G → ℝ) (g : G) :
    signedChainRaw A C (fun F => w F*‖signedFaceVector A F‖) g = coordinateSign A g*chainIncidenceProfile C w g := by
  rw [signedChainRaw_apply]
  apply congrArg (fun t => coordinateSign A g*t)
  apply Finset.sum_congr rfl
  intro F hF
  have hn : ‖signedFaceVector A F‖ ≠ 0 := norm_ne_zero_iff.mpr (signedFaceVector_ne_zero A F (hFaces F hF))
  dsimp only
  rw [mul_assoc,mul_inv_cancel₀ hn,mul_one]

theorem coordinate_sphere_barycentric_cover (F : Finset G) (u : RegularSphere G)
    (hu : u.val ∈ coordinateSupportSubspace F) :
    ∃ A : Finset G, A ⊆ F ∧ ∃ C : Finset (Finset G), C.Nonempty ∧
      (∀ E ∈ C, E.Nonempty ∧ E ⊆ F) ∧
      (∀ E ∈ C, ∀ D ∈ C, E ⊆ D ∨ D ⊆ E) ∧ u ∈ strictSignedBarycentricCell A C := by
  obtain ⟨D⟩ := exists_positive_chain_expansion F (fun g => |u.val g|) (fun g => abs_nonneg _)
    (fun g hg => by change |u.val g| = 0; rw [hu g hg,abs_zero])
  let A := F.filter (fun g => 0 < u.val g)
  let w : Finset G → ℝ := fun E => D.weight E*‖signedFaceVector A E‖
  have hRaw : signedChainRaw A D.faces w = u.val := by
    ext g
    rw [signedChainRaw_scaled_norms_apply A D.faces D.nonempty_faces D.weight g,D.formula]
    exact coordinate_sign_recovers_vector F u.val hu g
  have hC : D.faces.Nonempty := by
    by_contra hn
    have hC0 := Finset.not_nonempty_iff_eq_empty.mp hn
    obtain ⟨g,hg⟩ := unit_has_nonzero_coordinate u
    have he := D.formula g
    simp only [hC0,chainIncidenceProfile,Finset.sum_empty] at he
    exact (abs_ne_zero.mpr hg) he.symm
  refine ⟨A,Finset.filter_subset _ _,D.faces,hC,fun E hE => ⟨D.nonempty_faces E hE,D.support E hE⟩,
    D.chain,w,?_,?_⟩
  · intro E hE
    exact mul_pos (D.positive E hE) (norm_pos_iff.mpr (signedFaceVector_ne_zero A E (D.nonempty_faces E hE)))
  · rw [signedChainPoint,hRaw,sphericalNormalize_fixed u.val u.property]

end Paper28
