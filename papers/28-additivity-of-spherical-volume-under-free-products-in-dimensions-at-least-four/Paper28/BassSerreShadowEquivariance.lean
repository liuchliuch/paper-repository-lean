import Paper28.BassSerreSphereShadows
import Paper28.BassSerreBranchEquivariance
import Paper28.ProjectionErrorNeighborhood

/-! Equation (8) for the actual branch norm maps. The representative
cocycle acts by the actual regular action of the factor, and disappears
under its actual orbit quotient. No averaging by isotropy is introduced. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {G : Type} [Group G] [DecidableEq G] [Countable G] {A B : Subgroup G}
  (T : BassSerreObject A B)

theorem bassSerreSphereShadowA_translate (γ : G) (v : G ⧸ A) (u : RegularSphere G) :
    bassSerreSphereShadowA T (γ • v) (γ • u) =
      cosetTranslationCocycle A γ v • bassSerreSphereShadowA T v u := by
  apply Subtype.ext
  ext a
  change hilbertPartitionFold (bassSerreBranchA T (γ • v)) (leftRegular γ u.val) a =
    leftRegular (cosetTranslationCocycle A γ v) (hilbertPartitionFold (bassSerreBranchA T v) u.val) a
  rw [leftRegular_apply]
  have h := hilbertPartitionFold_reindex (bassSerreBranchA T v) (bassSerreBranchA T (γ • v))
    (Equiv.mulLeft γ) (Equiv.mulLeft (cosetTranslationCocycle A γ v))
    (bassSerreBranchA_translate T γ v) u.val (leftRegular γ u.val)
    (fun g => by simp [leftRegular_apply]) ((cosetTranslationCocycle A γ v)⁻¹*a)
  change hilbertPartitionFold (bassSerreBranchA T (γ • v)) (leftRegular γ u.val)
    ((cosetTranslationCocycle A γ v)*((cosetTranslationCocycle A γ v)⁻¹*a)) = _ at h
  simpa only [mul_inv_cancel_left] using h

theorem bassSerreSphereShadowB_translate (γ : G) (v : G ⧸ B) (u : RegularSphere G) :
    bassSerreSphereShadowB T (γ • v) (γ • u) =
      cosetTranslationCocycle B γ v • bassSerreSphereShadowB T v u := by
  apply Subtype.ext
  ext b
  change hilbertPartitionFold (bassSerreBranchB T (γ • v)) (leftRegular γ u.val) b =
    leftRegular (cosetTranslationCocycle B γ v) (hilbertPartitionFold (bassSerreBranchB T v) u.val) b
  rw [leftRegular_apply]
  have h := hilbertPartitionFold_reindex (bassSerreBranchB T v) (bassSerreBranchB T (γ • v))
    (Equiv.mulLeft γ) (Equiv.mulLeft (cosetTranslationCocycle B γ v))
    (bassSerreBranchB_translate T γ v) u.val (leftRegular γ u.val)
    (fun g => by simp [leftRegular_apply]) ((cosetTranslationCocycle B γ v)⁻¹*b)
  change hilbertPartitionFold (bassSerreBranchB T (γ • v)) (leftRegular γ u.val)
    ((cosetTranslationCocycle B γ v)*((cosetTranslationCocycle B γ v)⁻¹*b)) = _ at h
  simpa only [mul_inv_cancel_left] using h

theorem bassSerreQuotientShadowA_translate (γ : G) (v : G ⧸ A) (u : RegularSphere G) :
    bassSerreQuotientShadowA T (γ • v) (γ • u) = bassSerreQuotientShadowA T v u := by
  unfold bassSerreQuotientShadowA
  rw [bassSerreSphereShadowA_translate]
  exact regularQuotientMap_smul _ _

theorem bassSerreQuotientShadowB_translate (γ : G) (v : G ⧸ B) (u : RegularSphere G) :
    bassSerreQuotientShadowB T (γ • v) (γ • u) = bassSerreQuotientShadowB T v u := by
  unfold bassSerreQuotientShadowB
  rw [bassSerreSphereShadowB_translate]
  exact regularQuotientMap_smul _ _

end Paper28
