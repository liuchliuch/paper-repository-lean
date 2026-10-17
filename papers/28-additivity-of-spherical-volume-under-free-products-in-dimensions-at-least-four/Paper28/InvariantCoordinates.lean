import Paper28.RegularStabilizers
import Paper28.L2CompactProjection

/-! Stabilizer-invariant finite coordinate choices, enlarged by any prescribed
relative supports. Uniform compact approximation and exact relative fixing
are derived from the actual native l2 projections. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {G : Type*} [Group G] [DecidableEq G]

def subgroupCoordinateSaturation (H : Subgroup G) [Fintype H] (F : Finset G) : Finset G :=
  Finset.univ.biUnion (fun h : H => F.image (fun x => h.val*x))

theorem mem_subgroupCoordinateSaturation (H : Subgroup G) [Fintype H] (F : Finset G) (g : G) :
    g ∈ subgroupCoordinateSaturation H F ↔ ∃ h : H, ∃ x ∈ F, h.val*x = g := by
  simp only [subgroupCoordinateSaturation, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image]

theorem subset_subgroupCoordinateSaturation (H : Subgroup G) [Fintype H] (F : Finset G) :
    F ⊆ subgroupCoordinateSaturation H F := by
  intro g hg
  exact (mem_subgroupCoordinateSaturation H F g).mpr ⟨1,g,hg,by simp⟩

theorem subgroupCoordinateSaturation_invariant (H : Subgroup G) [Fintype H]
    (F : Finset G) (γ : H) (g : G) :
    g ∈ subgroupCoordinateSaturation H F ↔ γ.val*g ∈ subgroupCoordinateSaturation H F := by
  rw [mem_subgroupCoordinateSaturation, mem_subgroupCoordinateSaturation]
  constructor
  · rintro ⟨h,x,hx,rfl⟩
    exact ⟨γ*h,x,hx,by simp [mul_assoc]⟩
  · rintro ⟨h,x,hx,he⟩
    refine ⟨γ⁻¹*h,x,hx,?_⟩
    have ht := congrArg (fun z => γ.val⁻¹*z) he
    simpa [mul_assoc] using ht

/-- Exact fixing of every vector supported in the prescribed finite set. -/
theorem l2CoordinateProjection_fixed (F B : Finset G) (hBF : B ⊆ F)
    (u : CoordinateHilbert G) (hu : ∀ g ∉ B, u g = 0) : l2CoordinateProjection F u = u := by
  ext g
  rw [l2CoordinateProjection_apply]
  by_cases hg : g ∈ F
  · rw [if_pos hg]
  · rw [if_neg hg, hu g (fun h => hg (hBF h))]

/-- Invariance of the coordinate set gives actual equivariance of the
coordinate projection under the stabilizer's regular isometries. -/
theorem l2CoordinateProjection_commutes (F : Finset G) (γ : G)
    (hF : ∀ g, g ∈ F ↔ γ*g ∈ F) (u : CoordinateHilbert G) :
    l2CoordinateProjection F (leftRegular γ u) = leftRegular γ (l2CoordinateProjection F u) := by
  ext g
  simp only [l2CoordinateProjection_apply, leftRegular_apply]
  have he : (γ⁻¹*g ∈ F) ↔ g ∈ F := by simpa [mul_assoc] using hF (γ⁻¹*g)
  simp only [he]

/-- The finite projection may simultaneously approximate the compact set,
contain arbitrary finite relative supports, and commute with a finite subgroup. -/
theorem exists_invariant_relative_projection (H : Subgroup G) [Fintype H]
    (K : Set (CoordinateHilbert G)) (hK : IsCompact K) (B : Finset G)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset G, B ⊆ F ∧ (∀ γ : H, ∀ g, g ∈ F ↔ γ.val*g ∈ F) ∧
      (∀ u ∈ K, ‖l2CoordinateProjection F u-u‖ < ε) := by
  obtain ⟨E,hE⟩ := exists_l2CoordinateProjection_uniform_close K hK ε hε
  let F := subgroupCoordinateSaturation H (E∪B)
  have hEF : E ⊆ F := fun g hg => subset_subgroupCoordinateSaturation H (E∪B) (Finset.mem_union_left B hg)
  have hBF : B ⊆ F := fun g hg => subset_subgroupCoordinateSaturation H (E∪B) (Finset.mem_union_right E hg)
  refine ⟨F,hBF,subgroupCoordinateSaturation_invariant H (E∪B),?_⟩
  intro u hu
  exact (l2CoordinateProjection_error_mono E F hEF u).trans_lt (hE u hu)

end Paper28
