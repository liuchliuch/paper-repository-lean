import Paper28.BassSerreFactorBranches
import Paper28.BassSerreSphereShadows
import Paper28.GroupHomSphereFolding
import Paper28.FiniteCoordinateAreaInput

/-! Actual factor-sphere restrictions of all shadows. The central map is
the native factor absolute-value quotient map; every other shadow is
constant. Only ordinary Hilbert coordinate regrouping is a standard input.
No transfer or homology recovery conclusion is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
section Grouping
variable {D G K : Type} [Group D] [Group G] [Group K]
  [DecidableEq D] [DecidableEq G] [DecidableEq K] (Grouping : HilbertGroupingInput)

def sphericalCoordinateUnit (c : K) : RegularSphere K :=
  ⟨lp.single 2 c 1,by rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]; norm_num⟩

include Grouping in
theorem partitionShadow_constant_composition (θ : D →* G) (π : G → K) (c : K)
    (hπ : ∀ a, π (θ a) = c) (u : RegularSphere D) :
    partitionQuotientShadow π (groupHomSphereFold θ u) = regularQuotientMap (sphericalCoordinateUnit c) := by
  have he := Grouping.composition (θ : D → G) π u.val
  have hmap : π ∘ θ = fun _ : D => c := funext hπ
  rw [hmap,Grouping.constant,u.property] at he
  apply congrArg regularQuotientMap
  exact Subtype.ext he

include Grouping in
theorem partitionShadow_central_composition (θ : K →* G) (π : G → K) (c : K)
    (hπ : ∀ a, π (θ a) = c*a) (u : RegularSphere K) :
    partitionQuotientShadow π (groupHomSphereFold θ u) =
      groupHomQuotientFold (MonoidHom.id K) (regularQuotientMap u) := by
  have he := Grouping.composition (θ : K → G) π u.val
  have hmap : π ∘ θ = fun a : K => c*a := funext hπ
  rw [hmap,hilbertPartitionFold_left_mul] at he
  have hs : (⟨hilbertPartitionFold π (groupHomSphereFold θ u).val,
      (hilbertPartitionFold_norm _ _).trans (groupHomSphereFold θ u).property⟩ : RegularSphere K) =
      c • groupHomSphereFold (MonoidHom.id K) u := Subtype.ext he
  change regularQuotientMap _ = regularQuotientMap (groupHomSphereFold (MonoidHom.id K) u)
  rw [hs]
  exact regularQuotientMap_smul _ _
end Grouping

variable {G : Type} [Group G] [DecidableEq G] [Countable G] {A B : Subgroup G}
  (T : BassSerreObject A B) (Grouping : HilbertGroupingInput)

include Grouping in
theorem bassSerreFactorA_shadow_center (u : RegularSphere A) :
    bassSerreQuotientShadowA T (factorBaseCoset A) (groupHomSphereFold A.subtype u) =
      groupHomQuotientFold (MonoidHom.id A) (regularQuotientMap u) :=
  partitionShadow_central_composition Grouping A.subtype _ (factorBaseRepresentative A)⁻¹
    (bassSerreFactorBranchA_center T) u

include Grouping in
theorem bassSerreFactorB_shadow_center (u : RegularSphere B) :
    bassSerreQuotientShadowB T (factorBaseCoset B) (groupHomSphereFold B.subtype u) =
      groupHomQuotientFold (MonoidHom.id B) (regularQuotientMap u) :=
  partitionShadow_central_composition Grouping B.subtype _ (factorBaseRepresentative B)⁻¹
    (bassSerreFactorBranchB_center T) u

include Grouping in
theorem bassSerreFactorA_shadowA_constant (v : G ⧸ A) (hv : v ≠ factorBaseCoset A) :
    ∃ c : RegularOrbitQuotient A, ∀ u : RegularSphere A,
      bassSerreQuotientShadowA T v (groupHomSphereFold A.subtype u) = c := by
  obtain ⟨w,hw⟩ := bassSerreFactorA_branches_constant T (.inl v) (fun h => hv (Sum.inl.inj h))
  let c := (T.leftLabel v).symm w
  refine ⟨regularQuotientMap (sphericalCoordinateUnit c),?_⟩
  intro u
  exact partitionShadow_constant_composition Grouping A.subtype _ c
    (fun a => congrArg (T.leftLabel v).symm (hw a)) u

include Grouping in
theorem bassSerreFactorA_shadowB_constant (v : G ⧸ B) :
    ∃ c : RegularOrbitQuotient B, ∀ u : RegularSphere A,
      bassSerreQuotientShadowB T v (groupHomSphereFold A.subtype u) = c := by
  obtain ⟨w,hw⟩ := bassSerreFactorA_branches_constant T (.inr v) (by intro h; cases h)
  let c := (T.rightLabel v).symm w
  refine ⟨regularQuotientMap (sphericalCoordinateUnit c),?_⟩
  intro u
  exact partitionShadow_constant_composition Grouping A.subtype _ c
    (fun a => congrArg (T.rightLabel v).symm (hw a)) u

include Grouping in
theorem bassSerreFactorB_shadowA_constant (v : G ⧸ A) :
    ∃ c : RegularOrbitQuotient A, ∀ u : RegularSphere B,
      bassSerreQuotientShadowA T v (groupHomSphereFold B.subtype u) = c := by
  obtain ⟨w,hw⟩ := bassSerreFactorB_branches_constant T (.inl v) (by intro h; cases h)
  let c := (T.leftLabel v).symm w
  refine ⟨regularQuotientMap (sphericalCoordinateUnit c),?_⟩
  intro u
  exact partitionShadow_constant_composition Grouping B.subtype _ c
    (fun b => congrArg (T.leftLabel v).symm (hw b)) u

include Grouping in
theorem bassSerreFactorB_shadowB_constant (v : G ⧸ B) (hv : v ≠ factorBaseCoset B) :
    ∃ c : RegularOrbitQuotient B, ∀ u : RegularSphere B,
      bassSerreQuotientShadowB T v (groupHomSphereFold B.subtype u) = c := by
  obtain ⟨w,hw⟩ := bassSerreFactorB_branches_constant T (.inr v) (fun h => hv (Sum.inr.inj h))
  let c := (T.rightLabel v).symm w
  refine ⟨regularQuotientMap (sphericalCoordinateUnit c),?_⟩
  intro u
  exact partitionShadow_constant_composition Grouping B.subtype _ c
    (fun b => congrArg (T.rightLabel v).symm (hw b)) u

end Paper28
