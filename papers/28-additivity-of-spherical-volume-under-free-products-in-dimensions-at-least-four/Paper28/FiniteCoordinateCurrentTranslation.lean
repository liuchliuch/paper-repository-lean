import Paper28.FiniteCoordinateCurrentGroup

/-! Canonical regular-action pushforward preserves the native finite
coordinate current subgroup. This is the actual lift-change operation. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {G : Type} [Group G] [DecidableEq G]
  (J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance)
  (F : CanonicalGlobalCurrentCalculusInput)

def regularSphereActionLipschitz (γ : G) :
    ∃ L : NNReal, LipschitzWith L (fun u : RegularSphere G => γ • u) :=
  ⟨1,(isometry_smul (RegularSphere G) γ).lipschitz⟩

def regularSphereCurrentAction (γ : G) :
    GlobalCurrentPushforwardInput inferInstance inferInstance J J (fun u : RegularSphere G => γ • u) :=
  F.map J J _ (regularSphereActionLipschitz γ)

theorem regularSphereCurrentAction_support (γ : G) (k : ℕ) (C : J.Current k)
    (E : Finset G) (hE : J.support C ⊆ regularCoordinateSphere E) :
    J.support ((regularSphereCurrentAction J F γ).push k C) ⊆
      regularCoordinateSphere (E.image (fun g => γ*g)) := by
  intro x hx
  obtain ⟨u,hu,rfl⟩ := (regularSphereCurrentAction J F γ).support_subset k C hx
  intro g hg
  change leftRegular γ u.val g = 0
  rw [leftRegular_apply]
  apply hE hu (γ⁻¹*g)
  intro h
  exact hg (Finset.mem_image.mpr ⟨γ⁻¹*g,h,by simp⟩)

def finiteCoordinateCurrentAction (γ : G) (k : ℕ) :
    finiteCoordinateSupportedCurrents J k →+ finiteCoordinateSupportedCurrents J k where
  toFun C := ⟨(regularSphereCurrentAction J F γ).push k C.val,by
    obtain ⟨E,hE⟩ := C.property
    exact ⟨E.image (fun g => γ*g),regularSphereCurrentAction_support J F γ k C.val E hE⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' C D := Subtype.ext (map_add _ _ _)

end Paper28
