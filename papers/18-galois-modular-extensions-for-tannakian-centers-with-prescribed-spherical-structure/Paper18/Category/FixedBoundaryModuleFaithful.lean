import Paper18.Category.FixedBoundaryModuleRegular

/-!
# Fully faithful pullback of actual module transformations

An endomorphism of a fully faithful strong module functor pulls back to an
endomorphism of the actual identity module functor. The proof of module
naturality uses the original lineator and its naturality; no classification
of module functors is used.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u v' u' v'' u''
namespace Paper18.Category.ModuleFunctor
variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  {M : Type u'} [Category.{v'} M] [MonoidalLeftAction C M]
  {N : Type u''} [Category.{v''} N] [MonoidalLeftAction C N]
  (F : M ⥤ N) [F.Full] [F.Faithful] [F.LeftLinear C]

/-- Actual fully faithful pullback, component by component. -/
def fullyFaithfulModuleEnd (τ : F ⟶ F) : 𝟭 M ⟶ 𝟭 M where
  app X := F.preimage (τ.app X)
  naturality {X Y} f := by
    apply F.map_injective
    simpa only [F.map_comp, F.map_preimage] using τ.naturality f

@[simp] theorem fullyFaithfulModuleEnd_map (τ : F ⟶ F) (X : M) :
    F.map ((fullyFaithfulModuleEnd F τ).app X) = τ.app X :=
  F.map_preimage _

instance fullyFaithfulModuleEnd_moduleNatural (τ : F ⟶ F)
    [IsModuleNatural C τ] : IsModuleNatural C (fullyFaithfulModuleEnd F τ) where
  lineator X Y := by
    change 𝟙 _ ≫ F.preimage (τ.app (X ⊙ₗ Y)) =
      (X ⊴ₗ F.preimage (τ.app Y)) ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    apply F.map_injective
    apply (cancel_epi (Functor.LaxLeftLinear.μₗ F X Y)).mp
    rw [F.map_preimage, ← Functor.LaxLeftLinear.μₗ_naturality_right]
    rw [F.map_preimage]
    exact IsModuleNatural.lineator (C := C) (τ := τ) X Y

/-- An actual natural automorphism pulls back to an actual automorphism,
with the module compatibility just proved. -/
def fullyFaithfulModuleAut (τ : F ≅ F) : 𝟭 M ≅ 𝟭 M :=
  NatIso.ofComponents (fun X => F.preimageIso (τ.app X))
    (fun {X Y} f => (fullyFaithfulModuleEnd F τ.hom).naturality f)

instance fullyFaithfulModuleAut_moduleNatural (τ : F ≅ F)
    [IsModuleNatural C τ.hom] :
    IsModuleNatural C (fullyFaithfulModuleAut F τ).hom :=
  inferInstanceAs (IsModuleNatural C (fullyFaithfulModuleEnd F τ.hom))

@[simp] theorem fullyFaithfulModuleAut_map (τ : F ≅ F) (X : M) :
    F.map ((fullyFaithfulModuleAut F τ).hom.app X) = τ.hom.app X :=
  F.map_preimage _

end Paper18.Category.ModuleFunctor
