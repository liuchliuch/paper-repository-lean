import Paper18.Category.SphericalizationEquivalence
import Paper18.Category.SphericalizationLinear
import Paper18.Category.EquivariantSemisimple
import Paper18.Category.EquivariantLimits
import Paper18.Category.Integrality

/-!
# Actual fusion-category finiteness of braided sphericalization

The constructed square category is equivalent to the canonical order-two
categorical equivariantization. The finite simple family and actual biproduct
decompositions are transported from the proved equivariant semisimplicity
construction. No finiteness or fusion decomposition laws are assumed for the
new category.
-/
noncomputable section
universe v u w
namespace Paper18.Category
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
namespace Sphericalized

instance toEquivariant_isEquivalence : (toEquivariant (C := C)).IsEquivalence :=
  inferInstanceAs (equivariantEquivalence (C := C)).functor.IsEquivalence

instance inverse_isEquivalence :
    (WeakAction.Equivariant.toSphericalized (C := C)).IsEquivalence :=
  inferInstanceAs (equivariantEquivalence (C := C)).inverse.IsEquivalence

instance toEquivariant_additive : (toEquivariant (C := C)).Additive where
  map_add := by intros; rfl
instance toEquivariant_linear : (toEquivariant (C := C)).Linear ℂ where
  map_smul _ _ := rfl
instance inverse_additive : (WeakAction.Equivariant.toSphericalized (C := C)).Additive where
  map_add := by intros; rfl
instance inverse_linear : (WeakAction.Equivariant.toSphericalized (C := C)).Linear ℂ where
  map_smul _ _ := rfl

/-- Categorical simplicity is reflected by the actual equivalence. -/
lemma simple_of_equivariant (X : Sphericalized C) [Simple (toEquivariant.obj X)] : Simple X where
  mono_isIso_iff_nonzero f _ := by
    let F := toEquivariant (C := C)
    haveI : Mono (F.map f) := by infer_instance
    constructor
    · intro hf hz
      letI := hf
      have hn := (Simple.mono_isIso_iff_nonzero (F.map f)).mp (by infer_instance)
      exact hn (by simp [F, hz])
    · intro hf
      have hn : F.map f ≠ 0 := by
        intro h
        apply hf
        apply F.map_injective
        simpa only [Functor.map_zero] using h
      letI : IsIso (F.map f) := isIso_of_mono_of_nonzero hn
      exact isIso_of_fully_faithful F f

section Finite
variable [HasKernels C] [HasFiniteBiproducts C]

/-- Finite limits in the actual square category follow from the actual
order-two equivariantization equivalence. -/
instance hasFiniteLimits : HasFiniteLimits (Sphericalized C) where
  out J _ _ := Adjunction.hasLimitsOfShape_of_equivalence toEquivariant

/-- Actual biproducts, rather than numerical direct-sum certificates. -/
instance hasFiniteBiproducts : HasFiniteBiproducts (Sphericalized C) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

instance finiteDimensional_hom (X Y : Sphericalized C) :
    FiniteDimensional ℂ (X ⟶ Y) :=
  inferInstanceAs (FiniteDimensional ℂ (X.obj ⟶ Y.obj))

/-- The finite index set produced by actual simple decompositions of the
canonical order-two induction objects. -/
abbrev SimpleIndex := (sphericalizationAction C).SimpleIndex S

/-- Actual simple representatives of sphericalization. -/
def simpleObject (i : SimpleIndex S) : Sphericalized C :=
  WeakAction.Equivariant.toSphericalized.obj
    (((sphericalizationAction C).equivariantSkeleton S).simpleObject i)

instance simpleObject_simple (i : SimpleIndex S) : Simple (simpleObject S i) := by
  let E := equivariantEquivalence (C := C)
  let Y := ((sphericalizationAction C).equivariantSkeleton S).simpleObject i
  letI : Simple Y := ((sphericalizationAction C).equivariantSkeleton S).simple i
  letI : Simple (toEquivariant.obj (simpleObject S i)) :=
    Simple.of_iso (show toEquivariant.obj (simpleObject S i) ≅ Y from E.counitIso.app Y)
  exact simple_of_equivariant _

/-- The actual finite semisimple skeleton of the constructed braided
sphericalization. -/
def skeleton : FiniteSemisimpleSkeleton (Sphericalized C) (SimpleIndex S) where
  simpleObject := simpleObject S
  simple := simpleObject_simple S
  iso_injective i j h := by
    let T := (sphericalizationAction C).equivariantSkeleton S
    let E := equivariantEquivalence (C := C)
    apply T.iso_injective i j
    exact h.map (fun e => (E.counitIso.app (T.simpleObject i)).symm ≪≫
      toEquivariant.mapIso e ≪≫ E.counitIso.app (T.simpleObject j))
  length X := ((sphericalizationAction C).equivariantSkeleton S).length (toEquivariant.obj X)
  label X := ((sphericalizationAction C).equivariantSkeleton S).label (toEquivariant.obj X)
  decomposition X := (equivariantEquivalence (C := C)).unitIso.app X ≪≫
    WeakAction.Equivariant.toSphericalized.mapIso
      (((sphericalizationAction C).equivariantSkeleton S).decomposition (toEquivariant.obj X)) ≪≫
    WeakAction.Equivariant.toSphericalized.mapBiproduct _

/-- The constructed forgetful tensor functor is actually retract-dominant:
every original object is a summand of the image of an actual square object. -/
theorem forget_retract_dominant (X : C) :
    ∃ Y : Sphericalized C, Nonempty (Retract X (forget.obj Y)) := by
  obtain ⟨Y, hY⟩ := (sphericalizationAction C).forget_retract_dominant X
  exact ⟨WeakAction.Equivariant.toSphericalized.obj Y, hY⟩

variable [Simple (𝟙_ C)]

/-- The actual sphericalization tensor unit is simple. -/
instance simpleUnit : Simple (𝟙_ (Sphericalized C)) := by
  letI : Simple (toEquivariant.obj (𝟙_ (Sphericalized C))).obj := by
    change Simple (𝟙_ C)
    infer_instance
  letI : Simple (toEquivariant.obj (𝟙_ (Sphericalized C))) :=
    (sphericalizationAction C).simple_of_underlying_simple _
  exact simple_of_equivariant _

/-- Integrality is inherited and reflected by the constructed dominant
braided tensor functor, using actual categorical FP dimensions. -/
theorem integral_iff : (skeleton S).Integral ↔ S.Integral :=
  (skeleton S).integral_iff_of_dominant S forget forget_retract_dominant

end Finite
end Sphericalized
end Paper18.Category
