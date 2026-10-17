import Mathlib.RepresentationTheory.FDRep
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.RepresentationTheory.Maschke
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Paper18.Category.Semisimple

/-!
# Actual finite-dimensional representations of finite groups

The group-algebra functor below is the fully faithful ordinary representation
functor, restricted to finite-dimensional objects. Maschke's averaging theorem
therefore supplies actual categorical retractions; it is not an assumption on
fusion multiplicities.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped BigOperators
universe u
namespace Paper18.Category.Representation

variable {G : Type} [Group G]

instance : HasFiniteBiproducts (FDRep ℂ G) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The actual group algebra module carried by a finite-dimensional complex
representation. -/
def toGroupAlgebra : FDRep ℂ G ⥤ ModuleCat (MonoidAlgebra ℂ G) :=
  forget₂ (FDRep ℂ G) (Rep ℂ G) ⋙ Rep.toModuleMonoidAlgebra

instance : (Rep.toModuleMonoidAlgebra (k := ℂ) (G := G)).IsEquivalence :=
  (Rep.equivalenceModuleMonoidAlgebra (k := ℂ) (G := G)).isEquivalence_functor

instance : (toGroupAlgebra (G := G)).Full := by
  dsimp [toGroupAlgebra]
  infer_instance

instance : (toGroupAlgebra (G := G)).Faithful := by
  dsimp [toGroupAlgebra]
  infer_instance

instance : (toGroupAlgebra (G := G)).Additive where
  map_add := by intros; rfl

instance : PreservesFiniteLimits (toGroupAlgebra (G := G)) := by
  exact comp_preservesFiniteLimits _ _

/-- A simple group-algebra module defines a categorically simple
finite-dimensional representation. -/
theorem simple_of_groupAlgebra_simple (V : FDRep ℂ G)
    [Simple ((toGroupAlgebra (G := G)).obj V)] : Simple V where
  mono_isIso_iff_nonzero f := by
    intro m
    let F := toGroupAlgebra (G := G)
    constructor
    · intro h hf
      have : IsIso (F.map f) := by infer_instance
      have hn := (Simple.mono_isIso_iff_nonzero (F.map f)).mp this
      exact hn (by simp [hf])
    · intro hf
      have hn : F.map f ≠ 0 := by
        intro h
        exact hf (F.map_injective (by simpa using h))
      have : IsIso (F.map f) := (Simple.mono_isIso_iff_nonzero (F.map f)).mpr hn
      exact isIso_of_reflects_iso f F

/-- The tensor unit is the one-dimensional trivial representation, hence
categorically simple. -/
instance simple_unit : Simple (𝟙_ (FDRep ℂ G)) := by
  have hs : IsSimpleModule (MonoidAlgebra ℂ G)
      (_root_.Representation.asModule (FDRep.ρ (𝟙_ (FDRep ℂ G)))) := by
    apply (isSimpleModule_iff ..).mpr
    apply is_simple_module_of_finrank_eq_one (K := ℂ)
    rw [(_root_.Representation.asModuleEquiv (FDRep.ρ (𝟙_ (FDRep ℂ G)))).finrank_eq]
    exact Module.finrank_self ℂ
  letI := hs
  haveI : Simple ((toGroupAlgebra (G := G)).obj (𝟙_ (FDRep ℂ G))) := by
    change Simple (ModuleCat.of (MonoidAlgebra ℂ G)
      (_root_.Representation.asModule ((forget₂ (FDRep ℂ G) (Rep ℂ G)).obj
        (𝟙_ (FDRep ℂ G))).ρ))
    rw [FDRep.forget₂_ρ]
    exact simple_of_isSimpleModule
  exact simple_of_groupAlgebra_simple _

variable [Fintype G]

/-- Maschke's theorem as a splitting statement in the actual category
`FDRep ℂ G`: every monomorphism admits a left inverse. -/
theorem mono_splits {V W : FDRep ℂ G} (f : V ⟶ W) [Mono f] :
    ∃ r : W ⟶ V, f ≫ r = 𝟙 V := by
  let F := toGroupAlgebra (G := G)
  have hinj : Function.Injective (F.map f).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hker : LinearMap.ker (F.map f).hom = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  obtain ⟨r, hr⟩ := MonoidAlgebra.exists_leftInverse_of_injective (F.map f).hom hker
  refine ⟨F.preimage (ModuleCat.ofHom r), F.map_injective ?_⟩
  simpa [Functor.map_comp, ModuleCat.hom_ext_iff] using congrArg ModuleCat.ofHom hr

/-- In particular, each subrepresentation is an actual retract. -/
theorem exists_retract_of_mono {V W : FDRep ℂ G} (f : V ⟶ W) [Mono f] :
    Nonempty (Retract V W) := by
  obtain ⟨r, hr⟩ := mono_splits f
  exact ⟨⟨f, r, hr⟩⟩

end Paper18.Category.Representation
