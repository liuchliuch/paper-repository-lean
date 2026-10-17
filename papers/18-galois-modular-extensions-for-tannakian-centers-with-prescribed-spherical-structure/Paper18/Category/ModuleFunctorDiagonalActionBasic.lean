import Paper18.Category.ModuleAlphaInduction
import Paper18.Category.ModuleFunctorSemisimpleBiproducts
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Ordinary transformations between actual strong module functors -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.ModuleFunctor.DiagonalAction
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  (N : Type uN) [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [MonoidalLeftAction C N]

/-- The objects retain their genuine lineators; morphisms are all
ordinary natural transformations. This permits actual averaging. -/
def Ordinary := InducedCategory (M ⥤ N) (fun F : Bundled C M N => F.toFunctor)

instance ordinaryCategory : Category (Ordinary C M N) := inferInstanceAs
  (Category (InducedCategory (M ⥤ N) (fun F : Bundled C M N => F.toFunctor)))
instance ordinaryPreadditive : Preadditive (Ordinary C M N) := inferInstanceAs
  (Preadditive (InducedCategory (M ⥤ N) (fun F : Bundled C M N => F.toFunctor)))
instance ordinaryLinear : Linear ℂ (Ordinary C M N) := inferInstanceAs
  (Linear ℂ (InducedCategory (M ⥤ N) (fun F : Bundled C M N => F.toFunctor)))

variable {C M N}

def underlying (F : Ordinary C M N) : Bundled C M N := F
abbrev toFunctor (F : Ordinary C M N) : M ⥤ N := (underlying F).toFunctor
def ofBundled (F : Bundled C M N) : Ordinary C M N := F
instance (F : Ordinary C M N) : (toFunctor F).Additive := (underlying F).additive
instance (F : Ordinary C M N) : (toFunctor F).Linear ℂ := (underlying F).linear
instance (F : Ordinary C M N) : (toFunctor F).LeftLinear C := (underlying F).leftLinear

def forget : Ordinary C M N ⥤ (M ⥤ N) := inducedFunctor _
instance forgetFull : (forget (C := C) (M := M) (N := N)).Full := by
  exact (fullyFaithfulInducedFunctor (fun F : Bundled C M N => F.toFunctor)).full
instance forgetFaithful : (forget (C := C) (M := M) (N := N)).Faithful := by
  exact (fullyFaithfulInducedFunctor (fun F : Bundled C M N => F.toFunctor)).faithful

@[ext] lemma ordinary_hom_ext {F G : Ordinary C M N} (f g : F ⟶ G)
    (h : ∀ m, (forget.map f).app m = (forget.map g).app m) : f = g := by
  apply forget.map_injective
  exact NatTrans.ext (funext h)

variable [HasFiniteBiproducts N]
  [∀ X : C, (MonoidalLeftAction.actionLeft N X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft N X).Linear ℂ]

/-- Actual pointwise biproducts retain derived strong module structures,
while their universal property applies to all ordinary transformations. -/
def ordinaryBicone {I : Type} [Fintype I] (F : I → Ordinary C M N) : Bicone F where
  pt := ofBundled (moduleSum (fun i => underlying (F i)))
  π i := biproduct.π (fun j => toFunctor (F j)) i
  ι i := biproduct.ι (fun j => toFunctor (F j)) i
  ι_π i j := by
    by_cases h : i = j
    · subst j
      simp only [dif_pos rfl, eqToHom_refl]
      change biproduct.ι (fun j => toFunctor (F j)) i ≫
        biproduct.π (fun j => toFunctor (F j)) i = 𝟙 (toFunctor (F i))
      exact biproduct.ι_π_self _ _
    · simpa only [dif_neg h] using
        (biproduct.ι_π_ne (fun k => toFunctor (F k)) h)

instance ordinaryHasFiniteBiproducts : HasFiniteBiproducts (Ordinary C M N) where
  out n := ⟨fun F => hasBiproduct_of_total (ordinaryBicone F) (by
    exact biproduct.total (f := fun i => toFunctor (F i)))⟩

end Paper18.Category.ModuleFunctor.DiagonalAction
