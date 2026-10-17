import Paper18.Category.ModuleFunctorFiniteBasic
import Paper18.Category.EquivariantInduction
import Paper18.Category.ModuleFunctorAdjointStrong
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-! # Actual finite sums and comparison maps for native module functors -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators MonoidalLeftAction
universe v u v' u' v'' u''
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] Paper18.Category.additive_preservesBiproductsOfFiniteShape
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type u'} [Category.{v'} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  {N : Type u''} [Category.{v''} N] [Preadditive N] [Linear ℂ N]
  [HasFiniteBiproducts N] [MonoidalLeftAction C N]
  [∀ c : C, (actionLeft N c).Additive]
  [∀ c : C, (actionLeft N c).Linear ℂ]
  {I : Type} [Fintype I] (A : I → Bundled C M N)

/-- The actual finite sum in the underlying ordinary functor category. -/
def moduleSumUnderlying : M ⥤ N := ⨁ fun i => (A i).toFunctor

omit [∀ c : C, (actionLeft N c).Additive] [∀ c : C, (actionLeft N c).Linear ℂ] in
/-- Actual pointwise sum projections jointly detect maps, by evaluating
the actual biproduct total identity. -/
lemma moduleSum_hom_ext (m : M) {X : N} (f g : X ⟶ (moduleSumUnderlying A).obj m)
    (h : ∀ i, f ≫ (biproduct.π (fun i => (A i).toFunctor) i).app m =
      g ≫ (biproduct.π (fun i => (A i).toFunctor) i).app m) : f = g := by
  have ht : (∑ i, (biproduct.π (fun i => (A i).toFunctor) i).app m ≫
      (biproduct.ι (fun i => (A i).toFunctor) i).app m) =
        𝟙 ((moduleSumUnderlying A).obj m) := by
    simpa only [NatTrans.app_sum, NatTrans.comp_app, NatTrans.id_app] using
      congrArg (fun a : moduleSumUnderlying A ⟶ moduleSumUnderlying A => a.app m)
        (biproduct.total (f := fun i : I => (A i).toFunctor))
  calc
    f = ∑ i, (f ≫ (biproduct.π (fun i => (A i).toFunctor) i).app m) ≫
        (biproduct.ι (fun i => (A i).toFunctor) i).app m := by
      simp only [assoc]
      rw [← Preadditive.comp_sum, ht, comp_id]
    _ = ∑ i, (g ≫ (biproduct.π (fun i => (A i).toFunctor) i).app m) ≫
        (biproduct.ι (fun i => (A i).toFunctor) i).app m := by simp_rw [h]
    _ = g := by
      simp only [assoc]
      rw [← Preadditive.comp_sum, ht, comp_id]

instance moduleSumUnderlying_additive : (moduleSumUnderlying A).Additive where
  map_add {m n} f g := by
    apply moduleSum_hom_ext A n
    intro i
    change (moduleSumUnderlying A).map (f + g) ≫ (biproduct.π (fun i => (A i).toFunctor) i).app n =
      ((moduleSumUnderlying A).map f + (moduleSumUnderlying A).map g) ≫ (biproduct.π (fun i => (A i).toFunctor) i).app n
    simp only [moduleSumUnderlying, (biproduct.π (fun i => (A i).toFunctor) i).naturality,
      Preadditive.add_comp]
    erw [(A i).toFunctor.map_add]
    exact Preadditive.comp_add _ _ _ _ _ _

instance moduleSumUnderlying_linear : (moduleSumUnderlying A).Linear ℂ where
  map_smul {m n} f z := by
    apply moduleSum_hom_ext A n
    intro i
    change (moduleSumUnderlying A).map (z • f) ≫ (biproduct.π (fun i => (A i).toFunctor) i).app n =
      (z • (moduleSumUnderlying A).map f) ≫ (biproduct.π (fun i => (A i).toFunctor) i).app n
    simp only [moduleSumUnderlying, (biproduct.π (fun i => (A i).toFunctor) i).naturality,
      Linear.smul_comp]
    erw [(A i).toFunctor.map_smul]
    exact Linear.comp_smul _ _ _ _ _ _

local instance sumPostcompose_additive (c : C) :
    ((Functor.whiskeringRight M N N).obj (actionLeft N c)).Additive where
  map_add := by intros; ext m; exact (actionLeft N c).map_add

local instance sumPrecompose_additive (c : C) :
    ((Functor.whiskeringLeft M M N).obj (actionLeft M c)).Additive where
  map_add := by intros; rfl

/-- The actual strong comparison on a finite sum. -/
def moduleSumLineatorIso (c : C) :
    moduleSumUnderlying A ⋙ actionLeft N c ≅ actionLeft M c ⋙ moduleSumUnderlying A :=
  let R := (Functor.whiskeringRight M N N).obj (actionLeft N c)
  let L := (Functor.whiskeringLeft M M N).obj (actionLeft M c)
  R.mapBiproduct (fun i => (A i).toFunctor) ≪≫
    biproduct.mapIso (fun i => adjointActionLineatorIso (A i).toFunctor c) ≪≫
      (L.mapBiproduct (fun i => (A i).toFunctor)).symm

omit [∀ c : C, (actionLeft N c).Linear ℂ] in
@[reassoc]
lemma moduleSumLineatorIso_π (c : C) (m : M) (i : I) :
    (moduleSumLineatorIso A c).hom.app m ≫
      (biproduct.π (fun i => (A i).toFunctor) i).app (c ⊙ₗ m) =
    (c ⊴ₗ (biproduct.π (fun i => (A i).toFunctor) i).app m) ≫
      Functor.LaxLeftLinear.μₗ (A i).toFunctor c m := by
  let R := (Functor.whiskeringRight M N N).obj (actionLeft N c)
  let L := (Functor.whiskeringLeft M M N).obj (actionLeft M c)
  have hL : (L.mapBiproduct (fun i => (A i).toFunctor)).inv ≫
      L.map (biproduct.π (fun i => (A i).toFunctor) i) =
    biproduct.π (fun i => L.obj (A i).toFunctor) i := by
    apply (cancel_epi (L.mapBiproduct (fun i => (A i).toFunctor)).hom).mp
    simp only [← assoc, Iso.hom_inv_id, id_comp]
    rw [Functor.mapBiproduct_hom]
    exact (biproduct.lift_π (fun j : I => L.map (biproduct.π (fun i => (A i).toFunctor) j)) i).symm
  have h : (moduleSumLineatorIso A c).hom ≫
      L.map (biproduct.π (fun i => (A i).toFunctor) i) =
    R.map (biproduct.π (fun i => (A i).toFunctor) i) ≫
      (adjointActionLineatorIso (A i).toFunctor c).hom := by
    change (_ ≫ _ ≫ (L.mapBiproduct (fun i => (A i).toFunctor)).inv) ≫ _ = _
    simp only [assoc, hL, biproduct.mapIso_hom]
    erw [biproduct.map_π]
    rw [← assoc, Functor.mapBiproduct_hom]
    erw [biproduct.lift_π]
  exact congrArg (fun a => a.app m) h

omit [∀ c : C, (actionLeft N c).Linear ℂ] in
@[reassoc]
lemma moduleSumLineatorIso_ι (c : C) (m : M) (i : I) :
    (c ⊴ₗ (biproduct.ι (fun i => (A i).toFunctor) i).app m) ≫
      (moduleSumLineatorIso A c).hom.app m =
    Functor.LaxLeftLinear.μₗ (A i).toFunctor c m ≫
      (biproduct.ι (fun i => (A i).toFunctor) i).app (c ⊙ₗ m) := by
  let R := (Functor.whiskeringRight M N N).obj (actionLeft N c)
  let L := (Functor.whiskeringLeft M M N).obj (actionLeft M c)
  have hR : R.map (biproduct.ι (fun i => (A i).toFunctor) i) ≫
      (R.mapBiproduct (fun i => (A i).toFunctor)).hom =
    biproduct.ι (fun i => R.obj (A i).toFunctor) i :=
      map_biproduct_ι R (fun i => (A i).toFunctor) i
  have h : R.map (biproduct.ι (fun i => (A i).toFunctor) i) ≫
      (moduleSumLineatorIso A c).hom =
    (adjointActionLineatorIso (A i).toFunctor c).hom ≫
      L.map (biproduct.ι (fun i => (A i).toFunctor) i) := by
    change _ ≫ (_ ≫ _ ≫ (L.mapBiproduct (fun i => (A i).toFunctor)).inv) = _
    rw [← assoc, ← assoc, hR]
    dsimp only [biproduct.mapIso_hom]
    erw [biproduct.ι_map]
    simp only [assoc]
    rw [Functor.mapBiproduct_inv]
    erw [biproduct.ι_desc]
  exact congrArg (fun a => a.app m) h

end Paper18.Category.ModuleFunctor
