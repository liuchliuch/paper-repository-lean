import Paper18.Category.ModuleFunctorSemisimpleBiproductsBasic

/-! # Actual finite biproducts of strong module functors -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators MonoidalLeftAction
universe v u v' u' v'' u''
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type u'} [Category.{v'} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  {N : Type u''} [Category.{v''} N] [Preadditive N] [Linear ℂ N]
  [HasFiniteBiproducts N] [MonoidalLeftAction C N]
  [∀ c : C, (actionLeft N c).Additive]
  [∀ c : C, (actionLeft N c).Linear ℂ]
  {I : Type} [Fintype I] (A : I → Bundled C M N)

/-- The actual sum comparison satisfies all module coherence by its
jointly monic actual sum projections. -/
def moduleSumLaxLeftLinear : (moduleSumUnderlying A).LaxLeftLinear C where
  μₗ c m := (moduleSumLineatorIso A c).hom.app m
  μₗ_naturality_left {c c'} f m := by
    apply moduleSum_hom_ext A (c' ⊙ₗ m)
    intro i
    simp only [assoc]
    change (f ⊵ₗ (moduleSumUnderlying A).obj m) ≫ (moduleSumLineatorIso A c').hom.app m ≫
      (biproduct.π (fun i => (A i).toFunctor) i).app (c' ⊙ₗ m) =
        (moduleSumLineatorIso A c).hom.app m ≫ (moduleSumUnderlying A).map (f ⊵ₗ m) ≫
          (biproduct.π (fun i => (A i).toFunctor) i).app (c' ⊙ₗ m)
    erw [(biproduct.π (fun i => (A i).toFunctor) i).naturality]
    simp only [actionLeft_obj, moduleSumLineatorIso_π, moduleSumLineatorIso_π_assoc]
    rw [← action_exchange_assoc, Functor.LaxLeftLinear.μₗ_naturality_left]
  μₗ_naturality_right c {m n} f := (moduleSumLineatorIso A c).hom.naturality f
  μₗ_associativity c d m := by
    apply moduleSum_hom_ext A (c ⊙ₗ d ⊙ₗ m)
    intro i
    simp only [assoc]
    change (moduleSumLineatorIso A (c ⊗ d)).hom.app m ≫
      (moduleSumUnderlying A).map (αₗ c d m).hom ≫
        (biproduct.π (fun i => (A i).toFunctor) i).app (c ⊙ₗ d ⊙ₗ m) =
      (αₗ c d ((moduleSumUnderlying A).obj m)).hom ≫
        c ⊴ₗ (moduleSumLineatorIso A d).hom.app m ≫
          (moduleSumLineatorIso A c).hom.app (d ⊙ₗ m) ≫
            (biproduct.π (fun i => (A i).toFunctor) i).app (c ⊙ₗ d ⊙ₗ m)
    erw [(biproduct.π (fun i => (A i).toFunctor) i).naturality]
    simp only [actionLeft_obj, moduleSumLineatorIso_π, moduleSumLineatorIso_π_assoc]
    rw [← actionHomRight_comp_assoc, moduleSumLineatorIso_π, actionHomRight_comp]
    simp only [assoc]
    rw [Functor.LaxLeftLinear.μₗ_associativity]
    simp only [tensor_actionHomRight, assoc, Iso.inv_hom_id_assoc]
    rfl
  μₗ_unitality m := by
    apply moduleSum_hom_ext A m
    intro i
    simp only [assoc]
    change (λₗ[C] ((moduleSumUnderlying A).obj m)).hom ≫
      (biproduct.π (fun i => (A i).toFunctor) i).app m =
      (moduleSumLineatorIso A (𝟙_ C)).hom.app m ≫
        (moduleSumUnderlying A).map (λₗ[C] m).hom ≫
          (biproduct.π (fun i => (A i).toFunctor) i).app m
    erw [(biproduct.π (fun i => (A i).toFunctor) i).naturality]
    simp only [actionLeft_obj]
    rw [moduleSumLineatorIso_π_assoc, ← Functor.LaxLeftLinear.μₗ_unitality]
    exact actionUnitIso_hom_naturality _

def moduleSumLeftLinear : (moduleSumUnderlying A).LeftLinear C := by
  letI := moduleSumLaxLeftLinear A
  letI (c : C) (m : M) : IsIso (Functor.LaxLeftLinear.μₗ (moduleSumUnderlying A) c m) := by
    change IsIso ((moduleSumLineatorIso A c).hom.app m)
    infer_instance
  exact leftLinearOfLax (moduleSumUnderlying A)

/-- The genuine sum object, with its derived actual strong lineator. -/
def moduleSum : Bundled C M N where
  toFunctor := moduleSumUnderlying A
  leftLinear := moduleSumLeftLinear A
  additive := inferInstance
  linear := inferInstance

/-- The actual pointwise sum bicone has module natural legs. -/
def moduleBicone : Bicone A where
  pt := moduleSum A
  ι i := ⟨biproduct.ι (fun i => (A i).toFunctor) i,
    ⟨fun c m => (moduleSumLineatorIso_ι A c m i).symm⟩⟩
  π i := ⟨biproduct.π (fun i => (A i).toFunctor) i,
    ⟨fun c m => moduleSumLineatorIso_π A c m i⟩⟩
  ι_π i j := by
    split_ifs with h
    · subst j
      apply Subtype.ext
      change biproduct.ι (fun i => (A i).toFunctor) i ≫
        biproduct.π (fun i => (A i).toFunctor) i = 𝟙 _
      simp
    · apply Subtype.ext
      change biproduct.ι (fun i => (A i).toFunctor) i ≫
        biproduct.π (fun i => (A i).toFunctor) j = 0
      simp [h]

/-- The actual total identity proves the actual biproduct universal
properties inside the module-functor category. -/
def moduleBiconeIsBilimit : (moduleBicone A).IsBilimit :=
  isBilimitOfTotal _ (by
    apply (forget (C := C) (M := M) (N := N)).map_injective
    rw [Functor.map_sum]
    change (∑ i, biproduct.π (fun i => (A i).toFunctor) i ≫
      biproduct.ι (fun i => (A i).toFunctor) i) = 𝟙 _
    exact biproduct.total)

instance moduleFunctor_hasBiproduct : HasBiproduct A :=
  HasBiproduct.mk ⟨moduleBicone A, moduleBiconeIsBilimit A⟩

instance moduleFunctor_hasFiniteBiproducts : HasFiniteBiproducts (Bundled C M N) where
  out _ := ⟨fun _ => moduleFunctor_hasBiproduct _⟩

end Paper18.Category.ModuleFunctor
