import Paper18.Category.ModuleFunctorSemisimpleSeparableLinear

/-! # Actual finite biproducts for modules in a native action category -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj MonoidalLeftAction BigOperators
universe v u v' u' t
namespace Paper18.Category.ModuleFunctor.SeparableAction
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type u'} [Category.{v'} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  [∀ c : C, (actionLeft M c).Additive]
  [∀ c : C, (actionLeft M c).Linear ℂ]
  [HasFiniteBiproducts M] {A : C} [MonObj A]
  {J : Type t} [Fintype J] (P : J → Mod_ M A)

/-- The product universal property supplies the action on the underlying
finite biproduct. -/
def biproductAction : A ⊙ₗ (⨁ fun j => (P j).X) ⟶ ⨁ fun j => (P j).X :=
  biproduct.lift (fun j => (A ⊴ₗ biproduct.π (fun j => (P j).X) j) ≫ γ[A,(P j).X])

omit [Linear ℂ M] [∀ c : C, (actionLeft M c).Additive] [∀ c : C, (actionLeft M c).Linear ℂ] in
@[reassoc (attr := simp)]
theorem biproductAction_π (j : J) :
    biproductAction P ≫ biproduct.π (fun j => (P j).X) j =
      (A ⊴ₗ biproduct.π (fun j => (P j).X) j) ≫ γ[A,(P j).X] :=
  biproduct.lift_π _ _

/-- The actual finite biproduct module. -/
def biproductObj : Mod_ M A :=
  letI : ModObj A (⨁ fun j => (P j).X) :=
    { smul := biproductAction P
      one_smul' := by
        apply biproduct.hom_ext
        intro j
        rw [Category.assoc, biproductAction_π, ← action_exchange_assoc, ModObj.one_smul]
        exact (actionUnitIso_hom_naturality _).symm
      mul_smul' := by
        apply biproduct.hom_ext
        intro j
        simp only [Category.assoc, biproductAction_π]
        rw [← action_exchange_assoc, ModObj.mul_smul, action_assoc_naturality_assoc,
          ← actionHomRight_comp_assoc, ← biproductAction_π, actionHomRight_comp]
        simp only [Category.assoc, biproductAction_π] }
  ⟨⨁ fun j => (P j).X⟩

/-- The ordinary biproduct inclusions are actual module morphisms. -/
def biproductι (j : J) : P j ⟶ biproductObj P :=
  Mod_.Hom.mk' (biproduct.ι (fun j => (P j).X) j) (by
    change γ[A,(P j).X] ≫ biproduct.ι (fun j => (P j).X) j =
      (A ⊴ₗ biproduct.ι (fun j => (P j).X) j) ≫ biproductAction P
    apply biproduct.hom_ext
    intro k
    simp only [Category.assoc]
    rw [biproductAction_π, ← actionHomRight_comp_assoc]
    by_cases h : j = k
    · subst k
      simp
    · simp [h])

/-- The ordinary biproduct projections are actual module morphisms. -/
def biproductπ (j : J) : biproductObj P ⟶ P j :=
  Mod_.Hom.mk' (biproduct.π (fun j => (P j).X) j) (biproductAction_π P j)

/-- The actual finite module bicone. -/
def bicone : Bicone P where
  pt := biproductObj P
  ι := biproductι P
  π := biproductπ P
  ι_π j k := by
    apply Mod_.Hom.ext
    split_ifs with h
    · subst k
      simp [biproductι, biproductπ]
    · simp [biproductι, biproductπ, h]

/-- The underlying total identity proves the actual module bicone is a
biproduct. -/
def biconeIsBilimit : (bicone P).IsBilimit :=
  isBilimitOfTotal _ (by
    apply (Mod_.forget (D := M) A).map_injective
    rw [Functor.map_sum]
    change (∑ j, biproduct.π (fun j => (P j).X) j ≫
      biproduct.ι (fun j => (P j).X) j) = 𝟙 _
    exact IsBilimit.total (biproduct.isBilimit (fun j => (P j).X)))

instance hasBiproduct : HasBiproduct P := HasBiproduct.mk ⟨bicone P, biconeIsBilimit P⟩

instance hasFiniteBiproducts : HasFiniteBiproducts (Mod_ M A) where
  out _ := ⟨fun _ => hasBiproduct _⟩

end Paper18.Category.ModuleFunctor.SeparableAction
