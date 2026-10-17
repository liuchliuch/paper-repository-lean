import Paper18.Category.SeparableModulesLinear

/-! # Actual finite biproducts of internal modules -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj BigOperators
universe v u t
namespace Paper18.Category.InternalModule
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C] {A : C} [MonObj A]
  {J : Type t} [Fintype J] (P : J → Mod_ C A)

/-- The product universal property supplies the action on the underlying
finite biproduct. -/
def biproductAction : A ⊗ (⨁ fun j => (P j).X) ⟶ ⨁ fun j => (P j).X :=
  biproduct.lift (fun j => (A ◁ biproduct.π (fun j => (P j).X) j) ≫ γ[A,(P j).X])

omit [Linear ℂ C] [MonoidalLinear ℂ C] [MonoidalPreadditive C] in
@[reassoc (attr := simp)]
theorem biproductAction_π (j : J) :
    biproductAction P ≫ biproduct.π (fun j => (P j).X) j =
      (A ◁ biproduct.π (fun j => (P j).X) j) ≫ γ[A,(P j).X] :=
  biproduct.lift_π _ _

/-- The actual finite biproduct module. -/
def biproductObj : Mod_ C A :=
  letI : ModObj A (⨁ fun j => (P j).X) :=
    { smul := biproductAction P
      one_smul' := by
        change η[A] ▷ (⨁ fun j => (P j).X) ≫ biproductAction P =
          (λ_ (⨁ fun j => (P j).X)).hom
        apply biproduct.hom_ext
        intro j
        rw [Category.assoc, biproductAction_π, ← whisker_exchange_assoc, one_smul]
        exact leftUnitor_naturality _
      mul_smul' := by
        change μ[A] ▷ (⨁ fun j => (P j).X) ≫ biproductAction P =
          (α_ A A (⨁ fun j => (P j).X)).hom ≫ (A ◁ biproductAction P) ≫ biproductAction P
        apply biproduct.hom_ext
        intro j
        simp only [Category.assoc, biproductAction_π]
        rw [← whisker_exchange_assoc, mul_smul, associator_naturality_right_assoc,
          ← whiskerLeft_comp_assoc, ← biproductAction_π, whiskerLeft_comp]
        simp only [Category.assoc, biproductAction_π] }
  ⟨⨁ fun j => (P j).X⟩

/-- The ordinary biproduct inclusions are actual module morphisms. -/
def biproductι (j : J) : P j ⟶ biproductObj P :=
  Mod_.Hom.mk' (biproduct.ι (fun j => (P j).X) j) (by
    change γ[A,(P j).X] ≫ biproduct.ι (fun j => (P j).X) j =
      (A ◁ biproduct.ι (fun j => (P j).X) j) ≫ biproductAction P
    apply biproduct.hom_ext
    intro k
    simp only [Category.assoc]
    rw [biproductAction_π, ← whiskerLeft_comp_assoc]
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
    apply (Mod_.forget (D := C) A).map_injective
    rw [Functor.map_sum]
    change (∑ j, biproduct.π (fun j => (P j).X) j ≫
      biproduct.ι (fun j => (P j).X) j) = 𝟙 _
    exact IsBilimit.total (biproduct.isBilimit (fun j => (P j).X)))

instance hasBiproduct : HasBiproduct P := HasBiproduct.mk ⟨bicone P, biconeIsBilimit P⟩

instance hasFiniteBiproducts : HasFiniteBiproducts (Mod_ C A) where
  out _ := ⟨fun _ => hasBiproduct _⟩

end Paper18.Category.InternalModule
