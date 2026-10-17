import Paper18.Category.RelativeCenterLinear

/-!
# Actual finite biproducts in the Drinfeld center

Half-braidings on finite direct sums are constructed by the canonical tensor
distributors. Their coherence is checked after the actual biproduct projections.
-/
noncomputable section
universe v u
open Classical
namespace Paper18.Category.RelativeCenter

open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [MonoidalPreadditive C] [HasFiniteBiproducts C]
  {P : ObjectProperty C} [P.IsMonoidal]
  {J : Type} [Fintype J] (X : J → RelativeCenter P)

/-- The block diagonal half-braiding is built from actual distributor isomorphisms. -/
def biproductHalfBraidingIso (U : C) (hU : P U) :
    (⨁ fun j => (X j).1) ⊗ U ≅ U ⊗ (⨁ fun j => (X j).1) :=
  rightDistributor (fun j => (X j).1) U ≪≫
    biproduct.mapIso (fun j => (X j).2.β U hU) ≪≫
      (leftDistributor U (fun j => (X j).1)).symm

@[reassoc (attr := simp)]
lemma biproductHalfBraidingIso_hom_pi (U : C) (hU : P U) (j : J) :
    (biproductHalfBraidingIso X U hU).hom ≫ (U ◁ biproduct.π (fun j => (X j).1) j) =
      (biproduct.π (fun j => (X j).1) j ▷ U) ≫ ((X j).2.β U hU).hom := by
  simp [biproductHalfBraidingIso]

@[reassoc (attr := simp)]
lemma biproduct_iota_halfBraidingIso_hom (U : C) (hU : P U) (j : J) :
    (biproduct.ι (fun j => (X j).1) j ▷ U) ≫ (biproductHalfBraidingIso X U hU).hom =
      ((X j).2.β U hU).hom ≫ (U ◁ biproduct.ι (fun j => (X j).1) j) := by
  simp [biproductHalfBraidingIso]

/-- The block diagonal family satisfies half-braiding coherence. -/
def biproductHalfBraiding : RelativeHalfBraiding P (⨁ fun j => (X j).1) where
  β := biproductHalfBraidingIso X
  monoidal U V hU hV := by
    apply leftDistributor_ext_right
    intro j
    rw [biproductHalfBraidingIso_hom_pi (hU := ObjectProperty.prop_tensor hU hV)]
    simp only [assoc]
    rw [← associator_inv_naturality_right]
    rw [← whiskerLeft_comp_assoc, biproductHalfBraidingIso_hom_pi (hU := hV)]
    rw [whiskerLeft_comp]
    simp only [assoc]
    rw [← associator_naturality_middle_assoc]
    rw [← comp_whiskerRight_assoc, biproductHalfBraidingIso_hom_pi (hU := hU)]
    rw [comp_whiskerRight]
    simp only [assoc]
    rw [← associator_inv_naturality_left_assoc]
    rw [(X j).2.monoidal U V hU hV]
  naturality {U V} hU hV f := by
    apply leftDistributor_ext_right
    intro j
    simp only [assoc, biproductHalfBraidingIso_hom_pi (hU := hV)]
    rw [whisker_exchange_assoc]
    rw [← whisker_exchange f (biproduct.π (fun j => (X j).1) j)]
    rw [biproductHalfBraidingIso_hom_pi_assoc (hU := hU)]
    rw [(X j).2.naturality hU hV f]

/-- The direct sum object of the center with its constructed half-braiding. -/
def biproductObj : RelativeCenter P := ⟨_, biproductHalfBraiding X⟩

/-- Actual direct sum projection in the center. -/
def biproductPi (j : J) : biproductObj X ⟶ X j where
  f := biproduct.π (fun j => (X j).1) j
  comm U hU := (biproductHalfBraidingIso_hom_pi X U hU j).symm

/-- Actual direct sum inclusion in the center. -/
def biproductIota (j : J) : X j ⟶ biproductObj X where
  f := biproduct.ι (fun j => (X j).1) j
  comm U hU := biproduct_iota_halfBraidingIso_hom X U hU j

variable [Linear ℂ C] [MonoidalLinear ℂ C]

/-- The lifted direct sum bicone. -/
def biproductBicone : Bicone X where
  pt := biproductObj X
  π := biproductPi X
  ι := biproductIota X
  ι_π j k := by
    apply ext P
    dsimp [biproductPi, biproductIota]
    split_ifs with h
    · subst k
      simp
    · simp [h]

lemma biproductBicone_total :
    ∑ j : J, (biproductBicone X).π j ≫ (biproductBicone X).ι j = 𝟙 _ := by
  apply (forget P).map_injective
  rw [Functor.map_sum]
  change ∑ j : J, biproduct.π (fun j => (X j).1) j ≫
    biproduct.ι (fun j => (X j).1) j = 𝟙 _
  exact biproduct.total

instance hasBiproduct : HasBiproduct X :=
  HasBiproduct.mk ⟨biproductBicone X, isBilimitOfTotal _ (biproductBicone_total X)⟩

instance hasFiniteBiproducts : HasFiniteBiproducts (RelativeCenter P) where
  out _ := ⟨fun X => hasBiproduct X⟩

end Paper18.Category.RelativeCenter
