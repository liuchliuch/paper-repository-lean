import Paper18.Category.EquivariantMonoidal

/-! # Finite biproducts of equivariant objects -/

noncomputable section
open Classical CategoryTheory CategoryTheory.Limits
open scoped BigOperators
universe v u w t
namespace Paper18.Category.WeakAction
variable {G : Type w} [Group G] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear ℂ C] [HasFiniteBiproducts C]
  (A : WeakAction G C) [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]
  {J : Type t} [Fintype J] (X : J → A.Equivariant)

attribute [local instance] Paper18.Category.additive_preservesBiproductsOfFiniteShape

/-- The structure isomorphism on a finite sum of equivariant objects. -/
def biproductStructureIso (g : G) :
    (A.ρ g).obj (⨁ fun j => (X j).obj) ≅ ⨁ fun j => (X j).obj :=
  (A.ρ g).mapBiproduct (fun j => (X j).obj) ≪≫
    biproduct.mapIso (fun j => (X j).structureIso g)

omit [Linear ℂ C] [∀ g : G, (A.ρ g).Linear ℂ] in
@[reassoc (attr := simp)]
theorem map_ι_biproductStructureIso (g : G) (j : J) :
    (A.ρ g).map (biproduct.ι (fun j => (X j).obj) j) ≫ (A.biproductStructureIso X g).hom =
      ((X j).structureIso g).hom ≫ biproduct.ι (fun j => (X j).obj) j := by
  dsimp only [biproductStructureIso, Iso.trans_hom, biproduct.mapIso_hom]
  rw [← Category.assoc, Paper18.Category.map_biproduct_ι]
  simp

omit [Linear ℂ C] [∀ g : G, (A.ρ g).Linear ℂ] in
@[reassoc (attr := simp)]
theorem biproductStructureIso_π (g : G) (j : J) :
    (A.biproductStructureIso X g).hom ≫ biproduct.π (fun j => (X j).obj) j =
      (A.ρ g).map (biproduct.π (fun j => (X j).obj) j) ≫ ((X j).structureIso g).hom := by
  dsimp only [biproductStructureIso, Iso.trans_hom, biproduct.mapIso_hom]
  rw [Category.assoc, biproduct.map_π, ← Category.assoc, Functor.mapBiproduct_hom]
  erw [biproduct.lift_π]

/-- The actual biproduct object in the equivariantization. -/
def equivariantBiproductObj : A.Equivariant where
  obj := ⨁ fun j => (X j).obj
  structureIso := A.biproductStructureIso X
  unit := by
    apply Paper18.Category.map_biproduct_hom_ext (A.ρ 1) (fun j => (X j).obj)
    intro j
    rw [A.map_ι_biproductStructureIso, (X j).unit]
    exact (A.unitIso.hom.naturality _).symm
  mul g h := by
    apply Paper18.Category.map_biproduct_hom_ext (A.ρ h ⋙ A.ρ g) (fun j => (X j).obj)
    intro j
    change (A.ρ g).map ((A.ρ h).map (biproduct.ι _ j)) ≫ _ = _
    rw [← Functor.map_comp_assoc, A.map_ι_biproductStructureIso, Functor.map_comp,
      Category.assoc, A.map_ι_biproductStructureIso,
      ← Category.assoc, (X j).mul]
    conv_rhs =>
      erw [← Category.assoc, (A.mulIso g h).hom.naturality
        (biproduct.ι (fun j => (X j).obj) j), Category.assoc,
        A.map_ι_biproductStructureIso]
    simp only [Category.assoc]

/-- The actual biproduct bicone in the equivariant category. -/
def equivariantBicone : Bicone X where
  pt := A.equivariantBiproductObj X
  ι j := ⟨biproduct.ι (fun j => (X j).obj) j, fun g => A.map_ι_biproductStructureIso X g j⟩
  π j := ⟨biproduct.π (fun j => (X j).obj) j, fun g => (A.biproductStructureIso_π X g j).symm⟩
  ι_π j k := by
    apply Equivariant.Hom.ext
    split_ifs with h
    · subst k
      simp
    · simp [h]

/-- The underlying finite sum satisfies the total identity, hence is a
biproduct also in the equivariant category. -/
def equivariantBiconeIsBilimit : (A.equivariantBicone X).IsBilimit :=
  isBilimitOfTotal _ (by
    apply A.forget.map_injective
    rw [Functor.map_sum]
    change (∑ j, biproduct.π (fun j => (X j).obj) j ≫
      biproduct.ι (fun j => (X j).obj) j) = 𝟙 (⨁ fun j => (X j).obj)
    exact IsBilimit.total (biproduct.isBilimit (fun j : J => (X j).obj)))

instance equivariant_hasBiproduct : HasBiproduct X :=
  HasBiproduct.mk ⟨A.equivariantBicone X, A.equivariantBiconeIsBilimit X⟩

instance equivariant_hasFiniteBiproducts : HasFiniteBiproducts A.Equivariant where
  out _ := ⟨fun _ => A.equivariant_hasBiproduct _⟩

end Paper18.Category.WeakAction
