import Paper18.Category.CrossedBraidedGaugingBraidingBasic

/-! # The actual gauging crossing on its actual homogeneous components -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.CrossedBraidedGauging.CrossedBraiding
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasKernels C] [HasFiniteBiproducts C]
  {P : Grading G C} {A : WeakAction G C}
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  {Q : GradedAction P A} (B : CrossedBraiding P A Q)

/-- On each actual homogeneous inclusion, the assembled isomorphism is
exactly the original crossed map followed by the actual equivariant map. -/
@[reassoc] theorem halfSwapIso_component (g : G) (X : C) (Y : A.Equivariant) :
    (P.componentInclusion g X ▷ Y.obj) ≫ (B.halfSwapIso X Y).hom =
      (B.blockIso g (P.component g X) (P.component_homogeneous g X) Y).hom ≫
        (Y.obj ◁ P.componentInclusion g X) := by
  let f := fun h : G => P.component h X
  let R := (tensoringRight C).obj Y.obj
  let L := (tensoringLeft C).obj Y.obj
  letI : PreservesBiproduct f R := preservesFiniteBiproductOfAdditive R f
  letI : PreservesBiproduct f L := preservesFiniteBiproductOfAdditive L f
  simp only [halfSwapIso, Iso.trans_hom, Iso.symm_hom,
    whiskerRightIso_hom, whiskerLeftIso_hom, Category.assoc]
  change R.map (P.componentInclusion g X) ≫ R.map (P.decompositionIso X).hom ≫
      (R.mapBiproduct f).hom ≫
        (biproduct.mapIso (fun h : G => B.blockIso h (P.component h X)
          (P.component_homogeneous h X) Y)).hom ≫
          (L.mapBiproduct f).inv ≫ L.map (P.decompositionIso X).inv = _
  rw [← R.map_comp_assoc, P.componentInclusion_decompositionIso_hom,
    mapBiproduct_inclusion_assoc]
  change (biproduct.ι (R.obj ∘ f) g) ≫
      (biproduct.map (fun h : G => (B.blockIso h (P.component h X)
        (P.component_homogeneous h X) Y).hom)) ≫ _ = _
  rw [biproduct.ι_map_assoc, Functor.mapBiproduct_inv, biproduct.ι_desc_assoc,
    ← L.map_comp]
  have hι : biproduct.ι f g ≫ (P.decompositionIso X).inv = P.componentInclusion g X := by
    rw [P.decompositionIso_inv, biproduct.ι_desc]
  rw [hι]
  rfl

end Paper18.Category.CrossedBraidedGauging.CrossedBraiding
