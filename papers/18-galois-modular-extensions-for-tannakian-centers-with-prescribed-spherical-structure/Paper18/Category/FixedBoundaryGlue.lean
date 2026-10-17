import Paper18.Category.FixedBoundaryEigensplitFunctor

/-!
# Actual gluing of comparisons on the two homogeneous components

The split projections onto the actual sign kernels glue an ordinary
natural comparison on the neutral component and one on the odd component
to an ordinary natural isomorphism on the original category. The specified
neutral comparison is retained exactly, component by component.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace Paper18.Category.FixedBoundary
open SignKernel
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [HasKernels C]
  (χ : 𝟭 C ≅ 𝟭 C)
  (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)
  (F : C ⥤ C) [F.Additive]
  (a : SignKernel.inclusion χ ⋙ F ≅ SignKernel.inclusion χ)
  (b : ObjectProperty.ι (Homogeneous χ 1) ⋙ F ≅ ObjectProperty.ι (Homogeneous χ 1))

/-- An actual glued component, written in terms of the two actual split
projections and the two prescribed categorical comparisons. -/
def gluedComponent (X : C) : F.obj X ⟶ X :=
  F.map (plusπ χ hχ X) ≫ a.hom.app ((plusFunctor χ).obj X) ≫ plusι χ X +
    F.map (minusπ χ hχ X) ≫ b.hom.app ((minusFunctor χ).obj X) ≫ minusι χ X

/-- The inverse uses the actual inverse comparisons on each component. -/
def gluedInverseComponent (X : C) : X ⟶ F.obj X :=
  plusπ χ hχ X ≫ a.inv.app ((plusFunctor χ).obj X) ≫ F.map (plusι χ X) +
    minusπ χ hχ X ≫ b.inv.app ((minusFunctor χ).obj X) ≫ F.map (minusι χ X)

theorem gluedComponent_naturality {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ gluedComponent χ hχ F a b Y = gluedComponent χ hχ F a b X ≫ f := by
  unfold gluedComponent
  simp only [Preadditive.comp_add, Preadditive.add_comp, Category.assoc]
  congr 1
  · have hn := a.hom.naturality ((plusFunctor χ).map f)
    change F.map (plusMap χ f) ≫ a.hom.app ((plusFunctor χ).obj Y) =
      a.hom.app ((plusFunctor χ).obj X) ≫ plusMap χ f at hn
    rw [← F.map_comp_assoc, plusπ_naturality, F.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hn, plusMap_ι]
  · have hn := b.hom.naturality ((minusFunctor χ).map f)
    change F.map (minusMap χ f) ≫ b.hom.app ((minusFunctor χ).obj Y) =
      b.hom.app ((minusFunctor χ).obj X) ≫ minusMap χ f at hn
    rw [← F.map_comp_assoc, minusπ_naturality, F.map_comp]
    simp only [Category.assoc]
    rw [reassoc_of% hn, minusMap_ι]

private theorem plusι_π_tail (X : C) {Y : C} (f : plusObject χ X ⟶ Y) :
    plusι χ X ≫ plusπ χ hχ X ≫ f = f := by
  rw [← Category.assoc, plusι_π, Category.id_comp]

private theorem plusι_minusπ_tail (X : C) {Y : C} (f : minusObject χ X ⟶ Y) :
    plusι χ X ≫ minusπ χ hχ X ≫ f = 0 := by
  rw [← Category.assoc, plusι_minusπ, zero_comp]

private theorem minusι_plusπ_tail (X : C) {Y : C} (f : plusObject χ X ⟶ Y) :
    minusι χ X ≫ plusπ χ hχ X ≫ f = 0 := by
  rw [← Category.assoc, minusι_plusπ, zero_comp]

private theorem minusι_π_tail (X : C) {Y : C} (f : minusObject χ X ⟶ Y) :
    minusι χ X ≫ minusπ χ hχ X ≫ f = f := by
  rw [← Category.assoc, minusι_π, Category.id_comp]

theorem gluedComponent_hom_inv_id (X : C) :
    gluedComponent χ hχ F a b X ≫ gluedInverseComponent χ hχ F a b X = 𝟙 _ := by
  unfold gluedComponent gluedInverseComponent
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
    plusι_π_tail, plusι_minusπ_tail, minusι_plusπ_tail, minusι_π_tail,
    Iso.hom_inv_id_app_assoc, Category.comp_id, Category.id_comp,
    comp_zero, zero_comp, add_zero, zero_add]
  rw [← F.map_comp, ← F.map_comp, ← F.map_add, split_resolution, F.map_id]

theorem gluedComponent_inv_hom_id (X : C) :
    gluedInverseComponent χ hχ F a b X ≫ gluedComponent χ hχ F a b X = 𝟙 _ := by
  unfold gluedComponent gluedInverseComponent
  simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
    ← F.map_comp_assoc, plusι_π, plusι_minusπ, minusι_plusπ, minusι_π,
    F.map_id, F.map_zero, Iso.inv_hom_id_app_assoc, Category.comp_id, Category.id_comp,
    comp_zero, zero_comp, add_zero, zero_add]
  erw [F.map_id, F.map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app_assoc]
  exact split_resolution χ hχ X

/-- Actual natural isomorphisms on the two actual homogeneous categories
glue to an actual natural isomorphism on the original category. -/
def glueNatIso : F ≅ 𝟭 C :=
  NatIso.ofComponents (fun X =>
    { hom := gluedComponent χ hχ F a b X
      inv := gluedInverseComponent χ hχ F a b X
      hom_inv_id := gluedComponent_hom_inv_id χ hχ F a b X
      inv_hom_id := gluedComponent_inv_hom_id χ hχ F a b X })
    (fun f => gluedComponent_naturality χ hχ F a b f)

/-- The glued comparison has exactly the prescribed neutral component. -/
theorem glueNatIso_positive (X : SignKernel.Positive χ) :
    (glueNatIso χ hχ F a b).hom.app X.obj = a.hom.app X := by
  change gluedComponent χ hχ F a b X.obj = _
  have hm : minusπ χ hχ X.obj = 0 :=
    homogeneous_hom_zero χ (by decide : (0 : ZMod 2) ≠ 1) X.property
      (minusObject_negative χ X.obj) _
  have hn := a.hom.naturality
    (show X ⟶ (plusFunctor χ).obj X.obj from plusπ χ hχ X.obj)
  change F.map (plusπ χ hχ X.obj) ≫ a.hom.app ((plusFunctor χ).obj X.obj) =
    a.hom.app X ≫ plusπ χ hχ X.obj at hn
  have hr := split_resolution χ hχ X.obj
  rw [hm, zero_comp, add_zero] at hr
  unfold gluedComponent
  simp only [hm, F.map_zero, zero_comp, add_zero]
  rw [← Category.assoc, hn, Category.assoc, hr]
  exact Category.comp_id _

/-- The actual odd comparison is retained exactly as well. -/
theorem glueNatIso_negative (X : HomogeneousCategory χ 1) :
    (glueNatIso χ hχ F a b).hom.app X.obj = b.hom.app X := by
  change gluedComponent χ hχ F a b X.obj = _
  have hp : plusπ χ hχ X.obj = 0 :=
    homogeneous_hom_zero χ (by decide : (1 : ZMod 2) ≠ 0) X.property
      (plusObject_positive χ X.obj) _
  have hn := b.hom.naturality
    (show X ⟶ (minusFunctor χ).obj X.obj from minusπ χ hχ X.obj)
  change F.map (minusπ χ hχ X.obj) ≫ b.hom.app ((minusFunctor χ).obj X.obj) =
    b.hom.app X ≫ minusπ χ hχ X.obj at hn
  have hr := split_resolution χ hχ X.obj
  rw [hp, zero_comp, zero_add] at hr
  unfold gluedComponent
  simp only [hp, F.map_zero, zero_comp, zero_add]
  rw [← Category.assoc, hn, Category.assoc, hr]
  exact Category.comp_id _

end Paper18.Category.FixedBoundary
