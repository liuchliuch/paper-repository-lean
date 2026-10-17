import Paper18.Category.LocalModulesBraiding
import Paper18.Category.RelativeTensorCoherence

/-! # Naturality and hexagons of the actual local-module braiding -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]
open RelativeTensor

@[reassoc]
theorem localBraiding_naturality_right (M : Mod_ C A) {N P : Mod_ C A}
    (f : N ⟶ P) (hN : IsLocalModule N) (hP : IsLocalModule P) :
    M ◁ f ≫ localBraidingHom M P hP = localBraidingHom M N hN ≫ f ▷ M := by
  apply module_hom_ext
  change π M N ≫ (M ◁ f).hom ≫ (localBraidingHom M P hP).hom =
    π M N ≫ (localBraidingHom M N hN).hom ≫ (f ▷ M).hom
  rw [π_whiskerLeft_assoc, π_localBraidingHom, π_localBraidingHom_assoc, π_whiskerRight]
  rw [braiding_naturality_right_assoc]

@[reassoc]
theorem localBraiding_naturality_left {M N : Mod_ C A} (f : M ⟶ N) (P : Mod_ C A)
    (hP : IsLocalModule P) :
    f ▷ P ≫ localBraidingHom N P hP = localBraidingHom M P hP ≫ P ◁ f := by
  apply module_hom_ext
  change π M P ≫ (f ▷ P).hom ≫ (localBraidingHom N P hP).hom =
    π M P ≫ (localBraidingHom M P hP).hom ≫ (P ◁ f).hom
  rw [π_whiskerRight_assoc, π_localBraidingHom, π_localBraidingHom_assoc, π_whiskerLeft]
  rw [braiding_naturality_left_assoc]

/-- The first hexagon holds after both actual balancing quotients. -/
theorem localBraiding_hexagon_forward (M N P : Mod_ C A)
    (hN : IsLocalModule N) (hP : IsLocalModule P) :
    (α_ M N P).hom ≫ localBraidingHom M (N ⊗ P) (hN.tensor hP) ≫ (α_ N P M).hom =
      localBraidingHom M N hN ▷ P ≫ (α_ N M P).hom ≫ N ◁ localBraidingHom M P hP := by
  apply triple_hom_ext
  change (π M N ▷ P.X) ≫ π (M ⊗ N) P ≫ (α_ M N P).hom.hom ≫
      (localBraidingHom M (N ⊗ P) (hN.tensor hP)).hom ≫ (α_ N P M).hom.hom =
    (π M N ▷ P.X) ≫ π (M ⊗ N) P ≫ (localBraidingHom M N hN ▷ P).hom ≫
      (α_ N M P).hom.hom ≫ (N ◁ localBraidingHom M P hP).hom
  rw [π_associator_assoc, π_localBraidingHom_assoc]
  erw [braiding_naturality_right_assoc]
  rw [π_associator]
  rw [π_whiskerRight_assoc, ← comp_whiskerRight_assoc, π_localBraidingHom,
    comp_whiskerRight_assoc, π_associator_assoc, π_whiskerLeft]
  rw [← whiskerLeft_comp_assoc, π_localBraidingHom, whiskerLeft_comp_assoc]
  rw [hexagon_forward_assoc]

/-- The reverse hexagon also follows from the ambient hexagon before the quotients. -/
theorem localBraiding_hexagon_reverse (M N P : Mod_ C A)
    (hP : IsLocalModule P) :
    (α_ M N P).inv ≫ localBraidingHom (M ⊗ N) P hP ≫ (α_ P M N).inv =
      M ◁ localBraidingHom N P hP ≫ (α_ M P N).inv ≫ localBraidingHom M P hP ▷ N := by
  apply triple_hom_ext'
  change (M.X ◁ π N P) ≫ π M (N ⊗ P) ≫ (α_ M N P).inv.hom ≫
      (localBraidingHom (M ⊗ N) P hP).hom ≫ (α_ P M N).inv.hom =
    (M.X ◁ π N P) ≫ π M (N ⊗ P) ≫ (M ◁ localBraidingHom N P hP).hom ≫
      (α_ M P N).inv.hom ≫ (localBraidingHom M P hP ▷ N).hom
  rw [π_associator_inv_assoc, π_localBraidingHom_assoc]
  erw [braiding_naturality_left_assoc]
  rw [π_associator_inv]
  rw [π_whiskerLeft_assoc, ← whiskerLeft_comp_assoc, π_localBraidingHom,
    whiskerLeft_comp_assoc, π_associator_inv_assoc, π_whiskerRight]
  rw [← comp_whiskerRight_assoc, π_localBraidingHom, comp_whiskerRight_assoc]
  rw [hexagon_reverse_assoc]

/-- Local modules form an actual braided category under the relative tensor product. -/
instance localModulesBraided : BraidedCategory (LocalModules A) where
  braiding M N := (localModuleProperty (A := A)).isoMk
    (localBraidingIso M.obj N.obj M.property N.property)
  braiding_naturality_right M N P f :=
    localBraiding_naturality_right M.obj f N.property P.property
  braiding_naturality_left f P := localBraiding_naturality_left f P.obj P.property
  hexagon_forward M N P := localBraiding_hexagon_forward M.obj N.obj P.obj N.property P.property
  hexagon_reverse M N P := localBraiding_hexagon_reverse M.obj N.obj P.obj P.property

/-- All modules over a transparent commutative algebra carry the descended
ambient braiding. -/
def moduleBraidedOfTransparent (hA : A ∈ mugerCenter (C := C)) :
    BraidedCategory (Mod_ C A) where
  braiding M N := localBraidingIso M N
    (localModule_of_transparent hA M) (localModule_of_transparent hA N)
  braiding_naturality_right M N P f := localBraiding_naturality_right M f
    (localModule_of_transparent hA N) (localModule_of_transparent hA P)
  braiding_naturality_left f P := localBraiding_naturality_left f P
    (localModule_of_transparent hA P)
  hexagon_forward M N P := localBraiding_hexagon_forward M N P
    (localModule_of_transparent hA N) (localModule_of_transparent hA P)
  hexagon_reverse M N P := localBraiding_hexagon_reverse M N P
    (localModule_of_transparent hA P)

@[reassoc]
theorem π_moduleBraidingOfTransparent (hA : A ∈ mugerCenter (C := C)) (M N : Mod_ C A) :
    letI := moduleBraidedOfTransparent hA
    π M N ≫ (β_ M N).hom.hom = (β_ M.X N.X).hom ≫ π N M :=
  π_localBraidingHom M N (localModule_of_transparent hA N)

@[reassoc]
theorem π_localModulesBraiding (M N : LocalModules A) :
    π M.obj N.obj ≫ (β_ M N).hom.hom = (β_ M.obj.X N.obj.X).hom ≫ π N.obj M.obj :=
  π_localBraidingHom M.obj N.obj N.property

end Paper18.Category
