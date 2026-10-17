import Paper18.Category.SphericalizationKernelUnitSums

/-! # The actual forgetful kernel and full faithfulness of its C₂ representation -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u
namespace Paper18.Category.Sphericalized
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasFiniteBiproducts C]

/-- Membership in the actual tensor kernel means that the forgotten object
is actually isomorphic to a finite biproduct of ambient units. -/
def kernelProperty : ObjectProperty (Sphericalized C) := fun X => IsUnitSum X.obj.obj

abbrev Kernel := (kernelProperty (C := C)).FullSubcategory

def kernelInclusion : Kernel (C := C) ⥤ Sphericalized C := kernelProperty.ι

variable [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]

def kernelRepresentation : Kernel (C := C) ⥤ FDRep ℂ RepresentationZ2.H :=
  kernelInclusion ⋙ unitHomRepresentation

instance kernelRepresentation_additive : (kernelRepresentation (C := C)).Additive := by
  dsimp [kernelRepresentation, kernelInclusion]
  infer_instance

instance kernelRepresentation_linear : (kernelRepresentation (C := C)).Linear ℂ := by
  dsimp [kernelRepresentation, kernelInclusion]
  infer_instance

instance kernelRepresentation_faithful : (kernelRepresentation (C := C)).Faithful where
  map_injective {X Y} f g h := by
    apply Pivotalized.Hom.ext
    apply X.property.hom_ext
    intro a
    have ha := LinearMap.congr_fun (congrArg (fun k => k.hom.hom) h) (unitHomCoordinate X.obj a)
    change unitHomCoordinate Y.obj
        ((unitHomCoordinate X.obj).symm (unitHomCoordinate X.obj a) ≫ f.hom) =
      unitHomCoordinate Y.obj
        ((unitHomCoordinate X.obj).symm (unitHomCoordinate X.obj a) ≫ g.hom) at ha
    simp only [LinearEquiv.symm_apply_apply] at ha
    exact (unitHomCoordinate Y.obj).injective ha

variable [HasKernels C] [Simple (𝟙_ C)]

def kernelIntertwinerLinear {X Y : Kernel (C := C)}
    (f : kernelRepresentation.obj X ⟶ kernelRepresentation.obj Y) :
    (𝟙_ C ⟶ X.obj.obj.obj) →ₗ[ℂ] (𝟙_ C ⟶ Y.obj.obj.obj) :=
  (unitHomCoordinate Y.obj).symm.toLinearMap ∘ₗ f.hom.hom ∘ₗ
    (unitHomCoordinate X.obj).toLinearMap

omit [HasKernels C] [Simple (𝟙_ C)] in
lemma kernelIntertwinerLinear_involution {X Y : Kernel (C := C)}
    (f : kernelRepresentation.obj X ⟶ kernelRepresentation.obj Y)
    (g : 𝟙_ C ⟶ X.obj.obj.obj) :
    kernelIntertwinerLinear f (unitHomInvolution X.obj g) =
      unitHomInvolution Y.obj (kernelIntertwinerLinear f g) := by
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom
    (f.comm RepresentationZ2.generator)) (unitHomCoordinate X.obj g)
  change f.hom.hom ((unitHomRepresentation.obj X.obj).ρ RepresentationZ2.generator
      (unitHomCoordinate X.obj g)) =
    (unitHomRepresentation.obj Y.obj).ρ RepresentationZ2.generator
      (f.hom.hom (unitHomCoordinate X.obj g)) at h
  rw [unitHomRepresentation_generator] at h
  apply (unitHomCoordinate Y.obj).injective
  change unitHomCoordinate Y.obj
      ((unitHomCoordinate Y.obj).symm (f.hom.hom
        (unitHomCoordinate X.obj (unitHomInvolution X.obj g)))) =
    unitHomCoordinate Y.obj (unitHomInvolution Y.obj
      ((unitHomCoordinate Y.obj).symm (f.hom.hom (unitHomCoordinate X.obj g))))
  rw [LinearEquiv.apply_symm_apply, h]
  simpa only [LinearEquiv.apply_symm_apply] using
    unitHomRepresentation_generator Y.obj
      ((unitHomCoordinate Y.obj).symm (f.hom.hom (unitHomCoordinate X.obj g)))

def kernelIntertwinerUnderlying {X Y : Kernel (C := C)}
    (f : kernelRepresentation.obj X ⟶ kernelRepresentation.obj Y) :
    X.obj.obj.obj ⟶ Y.obj.obj.obj := X.property.homFromUnitMap (kernelIntertwinerLinear f)

lemma comp_kernelIntertwinerUnderlying {X Y : Kernel (C := C)}
    (f : kernelRepresentation.obj X ⟶ kernelRepresentation.obj Y)
    (g : 𝟙_ C ⟶ X.obj.obj.obj) :
    g ≫ kernelIntertwinerUnderlying f = kernelIntertwinerLinear f g :=
  X.property.comp_homFromUnitMap _ _

/-- Representation intertwiners lift to genuine square-commuting morphisms. -/
def kernelIntertwiner {X Y : Kernel (C := C)}
    (f : kernelRepresentation.obj X ⟶ kernelRepresentation.obj Y) : X ⟶ Y where
  hom := kernelIntertwinerUnderlying f
  comm := by
    apply X.property.hom_ext
    intro g
    let q := unitHomInvolution X.obj g
    have hq : unitHomInvolution X.obj q = g := unitHomInvolution_sq X.obj g
    have hi (a : 𝟙_ C ⟶ X.obj.obj.obj) :
        unitHomInvolution X.obj a ≫ kernelIntertwinerUnderlying f =
          unitHomInvolution Y.obj (a ≫ kernelIntertwinerUnderlying f) := by
      rw [comp_kernelIntertwinerUnderlying, comp_kernelIntertwinerUnderlying,
        kernelIntertwinerLinear_involution]
    calc
      g ≫ kernelIntertwinerUnderlying f ≫ Y.obj.obj.phi.hom =
          unitHomInvolution X.obj q ≫ kernelIntertwinerUnderlying f ≫ Y.obj.obj.phi.hom := by rw [hq]
      _ = unitHomInvolution Y.obj (q ≫ kernelIntertwinerUnderlying f) ≫ Y.obj.obj.phi.hom := by
        rw [← Category.assoc, hi]
      _ = (unitHomInvolution X.obj q ≫ X.obj.obj.phi.hom) ≫
          (doubleDualFunctor C).map (kernelIntertwinerUnderlying f) := by
        change (Functor.LaxMonoidal.ε (doubleDualFunctor C) ≫
          (doubleDualFunctor C).map (q ≫ kernelIntertwinerUnderlying f) ≫ Y.obj.obj.phi.inv) ≫
            Y.obj.obj.phi.hom =
          ((Functor.LaxMonoidal.ε (doubleDualFunctor C) ≫ (doubleDualFunctor C).map q ≫
            X.obj.obj.phi.inv) ≫ X.obj.obj.phi.hom) ≫
              (doubleDualFunctor C).map (kernelIntertwinerUnderlying f)
        simp only [Functor.map_comp, Category.assoc,
          Iso.inv_hom_id, Category.comp_id]
      _ = g ≫ X.obj.obj.phi.hom ≫ (doubleDualFunctor C).map (kernelIntertwinerUnderlying f) := by
        rw [hq, Category.assoc]

lemma kernelRepresentation_map_intertwiner {X Y : Kernel (C := C)}
    (f : kernelRepresentation.obj X ⟶ kernelRepresentation.obj Y) :
    kernelRepresentation.map (kernelIntertwiner f) = f := by
  apply Action.Hom.ext
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change unitHomCoordinate Y.obj
      ((unitHomCoordinate X.obj).symm x ≫ kernelIntertwinerUnderlying f) = f.hom.hom x
  rw [comp_kernelIntertwinerUnderlying]
  change unitHomCoordinate Y.obj ((unitHomCoordinate Y.obj).symm
    (f.hom.hom (unitHomCoordinate X.obj ((unitHomCoordinate X.obj).symm x)))) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

instance kernelRepresentation_full : (kernelRepresentation (C := C)).Full where
  map_surjective f := ⟨kernelIntertwiner f, kernelRepresentation_map_intertwiner f⟩

end Paper18.Category.Sphericalized
