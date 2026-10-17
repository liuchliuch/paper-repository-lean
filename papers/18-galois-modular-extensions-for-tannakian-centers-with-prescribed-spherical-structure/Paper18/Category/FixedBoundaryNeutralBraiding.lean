import Paper18.Category.FixedBoundaryNeutralCenter

/-!
# Actual neutral braiding and its exact central-crossing convention

The actual neutral module category inherits the actual local-module
braiding through its faithful tensor functor. The central lift uses the
inverse braiding with exchanged inputs, so it supplies precisely the
negative alpha-induction convention on neutral objects.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category.FixedBoundary
variable {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A] [MonoidalPreadditive A] [MonoidalLinear ℂ A]
  [HasKernels A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [HasCoequalizers N]
  (i : A ⥤ N) [i.Braided] [i.Full] [i.Faithful] [i.Additive] [i.Linear ℂ]
  (R : A) [MonObj R] [IsCommMonObj R]
  {T : N} (B : TensorInverse T)
  (himage : ∀ X : A, Centralizes T (i.obj X))
  (S : SeparableAlgebra R)
  (hfull : ∀ Y : N, Centralizes T Y → ∃ X : A, Nonempty (i.obj X ≅ Y))
  (hR : R ∈ mugerCenter (C := A))

/-- The actual local braiding, lifted between actual neutral objects. -/
def neutralBraidingIso
    (M L : SignKernel.Positive (neutralModuleCharacter i R B himage)) : M ⊗ L ≅ L ⊗ M :=
  ObjectProperty.isoMk _ ((ObjectProperty.ι (localModuleProperty (A := i.obj R))).mapIso
    (β_ ((neutralToLocal i R B himage S hfull hR).obj M)
      ((neutralToLocal i R B himage S hfull hR).obj L)))

/-- Naturality and both actual hexagons are reflected by the faithful
strong tensor functor to actual local modules. -/
def neutralModuleBraided : BraidedCategory
    (SignKernel.Positive (neutralModuleCharacter i R B himage)) :=
  BraidedCategory.ofFaithful (neutralToLocal i R B himage S hfull hR)
    (neutralBraidingIso i R B himage S hfull hR) (by
      intro M L
      change 𝟙 _ ≫ (β_ ((neutralToLocal i R B himage S hfull hR).obj M)
        ((neutralToLocal i R B himage S hfull hR).obj L)).hom =
        (β_ ((neutralToLocal i R B himage S hfull hR).obj M)
          ((neutralToLocal i R B himage S hfull hR).obj L)).hom ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id])

/-- The neutral-to-local tensor functor preserves the actual braiding. -/
def neutralToLocalBraided :
    letI := neutralModuleBraided i R B himage S hfull hR
    (neutralToLocal i R B himage S hfull hR).Braided := by
  letI := neutralModuleBraided i R B himage S hfull hR
  refine { braided := ?_ }
  intro M L
  change 𝟙 _ ≫ (β_ ((neutralToLocal i R B himage S hfull hR).obj M)
    ((neutralToLocal i R B himage S hfull hR).obj L)).hom =
    (β_ ((neutralToLocal i R B himage S hfull hR).obj M)
      ((neutralToLocal i R B himage S hfull hR).obj L)).hom ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

/-- The actual central lift restricts to the exact inverse, exchanged
neutral braiding required for negative alpha induction. -/
theorem neutralCenterFunctor_halfBraiding_neutral
    (M L : SignKernel.Positive (neutralModuleCharacter i R B himage)) :
    letI := neutralModuleBraided i R B himage S hfull hR
    (((neutralCenterFunctor i R B himage S hfull hR).obj M).2.β L.obj).hom =
      (SignKernel.inclusion (neutralModuleCharacter i R B himage)).map (β_ L M).inv := by
  letI := neutralModuleBraided i R B himage S hfull hR
  exact (S.map i).localCenter_braiding
    ((neutralToLocal i R B himage S hfull hR).obj M)
    ((neutralToLocal i R B himage S hfull hR).obj L)

end Paper18.Category.FixedBoundary
