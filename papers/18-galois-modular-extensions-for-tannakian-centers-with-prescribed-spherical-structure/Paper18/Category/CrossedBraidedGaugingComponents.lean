import Paper18.Category.CrossedBraidedGaugingGrading

/-! # Actual homogeneous kernel images and complete graded decompositions

The grading projectors split by the actual kernel of identity minus the
projector. The resulting functors and actual biproduct decomposition are
constructed, rather than included in the crossed-category data.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.CrossedBraidedGauging.Grading
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [MonoidalCategory C]
  [HasKernels C] (P : Grading G C)

/-- The actual complementary endomorphism to one actual degree projection. -/
def complement (g : G) (X : C) : X ⟶ X := 𝟙 X - (show X ⟶ X from (P.projection g).app X)

/-- The actual homogeneous part is the kernel of the actual complement. -/
def component (g : G) (X : C) : C := kernel (P.complement g X)

def componentInclusion (g : G) (X : C) : P.component g X ⟶ X :=
  kernel.ι (P.complement g X)

instance componentInclusion_mono (g : G) (X : C) : Mono (P.componentInclusion g X) :=
  inferInstanceAs (Mono (kernel.ι _))

@[reassoc] theorem componentInclusion_projector (g : G) (X : C) :
    P.componentInclusion g X ≫ (P.projection g).app X = P.componentInclusion g X := by
  have h := kernel.condition (P.complement g X)
  change P.componentInclusion g X ≫ (𝟙 X - (show X ⟶ X from (P.projection g).app X)) = 0 at h
  rw [Preadditive.comp_sub] at h
  erw [Category.comp_id] at h
  exact (sub_eq_zero.mp h).symm

/-- The actual kernel image has its claimed homogeneous degree. -/
theorem component_homogeneous (g : G) (X : C) : P.Homogeneous g (P.component g X) := by
  change (P.projection g).app (P.component g X) = 𝟙 _
  apply (cancel_mono (P.componentInclusion g X)).mp
  erw [Category.id_comp]
  rw [← P.projection_naturality g (P.componentInclusion g X)]
  exact P.componentInclusion_projector g X

/-- The actual projection onto the kernel image comes from idempotence. -/
def componentProjection (g : G) (X : C) : X ⟶ P.component g X :=
  kernel.lift (P.complement g X) ((P.projection g).app X) (by
    change (P.projection g).app X ≫ (𝟙 X - (show X ⟶ X from (P.projection g).app X)) = 0
    rw [Preadditive.comp_sub]
    erw [Category.comp_id]
    rw [P.projection_idempotent, sub_self])

@[simp, reassoc] theorem componentProjection_inclusion (g : G) (X : C) :
    P.componentProjection g X ≫ P.componentInclusion g X = (P.projection g).app X :=
  kernel.lift_ι _ _ _

@[simp, reassoc] theorem componentInclusion_projection (g : G) (X : C) :
    P.componentInclusion g X ≫ P.componentProjection g X = 𝟙 _ := by
  apply (cancel_mono (P.componentInclusion g X)).mp
  rw [Category.assoc, P.componentProjection_inclusion]
  erw [Category.id_comp]
  exact P.componentInclusion_projector g X

@[simp, reassoc] theorem projector_componentProjection (g : G) (X : C) :
    (P.projection g).app X ≫ P.componentProjection g X = P.componentProjection g X := by
  apply (cancel_mono (P.componentInclusion g X)).mp
  simp only [Category.assoc]
  erw [P.componentProjection_inclusion]
  exact P.projection_idempotent g X

/-- Each actual homogeneous part is an actual functor. -/
def componentFunctor (g : G) : C ⥤ C where
  obj := P.component g
  map {X Y} f := P.componentInclusion g X ≫ f ≫ P.componentProjection g Y
  map_id X := by
    erw [Category.id_comp]
    exact P.componentInclusion_projection g X
  map_comp {X Y Z} f h := by
    simp only [Category.assoc, P.componentProjection_inclusion_assoc]
    rw [P.projection_naturality_assoc g f, P.componentInclusion_projector_assoc]

/-- The actual degree inclusions are natural. -/
def componentInclusionNatTrans (g : G) : P.componentFunctor g ⟶ 𝟭 C where
  app := P.componentInclusion g
  naturality {X Y} f := by
    change (P.componentInclusion g X ≫ f ≫ P.componentProjection g Y) ≫
      P.componentInclusion g Y = P.componentInclusion g X ≫ f
    rw [Category.assoc, Category.assoc, P.componentProjection_inclusion,
      P.projection_naturality, ← Category.assoc, P.componentInclusion_projector]

/-- The actual degree projections are natural. -/
def componentProjectionNatTrans (g : G) : 𝟭 C ⟶ P.componentFunctor g where
  app := P.componentProjection g
  naturality {X Y} f := by
    change f ≫ P.componentProjection g Y = P.componentProjection g X ≫
      P.componentInclusion g X ≫ f ≫ P.componentProjection g Y
    rw [← Category.assoc, ← Category.assoc, P.componentProjection_inclusion,
      ← P.projection_naturality, Category.assoc, P.projector_componentProjection]

variable [MonoidalPreadditive C] [HasFiniteBiproducts C]

/-- Distinct actual degree images are orthogonal in the actual category. -/
theorem componentInclusion_projection_of_ne {g h : G} (hgh : g ≠ h) (X : C) :
    P.componentInclusion g X ≫ P.componentProjection h X = 0 :=
  P.homogeneous_hom_zero hgh (P.component_homogeneous g X) (P.component_homogeneous h X) _

/-- The actual homogeneous images resolve every actual object. -/
theorem component_total (X : C) :
    ∑ g : G, P.componentProjection g X ≫ P.componentInclusion g X = 𝟙 X := by
  simp only [P.componentProjection_inclusion]
  exact P.total X

/-- The actual graded components form a bicone on the original object. -/
def componentBicone (X : C) : Bicone (fun g : G => P.component g X) where
  pt := X
  ι := fun g => P.componentInclusion g X
  π := fun g => P.componentProjection g X
  ι_π g h := by
    split_ifs with hgh
    · subst h
      simpa only [eqToHom_refl] using P.componentInclusion_projection g X
    · exact P.componentInclusion_projection_of_ne hgh X

/-- Orthogonality and the actual total projector identity prove the actual
bicone is a biproduct. -/
def componentBiconeIsBilimit (X : C) : (P.componentBicone X).IsBilimit :=
  isBilimitOfTotal _ (P.component_total X)

/-- The complete actual direct-sum decomposition into actual homogeneous
kernel images, derived from the grading projectors. -/
def decompositionIso (X : C) : X ≅ ⨁ fun g : G => P.component g X :=
  (P.componentBiconeIsBilimit X).isLimit.conePointUniqueUpToIso (biproduct.isLimit _)

@[simp] theorem decompositionIso_hom (X : C) : (P.decompositionIso X).hom =
    biproduct.lift (fun g : G => P.componentProjection g X) := rfl

@[simp] theorem decompositionIso_inv (X : C) : (P.decompositionIso X).inv =
    biproduct.desc (fun g : G => P.componentInclusion g X) :=
  biproduct.conePointUniqueUpToIso_inv _ _

/-- A homogeneous object is actually isomorphic to its matching kernel image. -/
def componentIso (g : G) (X : C) (hX : P.Homogeneous g X) : P.component g X ≅ X where
  hom := P.componentInclusion g X
  inv := P.componentProjection g X
  hom_inv_id := P.componentInclusion_projection g X
  inv_hom_id := (P.componentProjection_inclusion g X).trans hX

@[reassoc] theorem componentFunctor_map_inclusion (g : G) {X Y : C} (f : X ⟶ Y) :
    (P.componentFunctor g).map f ≫ P.componentInclusion g Y =
      P.componentInclusion g X ≫ f := by
  simpa only [Functor.id_map] using (P.componentInclusionNatTrans g).naturality f

end Paper18.Category.CrossedBraidedGauging.Grading
