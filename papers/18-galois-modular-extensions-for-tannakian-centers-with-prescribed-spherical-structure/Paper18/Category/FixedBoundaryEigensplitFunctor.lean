import Paper18.Category.SignKernelSplit

/-!
# Functorial actual sign eigenspaces

The actual kernels of χ-id and χ+id form functors. Their inclusions and
the explicit split projections are natural morphisms. These are used to
glue fixed comparisons on the two actual homogeneous subcategories.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
universe v u
namespace Paper18.Category.FixedBoundary
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [HasKernels C]
  (χ : 𝟭 C ≅ 𝟭 C)
open SignKernel

/-- The actual induced map between the kernels of χ-id. -/
def plusMap {X Y : C} (f : X ⟶ Y) : plusObject χ X ⟶ plusObject χ Y :=
  kernel.lift _ (plusι χ X ≫ f) (by
    have hn := χ.hom.naturality f
    change f ≫ χ.hom.app Y = χ.hom.app X ≫ f at hn
    simp only [component, Preadditive.comp_sub, Category.comp_id, Category.assoc]
    rw [hn, ← Category.assoc, plusι_component]
    simp)

/-- The actual induced map between the kernels of χ+id. -/
def minusMap {X Y : C} (f : X ⟶ Y) : minusObject χ X ⟶ minusObject χ Y :=
  kernel.lift _ (minusι χ X ≫ f) (by
    have hn := χ.hom.naturality f
    change f ≫ χ.hom.app Y = χ.hom.app X ≫ f at hn
    simp only [component, Preadditive.comp_add, Category.comp_id, Category.assoc]
    rw [hn, ← Category.assoc, minusι_component]
    simp)

@[reassoc (attr := simp)] theorem plusMap_ι {X Y : C} (f : X ⟶ Y) :
    plusMap χ f ≫ plusι χ Y = plusι χ X ≫ f := kernel.lift_ι _ _ _

@[reassoc (attr := simp)] theorem minusMap_ι {X Y : C} (f : X ⟶ Y) :
    minusMap χ f ≫ minusι χ Y = minusι χ X ≫ f := kernel.lift_ι _ _ _

@[simp] theorem plusMap_id (X : C) : plusMap χ (𝟙 X) = 𝟙 _ := by
  apply (cancel_mono (plusι χ X)).mp
  simp

@[simp] theorem minusMap_id (X : C) : minusMap χ (𝟙 X) = 𝟙 _ := by
  apply (cancel_mono (minusι χ X)).mp
  simp

@[simp] theorem plusMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    plusMap χ (f ≫ g) = plusMap χ f ≫ plusMap χ g := by
  apply (cancel_mono (plusι χ Z)).mp
  simp [Category.assoc]

@[simp] theorem minusMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    minusMap χ (f ≫ g) = minusMap χ f ≫ minusMap χ g := by
  apply (cancel_mono (minusι χ Z)).mp
  simp [Category.assoc]

/-- The actual positive eigenspace, as an object of the actual neutral category. -/
def plusFunctor : C ⥤ SignKernel.Positive χ where
  obj X := ⟨plusObject χ X, plusObject_positive χ X⟩
  map f := plusMap χ f
  map_id X := plusMap_id χ X
  map_comp f g := plusMap_comp χ f g

/-- The actual negative eigenspace, as an object of the actual odd category. -/
def minusFunctor : C ⥤ HomogeneousCategory χ 1 where
  obj X := ⟨minusObject χ X, minusObject_negative χ X⟩
  map f := minusMap χ f
  map_id X := minusMap_id χ X
  map_comp f g := minusMap_comp χ f g

variable (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)

@[reassoc] theorem plusπ_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ plusπ χ hχ Y = plusπ χ hχ X ≫ plusMap χ f := by
  apply (cancel_mono (plusι χ Y)).mp
  simp only [Category.assoc, plusMap_ι, plusπ_ι, plusπ_ι_assoc]
  have hn := χ.hom.naturality f
  change f ≫ χ.hom.app Y = χ.hom.app X ≫ f at hn
  simp only [plusEnd, component, Linear.comp_smul, Linear.smul_comp,
    Preadditive.comp_add, Preadditive.add_comp, Category.comp_id, Category.id_comp]
  rw [hn]

@[reassoc] theorem minusπ_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ minusπ χ hχ Y = minusπ χ hχ X ≫ minusMap χ f := by
  apply (cancel_mono (minusι χ Y)).mp
  simp only [Category.assoc, minusMap_ι, minusπ_ι, minusπ_ι_assoc]
  have hn := χ.hom.naturality f
  change f ≫ χ.hom.app Y = χ.hom.app X ≫ f at hn
  simp only [minusEnd, component, Linear.comp_smul, Linear.smul_comp,
    Preadditive.comp_sub, Preadditive.sub_comp, Category.comp_id, Category.id_comp]
  rw [hn]

end Paper18.Category.FixedBoundary
