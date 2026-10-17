import Paper18.Category.SignKernelBasic

/-! # Actual two-term eigensplitting of an involutive tensor character -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
namespace Paper18.Category.SignKernel
open FixedBoundary
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C] [HasKernels C]
  (χ : 𝟭 C ≅ 𝟭 C)

def component (X : C) : X ⟶ X := χ.hom.app X

def plusObject (X : C) : C := kernel (component χ X - 𝟙 X)
def minusObject (X : C) : C := kernel (component χ X + 𝟙 X)
def plusι (X : C) : plusObject χ X ⟶ X := kernel.ι _
def minusι (X : C) : minusObject χ X ⟶ X := kernel.ι _

instance plusι_mono (X : C) : Mono (plusι χ X) := inferInstanceAs (Mono (kernel.ι _))
instance minusι_mono (X : C) : Mono (minusι χ X) := inferInstanceAs (Mono (kernel.ι _))

omit [Linear ℂ C] in
lemma plusι_component (X : C) : plusι χ X ≫ χ.hom.app X = plusι χ X := by
  have h := kernel.condition (component χ X - 𝟙 X)
  simpa only [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] using h

omit [Linear ℂ C] in
lemma minusι_component (X : C) : minusι χ X ≫ χ.hom.app X = -(minusι χ X) := by
  have h := kernel.condition (component χ X + 𝟙 X)
  simpa only [Preadditive.comp_add, Category.comp_id, add_eq_zero_iff_eq_neg] using h

lemma plusObject_positive (X : C) : positiveProperty χ (plusObject χ X) := by
  rw [mem_positive]
  apply (cancel_mono (plusι χ X)).mp
  change χ.hom.app (plusObject χ X) ≫ plusι χ X = 𝟙 _ ≫ plusι χ X
  have hn := χ.hom.naturality (plusι χ X)
  change plusι χ X ≫ χ.hom.app X = χ.hom.app (plusObject χ X) ≫ plusι χ X at hn
  rw [← hn, plusι_component, Category.id_comp]

lemma minusObject_negative (X : C) : Homogeneous χ 1 (minusObject χ X) := by
  change χ.hom.app (minusObject χ X) = (-1 : ℂ) • 𝟙 _
  apply (cancel_mono (minusι χ X)).mp
  have hn := χ.hom.naturality (minusι χ X)
  change minusι χ X ≫ χ.hom.app X = χ.hom.app (minusObject χ X) ≫ minusι χ X at hn
  rw [← hn, minusι_component]
  simp

def plusEnd (X : C) : X ⟶ X := (2 : ℂ)⁻¹ • (𝟙 X + component χ X)
def minusEnd (X : C) : X ⟶ X := (2 : ℂ)⁻¹ • (𝟙 X - component χ X)

variable (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)

omit [HasKernels C] in
include hχ in
lemma plusEnd_condition (X : C) : plusEnd χ X ≫ (component χ X - 𝟙 X) = 0 := by
  simp [plusEnd, component, Preadditive.comp_sub, Preadditive.add_comp, hχ X, add_comm]

omit [HasKernels C] in
include hχ in
lemma minusEnd_condition (X : C) : minusEnd χ X ≫ (component χ X + 𝟙 X) = 0 := by
  simp [minusEnd, component, Preadditive.comp_add, Preadditive.sub_comp, hχ X]
  module

def plusπ (X : C) : X ⟶ plusObject χ X := kernel.lift _ (plusEnd χ X) (plusEnd_condition χ hχ X)
def minusπ (X : C) : X ⟶ minusObject χ X := kernel.lift _ (minusEnd χ X) (minusEnd_condition χ hχ X)

@[reassoc (attr := simp)] lemma plusπ_ι (X : C) : plusπ χ hχ X ≫ plusι χ X = plusEnd χ X :=
  kernel.lift_ι _ _ _
@[reassoc (attr := simp)] lemma minusπ_ι (X : C) : minusπ χ hχ X ≫ minusι χ X = minusEnd χ X :=
  kernel.lift_ι _ _ _

@[simp] lemma plusι_π (X : C) : plusι χ X ≫ plusπ χ hχ X = 𝟙 _ := by
  apply (cancel_mono (plusι χ X)).mp
  rw [Category.assoc, plusπ_ι, Category.id_comp]
  simp only [plusEnd, component, Linear.comp_smul, Preadditive.comp_add,
    Category.comp_id, plusι_component]
  module

@[simp] lemma minusι_π (X : C) : minusι χ X ≫ minusπ χ hχ X = 𝟙 _ := by
  apply (cancel_mono (minusι χ X)).mp
  rw [Category.assoc, minusπ_ι, Category.id_comp]
  simp only [minusEnd, component, Linear.comp_smul, Preadditive.comp_sub,
    Category.comp_id, minusι_component]
  module

@[simp] lemma plusι_minusπ (X : C) : plusι χ X ≫ minusπ χ hχ X = 0 := by
  apply (cancel_mono (minusι χ X)).mp
  rw [Category.assoc, minusπ_ι, zero_comp]
  simp [minusEnd, component, plusι_component]

@[simp] lemma minusι_plusπ (X : C) : minusι χ X ≫ plusπ χ hχ X = 0 := by
  apply (cancel_mono (plusι χ X)).mp
  rw [Category.assoc, plusπ_ι, zero_comp]
  simp [plusEnd, component, minusι_component]

lemma split_resolution (X : C) :
    plusπ χ hχ X ≫ plusι χ X + minusπ χ hχ X ≫ minusι χ X = 𝟙 X := by
  rw [plusπ_ι, minusπ_ι]
  simp only [plusEnd, minusEnd, ← smul_add]
  module

variable [HasFiniteBiproducts C]

/-- A concrete two-term decomposition into the actual kernels of χ-id and
χ+id, with all four matrix identities and the total resolution proved. -/
def splitIso (X : C) : X ≅ plusObject χ X ⊞ minusObject χ X where
  hom := biprod.lift (plusπ χ hχ X) (minusπ χ hχ X)
  inv := biprod.desc (plusι χ X) (minusι χ X)
  hom_inv_id := by rw [biprod.lift_desc]; exact split_resolution χ hχ X
  inv_hom_id := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp

end Paper18.Category.SignKernel
