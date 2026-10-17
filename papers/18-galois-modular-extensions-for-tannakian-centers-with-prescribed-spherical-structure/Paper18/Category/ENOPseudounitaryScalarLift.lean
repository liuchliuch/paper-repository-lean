import Paper18.Category.TensorCharacters
import Paper18.Fusion.Grading

/-! # Actual natural scalar actions from finite semisimple decompositions -/

noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w

namespace Paper18.Category.FiniteSemisimpleSkeleton

variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

def scalarInclusion (X : C) (a : Fin (S.length X)) : S.simpleObject (S.label X a) ⟶ X :=
  biproduct.ι (fun b => S.simpleObject (S.label X b)) a ≫ (S.decomposition X).inv

def scalarProjection (X : C) (a : Fin (S.length X)) : X ⟶ S.simpleObject (S.label X a) :=
  (S.decomposition X).hom ≫ biproduct.π (fun b => S.simpleObject (S.label X b)) a

lemma scalar_resolution (X : C) :
    ∑ a, S.scalarProjection X a ≫ S.scalarInclusion X a = 𝟙 X := by
  simp only [scalarProjection, scalarInclusion, Category.assoc, ← Preadditive.comp_sum]
  simp_rw [← Category.assoc]
  rw [← Preadditive.sum_comp, biproduct.total, Category.id_comp, Iso.hom_inv_id]

/-- Multiply each actual simple summand by its assigned scalar. -/
def scalarAction (s : ι → ℂ) (X : C) : X ⟶ X :=
  (S.decomposition X).hom ≫
    biproduct.map (fun a => s (S.label X a) • 𝟙 (S.simpleObject (S.label X a))) ≫
    (S.decomposition X).inv

@[reassoc (attr := simp)]
lemma scalarInclusion_action (s : ι → ℂ) (X : C) (a : Fin (S.length X)) :
    S.scalarInclusion X a ≫ S.scalarAction s X =
      s (S.label X a) • S.scalarInclusion X a := by
  simp [scalarInclusion, scalarAction]

@[reassoc (attr := simp)]
lemma scalarAction_projection (s : ι → ℂ) (X : C) (a : Fin (S.length X)) :
    S.scalarAction s X ≫ S.scalarProjection X a =
      s (S.label X a) • S.scalarProjection X a := by
  simp [scalarProjection, scalarAction, Category.assoc]

lemma scalarAction_hom_ext {X Y : C} (f g : X ⟶ Y)
    (h : ∀ a b, S.scalarInclusion X a ≫ f ≫ S.scalarProjection Y b =
      S.scalarInclusion X a ≫ g ≫ S.scalarProjection Y b) : f = g := by
  apply (cancel_epi (S.decomposition X).inv).mp
  apply biproduct.hom_ext'
  intro a
  apply (cancel_mono (S.decomposition Y).hom).mp
  apply biproduct.hom_ext
  intro b
  simpa only [scalarInclusion, scalarProjection, Category.assoc] using h a b

lemma simple_hom_scalar (s : ι → ℂ) (i j : ι) (f : S.simpleObject i ⟶ S.simpleObject j) :
    s i • f = s j • f := by
  by_cases hf : f = 0
  · simp [hf]
  · letI := CategoryTheory.isIso_of_hom_simple hf
    have hij := S.iso_injective i j ⟨asIso f⟩
    subst j
    rfl

lemma scalarAction_naturality (s : ι → ℂ) {X Y : C} (f : X ⟶ Y) :
    f ≫ S.scalarAction s Y = S.scalarAction s X ≫ f := by
  apply S.scalarAction_hom_ext
  intro a b
  simp only [Category.assoc, scalarAction_projection, Linear.comp_smul,
    scalarInclusion_action_assoc, Linear.smul_comp]
  exact (S.simple_hom_scalar s _ _
    (S.scalarInclusion X a ≫ f ≫ S.scalarProjection Y b)).symm

lemma scalarAction_simple (s : ι → ℂ) (i : ι) :
    S.scalarAction s (S.simpleObject i) = s i • 𝟙 (S.simpleObject i) := by
  apply (cancel_epi (S.decomposition (S.simpleObject i)).inv).mp
  apply biproduct.hom_ext'
  intro a
  rw [← Category.assoc]
  change S.scalarInclusion (S.simpleObject i) a ≫ S.scalarAction s (S.simpleObject i) = _
  rw [S.scalarInclusion_action]
  simpa only [Category.assoc, Linear.comp_smul, Category.comp_id] using
    S.simple_hom_scalar s _ i (S.scalarInclusion (S.simpleObject i) a)

/-- A nowhere-zero scalar on each actual simple object extends to an
actual natural automorphism of the identity on the full category. -/
def scalarNatIso (s : ι → ℂ) (hs : ∀ i, s i ≠ 0) : 𝟭 C ≅ 𝟭 C where
  hom :=
    { app := S.scalarAction s
      naturality := fun {X Y} f => S.scalarAction_naturality s f }
  inv :=
    { app := S.scalarAction (fun i => (s i)⁻¹)
      naturality := fun {X Y} f => S.scalarAction_naturality _ f }
  hom_inv_id := by
    ext X
    apply (cancel_epi (S.decomposition X).inv).mp
    apply biproduct.hom_ext'
    intro a
    simp only [← Category.assoc]
    change S.scalarInclusion X a ≫ (S.scalarAction s X ≫ S.scalarAction (fun i => (s i)⁻¹) X) =
      S.scalarInclusion X a ≫ 𝟙 X
    simp [← mul_smul, hs]
  inv_hom_id := by
    ext X
    apply (cancel_epi (S.decomposition X).inv).mp
    apply biproduct.hom_ext'
    intro a
    simp only [← Category.assoc]
    change S.scalarInclusion X a ≫ (S.scalarAction (fun i => (s i)⁻¹) X ≫ S.scalarAction s X) =
      S.scalarInclusion X a ≫ 𝟙 X
    simp [← mul_smul, hs]

@[simp] lemma scalarNatIso_scalar (s : ι → ℂ) (hs : ∀ i, s i ≠ 0) (i : ι) :
    TensorAutomorphism.scalar (S.scalarNatIso s hs) (S.simpleObject i) = s i := by
  unfold TensorAutomorphism.scalar
  rw [show (S.scalarNatIso s hs).hom.app (S.simpleObject i) = S.scalarAction s (S.simpleObject i) from rfl,
    S.scalarAction_simple, simpleScalarEquiv_smul_id]

variable [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]

lemma scalarAction_unit (s : ι → ℂ) (hs : s S.unitLabel = 1) :
    S.scalarAction s (𝟙_ C) = 𝟙 (𝟙_ C) := by
  apply (cancel_epi S.unitIso.hom).mp
  have hn := S.scalarAction_naturality s S.unitIso.hom
  rw [S.scalarAction_simple, hs, one_smul, Category.id_comp] at hn
  simpa only [Category.comp_id] using hn

lemma tensor_scalar_resolution (X Y : C) :
    (∑ a, ∑ b,
      (S.scalarProjection X a ⊗ₘ S.scalarProjection Y b) ≫
        (S.scalarInclusion X a ⊗ₘ S.scalarInclusion Y b)) = 𝟙 (X ⊗ Y) := by
  calc
    _ = (∑ a, S.scalarProjection X a ≫ S.scalarInclusion X a) ⊗ₘ
        (∑ b, S.scalarProjection Y b ≫ S.scalarInclusion Y b) := by
      simp only [tensorHom_comp_tensorHom, tensor_sum, sum_tensor]
      rw [Finset.sum_comm]
    _ = _ := by rw [S.scalar_resolution, S.scalar_resolution, id_tensorHom_id]

lemma tensor_scalar_hom_ext {X Y Z : C} (f g : X ⊗ Y ⟶ Z)
    (h : ∀ a b, (S.scalarInclusion X a ⊗ₘ S.scalarInclusion Y b) ≫ f =
      (S.scalarInclusion X a ⊗ₘ S.scalarInclusion Y b) ≫ g) : f = g := by
  calc
    f = (∑ a, ∑ b, (S.scalarProjection X a ⊗ₘ S.scalarProjection Y b) ≫
        (S.scalarInclusion X a ⊗ₘ S.scalarInclusion Y b)) ≫ f := by
      rw [S.tensor_scalar_resolution, Category.id_comp]
    _ = (∑ a, ∑ b, (S.scalarProjection X a ⊗ₘ S.scalarProjection Y b) ≫
        (S.scalarInclusion X a ⊗ₘ S.scalarInclusion Y b)) ≫ g := by
      simp only [Preadditive.sum_comp, Category.assoc]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [h a b]
    _ = g := by rw [S.tensor_scalar_resolution, Category.id_comp]

lemma scalarAction_tensor_simples (χ : Paper18.SignCharacter S.fusionBasis) (i j : ι) :
    S.scalarAction χ.val (S.simpleObject i ⊗ S.simpleObject j) =
      (χ.val i * χ.val j) • 𝟙 (S.simpleObject i ⊗ S.simpleObject j) := by
  let X := S.simpleObject i ⊗ S.simpleObject j
  apply (cancel_epi (S.decomposition X).inv).mp
  apply biproduct.hom_ext'
  intro a
  simp only [← Category.assoc]
  change S.scalarInclusion X a ≫ S.scalarAction χ.val X =
    S.scalarInclusion X a ≫ ((χ.val i * χ.val j) • 𝟙 X)
  rw [S.scalarInclusion_action, Linear.comp_smul, Category.comp_id]
  have hp : 0 < S.fusionCoeff i j (S.label X a) :=
    (S.multiplicity_pos_iff_label X (S.label X a)).mpr ⟨a, rfl⟩
  rw [χ.val_tensor i j (S.label X a) hp]

lemma scalarAction_tensor (χ : Paper18.SignCharacter S.fusionBasis) (X Y : C) :
    S.scalarAction χ.val (X ⊗ Y) = S.scalarAction χ.val X ⊗ₘ S.scalarAction χ.val Y := by
  apply S.tensor_scalar_hom_ext
  intro a b
  rw [S.scalarAction_naturality, S.scalarAction_tensor_simples, Linear.smul_comp, Category.id_comp,
    tensorHom_comp_tensorHom, S.scalarInclusion_action, S.scalarInclusion_action]
  simp [tensorHom_def, smul_smul, mul_comm]

/-- A derived sign character supplies a genuine tensor natural
automorphism on the entire actual category. -/
def signNatIso (χ : Paper18.SignCharacter S.fusionBasis) : 𝟭 C ≅ 𝟭 C :=
  S.scalarNatIso χ.val (fun i => by rcases χ.val_mem i with h | h <;> simp [h])

instance signNatIso_monoidal (χ : Paper18.SignCharacter S.fusionBasis) :
    (S.signNatIso χ).hom.IsMonoidal where
  unit := by
    change 𝟙 _ ≫ S.scalarAction χ.val (𝟙_ C) = 𝟙 _
    rw [Category.id_comp, S.scalarAction_unit χ.val χ.val_one]
  tensor X Y := by
    change 𝟙 _ ≫ S.scalarAction χ.val (X ⊗ Y) =
      (S.scalarAction χ.val X ⊗ₘ S.scalarAction χ.val Y) ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id, S.scalarAction_tensor]

lemma signNatIso_involutive (χ : Paper18.SignCharacter S.fusionBasis) (X : C) :
    (S.signNatIso χ).hom.app X ≫ (S.signNatIso χ).hom.app X = 𝟙 X := by
  have h : (fun i => (χ.val i)⁻¹) = χ.val := funext χ.val_inv
  have he := (S.signNatIso χ).hom_inv_id_app X
  change S.scalarAction χ.val X ≫ S.scalarAction (fun i => (χ.val i)⁻¹) X = 𝟙 X at he
  rw [h] at he
  exact he

@[simp] lemma signNatIso_scalar (χ : Paper18.SignCharacter S.fusionBasis) (i : ι) :
    TensorAutomorphism.scalar (S.signNatIso χ) (S.simpleObject i) = χ.val i :=
  S.scalarNatIso_scalar _ _ i

end Paper18.Category.FiniteSemisimpleSkeleton
