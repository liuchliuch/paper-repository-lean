import Paper18.Category.FixedBoundaryGrading
import Paper18.Category.FixedBoundaryBasic
import Paper18.Category.SignKernelSplit
import Paper18.Category.ENOPseudounitaryScalarLift

/-!
# Actual scalar gauge transformations for an involutive character

A nonzero scalar on the negative eigenspace and the identity on the positive
one define an actual natural isomorphism on the original category. The
construction uses the actual character, rather than a category of labels.
The scalar-defect theorem below is the cochain-to-category direction of the
fixed-boundary argument; it does not assert that arbitrary boundary pairs
have such scalar coordinates.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.FixedBoundary

section Gauge
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  (χ : 𝟭 C ≅ 𝟭 C)

/-- The actual endomorphism equal to one on the positive eigenspace and
`z` on the negative eigenspace. -/
def gaugeComponent (z : ℂ) (X : C) : X ⟶ X :=
  ((1 + z) / 2) • 𝟙 X + ((1 - z) / 2) • (show X ⟶ X from χ.hom.app X)

lemma gaugeComponent_naturality (z : ℂ) {X Y : C} (f : X ⟶ Y) :
    f ≫ gaugeComponent χ z Y = gaugeComponent χ z X ≫ f := by
  simp only [gaugeComponent, Preadditive.comp_add, Preadditive.add_comp,
    Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp]
  have hn := χ.hom.naturality f
  change f ≫ χ.hom.app Y = χ.hom.app X ≫ f at hn
  rw [hn]

lemma gaugeComponent_homogeneous (z : ℂ) {g : ZMod 2} {X : C}
    (hX : Homogeneous χ g X) :
    gaugeComponent χ z X = (if g = 0 then 1 else z) • 𝟙 X := by
  rw [gaugeComponent, hX]
  rcases Paper18.ZMod.two_eq_zero_or_one g with rfl | rfl <;>
    simp only [paritySign_zero, paritySign_one, smul_smul, ↓reduceIte, one_ne_zero]
  all_goals module

variable (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)

include hχ in
lemma gaugeComponent_mul (z t : ℂ) (X : C) :
    gaugeComponent χ z X ≫ gaugeComponent χ t X = gaugeComponent χ (z * t) X := by
  simp only [gaugeComponent, Preadditive.comp_add, Preadditive.add_comp,
    Linear.comp_smul, Linear.smul_comp, Category.comp_id, Category.id_comp,
    smul_smul, hχ X]
  module

@[simp] lemma gaugeComponent_one (X : C) : gaugeComponent χ 1 X = 𝟙 X := by
  simp [gaugeComponent]

/-- A scalar unit produces an actual natural isomorphism on the whole
category, with inverse obtained from its multiplicative inverse. -/
def gaugeNatIso (z : ℂˣ) : 𝟭 C ≅ 𝟭 C where
  hom := { app := gaugeComponent χ (z : ℂ)
           naturality := fun {X Y} f => gaugeComponent_naturality χ _ f }
  inv := { app := gaugeComponent χ ((z⁻¹ : ℂˣ) : ℂ)
           naturality := fun {X Y} f => gaugeComponent_naturality χ _ f }
  hom_inv_id := by
    ext X
    change gaugeComponent χ (z : ℂ) X ≫ gaugeComponent χ ((z⁻¹ : ℂˣ) : ℂ) X = 𝟙 X
    rw [gaugeComponent_mul χ hχ, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      gaugeComponent_one]
  inv_hom_id := by
    ext X
    change gaugeComponent χ ((z⁻¹ : ℂˣ) : ℂ) X ≫ gaugeComponent χ (z : ℂ) X = 𝟙 X
    rw [gaugeComponent_mul χ hχ, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      gaugeComponent_one]

lemma gaugeNatIso_homogeneous (μ : ZMod 2 → ℂˣ) (hμ : μ 0 = 1)
    {g : ZMod 2} {X : C} (hX : Homogeneous χ g X) :
    (gaugeNatIso χ hχ (μ 1)).hom.app X = (μ g : ℂ) • 𝟙 X := by
  change gaugeComponent χ (μ 1 : ℂ) X = _
  rw [gaugeComponent_homogeneous χ _ hX]
  rcases Paper18.ZMod.two_eq_zero_or_one g with rfl | rfl <;> simp [hμ]

end Gauge

section Defect
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  (F : C ⥤ C) [F.Monoidal] (e : F ≅ 𝟭 C)

/-- The actual tensorator defect of an ordinary natural identification with
identity. Its scalar coordinates must be established independently. -/
def tensoratorDefect (X Y : C) : X ⊗ Y ⟶ X ⊗ Y :=
  (e.inv.app X ⊗ₘ e.inv.app Y) ≫ Functor.LaxMonoidal.μ F X Y ≫ e.hom.app (X ⊗ Y)

@[reassoc] lemma tensoratorDefect_naturality {X X' Y Y' : C}
    (f : X ⟶ X') (g : Y ⟶ Y') :
    (f ⊗ₘ g) ≫ tensoratorDefect F e X' Y' =
      tensoratorDefect F e X Y ≫ (f ⊗ₘ g) := by
  have hi (a b : C) (k : a ⟶ b) :
      k ≫ e.inv.app b = e.inv.app a ≫ F.map k := e.inv.naturality k
  have hh (a b : C) (k : a ⟶ b) :
      F.map k ≫ e.hom.app b = e.hom.app a ≫ k := e.hom.naturality k
  simp only [tensoratorDefect, ← Category.assoc]
  rw [tensorHom_comp_tensorHom, hi, hi, ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [Functor.LaxMonoidal.μ_natural_assoc, hh]

variable (χ : 𝟭 C ≅ 𝟭 C) [NatTrans.IsMonoidal χ.hom]
  (hχ : ∀ X : C, χ.hom.app X ≫ χ.hom.app X = 𝟙 X)
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- An actual scalar cochain correction of the original natural isomorphism. -/
def correctedIso (μ : ZMod 2 → ℂˣ) : F ≅ 𝟭 C :=
  e ≪≫ gaugeNatIso χ hχ (μ 1)

include S in
/-- A coboundary scalar defect gives an actual monoidal natural isomorphism.
This establishes the cochain-to-category direction only; the defect
hypothesis is an equality of actual tensorators on actual homogeneous
objects, not an assumed classification equivalence. -/
theorem correctedIso_monoidal (lam : Paper18.Z2Cocycle)
    (μ : ZMod 2 → ℂˣ) (hμ0 : μ 0 = 1)
    (hμ : Paper18.dOne μ = lam.toFun)
    (hu : Functor.LaxMonoidal.ε F ≫ e.hom.app (𝟙_ C) = 𝟙 (𝟙_ C))
    (hd : ∀ (g h : ZMod 2) (X Y : C), Homogeneous χ g X → Homogeneous χ h Y →
      tensoratorDefect F e X Y = (lam.toFun g h : ℂ) • 𝟙 (X ⊗ Y)) :
    NatTrans.IsMonoidal (correctedIso F e χ hχ μ).hom := by
  let t := gaugeNatIso χ hχ (μ 1)
  have ht {g : ZMod 2} {X : C} (hX : Homogeneous χ g X) :
      t.hom.app X = (μ g : ℂ) • 𝟙 X := gaugeNatIso_homogeneous χ hχ μ hμ0 hX
  have hm (g h : ZMod 2) :
      (lam.toFun g h : ℂ) * (μ (g + h) : ℂ) = (μ g : ℂ) * (μ h : ℂ) := by
    have he := congrFun (congrFun hμ g) h
    have he' : lam.toFun g h * μ (g+h) = μ g * μ h := by
      rw [← he, Paper18.dOne]
      simp only [mul_assoc, inv_mul_cancel, mul_one]
    exact congrArg Units.val he'
  have htensor (X Y : C) :
      tensoratorDefect F e X Y ≫ t.hom.app (X ⊗ Y) =
        (t.hom.app X ⊗ₘ t.hom.app Y) := by
    apply S.tensor_scalar_hom_ext
    intro a b
    let f := S.scalarInclusion X a
    let g := S.scalarInclusion Y b
    obtain ⟨p, hp⟩ := simple_homogeneous χ hχ (S.simpleObject (S.label X a))
    obtain ⟨q, hq⟩ := simple_homogeneous χ hχ (S.simpleObject (S.label Y b))
    have hn : (f ⊗ₘ g) ≫ t.hom.app (X ⊗ Y) =
        t.hom.app (_ ⊗ _) ≫ (f ⊗ₘ g) := t.hom.naturality (f ⊗ₘ g)
    have hnf : f ≫ t.hom.app X = t.hom.app _ ≫ f := t.hom.naturality f
    have hng : g ≫ t.hom.app Y = t.hom.app _ ≫ g := t.hom.naturality g
    change (f ⊗ₘ g) ≫ (tensoratorDefect F e X Y ≫ t.hom.app (X ⊗ Y)) =
      (f ⊗ₘ g) ≫ (t.hom.app X ⊗ₘ t.hom.app Y)
    rw [← Category.assoc, tensoratorDefect_naturality, Category.assoc, hn,
      ← Category.assoc, hd p q _ _ hp hq, ht (homogeneous_tensor χ hp hq)]
    rw [tensorHom_comp_tensorHom, hnf, hng, ← tensorHom_comp_tensorHom, ht hp, ht hq]
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
    simp only [MonoidalCategory.tensorHom_def, MonoidalLinear.smul_whiskerRight,
      MonoidalLinear.whiskerLeft_smul, id_whiskerRight,
      whiskerLeft_id, Category.id_comp, Linear.smul_comp, Linear.comp_smul, smul_smul]
    erw [Category.id_comp]
    simpa only [mul_comm, MonoidalCategory.tensorHom_def] using
      congrArg (fun z : ℂ => z • (f ⊗ₘ g)) (hm p q)
  constructor
  · change Functor.LaxMonoidal.ε F ≫ (e.hom.app (𝟙_ C) ≫ t.hom.app (𝟙_ C)) = 𝟙 _
    rw [← Category.assoc, hu, Category.id_comp, ht (homogeneous_unit χ), hμ0]
    simp
  · intro X Y
    change Functor.LaxMonoidal.μ F X Y ≫ (e.hom.app (X ⊗ Y) ≫ t.hom.app (X ⊗ Y)) =
      ((e.hom.app X ≫ t.hom.app X) ⊗ₘ (e.hom.app Y ≫ t.hom.app Y)) ≫ 𝟙 _
    apply (cancel_epi (e.inv.app X ⊗ₘ e.inv.app Y)).mp
    simp only [Category.comp_id]
    rw [tensorHom_comp_tensorHom]
    simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
    simpa only [tensoratorDefect, ← Category.assoc] using htensor X Y

end Defect
end Paper18.Category.FixedBoundary
