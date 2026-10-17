import Paper18.Category.PivotalDimensionFusion
import Paper18.Category.LinearMatMonoidalLift
import Paper18.Category.RigidDoubleDual

/-! # Actual closure criteria for pointed pivotal coherence -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.QuasiFusion.PivotalCriterion
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- Close an actual double-dual identification using the actual chosen cup and cap. -/
def closure {X : C} (p : X ⟶ (doubleDualFunctor C).obj X) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ X (dual C X) ≫ p ▷ dual C X ≫ ε_ (dual C X) (dual C (dual C X))

/-- The actual closure associated with a natural bidual identification
is invariant under actual isomorphisms, before tensor coherence is known. -/
lemma closure_iso (j : 𝟭 C ≅ doubleDualFunctor C) {X Y : C} (e : X ≅ Y) :
    closure (j.hom.app X) = closure (j.hom.app Y) := by
  let tr {Z : C} (f : Z ⟶ Z) :=
    η_ Z (dual C Z) ≫ f ▷ dual C Z ≫ j.hom.app Z ▷ dual C Z ≫
      ε_ (dual C Z) (dual C (dual C Z))
  have hc {U V : C} (f : U ⟶ V) (g : V ⟶ U) : tr (f ≫ g) = tr (g ≫ f) := by
    dsimp only [tr]
    simp only [comp_whiskerRight, assoc]
    rw [← coevaluation_comp_rightAdjointMate_assoc f]
    rw [whisker_exchange_assoc, whisker_exchange_assoc]
    dsimp only [doubleDualFunctor, dual, dualMap] at *
    rw [← rightAdjointMate_comp_evaluation (rightAdjointMate f)]
    have hn := congrArg (fun k => k ▷ dual C V) (j.hom.naturality f).symm
    dsimp only [doubleDualFunctor, dualMap, Functor.id_map] at hn
    simp only [comp_whiskerRight] at hn
    rw [reassoc_of% hn]
  simpa only [tr, Iso.hom_inv_id, Iso.inv_hom_id, id_whiskerRight, id_comp,
    closure] using hc e.hom e.inv

lemma tensor_cap {X Y : C} (p : X ⟶ (doubleDualFunctor C).obj X)
    (q : Y ⟶ (doubleDualFunctor C).obj Y) :
    (X ⊗ Y) ◁ (dualTensorIso X Y).inv ≫
      ((p ⊗ₘ q) ≫ doubleDualTensorHom C X Y) ▷ dual C (X ⊗ Y) ≫
        ε_ (dual C (X ⊗ Y)) (dual C (dual C (X ⊗ Y))) =
      (p ⊗ₘ q) ▷ (dual C Y ⊗ dual C X) ≫
        tensorEvaluation C (dual C Y) (dual C X) := by
  simp only [doubleDualTensorHom, comp_whiskerRight, assoc]
  rw [rightAdjointMate_comp_evaluation (dualTensorTo C X Y)]
  rw [whisker_exchange_assoc, whisker_exchange_assoc]
  simp only [← whiskerLeft_comp_assoc, ← dualTensorIso_hom,
    Iso.inv_hom_id, whiskerLeft_id, id_comp]
  rw [← dualTensorIso_inv, dualTensorIso_inv_evaluation]

/-- Closing the canonical tensor of arbitrary bidual maps is a nested
actual closure. No pivotal tensor law is an input. -/
lemma closure_tensor_nested {X Y : C} (p : X ⟶ (doubleDualFunctor C).obj X)
    (q : Y ⟶ (doubleDualFunctor C).obj Y) :
    closure ((p ⊗ₘ q) ≫ doubleDualTensorHom C X Y) =
      η_ X (dual C X) ≫ X ◁ ((λ_ (dual C X)).inv ≫ closure q ▷ dual C X ≫
        (λ_ (dual C X)).hom) ≫ p ▷ dual C X ≫ ε_ (dual C X) (dual C (dual C X)) := by
  dsimp only [doubleDualFunctor] at p q
  have hc : η_ (X ⊗ Y) (dual C (X ⊗ Y)) =
      tensorCoevaluation C X Y ≫ (X ⊗ Y) ◁ (dualTensorIso X Y).inv := by
    rw [← dualTensorIso_coevaluation]
    simp only [assoc, ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, comp_id]
  rw [closure, hc, assoc, tensor_cap]
  calc
    _ = 𝟙 (𝟙_ C) ⊗≫ η_ X (dual C X) ⊗≫ X ◁ η_ Y (dual C Y) ▷ dual C X ⊗≫
        X ◁ q ▷ dual C Y ▷ dual C X ⊗≫
        (p ▷ ((dual C (dual C Y) ⊗ dual C Y) ⊗ dual C X) ≫
          dual C (dual C X) ◁ (ε_ (dual C Y) (dual C (dual C Y)) ▷ dual C X)) ⊗≫
        ε_ (dual C X) (dual C (dual C X)) ⊗≫ 𝟙 (𝟙_ C) := by
      dsimp [tensorCoevaluation, tensorEvaluation, doubleDualFunctor]
      rw [tensorHom_def']
      monoidal
    _ = _ := by
      rw [← whisker_exchange]
      dsimp [closure, doubleDualFunctor]
      monoidal

lemma closure_tensor_one {X Y : C} (p : X ⟶ (doubleDualFunctor C).obj X)
    (q : Y ⟶ (doubleDualFunctor C).obj Y) (hp : closure p = 𝟙 (𝟙_ C))
    (hq : closure q = 𝟙 (𝟙_ C)) :
    closure ((p ⊗ₘ q) ≫ doubleDualTensorHom C X Y) = 𝟙 (𝟙_ C) := by
  simp only [closure_tensor_nested, hq, id_whiskerRight, id_comp, comp_id,
    Iso.inv_hom_id, whiskerLeft_id]
  exact hp

section Linear
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]

lemma closure_smul {X : C} (p : X ⟶ (doubleDualFunctor C).obj X) (c : ℂ) :
    closure (c • p) = c • closure p := by
  simp [closure]

/-- On an actual simple, a nonzero normalized closure detects the actual
bidual map. This is Schur injectivity of the closure, rather than an
assumption about scalar dimensions. -/
lemma closure_injective {X : C} [Simple X] (e : X ≅ (doubleDualFunctor C).obj X)
    (he : closure e.hom = 𝟙 (𝟙_ C)) : Function.Injective
      (closure (C := C) (X := X)) := by
  intro f g h
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ (f ≫ e.inv)
  obtain ⟨d, hd⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ (g ≫ e.inv)
  have hf : f = c • e.hom := by
    have hh := congrArg (fun t => t ≫ e.hom) hc
    simpa only [Linear.smul_comp, id_comp, assoc, Iso.inv_hom_id, comp_id] using hh.symm
  have hg : g = d • e.hom := by
    have hh := congrArg (fun t => t ≫ e.hom) hd
    simpa only [Linear.smul_comp, id_comp, assoc, Iso.inv_hom_id, comp_id] using hh.symm
  rw [hf, hg, closure_smul, closure_smul, he] at h
  have hcd := smul_left_injective ℂ (CategoryTheory.id_nonzero (𝟙_ C)) h
  rw [hf, hg, hcd]

/-- For a simple tensor of actual simples, normalized actual closures force
the actual pivotal tensor coherence equation. -/
lemma tensor_of_normalized_closure (j : 𝟭 C ≅ doubleDualFunctor C)
    (hn : ∀ X : C, Simple X → closure (j.hom.app X) = 𝟙 (𝟙_ C))
    (X Y : C) [Simple X] [Simple Y] [Simple (X ⊗ Y)] :
    j.hom.app (X ⊗ Y) = (j.hom.app X ⊗ₘ j.hom.app Y) ≫ doubleDualTensorHom C X Y := by
  apply closure_injective (X := X ⊗ Y) (j.app (X ⊗ Y)) (hn _ inferInstance)
  exact (hn _ inferInstance).trans
    (closure_tensor_one _ _ (hn X inferInstance) (hn Y inferInstance)).symm


section Extension
variable [HasFiniteBiproducts C] {ι : Type w} [Fintype ι]
  (S : FiniteSemisimpleSkeleton C ι)

/-- Actual finite biproduct decompositions extend the tensor coherence
from pairs of actual simple representatives to arbitrary actual objects. -/
lemma tensor_of_representatives (j : 𝟭 C ≅ doubleDualFunctor C)
    (h : ∀ i k, j.hom.app (S.simpleObject i ⊗ S.simpleObject k) =
      (j.hom.app (S.simpleObject i) ⊗ₘ j.hom.app (S.simpleObject k)) ≫
        doubleDualTensorHom C (S.simpleObject i) (S.simpleObject k)) (X Y : C) :
    j.hom.app (X ⊗ Y) = (j.hom.app X ⊗ₘ j.hom.app Y) ≫ doubleDualTensorHom C X Y := by
  let ex := S.decomposition X
  let ey := S.decomposition Y
  apply (cancel_epi (ex.inv ⊗ₘ ey.inv)).mp
  apply LinearMat.tensorBiproduct_hom_ext
  intro i k
  simp only [tensorHom_comp_tensorHom_assoc]
  let ix := biproduct.ι (fun a => S.simpleObject (S.label X a)) i ≫ ex.inv
  let iy := biproduct.ι (fun a => S.simpleObject (S.label Y a)) k ≫ ey.inv
  simp only [← assoc]
  change (ix ⊗ₘ iy) ≫ j.hom.app (X ⊗ Y) =
    ((ix ≫ j.hom.app X) ⊗ₘ (iy ≫ j.hom.app Y)) ≫ doubleDualTensorHom C X Y
  have hj := j.hom.naturality (ix ⊗ₘ iy)
  simp only [Functor.id_map] at hj
  rw [hj, h]
  have hn := Functor.LaxMonoidal.μ_natural (doubleDualFunctor C) ix iy
  rw [canonicalDoubleDual_tensor, canonicalDoubleDual_tensor] at hn
  rw [assoc, ← hn, tensorHom_comp_tensorHom_assoc]
  have hi := j.hom.naturality ix
  have hk := j.hom.naturality iy
  simp only [Functor.id_map] at hi hk
  rw [← hi, ← hk]

end Extension
end Linear

/-- An invertible tensor-natural comparison automatically preserves the
unit. The proof uses actual unitors and invertibility of the tensorators. -/
lemma unit_of_tensor (j : 𝟭 C ≅ doubleDualFunctor C)
    (ht : ∀ X Y : C, j.hom.app (X ⊗ Y) =
      (j.hom.app X ⊗ₘ j.hom.app Y) ≫ doubleDualTensorHom C X Y) :
    j.hom.app (𝟙_ C) = doubleDualUnitHom C := by
  let D := doubleDualFunctor C
  have h : j.hom.app (𝟙_ C) ▷ D.obj (𝟙_ C) =
      Functor.LaxMonoidal.ε D ▷ D.obj (𝟙_ C) := by
    apply (cancel_mono (Functor.LaxMonoidal.μ D (𝟙_ C) (𝟙_ C) ≫
      D.map (λ_ (𝟙_ C)).hom)).mp
    apply (cancel_epi ((𝟙_ C) ◁ j.hom.app (𝟙_ C))).mp
    rw [← reassoc_of% (tensorHom_def' (j.hom.app (𝟙_ C)) (j.hom.app (𝟙_ C)))]
    rw [canonicalDoubleDual_tensor, ← reassoc_of% (ht (𝟙_ C) (𝟙_ C))]
    rw [← j.hom.naturality]
    have hl : Functor.LaxMonoidal.ε D ▷ D.obj (𝟙_ C) ≫
        doubleDualTensorHom C (𝟙_ C) (𝟙_ C) ≫ D.map (λ_ (𝟙_ C)).hom =
      (λ_ (D.obj (𝟙_ C))).hom := by
      simpa only [D, canonicalDoubleDual_tensor] using
        (Functor.LaxMonoidal.left_unitality D (𝟙_ C)).symm
    rw [hl]
    simpa only [Functor.id_obj, Functor.id_map] using
      (leftUnitor_naturality (j.hom.app (𝟙_ C))).symm
  have hh := congrArg (fun f => f ≫ D.obj (𝟙_ C) ◁ Functor.OplaxMonoidal.η D) h
  dsimp only at hh
  rw [← whisker_exchange, ← whisker_exchange] at hh
  have hh' := (cancel_epi ((𝟙_ C) ◁ Functor.OplaxMonoidal.η D)).mp hh
  have hh'' := congrArg (fun f => f ≫ (ρ_ (D.obj (𝟙_ C))).hom) hh'
  dsimp only at hh''
  rw [rightUnitor_naturality, rightUnitor_naturality] at hh''
  have hu := (cancel_epi (ρ_ (𝟙_ C)).hom).mp hh''
  exact hu.trans (canonicalDoubleDual_unit (C := C))

end Paper18.Category.QuasiFusion.PivotalCriterion
