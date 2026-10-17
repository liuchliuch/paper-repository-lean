import Paper18.Category.PointedBasic
import Mathlib.Algebra.Category.ModuleCat.Simple
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Classical

namespace Paper18.Category.PointedVec

variable {A : Type} [Fintype A] [AddGroup A]

omit [Fintype A] [AddGroup A] in
/-- Monomorphisms of graded vector spaces are injective in every degree. -/
lemma mono_component {X Y : PointedVec A} (f : X ⟶ Y) [Mono f] (a : A) : Mono (f a) where
  right_cancellation := by
    intro Z g h heq
    let W : PointedVec A := fun _ => Z
    let lift (u : Z ⟶ X a) : W ⟶ X := fun b =>
      if hb : b = a then u ≫ eqToHom (congrArg X hb).symm else 0
    have heq' : lift g ≫ f = lift h ≫ f := by
      funext b
      by_cases hb : b = a
      · subst b
        simpa [lift] using heq
      · simp [lift, hb]
    have hh := congrFun ((cancel_mono f).mp heq') a
    simpa [lift] using hh

lemma simple_complex_line : Simple (FGModuleCat.of ℂ ℂ) := by
  let F := forget₂ (FGModuleCat ℂ) (ModuleCat ℂ)
  have hs : Simple (F.obj (FGModuleCat.of ℂ ℂ)) := by
    change Simple (ModuleCat.of ℂ ℂ)
    exact simple_of_finrank_eq_one (k := ℂ) (by simp)
  letI := hs
  constructor
  intro Y f hf
  haveI : Mono (F.map f) := inferInstance
  rw [← isIso_iff_of_reflects_iso f F, Simple.mono_isIso_iff_nonzero]
  constructor
  · intro h hzero
    apply h
    simp [hzero]
  · intro h hzero
    apply h
    exact F.map_injective (by simpa using hzero)

omit [Fintype A] [AddGroup A] in
/-- The one-dimensional homogeneous objects are categorical simple objects. -/
theorem simple_simpleObject (a : A) : Simple (simpleObject A a) := by
  have hline := simple_complex_line
  letI := hline
  have hsa : Simple ((simpleObject A a) a) :=
    Simple.of_iso (GradedObject.singleObjApplyIso a (FGModuleCat.of ℂ ℂ))
  letI := hsa
  have hs0 (b : A) (hb : b ≠ a) : IsZero ((simpleObject A a) b) :=
    (GradedObject.isInitialSingleObjApply a (FGModuleCat.of ℂ ℂ) b hb).isZero
  constructor
  intro Y f hf
  constructor
  · intro hi hzero
    haveI := hi
    haveI : IsIso (f a) := GradedObject.isIso_apply_of_isIso f a
    have hn := (Simple.mono_isIso_iff_nonzero (f a)).mp (by infer_instance)
    exact hn (by rw [hzero]; rfl)
  · intro hn
    have hfa : f a ≠ 0 := by
      intro hfa
      apply hn
      funext b
      by_cases hb : b = a
      · subst b
        exact hfa
      · exact (hs0 b hb).eq_of_tgt _ _
    haveI : ∀ b, Mono (f b) := fun b => mono_component f b
    haveI : ∀ b, IsIso (f b) := by
      intro b
      by_cases hb : b = a
      · subst b
        exact (Simple.mono_isIso_iff_nonzero (f a)).mpr hfa
      · have hy : IsZero (Y b) := IsZero.of_mono (f b) (hs0 b hb)
        have heq : f b = (hy.iso (hs0 b hb)).hom := hy.eq_of_src _ _
        rw [heq]
        infer_instance
    exact GradedObject.isIso_of_isIso_apply f

omit [Fintype A] [AddGroup A] in
/-- Distinct degrees give nonisomorphic simple vector spaces. -/
theorem simpleObject_iso_injective (a b : A)
    (e : simpleObject A a ≅ simpleObject A b) : a = b := by
  by_contra hab
  have hz : IsZero ((simpleObject A b) a) :=
    (GradedObject.isInitialSingleObjApply b (FGModuleCat.of ℂ ℂ) a hab).isZero
  have hz' : IsZero ((simpleObject A a) a) :=
    hz.of_iso ((GradedObject.eval a).mapIso e)
  have hzline : IsZero (FGModuleCat.of ℂ ℂ) :=
    hz'.of_iso (GradedObject.singleObjApplyIso a (FGModuleCat.of ℂ ℂ)).symm
  letI := simple_complex_line
  exact Simple.not_isZero _ hzline

omit [Fintype A] [AddGroup A] in
lemma mono_of_components {X Y : PointedVec A} (f : X ⟶ Y) (h : ∀ a, Mono (f a)) : Mono f where
  right_cancellation g k hgk := by
    funext a
    letI := h a
    exact (cancel_mono (f a)).mp (congrFun hgk a)

/-- The homogeneous map from a concentrated line specified by a vector. -/
def fromSimple (a : A) (X : PointedVec A) (v : X a) : simpleObject A a ⟶ X := fun b =>
  if hb : b = a then
    (GradedObject.singleObjApplyIsoOfEq a (FGModuleCat.of ℂ ℂ) b hb).hom ≫
      FGModuleCat.ofHom (LinearMap.toSpanSingleton ℂ (X a) v) ≫
      eqToHom (congrArg X hb).symm
  else 0

omit [Fintype A] [AddGroup A] in
/-- Every categorical simple object is one of the homogeneous lines. -/
theorem simple_classification (X : PointedVec A) [Simple X] :
    ∃ a, Nonempty (X ≅ simpleObject A a) := by
  obtain ⟨a, ha⟩ : ∃ a, (𝟙 (X a) : X a ⟶ X a) ≠ 0 := by
    by_contra! h
    apply id_nonzero X
    funext a
    exact h a
  obtain ⟨v, hv⟩ : ∃ v : X a, v ≠ 0 := by
    by_contra! h
    apply ha
    apply FGModuleCat.hom_ext
    ext v
    exact h v
  let m := FGModuleCat.ofHom (LinearMap.toSpanSingleton ℂ (X a) v)
  haveI hm : Mono m := by
    constructor
    intro Z g h heq
    apply FGModuleCat.hom_ext
    ext z
    apply smul_left_injective ℂ hv
    exact congrArg (fun t => t.hom z) heq
  haveI hmono : Mono (fromSimple a X v) := by
    apply mono_of_components
    intro b
    by_cases hb : b = a
    · subst b
      dsimp only [fromSimple]
      rw [dif_pos rfl]
      change Mono (_ ≫ m ≫ _)
      infer_instance
    · exact (GradedObject.isInitialSingleObjApply a (FGModuleCat.of ℂ ℂ) b hb).isZero.mono _
  have hn : fromSimple a X v ≠ 0 := by
    intro hz
    have hh := congrArg (fun t : simpleObject A a ⟶ X =>
      ((GradedObject.singleObjApplyIso a (FGModuleCat.of ℂ ℂ)).inv ≫ t a).hom 1) hz
    apply hv
    simpa [fromSimple, FGModuleCat.hom_comp] using hh
  haveI := isIso_of_mono_of_nonzero hn
  exact ⟨a, ⟨(asIso (fromSimple a X v)).symm⟩⟩

end Paper18.Category.PointedVec
