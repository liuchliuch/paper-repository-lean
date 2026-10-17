import Paper18.Category.PointedCharacters
import Paper18.Category.PointedFusion
import Paper18.Category.TensorCharacters

noncomputable section

open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace Paper18.Category.PointedVec

variable {A : Type} [Fintype A] [AddGroup A]

attribute [local instance] simple_simpleObject

lemma degreeMap_simple_eq_scalar (s : A → ℂ) (a : A) :
    degreeMap s (simpleObject A a) = s a • 𝟙 (simpleObject A a) := by
  funext b
  by_cases hb : b = a
  · subst b
    rfl
  · exact (simpleFiber_isZero A a b hb).eq_of_src _ _

omit [Fintype A] [AddGroup A] in
lemma fromSimple_ne_zero (a : A) (X : PointedVec A) (v : X a) (hv : v ≠ 0) :
    fromSimple a X v ≠ 0 := by
  intro h
  have hh := congrFun h a
  rw [fromSimple_at] at hh
  have he := congrArg (fun f => ((simpleFiberIso A a).inv ≫ f).hom (1 : ℂ)) hh
  apply hv
  simpa [Category.assoc, FGModuleCat.hom_comp] using he

/-- The actual tensor of two homogeneous lines has a nonzero constituent
in the sum degree, witnessed by the convolution inclusion. -/
lemma simple_tensor_nonzero_hom (a b : A) :
    ∃ f : simpleObject A (a + b) ⟶ simpleObject A a ⊗ simpleObject A b, f ≠ 0 := by
  let X := simpleObject A a
  let Y := simpleObject A b
  let i := tensorInclusion A X Y a b (a + b) rfl
  haveI : Mono i := tensorInclusion_mono _ _ _ _ _ _ _
  haveI : Simple (X a ⊗ Y b) := by
    letI := simple_complex_line
    exact Simple.of_iso ((simpleFiberIso A a ⊗ᵢ simpleFiberIso A b) ≪≫
      λ_ (FGModuleCat.of ℂ ℂ))
  have hi : i ≠ 0 := by
    intro hz
    exact Simple.not_isZero _ (IsZero.of_mono_eq_zero i hz)
  have hi' : i.hom ≠ 0 := fun hz => hi (FGModuleCat.hom_ext hz)
  have hex : ∃ v, i.hom v ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hi' (LinearMap.ext hn)
  obtain ⟨v, hv⟩ := hex
  exact ⟨fromSimple (a + b) (X ⊗ Y) (i.hom v),
    fromSimple_ne_zero _ _ _ hv⟩

variable (α : 𝟭 (PointedVec A) ≅ 𝟭 (PointedVec A)) [α.hom.IsMonoidal]

/-- Every actual tensor natural automorphism gives a character of the
grading group, obtained from its action on actual homogeneous lines. -/
def tensorCharacter : AddChar A ℂ where
  toFun a := TensorAutomorphism.scalar α (simpleObject A a)
  map_zero_eq_one' := by
    rw [TensorAutomorphism.scalar_iso α (unitSimpleIso A).symm,
      TensorAutomorphism.scalar_unit]
  map_add_eq_mul' a b := by
    obtain ⟨f, hf⟩ := simple_tensor_nonzero_hom a b
    exact TensorAutomorphism.scalar_of_nonzero_hom α _ _ _ f hf

@[simp] lemma tensorCharacter_apply (a : A) :
    tensorCharacter α a = TensorAutomorphism.scalar α (simpleObject A a) := rfl

/-- The character recovered from homogeneous lines determines the entire
actual tensor automorphism, using the proved finite decomposition. -/
theorem eq_characterAutomorphism : α = characterAutomorphism (tensorCharacter α) := by
  apply TensorAutomorphism.ext_simple α _ (skeleton A)
  intro a
  change TensorAutomorphism.scalar α (simpleObject A a) =
    simpleScalarEquiv (simpleObject A a) (degreeMap (tensorCharacter α) (simpleObject A a))
  rw [degreeMap_simple_eq_scalar, simpleScalarEquiv_smul_id]
  rfl

end Paper18.Category.PointedVec
