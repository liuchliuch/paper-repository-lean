import Paper18.Category.PointedBraiding
import Paper18.Category.PointedScalars
import Paper18.Category.PointedSimple
import Paper18.Category.PointedCharacters
import Paper18.Category.PointedFusion
import Paper18.Category.Braided
import Paper18.Category.NondegenerateBasic

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Category

namespace Paper18.Category.AppendixBPointed

/-- The nontrivial bicharacter defining the Appendix B braiding. -/
def bicharacter : ComplexBicharacter Paper18.PointedA where
  val p r := Units.mk0 (braidingScalar p r) (braidingScalar_ne_zero p r)
  add_left p r s := by
    apply Units.ext
    exact braidingScalar_add_left p r s
  add_right p r s := by
    apply Units.ext
    exact braidingScalar_add_right p r s

@[simp] lemma bicharacter_val (p r : Paper18.PointedA) :
    (bicharacter.val p r : ℂ) = braidingScalar p r := rfl

lemma q_add (p r : Paper18.PointedA) :
    Paper18.q (p + r) = Paper18.q p * Paper18.q r * Paper18.monodromy p r := by
  rw [← braidingScalar_self, braidingScalar_add_left,
    braidingScalar_add_right, braidingScalar_add_right,
    ← braidingScalar_self, ← braidingScalar_self, ← braidingScalar_monodromy]
  ring

lemma q_neg (p : Paper18.PointedA) : Paper18.q (-p) = Paper18.q p := by
  rw [← braidingScalar_self, ← braidingScalar_self]
  change fourthRoot ((-p.1) * (-p.2)) = fourthRoot (p.1 * p.2)
  rw [neg_mul_neg]

/-- The actual category of `ZMod 4 × ZMod 4`-graded finite-dimensional
complex vector spaces with the specified, nonsymmetric braiding. -/
abbrev Vec := PointedVec Paper18.PointedA

instance : BraidedCategory Vec := PointedVec.bicharacterBraidedCategory bicharacter

/-- Double braiding acts on a homogeneous tensor by the Appendix B pairing. -/
lemma inclusion_monodromy (X Y : Vec) (i j k : Paper18.PointedA) (h : i + j = k) :
    GradedObject.Monoidal.ιTensorObj X Y i j k h ≫
        (β_ X Y).hom k ≫ (β_ Y X).hom k =
      Paper18.monodromy i j • GradedObject.Monoidal.ιTensorObj X Y i j k h := by
  change GradedObject.Monoidal.ιTensorObj X Y i j k h ≫
      (PointedVec.bicharacterBraiding bicharacter X Y).hom k ≫
      (PointedVec.bicharacterBraiding bicharacter Y X).hom k = _
  rw [PointedVec.inclusion_bicharacterBraiding_assoc]
  simp only [Linear.smul_comp, Category.assoc,
    PointedVec.inclusion_bicharacterBraiding,
    Linear.comp_smul, Linear.smul_comp,
    SymmetricCategory.symmetry_assoc, bicharacter_val]
  rw [← mul_smul, braidingScalar_monodromy]

/-- Centralization of actual homogeneous lines forces the scalar pairing
to be trivial on their degrees. -/
lemma centralizes_simple_implies_monodromy (a b : Paper18.PointedA)
    (h : Centralizes (PointedVec.simpleObject Paper18.PointedA a)
      (PointedVec.simpleObject Paper18.PointedA b)) : Paper18.monodromy a b = 1 := by
  let X := PointedVec.simpleObject Paper18.PointedA a
  let Y := PointedVec.simpleObject Paper18.PointedA b
  let f := PointedVec.tensorInclusion Paper18.PointedA X Y a b (a + b) rfl
  haveI : Mono f := PointedVec.tensorInclusion_mono _ _ _ _ _ _ _
  haveI : Simple (X a ⊗ Y b) := by
    letI := PointedVec.simple_complex_line
    exact Simple.of_iso
      ((PointedVec.simpleFiberIso Paper18.PointedA a ⊗ᵢ
        PointedVec.simpleFiberIso Paper18.PointedA b) ≪≫
        λ_ (FGModuleCat.of ℂ ℂ))
  have hf : f ≠ 0 := by
    intro hf
    exact Simple.not_isZero _ (IsZero.of_mono_eq_zero f hf)
  have he := inclusion_monodromy X Y a b (a + b) rfl
  have hh := congrFun h (a + b)
  change (β_ X Y).hom (a + b) ≫ (β_ Y X).hom (a + b) = 𝟙 _ at hh
  rw [hh] at he
  have he' : f = Paper18.monodromy a b • f := (Category.comp_id f).symm.trans he
  apply smul_left_injective ℂ hf
  simpa only [one_smul] using he'.symm

lemma centralizes_simple_of_monodromy (a b : Paper18.PointedA)
    (h : Paper18.monodromy a b = 1) :
    Centralizes (PointedVec.simpleObject Paper18.PointedA a)
      (PointedVec.simpleObject Paper18.PointedA b) := by
  let X := PointedVec.simpleObject Paper18.PointedA a
  let Y := PointedVec.simpleObject Paper18.PointedA b
  apply GradedObject.hom_ext
  intro k
  apply GradedObject.Monoidal.tensorObj_ext
  intro i j hij
  change GradedObject.Monoidal.ιTensorObj X Y i j k hij ≫
      ((β_ X Y).hom k ≫ (β_ Y X).hom k) =
    GradedObject.Monoidal.ιTensorObj X Y i j k hij ≫ 𝟙 _
  by_cases hi : i = a
  · subst i
    by_cases hj : j = b
    · subst j
      rw [inclusion_monodromy, h, one_smul, Category.comp_id]
    · have hz : IsZero (X a ⊗ Y j) :=
        (tensorLeft (X a)).map_isZero (PointedVec.simpleFiber_isZero _ b j hj)
      exact hz.eq_of_src _ _
  · have hz : IsZero (X i ⊗ Y j) :=
      (tensorRight (Y j)).map_isZero (PointedVec.simpleFiber_isZero _ a i hi)
    exact hz.eq_of_src _ _

lemma centralizes_simple_iff (a b : Paper18.PointedA) :
    Centralizes (PointedVec.simpleObject Paper18.PointedA a)
      (PointedVec.simpleObject Paper18.PointedA b) ↔ Paper18.monodromy a b = 1 :=
  ⟨centralizes_simple_implies_monodromy a b, centralizes_simple_of_monodromy a b⟩

/-- The actual braided category has no nontrivial transparent homogeneous
simple object: this now follows from its double braiding morphisms. -/
theorem transparent_simple_degree_zero (a : Paper18.PointedA)
    (h : PointedVec.simpleObject Paper18.PointedA a ∈ mugerCenter) : a = 0 := by
  apply Paper18.appendixB_monodromy_nondegenerate
  intro b
  exact centralizes_simple_implies_monodromy a b (h _ (Set.mem_univ _))

/-- Every transparent actual object is a finite direct sum of tensor units.
This is categorical Müger nondegeneracy, obtained from the explicit double
braiding and the proved homogeneous-line decomposition. -/
theorem nondegenerate : IsNondegenerate (C := Vec) := by
  apply (nondegenerate_iff_simple_center (PointedVec.skeleton Paper18.PointedA)).mpr
  intro a ha
  have ha0 := transparent_simple_degree_zero a ha
  have hu : (PointedVec.skeleton Paper18.PointedA).unitLabel = 0 :=
    PointedVec.simpleObject_iso_injective _ _
      ((PointedVec.skeleton Paper18.PointedA).unitIso ≪≫
        PointedVec.unitSimpleIso Paper18.PointedA)
  exact ha0.trans hu.symm

/-- The twist on the actual graded category has scalar `q(a,b)=i^(ab)`. -/
def twist : 𝟭 Vec ≅ 𝟭 Vec :=
  PointedVec.degreeAutomorphism Paper18.q (fun p => by
    rw [← braidingScalar_self]
    exact braidingScalar_ne_zero p p)

@[simp] lemma twist_component (X : Vec) (p : Paper18.PointedA) :
    twist.hom.app X p = Paper18.q p • 𝟙 (X p) := rfl

/-- The specified twist satisfies the categorical balancing identity. -/
lemma twist_balancing (X Y : Vec) :
    twist.hom.app (X ⊗ Y) = (twist.hom.app X ⊗ₘ twist.hom.app Y) ≫
      (β_ X Y).hom ≫ (β_ Y X).hom := by
  apply GradedObject.hom_ext
  intro k
  apply GradedObject.Monoidal.tensorObj_ext
  intro i j h
  change GradedObject.Monoidal.ιTensorObj X Y i j k h ≫
      PointedVec.degreeMap Paper18.q (X ⊗ Y) k =
    GradedObject.Monoidal.ιTensorObj X Y i j k h ≫
      (GradedObject.Monoidal.tensorHom (PointedVec.degreeMap Paper18.q X)
          (PointedVec.degreeMap Paper18.q Y) k ≫
        (β_ X Y).hom k ≫ (β_ Y X).hom k)
  rw [GradedObject.Monoidal.ι_tensorHom_assoc]
  simp only [PointedVec.degreeMap_apply, PointedVec.scalar_tensor,
    Linear.smul_comp, Linear.comp_smul, Category.id_comp]
  rw [inclusion_monodromy]
  subst k
  rw [q_add, mul_smul]
  exact congrArg (fun t => (Paper18.q i * Paper18.q j) • t)
    (congrArg (fun t => Paper18.monodromy i j • t) (Category.comp_id _))

/-- The subgroup with even second coordinate, expressed without a chosen
integer representative as the kernel of doubling that coordinate. -/
def evenSecond : AddSubgroup Paper18.PointedA :=
  AddMonoidHom.ker
    { toFun := fun p => (2 : ℕ) • p.2
      map_zero' := by simp
      map_add' := fun p r => by simp }

/-- The prescribed character on the actual even-degree subcategory. -/
def restrictedChi : AddChar evenSecond ℂ :=
  Paper18.chi.compAddMonoidHom evenSecond.subtype

lemma restrictedChi_sq (p : evenSecond) : restrictedChi p ^ 2 = 1 := by
  have hp : (2 : ℕ) • p.val.2 = 0 := p.property
  change fourthRoot p.val.2 ^ 2 = 1
  rw [← fourthRoot.map_nsmul_eq_pow, hp, fourthRoot.map_zero_eq_one]

/-- The character gives an actual tensor-compatible natural automorphism on
the even-degree category, suitable for the prescribed pivotal modification. -/
def prescribedCharacterAutomorphism :
    𝟭 (PointedVec evenSecond) ≅ 𝟭 (PointedVec evenSecond) :=
  PointedVec.characterAutomorphism restrictedChi

/-- The obstruction is visible on actual morphisms of a homogeneous line,
not just as an inequality between label functions. -/
theorem character_modification_does_not_extend
    (ψ : AddChar Paper18.PointedA ℂ) (hsq : ∀ p, ψ p ^ 2 = 1) :
    PointedVec.degreeMap ψ
        (PointedVec.simpleObject Paper18.PointedA (0, 2)) ≠
      PointedVec.degreeMap Paper18.chi
        (PointedVec.simpleObject Paper18.PointedA (0, 2)) := by
  intro h
  have he := PointedVec.degreeMap_simple_injective ψ Paper18.chi (0, 2) h
  have h1 := Paper18.appendixB_chi_0_2 ψ hsq
  have h2 := Paper18.appendixB_chi_at_zero_two
  rw [h1, h2] at he
  norm_num at he

end Paper18.Category.AppendixBPointed
