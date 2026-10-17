import Paper18.Category.PointedMinimal
import Paper18.Category.PointedPrescribed

noncomputable section

open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits

namespace Paper18.Category.AppendixBPointed

attribute [local instance] PointedVec.simple_simpleObject

/-- Actual tensor multiplication of the homogeneous simple representatives.
The isomorphism comes from a nonzero convolution constituent and the proved
categorical invertibility of FP-dimension-one simples. -/
def simpleTensorIso (a b : Paper18.PointedA) :
    PointedVec.simpleObject Paper18.PointedA a ⊗ PointedVec.simpleObject Paper18.PointedA b ≅
      PointedVec.simpleObject Paper18.PointedA (a + b) := by
  let S := PointedVec.skeleton Paper18.PointedA
  let T := S.tensorInverseOfFpdimEqOne a (ambient_fpdim_simple a)
  letI : Simple (PointedVec.simpleObject Paper18.PointedA a ⊗
      PointedVec.simpleObject Paper18.PointedA b) :=
    T.simple_tensor S (PointedVec.simpleObject Paper18.PointedA b)
  let f := Classical.choose (PointedVec.simple_tensor_nonzero_hom a b)
  have hf := Classical.choose_spec (PointedVec.simple_tensor_nonzero_hom a b)
  letI := CategoryTheory.isIso_of_hom_simple hf
  exact (asIso f).symm

/-- The actual convolution fusion coefficients are the group law, derived
from the tensor-product isomorphisms of the homogeneous simple objects. -/
lemma fusionCoeff_eq (a b c : Paper18.PointedA) :
    (PointedVec.skeleton Paper18.PointedA).fusionCoeff a b c =
      if a + b = c then 1 else 0 := by
  change (PointedVec.skeleton Paper18.PointedA).multiplicity
    (PointedVec.simpleObject Paper18.PointedA a ⊗ PointedVec.simpleObject Paper18.PointedA b) c = _
  rw [FiniteSemisimpleSkeleton.multiplicity_iso _ (simpleTensorIso a b)]
  have h := (PointedVec.skeleton Paper18.PointedA).multiplicity_simple c (a + b)
  by_cases hc : a + b = c
  · subst c
    rw [if_pos rfl] at h ⊢
    exact h
  · rw [if_neg hc]
    rw [if_neg (Ne.symm hc)] at h
    exact h

def distinguishedSquareIso : distinguished ⊗ distinguished ≅ 𝟙_ Vec :=
  simpleTensorIso Paper18.f Paper18.f ≪≫
    eqToIso (congrArg (PointedVec.simpleObject Paper18.PointedA)
      (show Paper18.f + Paper18.f = 0 by decide)) ≪≫
    (PointedVec.unitSimpleIso Paper18.PointedA).symm

def distinguishedDegree : evenSecond := ⟨Paper18.f, by
  change (2 : ℕ) • (0 : ZMod 4) = 0
  simp⟩

abbrev bDistinguished : B := bSimple distinguishedDegree

def bDistinguishedSquareIso : bDistinguished ⊗ bDistinguished ≅ 𝟙_ B :=
  (centralizerProperty centralizerSet).isoMk distinguishedSquareIso

/-- The character modification preserves the actual induced twist of
the distinguished boson. -/
theorem nonsphericalPivotalExtension_twist_distinguished :
    (nonsphericalPivotalExtension.twistIso distinguished).hom = 𝟙 distinguished := by
  rw [PivotalStructure.twistIso_hom]
  change (PointedVec.degreeMap Paper18.chi distinguished ≫
    (PointedVec.pivotalStructure Paper18.PointedA).j.hom.app distinguished) ≫
      (drinfeldIso distinguished).inv = _
  rw [Category.assoc]
  change PointedVec.degreeMap Paper18.chi distinguished ≫
    (PointedVec.pivotalStructure Paper18.PointedA).twistNatIso.hom.app distinguished = _
  rw [canonical_twist]
  change PointedVec.degreeMap Paper18.chi distinguished ≫ PointedVec.degreeMap Paper18.q distinguished = _
  dsimp only [distinguished]
  rw [PointedVec.degreeMap_simple_eq_scalar, PointedVec.degreeMap_simple_eq_scalar,
    Paper18.appendixB_chi_on_f, Paper18.appendixB_twist_f]
  simp

lemma vector_line_selfBraiding :
    (β_ (FGModuleCat.of ℂ ℂ) (FGModuleCat.of ℂ ℂ)).hom =
      𝟙 (FGModuleCat.of ℂ ℂ ⊗ FGModuleCat.of ℂ ℂ) := by
  change (β_ (𝟙_ (FGModuleCat ℂ)) (𝟙_ (FGModuleCat ℂ))).hom = _
  rw [braiding_tensorUnit_left]
  monoidal

/-- The distinguished actual invertible has trivial self-braiding. -/
theorem distinguished_selfBraiding :
    (β_ distinguished distinguished).hom = 𝟙 (distinguished ⊗ distinguished) := by
  let X := distinguished
  have hb : (β_ (X Paper18.f) (X Paper18.f)).hom = 𝟙 (X Paper18.f ⊗ X Paper18.f) := by
    let e := PointedVec.simpleFiberIso Paper18.PointedA Paper18.f
    apply (cancel_mono (e.hom ⊗ₘ e.hom)).mp
    have hn := BraidedCategory.braiding_naturality e.hom e.hom
    rw [vector_line_selfBraiding] at hn
    simpa only [Category.id_comp, Category.comp_id] using hn.symm
  apply GradedObject.hom_ext
  intro k
  apply GradedObject.Monoidal.tensorObj_ext
  intro i j hij
  change GradedObject.Monoidal.ιTensorObj X X i j k hij ≫
      (PointedVec.bicharacterBraiding bicharacter X X).hom k =
    GradedObject.Monoidal.ιTensorObj X X i j k hij ≫ 𝟙 _
  by_cases hi : i = Paper18.f
  · subst i
    by_cases hj : j = Paper18.f
    · subst j
      rw [PointedVec.inclusion_bicharacterBraiding]
      have hc : (bicharacter.val Paper18.f Paper18.f : ℂ) = 1 := by
        simp [braidingScalar, Paper18.f]
      simp only [hc, one_smul, hb, Category.id_comp, Category.comp_id]
    · have hz : IsZero (X Paper18.f ⊗ X j) :=
        (tensorLeft (X Paper18.f)).map_isZero
          (PointedVec.simpleFiber_isZero _ Paper18.f j hj)
      exact hz.eq_of_src _ _
  · have hz : IsZero (X i ⊗ X j) :=
      (tensorRight (X j)).map_isZero
        (PointedVec.simpleFiber_isZero _ Paper18.f i hi)
    exact hz.eq_of_src _ _

theorem bDistinguished_selfBraiding :
    (β_ bDistinguished bDistinguished).hom = 𝟙 (bDistinguished ⊗ bDistinguished) :=
  distinguished_selfBraiding

def centerDistinguished : BCenter :=
  ⟨bDistinguished, (bSimple_transparent_iff distinguishedDegree).mpr (Or.inr rfl)⟩

def centerDistinguishedSquareIso : centerDistinguished ⊗ centerDistinguished ≅ 𝟙_ BCenter :=
  (centralizerProperty (Set.univ : Set B)).isoMk bDistinguishedSquareIso

theorem centerDistinguished_selfBraiding :
    (β_ centerDistinguished centerDistinguished).hom =
      𝟙 (centerDistinguished ⊗ centerDistinguished) :=
  distinguished_selfBraiding

end Paper18.Category.AppendixBPointed
