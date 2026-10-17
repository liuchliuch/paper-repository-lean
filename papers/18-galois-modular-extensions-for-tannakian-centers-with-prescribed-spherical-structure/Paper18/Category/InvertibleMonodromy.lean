import Paper18.Category.InvertibleObjects
import Paper18.Category.NondegenerateBasic
import Paper18.Category.TensorCharacters

/-!
# Monodromy characters of actual invertible objects

Left tensoring by an actual invertible object is fully faithful. Consequently
its actual double braiding has a unique preimage on each object. Naturality and
monoidal coherence of that preimage are derived below from the braiding axioms.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

lemma doubleBraiding_naturality_right (T : C) {X Y : C} (f : X ⟶ Y) :
    T ◁ f ≫ (doubleBraiding T Y).hom = (doubleBraiding T X).hom ≫ T ◁ f := by
  simp only [doubleBraiding, Iso.trans_hom, assoc]
  rw [braiding_naturality_right_assoc, braiding_naturality_left]

namespace TensorInverse
variable {T : C} (A : TensorInverse T)

/-- The actual monodromy character of an invertible object, obtained by
fully faithful preimage through its actual tensor autoequivalence. -/
def monodromyCharacter : 𝟭 C ≅ 𝟭 C := by
  letI := A.tensorLeftIsEquivalence
  refine NatIso.ofComponents (fun X => (tensorLeft T).preimageIso (doubleBraiding T X)) ?_
  intro X Y f
  apply (tensorLeft T).map_injective
  change (tensorLeft T).map (f ≫ (tensorLeft T).preimage (doubleBraiding T Y).hom) =
    (tensorLeft T).map ((tensorLeft T).preimage (doubleBraiding T X).hom ≫ f)
  rw [Functor.map_comp, Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
  exact doubleBraiding_naturality_right T f

/-- The defining identity relates actual morphisms, not supplied scalars. -/
lemma monodromyCharacter_spec (X : C) :
    T ◁ (A.monodromyCharacter.hom.app X) = (doubleBraiding T X).hom := by
  letI := A.tensorLeftIsEquivalence
  change (tensorLeft T).map ((tensorLeft T).preimage (doubleBraiding T X).hom) = _
  exact Functor.map_preimage _ _

/-- The character is independent of the choice of actual inverse data. -/
lemma monodromyCharacter_independent (B : TensorInverse T) :
    A.monodromyCharacter = B.monodromyCharacter := by
  letI := A.tensorLeftIsEquivalence
  ext X
  apply (tensorLeft T).map_injective
  exact (A.monodromyCharacter_spec X).trans (B.monodromyCharacter_spec X).symm

/-- Any actual natural automorphism satisfying the monodromy equation is
the canonical fully faithful preimage. -/
lemma monodromyCharacter_eq_of_spec (χ : 𝟭 C ≅ 𝟭 C)
    (h : ∀ X, T ◁ χ.hom.app X = (doubleBraiding T X).hom) : A.monodromyCharacter = χ := by
  letI := A.tensorLeftIsEquivalence
  ext X
  apply (tensorLeft T).map_injective
  exact (A.monodromyCharacter_spec X).trans (h X).symm

/-- Actual monodromy on a tensor product factors through the induced
components on each factor. This is proved from the two hexagon axioms. -/
lemma monodromy_tensor (X Y : C) :
    (doubleBraiding T (X ⊗ Y)).hom =
      T ◁ (A.monodromyCharacter.hom.app X ⊗ₘ A.monodromyCharacter.hom.app Y) := by
  simp only [doubleBraiding, Iso.trans_hom,
    braiding_tensor_right_hom, braiding_tensor_left_hom, assoc,
    Iso.inv_hom_id_assoc]
  have hY : (β_ T Y).hom ≫ (β_ Y T).hom = T ◁ A.monodromyCharacter.hom.app Y :=
    (A.monodromyCharacter_spec Y).symm
  have hX : (β_ T X).hom ≫ (β_ X T).hom = T ◁ A.monodromyCharacter.hom.app X :=
    (A.monodromyCharacter_spec X).symm
  rw [← whiskerLeft_comp_assoc, hY]
  calc
    _ = (α_ T X Y).inv ≫ (β_ T X).hom ▷ Y ≫
        (X ⊗ T) ◁ A.monodromyCharacter.hom.app Y ≫
        (β_ X T).hom ▷ Y ≫ (α_ T X Y).hom := by monoidal
    _ = (α_ T X Y).inv ≫ (T ⊗ X) ◁ A.monodromyCharacter.hom.app Y ≫
        ((β_ T X).hom ≫ (β_ X T).hom) ▷ Y ≫ (α_ T X Y).hom := by
      rw [← whisker_exchange_assoc, comp_whiskerRight]
      simp only [assoc]
      rfl
    _ = _ := by
      rw [hX]
      simp only [tensorHom_def']
      monoidal

/-- The induced natural automorphism is monoidal as a theorem. -/
instance monodromyCharacter_isMonoidal : NatTrans.IsMonoidal A.monodromyCharacter.hom where
  unit := by
    letI := A.tensorLeftIsEquivalence
    change 𝟙 (𝟙_ C) ≫ A.monodromyCharacter.hom.app (𝟙_ C) = 𝟙 (𝟙_ C)
    rw [id_comp]
    apply (tensorLeft T).map_injective
    change T ◁ A.monodromyCharacter.hom.app (𝟙_ C) = T ◁ 𝟙 (𝟙_ C)
    rw [A.monodromyCharacter_spec]
    simpa only [whiskerLeft_id] using centralizes_unit_right T
  tensor X Y := by
    letI := A.tensorLeftIsEquivalence
    change 𝟙 (X ⊗ Y) ≫ A.monodromyCharacter.hom.app (X ⊗ Y) =
      (A.monodromyCharacter.hom.app X ⊗ₘ A.monodromyCharacter.hom.app Y) ≫ 𝟙 (X ⊗ Y)
    rw [id_comp]
    calc
      A.monodromyCharacter.hom.app (X ⊗ Y) =
          A.monodromyCharacter.hom.app X ⊗ₘ A.monodromyCharacter.hom.app Y := by
        apply (tensorLeft T).map_injective
        exact (A.monodromyCharacter_spec (X ⊗ Y)).trans (A.monodromy_tensor X Y)
      _ = _ := (Category.comp_id _).symm


/-- The product inverse is constructed from the two actual inverse objects. -/
def tensor {U : C} (B : TensorInverse U) : TensorInverse (T ⊗ U) :=
  Classical.choice (IsTensorInvertible.tensor ⟨A⟩ ⟨B⟩)

/-- Monodromy is multiplicative in the invertible object. This identity is
an equality of actual categorical morphisms derived from the hexagons. -/
lemma monodromy_object_tensor {U : C} (B : TensorInverse U) (X : C) :
    (doubleBraiding (T ⊗ U) X).hom =
      (T ⊗ U) ◁ (A.monodromyCharacter.hom.app X ≫ B.monodromyCharacter.hom.app X) := by
  have hT : (β_ T X).hom ≫ (β_ X T).hom = T ◁ A.monodromyCharacter.hom.app X :=
    (A.monodromyCharacter_spec X).symm
  have hU : (β_ U X).hom ≫ (β_ X U).hom = U ◁ B.monodromyCharacter.hom.app X :=
    (B.monodromyCharacter_spec X).symm
  simp only [doubleBraiding, Iso.trans_hom,
    braiding_tensor_left_hom, braiding_tensor_right_hom, assoc,
    Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, hT]
  calc
    _ = (α_ T U X).hom ≫
        T ◁ ((β_ U X).hom ≫ A.monodromyCharacter.hom.app X ▷ U ≫ (β_ X U).hom) ≫
        (α_ T U X).inv := by monoidal
    _ = (α_ T U X).hom ≫
        T ◁ (U ◁ A.monodromyCharacter.hom.app X ≫
          ((β_ U X).hom ≫ (β_ X U).hom)) ≫ (α_ T U X).inv := by
      rw [← braiding_naturality_right_assoc]
      rfl
    _ = _ := by
      rw [hU]
      monoidal

/-- The actual natural monodromy characters multiply along invertible objects. -/
lemma monodromyCharacter_tensor {U : C} (B : TensorInverse U) :
    (A.tensor B).monodromyCharacter = A.monodromyCharacter ≪≫ B.monodromyCharacter := by
  letI := (A.tensor B).tensorLeftIsEquivalence
  ext X
  apply (tensorLeft (T ⊗ U)).map_injective
  exact ((A.tensor B).monodromyCharacter_spec X).trans (A.monodromy_object_tensor B X)

/-- The trivial character is exactly actual transparency of the invertible object. -/
lemma monodromyCharacter_eq_refl_iff : A.monodromyCharacter = Iso.refl (𝟭 C) ↔ T ∈ mugerCenter := by
  constructor
  · intro h X _
    rw [Centralizes, ← A.monodromyCharacter_spec X, h]
    simp
  · intro h
    letI := A.tensorLeftIsEquivalence
    ext X
    apply (tensorLeft T).map_injective
    calc
      _ = (doubleBraiding T X).hom := A.monodromyCharacter_spec X
      _ = 𝟙 (T ⊗ X) := h X (Set.mem_univ _)
      _ = _ := ((tensorLeft T).map_id X).symm

/-- The two characters of an object and its actual inverse cancel. -/
lemma monodromyCharacter_comp_inverse (X : C) :
    A.monodromyCharacter.hom.app X ≫ A.symm.monodromyCharacter.hom.app X = 𝟙 X := by
  let P := A.tensor A.symm
  letI := P.tensorLeftIsEquivalence
  apply (tensorLeft (T ⊗ A.inverse)).map_injective
  calc
    _ = (doubleBraiding (T ⊗ A.inverse) X).hom := (A.monodromy_object_tensor A.symm X).symm
    _ = 𝟙 _ := (centralizes_unit_left X).of_iso_left A.right
    _ = _ := ((tensorLeft (T ⊗ A.inverse)).map_id X).symm

end TensorInverse

section Uniqueness
attribute [local instance 2000] RightRigidCategory.rightDual
variable [Preadditive C] [Linear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

namespace TensorInverse
variable {T : C} (A : TensorInverse T)

/-- Monodromy with an actual invertible object is scalar on every actual
simple. This is derived from full faithfulness and Schur's lemma. -/
lemma doubleBraiding_scalar (X : C) [Simple X] :
    (doubleBraiding T X).hom =
      TensorAutomorphism.scalar A.monodromyCharacter X • 𝟙 (T ⊗ X) := by
  rw [← A.monodromyCharacter_spec X, ← TensorAutomorphism.scalar_spec A.monodromyCharacter X]
  simp

/-- An equation on actual simple monodromies determines the entire natural
character, by the actual finite semisimple decomposition. -/
lemma monodromyCharacter_eq_of_simple_spec (χ : 𝟭 C ≅ 𝟭 C)
    (h : ∀ i, (doubleBraiding T (S.simpleObject i)).hom =
      TensorAutomorphism.scalar χ (S.simpleObject i) • 𝟙 (T ⊗ S.simpleObject i)) :
    A.monodromyCharacter = χ := by
  letI := A.tensorLeftIsEquivalence
  apply TensorAutomorphism.ext_simple A.monodromyCharacter χ S
  intro i
  apply congrArg (simpleScalarEquiv (S.simpleObject i))
  apply (tensorLeft T).map_injective
  calc
    _ = (doubleBraiding T (S.simpleObject i)).hom := A.monodromyCharacter_spec _
    _ = _ := h i
    _ = _ := by rw [← TensorAutomorphism.scalar_spec χ (S.simpleObject i)]; simp

end TensorInverse

/-- In a nondegenerate actual fusion category, a transparent simple is
actually isomorphic to the tensor unit. -/
def isoUnitOfTransparentSimple (hC : IsNondegenerate (C := C)) (X : C) [Simple X]
    (hX : X ∈ mugerCenter) : X ≅ 𝟙_ C := by
  let i := Classical.choose (S.simple_isomorphic_representative X)
  let e : X ≅ S.simpleObject i := Classical.choice
    (Classical.choose_spec (S.simple_isomorphic_representative X))
  have hi : S.simpleObject i ∈ mugerCenter := by
    intro Y _
    exact (hX Y (Set.mem_univ _)).of_iso_left e.symm
  have he : i = S.unitLabel := (nondegenerate_iff_simple_center S).mp hC i hi
  exact e ≪≫ eqToIso (congrArg S.simpleObject he) ≪≫ S.unitIso

/-- Nondegeneracy gives uniqueness, up to actual isomorphism, of an invertible
object representing any prescribed monodromy character. -/
def isoOfEqualMonodromy (hC : IsNondegenerate (C := C)) {T U : C}
    (A : TensorInverse T) (B : TensorInverse U)
    (h : A.monodromyCharacter = B.monodromyCharacter) : T ≅ U := by
  let P := A.tensor B.symm
  letI := P.simple S
  have hp : T ⊗ B.inverse ∈ mugerCenter := by
    intro X _
    change (doubleBraiding (T ⊗ B.inverse) X).hom = 𝟙 _
    rw [A.monodromy_object_tensor B.symm X, h, B.monodromyCharacter_comp_inverse X]
    exact whiskerLeft_id _ _
  let e := isoUnitOfTransparentSimple S hC (T ⊗ B.inverse) hp
  exact ((ρ_ T).symm ≪≫ (Iso.refl T ⊗ᵢ B.left.symm) ≪≫
    (α_ T B.inverse U).symm) ≪≫ (e ⊗ᵢ Iso.refl U) ≪≫ λ_ U

/-- Actual invertible monodromy representatives have unique simple labels. -/
lemma monodromy_label_unique (hC : IsNondegenerate (C := C)) {i j : ι}
    (A : TensorInverse (S.simpleObject i)) (B : TensorInverse (S.simpleObject j))
    (h : A.monodromyCharacter = B.monodromyCharacter) : i = j :=
  S.iso_injective i j ⟨isoOfEqualMonodromy S hC A B h⟩

/-- The uniqueness part of the paper's invertible-representative statement,
formulated entirely with the actual monodromy equation. -/
def isoOfMonodromyRepresentatives (hC : IsNondegenerate (C := C)) {T U : C}
    (A : TensorInverse T) (B : TensorInverse U) (χ : 𝟭 C ≅ 𝟭 C)
    (hT : ∀ X, T ◁ χ.hom.app X = (doubleBraiding T X).hom)
    (hU : ∀ X, U ◁ χ.hom.app X = (doubleBraiding U X).hom) : T ≅ U :=
  isoOfEqualMonodromy S hC A B
    ((A.monodromyCharacter_eq_of_spec χ hT).trans
      (B.monodromyCharacter_eq_of_spec χ hU).symm)

/-- In a nondegenerate actual fusion category an involutive monodromy
character forces the actual invertible object to square to the tensor unit. -/
def tensorSelfIsoUnitOfInvolutiveMonodromy (hC : IsNondegenerate (C := C)) {T : C}
    (A : TensorInverse T)
    (h : A.monodromyCharacter ≪≫ A.monodromyCharacter = Iso.refl (𝟭 C)) : T ⊗ T ≅ 𝟙_ C := by
  let P := A.tensor A
  letI := P.simple S
  have hp : P.monodromyCharacter = Iso.refl (𝟭 C) :=
    (A.monodromyCharacter_tensor A).trans h
  exact isoUnitOfTransparentSimple S hC (T ⊗ T) (P.monodromyCharacter_eq_refl_iff.mp hp)

end Uniqueness
end Paper18.Category
