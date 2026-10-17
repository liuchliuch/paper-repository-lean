import Paper18.Category.LinearTensorAdditive
import Paper18.Category.SemisimpleCoendBasic

/-! # Actual simple-pair decompositions in the additive linear tensor product -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Limits
open scoped BigOperators TensorProduct
universe v u w v' u' w'
namespace Paper18.Category
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasFiniteBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [Linear ℂ D]
  [HasFiniteBiproducts D]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

namespace DeligneProduct

/-- A chosen simple pair as an actual object of the additive envelope. -/
def pairObject (i : ι) (j : κ) : DeligneProduct C D :=
  (Mat_.embedding (LinearTensor C D)).obj ⟨S.simpleObject i, T.simpleObject j⟩

/-- The actual finite family of pairs in the decompositions of two factors. -/
def pairDecompositionObject (X : C) (Y : D) : DeligneProduct C D where
  ι := Fin (S.length X) × Fin (T.length Y)
  X a := ⟨S.simpleObject (S.label X a.1), T.simpleObject (T.label Y a.2)⟩

/-- Tensoring actual inclusion/projection resolutions gives an actual
isomorphism to a finite family of simple pairs. -/
def pairDecompositionIso (X : C) (Y : D) :
    (Mat_.embedding (LinearTensor C D)).obj ⟨X, Y⟩ ≅ pairDecompositionObject S T X Y where
  hom _ a := S.coendProjection X a.1 ⊗ₜ[ℂ] T.coendProjection Y a.2
  inv a _ := S.coendInclusion X a.1 ⊗ₜ[ℂ] T.coendInclusion Y a.2
  hom_inv_id := by
    ext ⟨⟩ ⟨⟩
    simp only [Mat_.comp_apply, Mat_.id_apply_self, LinearTensor.id_def,
      LinearTensor.comp_def, LinearTensor.compLinear_tmul]
    change (∑ x : Fin (S.length X) × Fin (T.length Y),
      (S.coendProjection X x.1 ≫ S.coendInclusion X x.1) ⊗ₜ[ℂ]
      (T.coendProjection Y x.2 ≫ T.coendInclusion Y x.2)) =
        (𝟙 X) ⊗ₜ[ℂ] (𝟙 Y)
    rw [Fintype.sum_prod_type]
    simp_rw [← TensorProduct.tmul_sum]
    rw [← TensorProduct.sum_tmul, S.coendResolution, T.coendResolution]
  inv_hom_id := by
    dsimp only [pairDecompositionObject, Mat_.embedding]
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [Mat_.comp_apply, Fintype.sum_unique, LinearTensor.comp_def]
    rw [LinearTensor.compLinear_tmul
      (⟨S.simpleObject (S.label X a), T.simpleObject (T.label Y b)⟩ : LinearTensor C D)
      (⟨X, Y⟩ : LinearTensor C D)
      (⟨S.simpleObject (S.label X c), T.simpleObject (T.label Y d)⟩ : LinearTensor C D)
      (S.coendInclusion X a) (T.coendInclusion Y b)
      (S.coendProjection X c) (T.coendProjection Y d)]
    by_cases ha : a = c <;> by_cases hb : b = d
    · subst c; subst d
      simp [Mat_.id_apply, LinearTensor.id_def, FiniteSemisimpleSkeleton.coendInclusion,
        FiniteSemisimpleSkeleton.coendProjection, Category.assoc]
    · subst c
      simp [Mat_.id_apply, FiniteSemisimpleSkeleton.coendInclusion,
        FiniteSemisimpleSkeleton.coendProjection, Category.assoc, hb]
    · subst d
      simp [Mat_.id_apply, FiniteSemisimpleSkeleton.coendInclusion,
        FiniteSemisimpleSkeleton.coendProjection, Category.assoc, ha]
    · simp [Mat_.id_apply, FiniteSemisimpleSkeleton.coendInclusion,
        FiniteSemisimpleSkeleton.coendProjection, Category.assoc, ha, hb]

end DeligneProduct
end Paper18.Category
