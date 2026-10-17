import Paper20.FieldHeckePresentation
import Paper20.TableauPresentation

namespace Paper20.FieldHecke
open Paper20.YoungShapes Paper20.Seminormal Paper20.HeckeTraceAlgebra Paper20.HeckeMatrices
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

section Field
variable {F : Type*} [Field F]

lemma regularEquiv_generator (r : ℕ) (z : F) (i : Fin (r-1)) :
    regularEquiv r z (Paper20.PresentedHecke.generator F r z i)=
      ⟨fieldT r z i,Algebra.subset_adjoin (Set.mem_range_self i)⟩ :=
  regularRepresentation_generator r z i

lemma regularEquiv_symm_generator (r : ℕ) (z : F) (i : Fin (r-1)) :
    (regularEquiv r z).symm ⟨fieldT r z i,Algebra.subset_adjoin (Set.mem_range_self i)⟩=
      Paper20.PresentedHecke.generator F r z i := by
  apply (regularEquiv r z).injective
  rw [AlgEquiv.apply_symm_apply,regularEquiv_generator]

/-- A genuine representation of the original canonical regular Hecke
model on the actual standard Young filling space. The canonical model and
presentation are connected by the proved actual algebra isomorphism. -/
def canonicalRepresentation (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d)) {n : ℕ} (μ : Shape n) :
    fieldAlgebra n (v-v⁻¹) →ₐ[F]
      ((StandardFilling μ → F) →ₗ[F] (StandardFilling μ → F)) :=
  (blockRepresentation v hv hp μ).comp (regularEquiv n (v-v⁻¹)).symm.toAlgHom

@[simp] theorem canonicalRepresentation_generator (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d)) {n : ℕ} (μ : Shape n) (i : Fin (n-1)) :
    canonicalRepresentation v hv hp μ
      ⟨fieldT n (v-v⁻¹) i,Algebra.subset_adjoin (Set.mem_range_self i)⟩=
      adjacentGenerator (μ:=μ) v i := by
  change blockRepresentation v hv hp μ
    ((regularEquiv n (v-v⁻¹)).symm ⟨fieldT n (v-v⁻¹) i,_⟩)=_
  rw [regularEquiv_symm_generator,blockRepresentation_generator]

/-- Genuine coefficient specialization on the entire original canonical
polynomial Hecke algebra, retaining the actual concrete matrices. -/
def specializeAlgebra (n : ℕ) (z : F) : algebra n →+* fieldAlgebra n z where
  toFun A := ⟨matrixEval n z A.val,matrixEval_mem n z A.val A.property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' A B := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' A B := Subtype.ext (map_add _ _ _)

/-- The actual original Z[z] canonical Hecke algebra acts on the genuine
standard-tableau block after z=v-v^-1, with no character-formula premise. -/
def originalRepresentation (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d)) {n : ℕ} (μ : Shape n) :
    algebra n →+* ((StandardFilling μ → F) →ₗ[F] (StandardFilling μ → F)) :=
  (canonicalRepresentation v hv hp μ).toRingHom.comp (specializeAlgebra n (v-v⁻¹))

@[simp] theorem originalRepresentation_generator (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d)) {n : ℕ} (μ : Shape n) (i : Fin (n-1)) :
    originalRepresentation v hv hp μ
      ⟨T n i,Algebra.subset_adjoin (Set.mem_range_self i)⟩=adjacentGenerator (μ:=μ) v i :=
  canonicalRepresentation_generator v hv hp μ i

end Field
end
end Paper20.FieldHecke
