import Paper20.PresentedHecke
import Paper20.TableauFullTwist

namespace Paper20.Seminormal
open Paper20.YoungShapes
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

section Field
variable {F : Type*} [Field F]

/-- Standard generator indexing agrees with the source's r-1 adjacent
Hecke generators on the actual r-cell tableau space. -/
def adjacentGenerator (v : F) {n : ℕ} {μ : Shape n} (i : Fin (n-1)) :
    (StandardFilling μ → F) →ₗ[F] (StandardFilling μ → F) :=
  tableauLinear v ⟨i.val,by omega⟩ ⟨i.val+1,by omega⟩ rfl

lemma adjacentGenerator_quadratic (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} {μ : Shape n} (i : Fin (n-1)) :
    adjacentGenerator (μ:=μ) v i^2=(v-v⁻¹) • adjacentGenerator v i+1 :=
  tableauLinear_quadratic v hv hp _ _ rfl

lemma adjacentGenerator_braid (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} {μ : Shape n} (i j : Fin (n-1)) (h : j.val=i.val+1) :
    adjacentGenerator (μ:=μ) v i*adjacentGenerator v j*adjacentGenerator v i=
      adjacentGenerator v j*adjacentGenerator v i*adjacentGenerator v j := by
  have he : (⟨i.val+1,by omega⟩:Fin n)=⟨j.val,by omega⟩ := Fin.ext h.symm
  have hT : tableauLinear (μ:=μ) v ⟨i.val,by omega⟩ ⟨i.val+1,by omega⟩ rfl=
      tableauLinear (μ:=μ) v ⟨i.val,by omega⟩ ⟨j.val,by omega⟩ h := by congr 1
  simp only [adjacentGenerator]
  rw [hT]
  exact tableauLinear_braid v hv hp (μ:=μ) ⟨i.val,by omega⟩ ⟨j.val,by omega⟩ ⟨j.val+1,by omega⟩ h rfl

lemma adjacentGenerator_commute (v : F) {n : ℕ} {μ : Shape n} (i j : Fin (n-1))
    (h : i.val+1 < j.val ∨ j.val+1 < i.val) :
    adjacentGenerator (μ:=μ) v i*adjacentGenerator v j=adjacentGenerator v j*adjacentGenerator v i := by
  unfold adjacentGenerator
  apply tableauLinear_commute
  all_goals
    intro he
    have hv := congrArg Fin.val he
    dsimp only at hv
    omega

/-- The genuine standard-tableau representation of the honest Hecke
presentation, constructed from all proved operator relations by the actual
quotient universal property. No representation-law premise is assumed. -/
def blockRepresentation (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d)) {n : ℕ} (μ : Shape n) :
    Paper20.PresentedHecke.Presented F n (v-v⁻¹) →ₐ[F]
      ((StandardFilling μ → F) →ₗ[F] (StandardFilling μ → F)) :=
  Paper20.PresentedHecke.lift F n (v-v⁻¹) (adjacentGenerator (μ:=μ) v)
    (adjacentGenerator_quadratic v hv hp) (adjacentGenerator_braid v hv hp)
    (adjacentGenerator_commute v)

@[simp] theorem blockRepresentation_generator (v : F) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d)) {n : ℕ} (μ : Shape n) (i : Fin (n-1)) :
    blockRepresentation v hv hp μ (Paper20.PresentedHecke.generator F n (v-v⁻¹) i)=
      adjacentGenerator v i :=
  Paper20.PresentedHecke.lift_generator _ _ _ _ _ _ _ i

/-- The dimension of this actual representation space is the original
hook quotient, via the proved genuine standard-filling count. -/
theorem block_dimension {n : ℕ} (μ : Shape n) :
    Module.finrank F (StandardFilling μ → F)=dimension μ.val := by
  rw [Module.finrank_fintype_fun_eq_card,standardFilling_card]

end Field
end
end Paper20.Seminormal
