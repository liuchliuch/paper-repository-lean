import Paper18.Category.RepresentationFunctionSeparable
import Paper18.Category.RepresentationRightTranslation
import Paper18.Category.TensorCharacters

/-! # Recovering a group element from an actual tensor character of Rep(G)

The character preserves the actual regular function algebra by naturality
and its tensor law. Evaluation of that algebra map at the group identity
selects a delta idempotent, and hence an actual group element.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace Paper18.Category.TannakianSignKernel
open Representation
variable {G : Type} [Group G] [Fintype G]
  (χ : 𝟭 (FDRep ℂ G) ≅ 𝟭 (FDRep ℂ G)) [NatTrans.IsMonoidal χ.hom]

def functionsLinear : (G → ℂ) →ₗ[ℂ] (G → ℂ) := (χ.hom.app functions).hom.hom

lemma functionsLinear_one : functionsLinear χ (1 : G → ℂ) = 1 := by
  have hn := χ.hom.naturality (functionsOne (G := G))
  change functionsOne ≫ χ.hom.app functions = χ.hom.app (𝟙_ (FDRep ℂ G)) ≫ functionsOne at hn
  rw [TensorAutomorphism.unit_component χ] at hn
  have h := congrArg (fun k : 𝟙_ (FDRep ℂ G) ⟶ functions => k.hom.hom (1 : ℂ)) hn
  exact h

lemma functionsLinear_mul (f g : G → ℂ) :
    functionsLinear χ (f * g) = functionsLinear χ f * functionsLinear χ g := by
  have hn := χ.hom.naturality (functionsMul (G := G))
  change functionsMul ≫ χ.hom.app functions = χ.hom.app (functions ⊗ functions) ≫ functionsMul at hn
  rw [TensorAutomorphism.tensor_component χ] at hn
  exact congrArg (fun k : ((functions (G := G)) ⊗ (functions (G := G)) : FDRep ℂ G) ⟶
    functions => k.hom.hom (f ⊗ₜ[ℂ] g)) hn

/-- Naturality and monoidality give an actual algebra homomorphism on Fun(G). -/
def functionsAlgHom : (G → ℂ) →ₐ[ℂ] (G → ℂ) where
  toFun := functionsLinear χ
  map_zero' := map_zero _
  map_one' := functionsLinear_one χ
  map_add' := map_add _
  map_mul' := functionsLinear_mul χ
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [map_smul, functionsLinear_one]

def evaluationCharacter : (G → ℂ) →ₐ[ℂ] ℂ :=
  (Pi.evalAlgHom ℂ (fun _ : G => ℂ) 1).comp (functionsAlgHom χ)

@[simp] lemma evaluationCharacter_apply (f : G → ℂ) :
    evaluationCharacter χ f = functionsLinear χ f 1 := rfl

lemma sum_delta : (∑ g : G, delta g) = (1 : G → ℂ) := by
  funext x
  simp [Finset.sum_apply, delta_apply]

lemma exists_delta_eval_one : ∃ z : G, evaluationCharacter χ (delta z) = 1 := by
  have hi (z : G) : evaluationCharacter χ (delta z) = 0 ∨
      evaluationCharacter χ (delta z) = 1 := by
    have hd : delta z * delta z = delta z := by
      funext x
      simp [delta_apply]
    have he := congrArg (evaluationCharacter χ) hd
    rw [map_mul] at he
    have hz : evaluationCharacter χ (delta z) * (evaluationCharacter χ (delta z) - 1) = 0 := by
      rw [mul_sub, mul_one, he, sub_self]
    exact (mul_eq_zero.mp hz).imp_right sub_eq_zero.mp
  by_contra hn
  have hz (z : G) : evaluationCharacter χ (delta z) = 0 :=
    (hi z).resolve_right (fun h => hn ⟨z, h⟩)
  have he := congrArg (evaluationCharacter χ) (sum_delta (G := G))
  simpa only [map_sum, hz, Finset.sum_const_zero, map_one, zero_ne_one] using he

def evaluationPoint : G := Classical.choose (exists_delta_eval_one χ)

lemma evaluationPoint_spec : evaluationCharacter χ (delta (evaluationPoint χ)) = 1 :=
  Classical.choose_spec (exists_delta_eval_one χ)

/-- A unital character of the actual function algebra is evaluation at the
actual point selected by its delta idempotents. -/
lemma evaluationCharacter_eq (f : G → ℂ) :
    evaluationCharacter χ f = f (evaluationPoint χ) := by
  have h : evaluationCharacter χ (f * delta (evaluationPoint χ)) =
      evaluationCharacter χ f * evaluationCharacter χ (delta (evaluationPoint χ)) :=
    map_mul (evaluationCharacter χ) f (delta (evaluationPoint χ))
  rw [mul_delta, map_smul, evaluationPoint_spec] at h
  simpa using h.symm

/-- Equivariance upgrades evaluation at one point to actual right translation
on the entire regular function representation. -/
lemma functionsLinear_apply (f : G → ℂ) (x : G) :
    functionsLinear χ f x = f (x * evaluationPoint χ) := by
  have h := congrArg (fun k : FGModuleCat.of ℂ (G → ℂ) ⟶ FGModuleCat.of ℂ (G → ℂ) => k.hom f 1)
    ((χ.hom.app functions).comm x⁻¹)
  change functionsLinear χ (functionAction x⁻¹ f) 1 =
    functionAction x⁻¹ (functionsLinear χ f) 1 at h
  calc
    _ = evaluationCharacter χ (functionAction x⁻¹ f) := by
      simpa only [functionAction_apply, inv_inv, mul_one] using h.symm
    _ = _ := by rw [evaluationCharacter_eq]; simp

end Paper18.Category.TannakianSignKernel
