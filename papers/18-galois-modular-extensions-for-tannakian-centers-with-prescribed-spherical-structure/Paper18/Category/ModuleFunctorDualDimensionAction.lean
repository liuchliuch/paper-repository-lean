import Paper18.Category.ModuleFunctorSemisimpleComponent
import Paper18.Category.RelativeTensorDimensionBasic
import Paper18.Category.ModuleComponentConnected

/-! # Actual action matrices on finite semisimple module categories

Actual retract connectivity, together with the actual source simple
resolution, makes the finite action matrix strictly positive. Thus
positive common dimension vectors are proportional by the proved Perron
argument. No dual-category dimension identity is assumed.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators MonoidalLeftAction
universe v u vM uM w wM
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C M]
  [∀ c : C, (actionLeft M c).Additive]
  [∀ X : M, (actionRight C X).Additive]
  {ι : Type w} [Fintype ι] (SC : FiniteSemisimpleSkeleton C ι)
  {κ : Type wM} [Fintype κ] (SM : FiniteSemisimpleSkeleton M κ)

/-- The actual action multiplicity of one acting simple on a module simple. -/
def moduleActionCoeff (a : ι) (j k : κ) : ℕ :=
  SM.multiplicity (SC.simpleObject a ⊙ₗ SM.simpleObject j) k

/-- The actual finite matrix obtained by summing the simple action matrices. -/
def moduleActionMatrix : Matrix κ κ ℝ := fun j k => ∑ a, (moduleActionCoeff SC SM a j k : ℝ)

omit [HasKernels M] [∀ c : C, (actionLeft M c).Additive] in
lemma moduleActionCoeff_resolution (X : C) (j k : κ) :
    SM.multiplicity (X ⊙ₗ SM.simpleObject j) k =
      ∑ a, SC.multiplicity X a * moduleActionCoeff SC SM a j k :=
  SC.multiplicity_map SM (actionRight C (SM.simpleObject j)) X k

omit [∀ c : C, (actionLeft M c).Additive] in
/-- Actual retract connectivity yields strict positivity, rather than
requiring a numerical irreducibility or rank certificate. -/
lemma moduleActionMatrix_pos
    (hconn : ∀ j k : κ, ∃ X : C, Nonempty (Retract (SM.simpleObject k) (X ⊙ₗ SM.simpleObject j)))
    (j k : κ) : 0 < moduleActionMatrix SC SM j k := by
  obtain ⟨X, hX⟩ := hconn j k
  have hp : 0 < SM.multiplicity (X ⊙ₗ SM.simpleObject j) k :=
    (SM.multiplicity_pos_iff_retract _ k).mpr hX
  rw [moduleActionCoeff_resolution SC SM] at hp
  obtain ⟨a, _, ha⟩ := Finset.sum_pos_iff.mp hp
  have ha' : 0 < moduleActionCoeff SC SM a j k := Nat.pos_of_mul_pos_left ha
  exact Finset.sum_pos' (fun b _ => Nat.cast_nonneg _) ⟨a, Finset.mem_univ _, by exact_mod_cast ha'⟩

omit [∀ c : C, (actionLeft M c).Additive] in
/-- Positive common action eigenvectors are proportional, by the actual
strictly positive matrix supplied by retract connectivity. -/
lemma moduleAction_positive_vectors_proportional [Nonempty κ]
    (hconn : ∀ j k : κ, ∃ X : C, Nonempty (Retract (SM.simpleObject k) (X ⊙ₗ SM.simpleObject j)))
    (d : ι → ℝ) (r s : κ → ℝ) (hr : ∀ j, 0 < r j) (hs : ∀ j, 0 < s j)
    (hR : ∀ a j, ∑ k, (moduleActionCoeff SC SM a j k : ℝ) * r k = d a * r j)
    (hS : ∀ a j, ∑ k, (moduleActionCoeff SC SM a j k : ℝ) * s k = d a * s j) :
    ∃ c : ℝ, 0 < c ∧ ∀ j, s j = c * r j := by
  have rearrange (t : κ → ℝ) (j : κ) :
      ∑ k, moduleActionMatrix SC SM j k * t k =
        ∑ a, ∑ k, (moduleActionCoeff SC SM a j k : ℝ) * t k := by
    simp only [moduleActionMatrix, Finset.sum_mul]
    exact Finset.sum_comm
  have hRE (j : κ) : ∑ k, moduleActionMatrix SC SM j k * r k = (∑ a, d a) * r j := by
    rw [rearrange]
    simp_rw [hR]
    exact (Finset.sum_mul _ _ _).symm
  have hSE (j : κ) : ∑ k, moduleActionMatrix SC SM j k * s k = (∑ a, d a) * s j := by
    rw [rearrange]
    simp_rw [hS]
    exact (Finset.sum_mul _ _ _).symm
  exact posMatrix_positive_eigenspace_one_dim (moduleActionMatrix SC SM) _
    (moduleActionMatrix_pos SC SM hconn) s r hs hr hSE hRE

section Components
variable [RightRigidCategory C]

omit [Preadditive C] [Linear ℂ C] in
omit [HasKernels C] [HasFiniteBiproducts C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [∀ X : M, (actionRight C X).Additive] in
/-- Any two actual simples in one actual orbit are connected by one
actual action and an actual categorical retract. -/
lemma component_retract_connected (i : κ)
    (j k : {j : κ // ModuleComponent.property (C := C) SM i (SM.simpleObject j)}) :
    ∃ X : C, Nonempty (Retract
      ((ModuleComponent.skeleton (C := C) SM i).simpleObject k)
      (X ⊙ₗ (ModuleComponent.skeleton (C := C) SM i).simpleObject j)) := by
  have hj := (ModuleComponent.property_simple_iff SM i j.val).mp j.property
  have hk := (ModuleComponent.property_simple_iff SM i k.val).mp k.property
  have hjk := ModuleComponent.sameComponent_trans SM (ModuleComponent.sameComponent_symm SM hj) hk
  obtain ⟨X, ⟨r⟩⟩ := (ModuleComponent.sameComponent_iff_simpleStep SM j.val k.val).mp hjk
  exact ⟨X, ⟨⟨r.i, r.r, r.retract⟩⟩⟩

/-- Strict positivity for the actual action matrix of an actual orbit. -/
lemma componentActionMatrix_pos (i : κ)
    (j k : {j : κ // ModuleComponent.property (C := C) SM i (SM.simpleObject j)}) :
    0 < moduleActionMatrix SC (ModuleComponent.skeleton (C := C) SM i) j k := by
  letI := ModuleComponent.hasKernels (C := C) SM i
  exact moduleActionMatrix_pos SC (ModuleComponent.skeleton SM i)
    (component_retract_connected SM i) j k

end Components
end Paper18.Category.ModuleFunctor
