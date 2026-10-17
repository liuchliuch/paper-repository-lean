import Paper18.Category.ModuleBalancingFunctor
import Paper18.Category.SphericalComparisonPositive
import Paper18.Category.ENOPseudounitaryBounds

/-!
# Positivity descends along actual dominant pivotal tensor functors

The universal bound on the modulus of a pivotal dimension is saturated on
every image of a positive object. The actual simple decomposition and
dominance force saturation with positive sign on each target simple.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u v₁ u₁ w w₁
namespace Paper18.Category.PreservesPivotal
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {D : Type u₁} [Category.{v₁} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [RightRigidCategory D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {F : C ⥤ D} [F.Monoidal] [F.Additive] [F.Linear ℂ]
  {J : PivotalStructure C} {K : PivotalStructure D}
  (h : PreservesPivotal F J K)
include h

/-- Scalar dimensions are preserved by an actual complex-linear pivotal
tensor functor, after its actual unit comparison. -/
lemma rightDim_scalar (X : C) : K.rightDim (F.obj X) = J.rightDim X := by
  have hd := h.rightDimension X
  have hs := unitScalarEquiv_spec (C := C) (J.rightDimension X)
  change J.rightDim X • 𝟙 (𝟙_ C) = J.rightDimension X at hs
  rw [← hs] at hd
  simp only [Functor.map_smul, CategoryTheory.Functor.map_id, Linear.comp_smul,
    Linear.smul_comp, id_comp, Functor.Monoidal.ε_η] at hd
  have hh := congrArg (unitScalarEquiv (C := D)) hd
  simpa only [unitScalarEquiv_smul_id] using hh.symm

variable {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {κ : Type w₁} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)
include S T

/-- Positivity of actual categorical dimensions descends under a dominant
actual pivotal tensor functor. No positive structure on the target is assumed. -/
theorem positive_of_dominant
    (hdom : ∀ Y : D, Simple Y → ∃ X : C, Nonempty (Retract Y (F.obj X)))
    (pJ : J.Positive) : K.Positive := by
  have hb (i : κ) : ‖K.rightDim (T.simpleObject i)‖ ≤ T.fusionBasis.fpdim i :=
    (K.pivotalData T).norm_jdim_le_fpdim i
  have hr (i : κ) : (K.rightDim (T.simpleObject i)).re ≤ T.fusionBasis.fpdim i :=
    (Complex.re_le_norm _).trans (hb i)
  have he (X : C) :
      (∑ i, (T.multiplicity (F.obj X) i : ℝ) * (K.rightDim (T.simpleObject i)).re) =
        ∑ i, (T.multiplicity (F.obj X) i : ℝ) * T.fusionBasis.fpdim i := by
    have hh := congrArg Complex.re (K.rightDim_eq_sum_multiplicity T (F.obj X))
    rw [h.rightDim_scalar, J.rightDim_eq_fpdim S pJ] at hh
    simp only [Complex.ofReal_re, Complex.re_sum, Complex.mul_re,
      Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] at hh
    exact hh.symm.trans (S.fpdim_map T F X).symm
  have hs (i : κ) : K.rightDim (T.simpleObject i) = (T.fusionBasis.fpdim i : ℂ) := by
    obtain ⟨X, hi⟩ := hdom (T.simpleObject i) (T.simple i)
    have hm : 0 < T.multiplicity (F.obj X) i :=
      (T.multiplicity_pos_iff_retract _ i).mpr hi
    have ht := (Finset.sum_eq_sum_iff_of_le (fun k (_ : k ∈ Finset.univ) =>
      mul_le_mul_of_nonneg_left (hr k) (Nat.cast_nonneg (T.multiplicity (F.obj X) k)))).mp
        (he X) i (Finset.mem_univ i)
    have hre : (K.rightDim (T.simpleObject i)).re = T.fusionBasis.fpdim i :=
      mul_left_cancel₀ (ne_of_gt (show (0 : ℝ) < T.multiplicity (F.obj X) i by exact_mod_cast hm)) ht
    have hn := pow_le_pow_left₀ (norm_nonneg (K.rightDim (T.simpleObject i))) (hb i) 2
    rw [Complex.sq_norm, Complex.normSq_apply, hre] at hn
    have him : (K.rightDim (T.simpleObject i)).im = 0 := by
      nlinarith [sq_nonneg (K.rightDim (T.simpleObject i)).im]
    exact Complex.ext (by simpa using hre) (by simpa using him)
  intro Y hY
  letI := hY
  obtain ⟨i, ⟨e⟩⟩ := T.simple_isomorphic_representative Y
  rw [K.rightDim_iso e, hs]
  exact ⟨T.fusionBasis.fpdim_pos i, rfl⟩

end Paper18.Category.PreservesPivotal
