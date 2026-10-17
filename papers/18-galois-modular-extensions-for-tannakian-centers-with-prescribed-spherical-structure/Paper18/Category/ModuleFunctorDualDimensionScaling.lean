import Paper18.Category.ModuleFunctorDualDimensionWeight

/-! # Actual positive scaling of module functors on a connected action

Connectivity and actual module lineators force a nonzero module functor
to scale every positive common action weight by one positive constant.
The constant is an output, not a supplied dimension comparison.
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
  {κ : Type wM} [Fintype κ] [Nonempty κ] (SM : FiniteSemisimpleSkeleton M κ)
  (hconn : ∀ j k : κ, ∃ X : C, Nonempty (Retract (SM.simpleObject k) (X ⊙ₗ SM.simpleObject j)))
  (d : ι → ℝ) (r : κ → ℝ) (hr : ∀ j, 0 < r j)
  (hR : ∀ a j, ∑ k, (moduleActionCoeff SC SM a j k : ℝ) * r k = d a * r j)
  (F : M ⥤ M) [F.Additive] [F.LeftLinear C]

omit [Nonempty κ] in
include hr in
/-- An actual nonzero additive functor has a nonzero actual image weight
on at least one actual simple representative. -/
lemma moduleFunctorWeight_exists_pos (hF : (𝟙 F : F ⟶ F) ≠ 0) :
    ∃ j, 0 < moduleFunctorWeight SM F r j := by
  by_contra hn
  push_neg at hn
  apply hF
  apply natTrans_ext_simples SM F F
  intro j
  have hz : moduleFunctorWeight SM F r j = 0 :=
    le_antisymm (hn j) (moduleFunctorWeight_nonneg SM F r (fun k => (hr k).le) j)
  have ho : IsZero (F.obj (SM.simpleObject j)) :=
    (moduleObjectWeight_eq_zero_iff SM r hr _).mp hz
  change (𝟙 (F.obj (SM.simpleObject j))) = 0
  exact ho.eq_zero_of_src _

omit [Nonempty κ] in
include hconn hr hR in
/-- Strict positivity propagates to every simple by the genuine strictly
positive action matrix. -/
lemma moduleFunctorWeight_pos (hF : (𝟙 F : F ⟶ F) ≠ 0) (j : κ) :
    0 < moduleFunctorWeight SM F r j := by
  let s := moduleFunctorWeight SM F r
  have hs (k : κ) : 0 ≤ s k := moduleFunctorWeight_nonneg SM F r (fun l => (hr l).le) k
  obtain ⟨k, hk⟩ := moduleFunctorWeight_exists_pos SM r hr F hF
  have hrow : 0 < ∑ l, moduleActionMatrix SC SM j l * s l :=
    Finset.sum_pos' (fun l _ => mul_nonneg (moduleActionMatrix_pos SC SM hconn j l).le (hs l))
      ⟨k, Finset.mem_univ _, mul_pos (moduleActionMatrix_pos SC SM hconn j k) hk⟩
  have he : (∑ l, moduleActionMatrix SC SM j l * s l) = (∑ a, d a) * s j := by
    dsimp only [s]
    simp only [moduleActionMatrix, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [moduleFunctorWeight_action SC SM F d r hR]
  have hn : s j ≠ 0 := by
    intro hz
    rw [he, hz, mul_zero] at hrow
    exact (lt_irrefl _ hrow)
  exact lt_of_le_of_ne (hs j) (Ne.symm hn)

include hconn hr hR in
/-- A genuine nonzero strong module functor scales every actual object
weight by one derived positive constant. -/
theorem moduleFunctor_scales_weight (hF : (𝟙 F : F ⟶ F) ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ X : M,
      moduleObjectWeight SM r (F.obj X) = c * moduleObjectWeight SM r X := by
  obtain ⟨c, hc, hsimple⟩ := moduleAction_positive_vectors_proportional SC SM hconn d r
    (moduleFunctorWeight SM F r) hr (moduleFunctorWeight_pos SC SM hconn d r hr hR F hF) hR
    (moduleFunctorWeight_action SC SM F d r hR)
  refine ⟨c, hc, ?_⟩
  intro X
  rw [moduleObjectWeight_map SM r F]
  have hh (j : κ) : moduleObjectWeight SM r (F.obj (SM.simpleObject j)) = c * r j := hsimple j
  simp_rw [hh]
  simp only [moduleObjectWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Paper18.Category.ModuleFunctor
