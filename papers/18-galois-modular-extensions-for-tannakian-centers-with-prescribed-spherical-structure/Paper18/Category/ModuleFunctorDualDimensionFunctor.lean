import Paper18.Category.ModuleFunctorDualDimensionAction

/-! # Actual module functors commute with the actual simple action matrices -/
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
  (F : M ⥤ M) [F.Additive] [F.LeftLinear C]

/-- The actual matrix of an additive strong module endofunctor. -/
def moduleFunctorCoeff (j k : κ) : ℕ := SM.multiplicity (F.obj (SM.simpleObject j)) k

omit [Linear ℂ C] in
omit [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [∀ X : M, (actionRight C X).Additive] in
/-- Actual module lineators and actual simple resolutions give actual
commutation of the action and functor matrices. -/
lemma moduleFunctorCoeff_comm (a : ι) (j l : κ) :
    ∑ k, moduleActionCoeff SC SM a j k * moduleFunctorCoeff SM F k l =
      ∑ k, moduleFunctorCoeff SM F j k * moduleActionCoeff SC SM a k l := by
  have h := SM.multiplicity_iso
    (Functor.LeftLinear.μₗIso F (SC.simpleObject a) (SM.simpleObject j)) l
  rw [SM.multiplicity_map SM F] at h
  change SM.multiplicity ((actionLeft M (SC.simpleObject a)).obj
    (F.obj (SM.simpleObject j))) l = _ at h
  rw [SM.multiplicity_map SM (actionLeft M (SC.simpleObject a))] at h
  exact h.symm

/-- The nonnegative weight of an actual image of a module simple. -/
def moduleFunctorWeight (r : κ → ℝ) (j : κ) : ℝ :=
  ∑ k, (moduleFunctorCoeff SM F j k : ℝ) * r k

omit [HasKernels M] [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)] [F.Additive] in
lemma moduleFunctorWeight_nonneg (r : κ → ℝ) (hr : ∀ k, 0 ≤ r k) (j : κ) :
    0 ≤ moduleFunctorWeight SM F r j :=
  Finset.sum_nonneg (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hr k))

omit [HasKernels C] [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [∀ X : M, (actionRight C X).Additive] in
omit [Linear ℂ C] in
/-- A genuine strong module functor carries every common action
weight vector to another common vector with the same eigenvalues. -/
lemma moduleFunctorWeight_action (d : ι → ℝ) (r : κ → ℝ)
    (hR : ∀ a j, ∑ k, (moduleActionCoeff SC SM a j k : ℝ) * r k = d a * r j)
    (a : ι) (j : κ) :
    ∑ k, (moduleActionCoeff SC SM a j k : ℝ) * moduleFunctorWeight SM F r k =
      d a * moduleFunctorWeight SM F r j := by
  calc
    _ = ∑ l, (∑ k, (moduleActionCoeff SC SM a j k : ℝ) *
        (moduleFunctorCoeff SM F k l : ℝ)) * r l := by
      simp only [moduleFunctorWeight, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    _ = ∑ l, (∑ k, (moduleFunctorCoeff SM F j k : ℝ) *
        (moduleActionCoeff SC SM a k l : ℝ)) * r l := by
      apply Finset.sum_congr rfl
      intro l _
      congr 1
      exact_mod_cast moduleFunctorCoeff_comm SC SM F a j l
    _ = ∑ k, (moduleFunctorCoeff SM F j k : ℝ) *
        (∑ l, (moduleActionCoeff SC SM a k l : ℝ) * r l) := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
    _ = _ := by
      simp_rw [hR]
      simp only [moduleFunctorWeight, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring

end Paper18.Category.ModuleFunctor
