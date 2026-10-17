import Paper18.Category.ModuleFunctorDualDimensionFunctor

/-! # Positive additive weights on actual module objects -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators MonoidalLeftAction
universe v u w
namespace Paper18.Category.ModuleFunctor
variable {M : Type u} [Category.{v} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  {κ : Type w} [Fintype κ] (SM : FiniteSemisimpleSkeleton M κ)
  (r : κ → ℝ)

/-- An actual additive object weight, computed from actual multiplicities. -/
def moduleObjectWeight (X : M) : ℝ := ∑ j, (SM.multiplicity X j : ℝ) * r j

omit [HasKernels M] [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)] in
lemma moduleObjectWeight_nonneg (hr : ∀ j, 0 ≤ r j) (X : M) :
    0 ≤ moduleObjectWeight SM r X :=
  Finset.sum_nonneg (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hr j))

omit [HasKernels M] [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)] in
lemma moduleObjectWeight_iso {X Y : M} (e : X ≅ Y) :
    moduleObjectWeight SM r X = moduleObjectWeight SM r Y := by
  simp only [moduleObjectWeight, SM.multiplicity_iso e]

@[simp] lemma moduleObjectWeight_simple (j : κ) : moduleObjectWeight SM r (SM.simpleObject j) = r j := by
  simp [moduleObjectWeight, SM.multiplicity_simple]

/-- Every strictly positive actual simple weight detects exactly the zero objects. -/
lemma moduleObjectWeight_eq_zero_iff (hr : ∀ j, 0 < r j) (X : M) :
    moduleObjectWeight SM r X = 0 ↔ IsZero X := by
  constructor
  · intro h
    have hm (j : κ) : SM.multiplicity X j = 0 := by
      by_contra hn
      have hp : 0 < (SM.multiplicity X j : ℝ) * r j :=
        mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) (hr j)
      have hb := Finset.single_le_sum (s := Finset.univ)
        (f := fun k => (SM.multiplicity X k : ℝ) * r k)
        (fun k _ => mul_nonneg (Nat.cast_nonneg _) (hr k).le) (Finset.mem_univ j)
      change _ ≤ moduleObjectWeight SM r X at hb
      rw [h] at hb
      linarith
    apply (IsZero.iff_id_eq_zero X).mpr
    by_contra hn
    have hp : 0 < Module.finrank ℂ (X ⟶ X) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨𝟙 X, hn⟩
    rw [SM.finrank_hom_eq_sum] at hp
    simp [hm] at hp
  · intro h
    have hm (j : κ) : SM.multiplicity X j = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hp
      let q := SM.retractOfMultiplicityPos X j hp
      apply CategoryTheory.id_nonzero (SM.simpleObject j)
      rw [← q.retract, h.eq_zero_of_tgt q.i, zero_comp]
    simp [moduleObjectWeight, hm]

lemma moduleObjectWeight_pos (hr : ∀ j, 0 < r j) (X : M) (hX : ¬ IsZero X) :
    0 < moduleObjectWeight SM r X :=
  lt_of_le_of_ne (moduleObjectWeight_nonneg SM r (fun j => (hr j).le) X)
    (Ne.symm (fun hz => hX ((moduleObjectWeight_eq_zero_iff SM r hr X).mp hz)))

/-- The actual image decomposition computes every additive image weight. -/
lemma moduleObjectWeight_map (F : M ⥤ M) [F.Additive] (X : M) :
    moduleObjectWeight SM r (F.obj X) =
      ∑ j, (SM.multiplicity X j : ℝ) * moduleObjectWeight SM r (F.obj (SM.simpleObject j)) := by
  simp only [moduleObjectWeight, SM.multiplicity_map SM F X, Nat.cast_sum, Nat.cast_mul,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

end Paper18.Category.ModuleFunctor
