import Paper12.CircuitTools

/-! Tensor products on arbitrary finite wire sets, with exact multiplication
and identification of single-wire elementary gates. -/
noncomputable section
namespace Paper12
open Matrix Complex Classical
variable {J : Type*} [Fintype J]
abbrev QMat := Matrix (Fin 2) (Fin 2) ℂ

def tensorOp (m : J → QMat) : Op J := fun i j => ∏ x, m x (i x) (j x)

@[simp] theorem tensorOp_one : tensorOp (1 : J → QMat) = 1 := by
  ext i j
  change (∏ x : J, (1 : QMat) (i x) (j x)) = _
  by_cases h : i = j
  · subst j; simp
  · have hex : ∃ x, i x ≠ j x := Function.ne_iff.mp h
    obtain ⟨x, hx⟩ := hex
    rw [Matrix.one_apply, if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [Matrix.one_apply, hx])

theorem tensorOp_mul (m n : J → QMat) : tensorOp (m * n) = tensorOp m * tensorOp n := by
  ext i j
  simp only [tensorOp, Pi.mul_apply, Matrix.mul_apply]
  simp_rw [← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun x k => m x (i x) k * n x k (j x))

def tensorHom : (J → QMat) →* Op J where
  toFun := tensorOp
  map_one' := tensorOp_one
  map_mul' := tensorOp_mul

def atWire (x : J) (u : QMat) : J → QMat := Function.update 1 x u

theorem tensor_atWire (g : OneQubit J) : tensorOp (atWire g.wire g.u) = g.unitary := by
  ext i j
  unfold tensorOp OneQubit.unitary
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ g.wire)]
  simp only [Matrix.of_apply]
  have hself : atWire g.wire g.u g.wire = g.u := by simp [atWire]
  rw [hself]
  have hother : ∀ x ∈ (Finset.univ : Finset J).erase g.wire,
      atWire g.wire g.u x = 1 := by
    intro x hx
    exact Function.update_of_ne (Finset.mem_erase.mp hx).1 _ _
  by_cases hoff : ∀ w, w ≠ g.wire → i w = j w
  · rw [if_pos hoff]
    have hp : (∏ x ∈ (Finset.univ : Finset J).erase g.wire,
        atWire g.wire g.u x (i x) (j x)) = 1 := by
      apply Finset.prod_eq_one
      intro x hx
      rw [hother x hx]
      rw [hoff x (Finset.mem_erase.mp hx).1]
      exact Matrix.one_apply_eq _
    change g.u (i g.wire) (j g.wire) * _ = _
    rw [hp, mul_one]
  · rw [if_neg hoff]
    push_neg at hoff
    obtain ⟨x, hx, hij⟩ := hoff
    have hp : (∏ x ∈ (Finset.univ : Finset J).erase g.wire,
        atWire g.wire g.u x (i x) (j x)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩)
      rw [hother x (Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩)]
      simp [Matrix.one_apply, hij]
    change g.u (i g.wire) (j g.wire) * _ = _
    rw [hp, mul_zero]

theorem atWire_commute {x y : J} (hx : x ≠ y) (u v : QMat) :
    Commute (atWire x u) (atWire y v) := by
  change atWire x u * atWire y v = atWire y v * atWire x u
  funext z
  by_cases hzx : z = x
  · subst z; simp [atWire, hx, hx.symm]
  · by_cases hzy : z = y
    · subst z; simp [atWire, hx, hx.symm]
    · simp [atWire, hzx, hzy]

theorem one_qubit_disjoint_commute (g h : OneQubit J) (hne : g.wire ≠ h.wire) :
    Commute g.unitary h.unitary := by
  rw [← tensor_atWire g, ← tensor_atWire h]
  exact (atWire_commute hne g.u h.u).map tensorHom

theorem tensorOp_adjoint (m : J → QMat) :
    (tensorOp m)ᴴ = tensorOp (fun x => (m x)ᴴ) := by
  ext i j
  simp only [Matrix.conjTranspose_apply, tensorOp, star_prod]

theorem tensorOp_isUnitary (m : J → QMat) (hm : ∀ x, (m x)ᴴ * m x = 1) :
    (tensorOp m)ᴴ * tensorOp m = 1 := by
  rw [tensorOp_adjoint, ← tensorOp_mul]
  have heq : (fun x => (m x)ᴴ) * m = 1 := by funext x; exact hm x
  rw [heq, tensorOp_one]

theorem OneQubit.unitary_isUnitary (g : OneQubit J) : g.unitaryᴴ * g.unitary = 1 := by
  rw [← tensor_atWire g]
  apply tensorOp_isUnitary
  intro x
  by_cases hx : x = g.wire
  · subst x; simpa [atWire] using g.isUnitary
  · simp [atWire, hx]

end Paper12
