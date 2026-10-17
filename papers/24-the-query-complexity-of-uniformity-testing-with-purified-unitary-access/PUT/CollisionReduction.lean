import PUT.Collision
import PUT.ReflectionOracle
import PUT.SourceTargets

/-!
# The distribution part of the collision reduction, equation (22)

The distribution is induced by an actual function, including the identity
on tail labels. The four-to-one promise is a statement about its finite
fibres, rather than an assumed value of its total variation distance.
-/
noncomputable section
namespace PUT.CollisionReduction
open PUT.QueryModel PUT.SourceTargets

/-- Number of preimages of an output label. -/
def fiberCount {n : ℕ} (f : Fin n → Fin n) (y : Fin n) : ℕ :=
  (Finset.univ.filter fun x => f x = y).card

/-- The outcome law of a uniform input passed through `f`. -/
def law {n : ℕ} (f : Fin n → Fin n) (y : Fin n) : ℝ := fiberCount f y / (n : ℝ)

theorem fiberCount_sum {n : ℕ} (f : Fin n → Fin n) : ∑ y, fiberCount f y = n := by
  simpa [fiberCount] using Finset.sum_fiberwise (M := ℕ) Finset.univ f (fun _ => 1)

theorem fiberCount_eq_sum {n : ℕ} (f : Fin n → Fin n) (y : Fin n) :
    fiberCount f y = ∑ x, if f x = y then 1 else 0 := by
  simp [fiberCount, Finset.sum_boole]

theorem law_nonnegative {n : ℕ} (f : Fin n → Fin n) (y : Fin n) : 0 ≤ law f y := by
  unfold law; positivity

theorem law_total {n : ℕ} (hn : 0 < n) (f : Fin n → Fin n) : ∑ y, law f y = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  simp only [law, ← Finset.sum_div, ← Nat.cast_sum, fiberCount_sum]
  exact div_self hn0

theorem fiberCount_injective {n : ℕ} (f : Fin n → Fin n) (hf : Function.Injective f)
    (y : Fin n) : fiberCount f y = 1 := by
  obtain ⟨x, rfl⟩ := (Finite.surjective_of_injective hf) y
  simp only [fiberCount_eq_sum]
  have he : ∀ z, f z = f x ↔ z = x := fun _ => hf.eq_iff
  simp_rw [he]
  simp

theorem law_injective {n : ℕ} (f : Fin n → Fin n) (hf : Function.Injective f) :
    law f = uniform n := by
  funext y
  simp [law, fiberCount_injective f hf, uniform]

/-- Extend a collision function by the identity on all tail inputs. -/
def extend {D R : ℕ} (f : Fin D → Fin D) : Fin (D + R) → Fin (D + R) :=
  Fin.addCases (fun x => Fin.castAdd R (f x)) (Fin.natAdd D)

@[simp] theorem extend_left {D R : ℕ} (f : Fin D → Fin D) (x : Fin D) :
    extend (R := R) f (Fin.castAdd R x) = Fin.castAdd R (f x) := by simp [extend]

@[simp] theorem extend_right {D R : ℕ} (f : Fin D → Fin D) (x : Fin R) :
    extend f (Fin.natAdd D x) = Fin.natAdd D x := by simp [extend]

@[simp] theorem fiberCount_extend_left {D R : ℕ} (f : Fin D → Fin D) (y : Fin D) :
    fiberCount (extend (R := R) f) (Fin.castAdd R y) = fiberCount f y := by
  have hne (x : Fin R) : ¬Fin.natAdd D x = Fin.castAdd R y := by
    intro h
    have hv := congrArg Fin.val h
    change D + x.val = y.val at hv
    omega
  rw [fiberCount_eq_sum, Fin.sum_univ_add, fiberCount_eq_sum]
  simp [hne]

@[simp] theorem fiberCount_extend_right {D R : ℕ} (f : Fin D → Fin D) (y : Fin R) :
    fiberCount (extend f) (Fin.natAdd D y) = 1 := by
  have hne (x : Fin D) : ¬Fin.castAdd R (f x) = Fin.natAdd D y := by
    intro h
    have hv := congrArg Fin.val h
    change (f x).val = D + y.val at hv
    omega
  rw [fiberCount_eq_sum, Fin.sum_univ_add]
  simp [hne]

/-- The collision problem's actual four-to-one promise. -/
def FourToOne {D : ℕ} (f : Fin D → Fin D) : Prop :=
  ∀ y, fiberCount f y = 0 ∨ fiberCount f y = 4

/-- Uniformity on all labels, including tail labels, in the injective case. -/
theorem extend_law_injective {D R : ℕ} (f : Fin D → Fin D) (hf : Function.Injective f) :
    law (extend (R := R) f) = uniform (D + R) := by
  funext y
  refine Fin.addCases (fun i => ?_) (fun i => ?_) y
  · simp [law, fiberCount_injective f hf, uniform]
  · simp [law, uniform]

/-- Equation (22)'s alternative has exactly the claimed distance. -/
theorem fourToOne_tv {D R : ℕ} (hn : 0 < D + R) (f : Fin D → Fin D)
    (hf : FourToOne f) :
    tvDist (law (extend (R := R) f)) (uniform (D + R)) =
      (3 * D : ℝ) / (4 * (D + R)) := by
  have hn' : (0 : ℝ) < D + R := by exact_mod_cast hn
  have hsum : (∑ y, (fiberCount f y : ℝ)) = D := by exact_mod_cast fiberCount_sum f
  have ha (y : Fin D) : |(fiberCount f y : ℝ) - 1| = 1 + (fiberCount f y : ℝ) / 2 := by
    rcases hf y with h | h <;> simp [h] <;> norm_num
  have hleft (y : Fin D) :
      |law (extend (R := R) f) (Fin.castAdd R y) - uniform (D + R) (Fin.castAdd R y)| =
        (1 + (fiberCount f y : ℝ) / 2) / (D + R) := by
    simp only [law, fiberCount_extend_left, uniform, ← sub_div, abs_div, Nat.cast_add,
      abs_of_pos hn', ha]
  have hright (y : Fin R) :
      |law (extend f) (Fin.natAdd D y) - uniform (D + R) (Fin.natAdd D y)| = 0 := by
    simp [law, uniform]
  unfold tvDist
  rw [Fin.sum_univ_add]
  simp_rw [hleft, hright]
  simp only [Finset.sum_const_zero, add_zero, ← Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, hsum]
  field_simp
  <;> ring

/-- Applying the paper's integer rounding gives a strict promised alternative. -/
theorem rounded_fourToOne_tv {d : ℕ} (hd : 8 ≤ d)
    (f : Fin (collD d) → Fin (collD d)) (hf : FourToOne f) :
    (1 / 2 : ℝ) <
      tvDist (law (extend (R := d - collD d) f)) (uniform (collD d + (d - collD d))) := by
  have hD : collD d ≤ d := by unfold collD; omega
  have he : collD d + (d - collD d) = d := Nat.add_sub_of_le hD
  rw [fourToOne_tv (by omega) f hf]
  have her : (collD d : ℝ) + (d - collD d : ℕ) = d := by exact_mod_cast he
  simpa [her, collTV] using collTV_gt_half d hd

/-- A concrete point-mass probability vector. -/
def pointMass {d : ℕ} (i : Fin d) : Fin d → ℝ := fun j => if j = i then 1 else 0

theorem pointMass_total {d : ℕ} (i : Fin d) : ∑ j, pointMass i j = 1 := by
  simp [pointMass]

theorem pointMass_tv {d : ℕ} (hd : 1 ≤ d) (i : Fin d) :
    tvDist (pointMass i) (uniform d) = 1 - 1 / (d : ℝ) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hi : (1 : ℝ) / d ≤ 1 := (div_le_one hd0).2 (by exact_mod_cast hd)
  have hterm (j : Fin d) : |pointMass i j - uniform d j| =
      if j = i then 1 - 1 / (d : ℝ) else 1 / (d : ℝ) := by
    by_cases h : j = i
    · rw [show pointMass i j = 1 by simp [pointMass, h], uniform_apply, abs_of_nonneg (sub_nonneg.mpr hi)]
      simp [h]
    · simp [pointMass, uniform, h, abs_of_nonneg (le_of_lt hd0)]
  unfold tvDist
  simp_rw [hterm]
  rw [Finset.sum_ite]
  simp only [Finset.filter_eq', Finset.mem_univ, ↓reduceIte, Finset.sum_singleton,
    Finset.sum_const, Finset.card_singleton, nsmul_eq_mul]
  have hcard : (Finset.univ.filter fun j : Fin d => ¬j = i).card = d - 1 := by
    have he : (Finset.univ.filter fun j : Fin d => ¬j = i) = Finset.univ.erase i := by
      ext j; simp [ne_eq]
    rw [he, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp
  rw [hcard]
  have hcast : ((d - 1 : ℕ) : ℝ) = d - 1 := by rw [Nat.cast_sub hd]; norm_num
  rw [hcast]
  field_simp
  ring

/-- Concrete valid uniform/point-mass oracles close the small-dimension
zero-query loophole in the actual controlled circuit model. -/
theorem tester_needs_query {d : ℕ} (hd : 2 ≤ d) {ε : ℝ} (hε : ε < 1/2)
    (C : TesterFamily d) (Q : ℕ) (hC : C.Tests ε Q) : 1 ≤ Q := by
  by_contra hQ
  have hzero : Q = 0 := by omega
  subst Q
  let i : Fin d := ⟨0, by omega⟩
  let U := PUT.ReflectionOracle.preparationOracle (uniform d) (fun _ _ => 0)
    (by norm_num : 0 < 1) (fun _ => by simp [uniform])
    (by simp [uniform, Finset.sum_const]; field_simp)
  let V := PUT.ReflectionOracle.preparationOracle (pointMass i) (fun _ _ => 0)
    (by norm_num : 0 < 1) (fun j => by dsimp [pointMass]; split_ifs <;> norm_num)
    (pointMass_total i)
  have hu := (hC 1 U).1 (fun _ => rfl)
  have hv := (hC 1 V).2 (by
    change ε < tvDist (pointMass i) (uniform d)
    rw [pointMass_tv (by omega) i]
    exact lt_of_lt_of_le hε (point_mass_tv d hd))
  rw [(C.circuit 1).zero_queries (C.oracle V) (C.oracle U)] at hv
  linarith

end PUT.CollisionReduction
