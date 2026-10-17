import PUT.CollisionReduction

/-!
# Full compute/copy/uncompute collision preparation

All gates below are permutations of a finite orthonormal basis or a known
reflection. In particular, their action away from the designated input is
specified. The function-query compilation at the end uses legal dummy inputs
and works on every source basis state, including the unused flag state.
-/
noncomputable section
open scoped InnerProductSpace
namespace PUT.CollisionCircuit
open PUT.QueryModel PUT.ReflectionOracle PUT.CollisionReduction

/-- Quantize a reversible map of an orthonormal basis. -/
def lift {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) :
    EuclideanSpace ℂ A ≃ₗᵢ[ℂ] EuclideanSpace ℂ B :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

@[simp] theorem lift_single {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (e : A ≃ B) (a : A) (c : ℂ) :
    lift e (EuclideanSpace.single a c) = EuclideanSpace.single (e a) c := by
  ext b
  simp [lift, EuclideanSpace.single_apply, Equiv.symm_apply_eq]

theorem lift_trans {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (e : A ≃ B) (f : B ≃ C) : lift (e.trans f) = (lift e).trans (lift f) := by
  ext x b
  rfl

@[simp] theorem eval_sum {A I : Type*} [Fintype A] (s : Finset I)
    (v : I → EuclideanSpace ℂ A) (a : A) : (∑ i ∈ s, v i) a = ∑ i ∈ s, v i a := by
  exact map_sum (PiLp.projₗ (𝕜 := ℂ) 2 (fun _ : A => ℂ) a) v s

variable {D R : ℕ} [NeZero D]

instance positiveTotal : NeZero (D + R) := ⟨by have := NeZero.ne D; omega⟩

/-- Label, retained input, and scratch function value, plus a disjoint flag. -/
abbrev Basis (D R : ℕ) := Unit ⊕ (Fin (D+R) × (Fin (D+R) × Fin D))
abbrev Space (D R : ℕ) := EuclideanSpace ℂ (Basis D R)

/-- Legal address used for every input, including tail labels. -/
def dummy (x : Fin (D+R)) : Fin D := if h : x.val < D then ⟨x.val,h⟩ else 0

/-- The known copying rule, independent of the unknown function. -/
def value (x : Fin (D+R)) (z : Fin D) : Fin (D+R) :=
  if x.val < D then Fin.castAdd R z else x

/-- A padded evaluation of `f`, with a fixed legal dummy address on the tail. -/
def evaluate (f : Fin D → Fin D) : Equiv.Perm (Basis D R) where
  toFun := Sum.map id (fun ⟨o,x,z⟩ => (o,x,z + f (dummy x)))
  invFun := Sum.map id (fun ⟨o,x,z⟩ => (o,x,z - f (dummy x)))
  left_inv := by intro b; rcases b with u | ⟨o,x,z⟩ <;> simp
  right_inv := by intro b; rcases b with u | ⟨o,x,z⟩ <;> simp

/-- Copy the chosen label to the output, leaving the source and scratch. -/
def copy : Equiv.Perm (Basis D R) where
  toFun := Sum.map id (fun ⟨o,x,z⟩ => (o + value x z,x,z))
  invFun := Sum.map id (fun ⟨o,x,z⟩ => (o - value x z,x,z))
  left_inv := by intro b; rcases b with u | ⟨o,x,z⟩ <;> simp
  right_inv := by intro b; rcases b with u | ⟨o,x,z⟩ <;> simp

/-- The fully defined reversible compute/copy/uncompute operation. -/
def computeCopyUncompute (f : Fin D → Fin D) : Equiv.Perm (Basis D R) :=
  ((evaluate f).trans copy).trans (evaluate f).symm

@[simp] theorem value_evaluated (f : Fin D → Fin D) (x : Fin (D+R)) :
    value x (f (dummy x)) = extend (R := R) f x := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) x
  · simp [value, dummy, i.isLt]
  · have h : ¬ D + i.val < D := by omega
    simp [value, dummy, h]

/-- The scratch is exactly clean for every input, including tail labels. -/
theorem computeCopyUncompute_clean (f : Fin D → Fin D) (x : Fin (D+R)) :
    computeCopyUncompute f (Sum.inr (0,x,0)) = Sum.inr (extend f x,x,0) := by
  simp [computeCopyUncompute, evaluate, copy, Equiv.trans_apply]

/-- Oracle-independent normalized uniform seed. -/
def seed : Space D R :=
  ∑ x : Fin (D+R), EuclideanSpace.single (Sum.inr (0,x,0))
    ((Real.sqrt (D+R : ℕ) : ℂ)⁻¹)

def bot : Space D R := EuclideanSpace.single (Sum.inl ()) 1

@[simp] theorem seed_bot : seed (D := D) (R := R) (Sum.inl ()) = 0 := by
  simp [seed, EuclideanSpace.single_apply]

@[simp] theorem seed_output (o x : Fin (D+R)) (z : Fin D) :
    seed (D := D) (R := R) (Sum.inr (o,x,z)) =
      if o = 0 ∧ z = 0 then ((Real.sqrt (D+R : ℕ) : ℂ)⁻¹) else 0 := by
  classical
  simp only [seed, eval_sum, EuclideanSpace.single_apply, Sum.inr.injEq,
    Prod.mk.injEq]
  by_cases ho : o = 0 <;> by_cases hz : z = 0 <;> simp [ho, hz, eq_comm]

theorem seed_norm : ‖seed (D := D) (R := R)‖ = 1 := by
  have hn : (0 : ℝ) < (D+R : ℕ) := by exact_mod_cast (NeZero.pos (D+R))
  have hterm (o x : Fin (D+R)) (z : Fin D) :
      ‖seed (D := D) (R := R) (Sum.inr (o,x,z))‖ ^ 2 =
        if o = 0 then if z = 0 then (1 : ℝ) / (D+R : ℕ) else 0 else 0 := by
    rw [seed_output]
    by_cases ho : o = 0 <;> by_cases hz : z = 0 <;>
      simp [ho, hz, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (show (0 : ℝ) ≤ D + R by positivity)]
  have h : ‖seed (D := D) (R := R)‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Fintype.sum_sum_type, Fintype.sum_unique, seed_bot, norm_zero, zero_pow,
      OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, zero_add, Fintype.sum_prod_type,
      hterm]
    have hn0 : (D : ℝ) + R ≠ 0 := by exact_mod_cast (NeZero.ne (D+R))
    simp [Finset.sum_ite_irrel, hn0]
  nlinarith [norm_nonneg (seed (D := D) (R := R))]

/-- A known full unitary mapping the flag input to the uniform seed.
The one-dimensional reflection proves existence constructively. -/
def knownPreparation : Space D R ≃ₗᵢ[ℂ] Space D R :=
  (ℂ ∙ (bot (D := D) (R := R) + seed)).reflection

theorem knownPreparation_prepares : knownPreparation (bot (D := D) (R := R)) = seed := by
  have hb : ‖bot (D := D) (R := R)‖ = 1 := by simp [bot]
  have hbs : ⟪bot (D := D) (R := R), seed⟫_ℂ = 0 := by
    simp [bot, EuclideanSpace.inner_single_left]
  have hsb : ⟪seed (D := D) (R := R), bot⟫_ℂ = 0 := by
    simp [bot, EuclideanSpace.inner_single_right]
  have hnorm : ‖bot (D := D) (R := R) + seed‖ ^ 2 = (2 : ℝ) := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hbs
    rw [hb, seed_norm] at h
    nlinarith
  rw [knownPreparation, Submodule.reflection_singleton_apply]
  rw [inner_add_left, inner_self_eq_norm_sq_to_K, hb, hsb]
  norm_num only [Complex.ofReal_one, one_pow, add_zero]
  norm_num [← Complex.ofReal_pow, hnorm, two_smul]
  module

/-- The full preparation unitary, with no unspecified extension. -/
def unitary (f : Fin D → Fin D) : Space D R ≃ₗᵢ[ℂ] Space D R :=
  knownPreparation.trans (lift (computeCopyUncompute f))

/-- Equation (22), including clean scratch, for the complete circuit. -/
theorem unitary_prepares (f : Fin D → Fin D) :
    unitary (R := R) f bot =
      ∑ x : Fin (D+R), EuclideanSpace.single (Sum.inr (extend f x,x,0))
        ((Real.sqrt (D+R : ℕ) : ℂ)⁻¹) := by
  simp only [unitary, LinearIsometryEquiv.trans_apply, knownPreparation_prepares, seed,
    map_sum, lift_single, computeCopyUncompute_clean]

/-- Reshape the retained input and clean scratch into the model's garbage. -/
def reshape : Basis D R ≃ Unit ⊕ (Fin (D+R) × Fin ((D+R)*D)) :=
  Equiv.sumCongr (Equiv.refl Unit) (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv)

/-- This circuit has exactly the physical shape used by `PreparationOracle`. -/
def physicalUnitary (f : Fin D → Fin D) :
    PurificationSpace (D+R) ((D+R)*D) ≃ₗᵢ[ℂ] PurificationSpace (D+R) ((D+R)*D) :=
  ((lift reshape).symm.trans (unitary f)).trans (lift reshape)

theorem physicalUnitary_prepares (f : Fin D → Fin D) :
    physicalUnitary (R := R) f (zeroState (D+R) ((D+R)*D)) =
      ∑ x : Fin (D+R), EuclideanSpace.single
        (Sum.inr (extend f x,finProdFinEquiv (x,(0 : Fin D))))
        ((Real.sqrt (D+R : ℕ) : ℂ)⁻¹) := by
  have hb : (lift (reshape (D := D) (R := R))).symm
      (zeroState (D+R) ((D+R)*D)) = bot := by
    rw [show (lift (reshape (D := D) (R := R))).symm = lift (reshape (D := D) (R := R)).symm from
      LinearIsometryEquiv.piLpCongrLeft_symm _]
    change lift (reshape (D := D) (R := R)).symm (EuclideanSpace.single (Sum.inl ()) 1) = _
    rw [lift_single]
    rfl
  simp only [physicalUnitary, LinearIsometryEquiv.trans_apply, hb, unitary_prepares,
    map_sum, lift_single]
  rfl

/-! ## Turning the circuit into a valid preparation oracle -/

def outputSlice {d M : ℕ} (U : PurificationSpace d M ≃ₗᵢ[ℂ] PurificationSpace d M)
    (i : Fin d) : EuclideanSpace ℂ (Fin M) :=
  WithLp.toLp 2 (fun j => U (zeroState d M) (Sum.inr (i,j)))

def sliceGarbage {d M : ℕ} [NeZero M]
    (U : PurificationSpace d M ≃ₗᵢ[ℂ] PurificationSpace d M) (i : Fin d) :
    EuclideanSpace ℂ (Fin M) :=
  if ‖outputSlice U i‖ = 0 then EuclideanSpace.single 0 1 else
    ((‖outputSlice U i‖ : ℂ)⁻¹) • outputSlice U i

theorem sliceGarbage_norm {d M : ℕ} [NeZero M]
    (U : PurificationSpace d M ≃ₗᵢ[ℂ] PurificationSpace d M) (i : Fin d) :
    ‖sliceGarbage U i‖ = 1 := by
  unfold sliceGarbage
  split_ifs with h
  · simp
  · rw [norm_smul]
    simp [norm_inv, Complex.norm_real, abs_of_nonneg (norm_nonneg _), h]

theorem sliceGarbage_factor {d M : ℕ} [NeZero M]
    (U : PurificationSpace d M ≃ₗᵢ[ℂ] PurificationSpace d M) (i : Fin d) (j : Fin M) :
    U (zeroState d M) (Sum.inr (i,j)) =
      (Real.sqrt (‖outputSlice U i‖ ^ 2) : ℂ) * sliceGarbage U i j := by
  rw [Real.sqrt_sq (norm_nonneg _)]
  unfold sliceGarbage
  split_ifs with h
  · have hz : outputSlice U i = 0 := norm_eq_zero.mp h
    have hj := congrArg (fun v : EuclideanSpace ℂ (Fin M) => v j) hz
    simp only [outputSlice, PiLp.toLp_apply, PiLp.zero_apply] at hj
    simp [h, hj]
  · have hc : (‖outputSlice U i‖ : ℂ) ≠ 0 := by exact_mod_cast h
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [mul_inv_cancel_left₀ hc]
    rfl

/-- Every actual unitary with no flag amplitude defines normalized conditional
states, including its zero-probability labels. -/
def ofUnitary {d M : ℕ} [NeZero M]
    (U : PurificationSpace d M ≃ₗᵢ[ℂ] PurificationSpace d M)
    (hbot : U (zeroState d M) (Sum.inl ()) = 0) : PreparationOracle d M where
  unitary := U
  probability := fun i => ‖outputSlice U i‖ ^ 2
  nonnegative := fun _ => sq_nonneg _
  total := by
    have hn : ‖U (zeroState d M)‖ = 1 := by simp [zeroState]
    have h := EuclideanSpace.norm_sq_eq (U (zeroState d M))
    rw [hn] at h
    simp only [Fintype.sum_sum_type, Fintype.sum_unique, hbot, norm_zero, zero_pow,
      OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, zero_add, Fintype.sum_prod_type] at h
    simp_rw [EuclideanSpace.norm_sq_eq, outputSlice, PiLp.toLp_apply]
    simpa using h.symm
  garbage := sliceGarbage U
  garbage_norm := sliceGarbage_norm U
  preparation_bot := hbot
  preparation_output := sliceGarbage_factor U

/-- The actual circuit amplitude at an arbitrary physical basis state. -/
theorem physicalUnitary_amplitude (f : Fin D → Fin D) (i x : Fin (D+R)) (z : Fin D) :
    physicalUnitary (R := R) f (zeroState (D+R) ((D+R)*D))
      (Sum.inr (i,finProdFinEquiv (x,z))) =
        if i = extend f x ∧ z = 0 then ((Real.sqrt (D+R : ℕ) : ℂ)⁻¹) else 0 := by
  rw [physicalUnitary_prepares, eval_sum]
  simp only [EuclideanSpace.single_apply, Sum.inr.injEq, Prod.mk.injEq,
    Equiv.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases hz : z = 0
  · subst z
    simp only [and_true]
    have he (y : Fin (D+R)) : (i = extend f y ∧ x = y) ↔ (y = x ∧ i = extend f x) := by
      constructor
      · rintro ⟨h₁,h₂⟩; subst y; exact ⟨rfl,h₁⟩
      · rintro ⟨h₁,h₂⟩; subst y; exact ⟨h₂,rfl⟩
    simp_rw [he, ite_and]
    simp
  · simp [hz]

theorem physicalUnitary_bot (f : Fin D → Fin D) :
    physicalUnitary (R := R) f (zeroState (D+R) ((D+R)*D)) (Sum.inl ()) = 0 := by
  rw [physicalUnitary_prepares, eval_sum]
  simp [EuclideanSpace.single_apply]

instance positiveGarbage : NeZero ((D+R)*D) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩

/-- The full circuit, now with its normalized conditional garbage. -/
def preparationOracle (f : Fin D → Fin D) : PreparationOracle (D+R) ((D+R)*D) :=
  ofUnitary (physicalUnitary f) (physicalUnitary_bot f)

/-- The circuit's Born law is the function-induced distribution, not a
separately postulated probability vector. -/
theorem preparationOracle_law (f : Fin D → Fin D) :
    (preparationOracle (R := R) f).probability = law (extend f) := by
  have hn : (0 : ℝ) < D + R := by exact_mod_cast (NeZero.pos (D+R))
  funext i
  change ‖outputSlice (physicalUnitary f) i‖ ^ 2 = _
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ j : Fin ((D+R)*D),
    ‖physicalUnitary f (zeroState (D+R) ((D+R)*D)) (Sum.inr (i,j))‖ ^ 2) = _
  rw [← finProdFinEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, physicalUnitary_amplitude]
  have hterm (x : Fin (D+R)) (z : Fin D) :
      ‖if i = extend f x ∧ z = 0 then ((Real.sqrt (D+R : ℕ) : ℂ)⁻¹) else 0‖ ^ 2 =
        if z = 0 then if extend f x = i then (1 : ℝ) / (D+R) else 0 else 0 := by
    have he : (extend f x = i) = (i = extend f x) := propext eq_comm
    simp only [he]
    by_cases hz : z = 0 <;> by_cases hi : i = extend f x <;>
      simp [hz, hi, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (le_of_lt hn)]
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [law, fiberCount_eq_sum, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    Finset.sum_div, ite_div, zero_div, Nat.cast_add]

end PUT.CollisionCircuit
