import ELV.Costs

/-! Actual ray-supported query vectors and their two signed Gram contributions. -/
noncomputable section
open scoped ENNReal
namespace ELV.Query
open ELV.Stabilize ELV.Model
variable {C E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma lp_summable_norm_sq (f : lp (fun _ : C => ℂ) 2) :
    Summable (fun i => ‖f i‖ ^ 2) := by
  simpa using (lp.memℓp f).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)

/-- The tensor product `f tensor u`, represented in square summable control coordinates. -/
def tensorVector (f : lp (fun _ : C => ℂ) 2) (u : E) : lp (fun _ : C => E) 2 :=
  ⟨fun i => f i • u, by
    apply memℓp_gen
    simpa [norm_smul, mul_pow, Real.rpow_two] using
      (lp_summable_norm_sq f).mul_right (‖u‖ ^ 2)⟩

/-- Both directions, with their different prescribed rays. -/
def rayVector (f g : lp (fun _ : C => ℂ) 2) (u v : E) :
    lp (fun _ : C => HilbertPair E E) 2 :=
  ⟨fun i => WithLp.toLp 2 (f i • u, g i • v), by
    apply memℓp_gen
    simpa [WithLp.prod_norm_sq_eq_of_L2, norm_smul, mul_pow, Real.rpow_two] using
      ((lp_summable_norm_sq f).mul_right (‖u‖ ^ 2)).add
        ((lp_summable_norm_sq g).mul_right (‖v‖ ^ 2))⟩

@[simp] theorem rayVector_fst (f g : lp (fun _ : C => ℂ) 2) (u v : E) (i : C) :
    (rayVector f g u v i).fst = f i • u := rfl
@[simp] theorem rayVector_snd (f g : lp (fun _ : C => ℂ) 2) (u v : E) (i : C) :
    (rayVector f g u v i).snd = g i • v := rfl

lemma scalar_tensor_inner (c d : ℂ) (u v : E) :
    inner ℂ (c • u) (d • v) = inner ℂ c d * inner ℂ u v := by
  simp only [inner_smul_left, inner_smul_right, RCLike.inner_apply]
  ring

/-- The full cross-instance Gram formula, valid for arbitrary complex garbage. -/
theorem rayVector_inner (f g f' g' : lp (fun _ : C => ℂ) 2) (u v u' v' : E) :
    inner ℂ (rayVector f g u v) (rayVector f' g' u' v') =
      inner ℂ f f' * inner ℂ u u' + inner ℂ g g' * inner ℂ v v' := by
  change (∑' i, (inner ℂ (f i • u) (f' i • u') + inner ℂ (g i • v) (g' i • v'))) = _
  simp_rw [scalar_tensor_inner]
  rw [Summable.tsum_add ((lp.summable_inner f f').mul_right _) ((lp.summable_inner g g').mul_right _),
    tsum_mul_right, tsum_mul_right]
  rfl

/-- Squared norm of the actual query vector on unit rays. -/
theorem rayVector_norm_sq (f g : lp (fun _ : C => ℂ) 2) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    ‖rayVector f g u v‖ ^ 2 = ‖f‖ ^ 2 + ‖g‖ ^ 2 := by
  have hi := rayVector_inner f g f g u v u v
  have hr := congrArg Complex.re hi
  simpa [inner_self_eq_norm_sq_to_K, hu, hv, ← Complex.ofReal_pow] using hr

variable {n : ℕ} [NeZero n]

@[simp] theorem oracle_inverse_phi (O : Oracle n) : O.unitary.symm O.phi = knownInput n := by
  change O.unitary.symm (O.unitary (knownInput n)) = _
  exact O.unitary.symm_apply_apply _

/-- Equation (2.7), proved for the actual amplified full oracle. -/
theorem bidirectional_rayVector (O : Oracle n) (f g : lp (fun _ : C => ℂ) 2) :
    bidirectional C O (rayVector f g (knownInput n) O.phi) =
      rayVector f g O.phi (knownInput n) := by
  apply Subtype.ext
  funext i
  apply (WithLp.equiv 2 (Mspace n × Mspace n)).injective
  apply Prod.ext
  · change O.unitary (f i • knownInput n) = f i • O.phi
    rw [map_smul]
    rfl
  · change O.unitary.symm (g i • O.phi) = g i • knownInput n
    rw [map_smul, oracle_inverse_phi]

/-- The opposite signs of the forward and inverse filters in (4.2). -/
theorem ray_filter (Ox Oy : Oracle n) (f g f' g' : lp (fun _ : C => ℂ) 2) :
    inner ℂ (rayVector f g (knownInput n) Ox.phi) (rayVector f' g' (knownInput n) Oy.phi) -
      inner ℂ (bidirectional C Ox (rayVector f g (knownInput n) Ox.phi))
        (bidirectional C Oy (rayVector f' g' (knownInput n) Oy.phi)) =
    (1 - inner ℂ Ox.phi Oy.phi) * (inner ℂ f f' - inner ℂ g g') := by
  rw [bidirectional_rayVector, bidirectional_rayVector, rayVector_inner, rayVector_inner]
  have hs : inner ℂ (knownInput n) (knownInput n) = 1 := by
    simp [inner_self_eq_norm_sq_to_K, knownInput_norm]
  rw [hs]
  ring

/-- Existential ray support and the concrete query-vector construction coincide. -/
theorem raySupported_iff (O : Oracle n) (v : OracleQuerySpace n C) :
    Costs.RaySupported O v ↔ ∃ f g : lp (fun _ : C => ℂ) 2,
      v = rayVector f g (knownInput n) O.phi := by
  constructor
  · rintro ⟨f,g,h⟩
    refine ⟨f,g,?_⟩
    apply Subtype.ext
    funext i
    apply (WithLp.equiv 2 (Mspace n × Mspace n)).injective
    exact Prod.ext (h i).1 (h i).2
  · rintro ⟨f,g,rfl⟩
    exact ⟨f,g,fun _ => ⟨rfl,rfl⟩⟩

end ELV.Query
