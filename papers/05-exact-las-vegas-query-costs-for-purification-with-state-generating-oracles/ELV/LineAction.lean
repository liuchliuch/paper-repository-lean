import ELV.LineCatalyst

/-! The fixed line circuit acts correctly on every unknown invariant plane. -/
noncomputable section
namespace ELV.Line
open ELV.Stabilize ELV.Query
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {K : Submodule ℂ E} [CompleteSpace K]

@[simp] lemma project_known (s : K) : K.starProjection (s : E) = s :=
  Submodule.starProjection_mem_subspace_eq_self s
@[simp] lemma project_other (t : Kᗮ) : K.starProjection (t : E) = 0 := by
  change (K.orthogonalProjection (t : E) : E) = 0
  rw [proj_K_of_mem_orthogonal]
  rfl
@[simp] lemma project_perp_known (s : K) : Kᗮ.starProjection (s : E) = 0 := by
  change (Kᗮ.orthogonalProjection (s : E) : E) = 0
  rw [proj_Korth_of_mem_K]
  rfl
@[simp] lemma project_perp_other (t : Kᗮ) : Kᗮ.starProjection (t : E) = t :=
  Submodule.starProjection_mem_subspace_eq_self t

variable (q : ℝ) (hq : q^2 < 1) (s : K) (t : Kᗮ)

lemma shiftKnown_even (k : ℕ) : shiftKnown K (coupling q hq (s : E) (t : E)) (Sum.inl k) = 0 := by
  change K.starProjection (coupling q hq (s : E) (t : E) (Sum.inr k)) +
    Kᗮ.starProjection (coupling q hq (s : E) (t : E) (Sum.inl k)) = _
  simp

lemma shiftKnown_odd (k : ℕ) : shiftKnown K (coupling q hq (s : E) (t : E)) (Sum.inr k) =
    geometric q hq k • ((s : E)+(q : ℂ) • (t : E)) := by
  change K.starProjection (coupling q hq (s : E) (t : E) (Sum.inl k)) +
    Kᗮ.starProjection (coupling q hq (s : E) (t : E) (Sum.inr k)) = _
  simp [smul_add]

lemma shiftPerp_origin : shiftPerp K (coupling q hq (s : E) (t : E)) (Sum.inl 0) = (s : E) := by
  change K.starProjection (coupling q hq (s : E) (t : E) (Sum.inl 0)) +
    Kᗮ.starProjection (coupling q hq (s : E) (t : E) (Sum.inl 0)) = _
  simp

lemma shiftPerp_even (k : ℕ) : shiftPerp K (coupling q hq (s : E) (t : E)) (Sum.inl (k+1)) =
    geometric q hq k • (-(q : ℂ)^2 • (s : E)+(q : ℂ) • (t : E)) := by
  change K.starProjection (coupling q hq (s : E) (t : E) (Sum.inl (k+1))) +
    Kᗮ.starProjection (coupling q hq (s : E) (t : E) (Sum.inr k)) = _
  simp only [coupling_even,coupling_odd,geometric_succ,map_smul,
    project_known,project_perp_other]
  module

lemma shiftPerp_odd (k : ℕ) : shiftPerp K (coupling q hq (s : E) (t : E)) (Sum.inr k) = 0 := by
  change K.starProjection (coupling q hq (s : E) (t : E) (Sum.inr k)) +
    Kᗮ.starProjection (coupling q hq (s : E) (t : E) (Sum.inl (k+1))) = _
  simp

lemma shiftPerp_originVector : shiftPerp K (origin (s : E)) = origin (s : E) := by
  apply Subtype.ext
  funext i
  cases i with
  | inl k =>
    cases k with
    | zero => simp [origin,shiftPerp_apply,secondPairs,nextPair,lp.single_apply,Pi.single_apply]
    | succ k => simp [origin,shiftPerp_apply,secondPairs,nextPair,lp.single_apply,Pi.single_apply]
  | inr k => simp [origin,shiftPerp_apply,secondPairs,nextPair,lp.single_apply,Pi.single_apply]

/-- The first queried pairs are simultaneous eigenvectors of the oracle. -/
lemma first_reflection_eigen (R : E ≃ₗᵢ[ℂ] E) (ζ : ℂ)
    (he : R ((s : E)+(q : ℂ) • (t : E)) = ζ • ((s : E)+(q : ℂ) • (t : E))) :
    (shiftKnown K).symm ((Gate.query firstLayout).unitary (lpCongr R)
      (shiftKnown K (coupling q hq (s : E) (t : E)))) = ζ • coupling q hq (s : E) (t : E) := by
  have hquery : (Gate.query firstLayout).unitary (lpCongr R)
      (shiftKnown K (coupling q hq (s : E) (t : E))) = ζ • shiftKnown K (coupling q hq (s : E) (t : E)) := by
    apply Subtype.ext
    funext i
    cases i with
    | inl k =>
      change shiftKnown K (coupling q hq (s : E) (t : E)) (Sum.inl k) =
        ζ • shiftKnown K (coupling q hq (s : E) (t : E)) (Sum.inl k)
      rw [shiftKnown_even]
      simp
    | inr k =>
      change R (shiftKnown K (coupling q hq (s : E) (t : E)) (Sum.inr k)) =
        ζ • shiftKnown K (coupling q hq (s : E) (t : E)) (Sum.inr k)
      rw [shiftKnown_odd,map_smul,he]
      module
  rw [hquery,map_smul,LinearIsometryEquiv.symm_apply_apply]

/-- The second queried pairs have the opposite R eigenvalue; the known minus
sign restores them while the public boundary is not queried. -/
lemma second_reflection_eigen (R : E ≃ₗᵢ[ℂ] E) (ζ : ℂ)
    (he : R (-(q : ℂ)^2 • (s : E)+(q : ℂ) • (t : E)) =
      -ζ • (-(q : ℂ)^2 • (s : E)+(q : ℂ) • (t : E))) :
    (shiftPerp K).symm ((Gate.query secondLayout).unitary (lpCongr R)
      (secondMinus (shiftPerp K (coupling q hq (s : E) (t : E))))) =
        ζ • coupling q hq (s : E) (t : E) + (1-ζ) • origin (s : E) := by
  have hquery : (Gate.query secondLayout).unitary (lpCongr R)
      (secondMinus (shiftPerp K (coupling q hq (s : E) (t : E)))) =
        ζ • shiftPerp K (coupling q hq (s : E) (t : E)) + (1-ζ) • origin (s : E) := by
    apply Subtype.ext
    funext i
    cases i with
    | inl k =>
      cases k with
      | zero =>
        change shiftPerp K (coupling q hq (s : E) (t : E)) (Sum.inl 0) =
          ζ • shiftPerp K (coupling q hq (s : E) (t : E)) (Sum.inl 0) +
          (1-ζ) • origin (s : E) (Sum.inl 0)
        rw [shiftPerp_origin]
        simp only [origin,lp.single_apply_self]
        module
      | succ k =>
        change R (-shiftPerp K (coupling q hq (s : E) (t : E)) (Sum.inl (k+1))) =
          ζ • shiftPerp K (coupling q hq (s : E) (t : E)) (Sum.inl (k+1)) +
          (1-ζ) • origin (s : E) (Sum.inl (k+1))
        rw [shiftPerp_even,map_neg,map_smul,he]
        simp [origin,lp.single_apply,Pi.single_apply,smul_smul] <;> module
    | inr k =>
      change shiftPerp K (coupling q hq (s : E) (t : E)) (Sum.inr k) =
        ζ • shiftPerp K (coupling q hq (s : E) (t : E)) (Sum.inr k) +
        (1-ζ) • origin (s : E) (Sum.inr k)
      rw [shiftPerp_odd]
      simp [origin,lp.single_apply,Pi.single_apply]

  rw [hquery,map_add,map_smul,map_smul,LinearIsometryEquiv.symm_apply_apply]
  have ho := shiftPerp_originVector (K := K) s
  have hoi : (shiftPerp K).symm (origin (s : E)) = origin (s : E) := by
    calc
      _ = (shiftPerp K).symm (shiftPerp K (origin (s : E))) := by rw [ho]
      _ = _ := LinearIsometryEquiv.symm_apply_apply _ _
  rw [hoi]

/-- Exact returned catalyst equation for the fixed p,t-independent circuit. -/
theorem phaseCircuit_exact (R : E ≃ₗᵢ[ℂ] E) (ζ : ℂ) (hζ : ζ^2 = 1)
    (he1 : R ((s : E)+(q : ℂ) • (t : E)) = ζ • ((s : E)+(q : ℂ) • (t : E)))
    (he2 : R (-(q : ℂ)^2 • (s : E)+(q : ℂ) • (t : E)) =
      -ζ • (-(q : ℂ)^2 • (s : E)+(q : ℂ) • (t : E))) :
    Query.run (lpCongr R) (phaseCircuit K) (origin (s : E)+catalyst q hq (s : E) (t : E)) =
      ζ • origin (s : E)+catalyst q hq (s : E) (t : E) := by
  have hc : origin (s : E)+catalyst q hq (s : E) (t : E) = coupling q hq (s : E) (t : E) := by
    unfold catalyst
    abel
  rw [hc]
  change (shiftPerp K).symm ((Gate.query secondLayout).unitary (lpCongr R)
    (secondMinus (shiftPerp K ((shiftKnown K).symm
      ((Gate.query firstLayout).unitary (lpCongr R)
        (shiftKnown K (coupling q hq (s : E) (t : E)))))))) = _
  rw [first_reflection_eigen q hq s t R ζ he1]
  simp only [map_smul]
  rw [second_reflection_eigen q hq s t R ζ he2]
  have hzz : ζ*ζ = 1 := by simpa [pow_two] using hζ
  have hsub : ζ*(1-ζ) = ζ-1 := by linear_combination -hζ
  simp only [smul_add,smul_smul,hzz,hsub,one_smul]
  unfold catalyst
  module

end ELV.Line
