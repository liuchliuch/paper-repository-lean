import ELV.LineAction

/-! Las Vegas cost computed from the actual two-query trajectory. -/
noncomputable section
namespace ELV.Line
open ELV.Stabilize ELV.Query
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {K : Submodule ℂ E} [CompleteSpace K]
variable (q : ℝ) (hq : q^2 < 1) (s : K) (t : Kᗮ)

lemma first_query_norm_sq :
    ‖(firstLayout (shiftKnown K (coupling q hq (s : E) (t : E)))).snd‖ ^ 2 =
      ‖coupling q hq (s : E) (t : E)‖ ^ 2 := by
  have hzero : (firstLayout (shiftKnown K (coupling q hq (s : E) (t : E)))).fst = 0 := by
    apply Subtype.ext
    funext k
    exact shiftKnown_even q hq s t k
  have hn := congrArg (fun r : ℝ => r^2)
    (firstLayout.norm_map (shiftKnown K (coupling q hq (s : E) (t : E))))
  dsimp only at hn
  rw [WithLp.prod_norm_sq_eq_of_L2,hzero,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),zero_add,
    LinearIsometryEquiv.norm_map] at hn
  exact hn

lemma second_nonquery (hs : ‖(s : E)‖ = 1) :
    (secondLayout (shiftPerp K (coupling q hq (s : E) (t : E)))).fst = lp.single 2 0 (s : E) := by
  apply Subtype.ext
  funext k
  cases k with
  | zero => exact shiftPerp_origin q hq s t
  | succ k =>
    change shiftPerp K (coupling q hq (s : E) (t : E)) (Sum.inr k) = _
    rw [shiftPerp_odd]
    simp [lp.single_apply,Pi.single_apply]

lemma second_query_norm_sq (hs : ‖(s : E)‖ = 1) (ht : ‖(t : E)‖ = 1) :
    ‖(secondLayout (shiftPerp K (coupling q hq (s : E) (t : E)))).snd‖ ^ 2 = q^2/(1-q^2) := by
  have hn := congrArg (fun r : ℝ => r^2)
    (secondLayout.norm_map (shiftPerp K (coupling q hq (s : E) (t : E))))
  dsimp only at hn
  rw [WithLp.prod_norm_sq_eq_of_L2,second_nonquery q hq s t hs,
    lp.norm_single (by norm_num : (0 : ENNReal) < 2),hs,
    LinearIsometryEquiv.norm_map,coupling_norm_sq q hq (s : E) (t : E) hs ht] at hn
  have hden : 1-q^2 ≠ 0 := by linarith
  have heq : 1/(1-q^2)-1 = q^2/(1-q^2) := by field_simp [hden]; ring
  linarith

/-- The second queried norm is unaffected by the work minus sign and global phase. -/
lemma second_scaled_query_norm_sq (hs : ‖(s : E)‖ = 1) (ht : ‖(t : E)‖ = 1)
    (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
    ‖(secondLayout (secondMinus (shiftPerp K (ζ • coupling q hq (s : E) (t : E))))).snd‖ ^ 2 =
      q^2/(1-q^2) := by
  rw [secondMinus_query,norm_neg]
  have heq : (secondLayout (shiftPerp K (ζ • coupling q hq (s : E) (t : E)))).snd =
      ζ • (secondLayout (shiftPerp K (coupling q hq (s : E) (t : E)))).snd := by
    rw [map_smul,map_smul]
    rfl
  rw [heq,norm_smul,hζ,one_mul]
  exact second_query_norm_sq q hq s t hs ht

/-- Raw executed cost after the first eigen-relation; no normalization of t is needed. -/
lemma phaseCircuit_cost_raw (R : E ≃ₗᵢ[ℂ] E) (ζ : ℂ)
    (he1 : R ((s : E)+(q : ℂ) • (t : E)) = ζ • ((s : E)+(q : ℂ) • (t : E))) :
    Query.cost (lpCongr R) (phaseCircuit K) (origin (s : E)+catalyst q hq (s : E) (t : E)) =
      ‖coupling q hq (s : E) (t : E)‖ ^ 2 +
      ‖(secondLayout (secondMinus (shiftPerp K (ζ • coupling q hq (s : E) (t : E))))).snd‖ ^ 2 := by
  have hc : origin (s : E)+catalyst q hq (s : E) (t : E) = coupling q hq (s : E) (t : E) := by
    unfold catalyst
    abel
  rw [hc]
  simp only [phaseCircuit,Query.cost_cons,Query.cost_nil,Gate.queried,Gate.unitary,
    norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),zero_add,add_zero]
  change ‖(firstLayout (shiftKnown K (coupling q hq (s : E) (t : E)))).snd‖ ^ 2 +
    ‖(secondLayout (secondMinus (shiftPerp K ((shiftKnown K).symm
      ((Gate.query firstLayout).unitary (lpCongr R)
        (shiftKnown K (coupling q hq (s : E) (t : E)))))))).snd‖ ^ 2 = _
  rw [first_reflection_eigen q hq s t R ζ he1,first_query_norm_sq q hq s t]

/-- The actual executed reflection-query cost of the fixed circuit. -/
theorem phaseCircuit_cost (hs : ‖(s : E)‖ = 1) (ht : ‖(t : E)‖ = 1)
    (R : E ≃ₗᵢ[ℂ] E) (ζ : ℂ) (hζ : ζ^2 = 1)
    (he1 : R ((s : E)+(q : ℂ) • (t : E)) = ζ • ((s : E)+(q : ℂ) • (t : E))) :
    Query.cost (lpCongr R) (phaseCircuit K) (origin (s : E)+catalyst q hq (s : E) (t : E)) =
      (1+q^2)/(1-q^2) := by
  have hc : origin (s : E)+catalyst q hq (s : E) (t : E) = coupling q hq (s : E) (t : E) := by
    unfold catalyst
    abel
  have hζn : ‖ζ‖ = 1 := by
    have hh := congrArg norm hζ
    rw [norm_pow,norm_one] at hh
    nlinarith [norm_nonneg ζ]
  rw [phaseCircuit_cost_raw q hq s t R ζ he1,
    second_scaled_query_norm_sq q hq s t hs ht ζ hζn,
    coupling_norm_sq q hq (s : E) (t : E) hs ht]
  ring

lemma second_query_origin_zero (s : K) : (secondLayout (origin (s : E))).snd = 0 := by
  apply Subtype.ext
  funext k
  rw [secondLayout_snd]
  change origin (s : E) (Sum.inl (k+1)) = (0 : E)
  simp [origin,lp.single_apply,Pi.single_apply]

/-- The same fixed circuit handles R s = ± s with no catalyst. -/
theorem phaseCircuit_endpoint (s : K) (hs : ‖(s : E)‖ = 1)
    (R : E ≃ₗᵢ[ℂ] E) (ζ : ℂ) (hζ : ζ^2 = 1) (hRs : R (s : E) = ζ • (s : E)) :
    Query.run (lpCongr R) (phaseCircuit K) (origin (s : E)) = ζ • origin (s : E) ∧
    Query.cost (lpCongr R) (phaseCircuit K) (origin (s : E)) = 1 := by
  have he1 : R ((s : E)+(0 : ℂ) • (0 : E)) = ζ • ((s : E)+(0 : ℂ) • (0 : E)) := by
    simpa using hRs
  have he2 : R (-(0 : ℂ)^2 • (s : E)+(0 : ℂ) • (0 : E)) =
      -ζ • (-(0 : ℂ)^2 • (s : E)+(0 : ℂ) • (0 : E)) := by simp
  constructor
  · simpa only [catalyst_zero,add_zero] using
      phaseCircuit_exact 0 (by norm_num) s (0 : Kᗮ) R ζ hζ he1 he2
  · have hc := phaseCircuit_cost_raw 0 (by norm_num) s (0 : Kᗮ) R ζ he1
    rw [catalyst_zero,add_zero,coupling_zero] at hc
    have hz : (secondLayout (secondMinus (shiftPerp K (ζ • origin (s : E))))).snd = 0 := by
      rw [secondMinus_query,map_smul,shiftPerp_originVector,map_smul]
      change -(ζ • (secondLayout (origin (s : E))).snd) = 0
      rw [second_query_origin_zero]
      simp
    rw [hz,norm_zero,zero_pow (by decide : (2 : ℕ) ≠ 0),add_zero] at hc
    have hn : ‖origin (s : E)‖ = 1 := by simpa [origin] using hs
    simpa [hn] using hc

end ELV.Line
