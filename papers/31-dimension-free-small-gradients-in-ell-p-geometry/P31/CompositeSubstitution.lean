import P31.ExternalComposite
import P31.Schedule

/-! The source-to-paper algebra in Lemma 2.2 and the combined genuine
objective, distance, and finite query-count certificate. -/
noncomputable section
namespace P31

/-- The dimension-free nonlogarithmic factor displayed in (2.7). -/
def compositeStageFactor (p κ L μ D δ : ℝ) : ℝ :=
  (L / (μ * δ ^ (p - κ))) ^ Schedule.beta p κ * (D / δ) ^ (κ * Schedule.beta p κ)

/-- Exact substitution of eta=(mu/p)delta^p and phi=(a_p/p)D^p into
[6]'s nonlogarithmic term. The entire remaining factor depends only on p,kappa. -/
theorem composite_raw_power_substitution {p κ L μ D δ : ℝ}
    (hp : 2 ≤ p) (hκ : 1 < κ) (_hκhi : κ ≤ 2)
    (hL : 0 < L) (hμ : 0 < μ) (hD : 0 < D) (hδ : 0 < δ) :
    (L / ((μ / p) * δ ^ p)) ^ Schedule.beta p κ *
      ((atomScale p / p) * D ^ p) ^ (κ / Schedule.deltaDenom p κ) =
    (p ^ Schedule.beta p κ * (atomScale p / p) ^ (κ / Schedule.deltaDenom p κ)) *
      compositeStageFactor p κ L μ D δ := by
  have hp0 : 0 < p := by linarith
  have hΔ := Schedule.deltaDenom_pos hp hκ
  have hpc : p * (κ / Schedule.deltaDenom p κ) = κ * Schedule.beta p κ := by
    unfold Schedule.beta
    ring
  have hη : L / ((μ / p) * δ ^ p) = (p * (L / μ)) / δ ^ p := by
    field_simp
  have hfirst : (L / ((μ / p) * δ ^ p)) ^ Schedule.beta p κ =
      p ^ Schedule.beta p κ * (L / μ) ^ Schedule.beta p κ /
        δ ^ (p * Schedule.beta p κ) := by
    rw [hη, Real.div_rpow (mul_nonneg hp0.le (div_nonneg hL.le hμ.le))
      (Real.rpow_nonneg hδ.le p), Real.mul_rpow hp0.le (div_nonneg hL.le hμ.le),
      ← Real.rpow_mul hδ.le]
  have hsecond : ((atomScale p / p) * D ^ p) ^ (κ / Schedule.deltaDenom p κ) =
      (atomScale p / p) ^ (κ / Schedule.deltaDenom p κ) * D ^ (κ * Schedule.beta p κ) := by
    rw [Real.mul_rpow (div_nonneg (atomScale_pos p).le hp0.le) (Real.rpow_nonneg hD.le p),
      ← Real.rpow_mul hD.le, hpc]
  have htarget : compositeStageFactor p κ L μ D δ =
      ((L / μ) ^ Schedule.beta p κ * D ^ (κ * Schedule.beta p κ)) /
        δ ^ (p * Schedule.beta p κ) := by
    unfold compositeStageFactor
    have hbase : L / (μ * δ ^ (p - κ)) = (L / μ) / δ ^ (p - κ) := by rw [div_div]
    rw [hbase, Real.div_rpow (div_nonneg hL.le hμ.le) (Real.rpow_nonneg hδ.le _),
      ← Real.rpow_mul hδ.le, Real.div_rpow hD.le hδ.le, div_mul_div_comm,
      ← Real.rpow_add hδ]
    congr 2
    ring
  rw [hfirst, hsecond, htarget]
  ring

/-- The actual atom value at a point within radius D supplies the source
phi(zstar) upper bound used immediately before the substitution. -/
theorem powerAtom_upper_of_distance {ι : Type*} [Fintype ι] {p D : ℝ}
    (hp : 0 < p) (center zstar : ι → ℝ) (hd : lpNorm p (zstar - center) ≤ D) :
    powerAtom p center zstar ≤ (atomScale p / p) * D ^ p := by
  rw [powerAtom_eq_lpNorm hp]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (lpNorm_nonneg p _) hd hp.le)
    (div_nonneg (atomScale_pos p).le hp.le)

/-- The actual source term at zstar is bounded by the substituted paper
factor using the proved radial atom bound; its exponent is positive. -/
theorem composite_source_term_bound {ι : Type*} [Fintype ι] {p κ L μ D δ : ℝ}
    (hp : 2 ≤ p) (hκ : 1 < κ) (hκhi : κ ≤ 2)
    (hL : 0 < L) (hμ : 0 < μ) (hD : 0 < D) (hδ : 0 < δ)
    (center zstar : ι → ℝ) (hd : lpNorm p (zstar - center) ≤ D) :
    (L / ((μ / p) * δ ^ p)) ^ Schedule.beta p κ *
      powerAtom p center zstar ^ (κ / Schedule.deltaDenom p κ) ≤
    (p ^ Schedule.beta p κ * (atomScale p / p) ^ (κ / Schedule.deltaDenom p κ)) *
      compositeStageFactor p κ L μ D δ := by
  have hp0 : 0 < p := by linarith
  have hc : 0 ≤ κ / Schedule.deltaDenom p κ :=
    (div_pos (lt_trans zero_lt_one hκ) (Schedule.deltaDenom_pos hp hκ)).le
  have hphi := powerAtom_upper_of_distance hp0 center zstar hd
  have hpow := Real.rpow_le_rpow (powerAtom_nonneg hp0 center zstar) hphi hc
  have hmul := mul_le_mul_of_nonneg_left hpow
    (Real.rpow_nonneg (div_nonneg hL.le (mul_nonneg (div_nonneg hμ.le hp0.le)
      (Real.rpow_nonneg hδ.le p))) (Schedule.beta p κ))
  exact hmul.trans_eq (composite_raw_power_substitution hp hκ hκhi hL hμ hD hδ)

/-- Taking a natural-number ceiling costs at most one extra copy of 1+B. -/
theorem composite_ceiling_bound {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) :
    (⌈C * (1 + B)⌉₊ : ℝ) ≤ (C + 1) * (1 + B) := by
  have hceil := (Nat.ceil_lt_add_one (mul_nonneg hC (by linarith : 0 ≤ 1 + B))).le
  nlinarith

lemma compositeStageFactor_nonneg {p κ L μ D δ : ℝ}
    (hL : 0 ≤ L) (hμ : 0 ≤ μ) (hD : 0 ≤ D) (hδ : 0 ≤ δ) :
    0 ≤ compositeStageFactor p κ L μ D δ :=
  mul_nonneg (Real.rpow_nonneg (div_nonneg hL (mul_nonneg hμ (Real.rpow_nonneg hδ _))) _)
    (Real.rpow_nonneg (div_nonneg hD hδ) _)

/-- The fixed source budget implies the real-valued bound in Lemma 2.2. -/
theorem compositeQueryBudget_real_le {p κ C L μ D δ : ℝ}
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hμ : 0 ≤ μ) (hD : 0 ≤ D) (hδ : 0 ≤ δ) :
    (compositeQueryBudget C p κ L μ D δ : ℝ) ≤
      (C + 1) * (1 + compositeStageFactor p κ L μ D δ) :=
  composite_ceiling_bound hC (compositeStageFactor_nonneg hL hμ hD hδ)

/-- Lemma 2.2, with all three conclusions about the actual returned output
and actual gradient calls. Only the existing objective-only external engine
is used; distance follows from the proved Jensen growth theorem. -/
theorem lemma2_2 {ι : Type*} [Fintype ι] {p κ C L μ D δ : ℝ}
    (engine : ExternalComplementaryComposite ι p κ C)
    (hp : 2 ≤ p) (_hκ : 1 < κ) (_hκhi : κ ≤ 2) (hC : 0 ≤ C)
    (H : (ι → ℝ) → ℝ) (center : ι → ℝ) (prox : CompositeProx (ι → ℝ))
    (hL : 0 < L) (hμ : 0 < μ) (hD : 0 < D) (hδ : 0 < δ) (hδD : δ ≤ D)
    (hH : LpPowerJensen p μ H) (hprox : IsCompositeProx p H center prox)
    (f : (ι → ℝ) → ℝ) (grad : (ι → ℝ) → ι → ℝ) (zstar : ι → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    (hg : ∀ x, HasFDerivAt f (coordinateFunctional (grad x)) x)
    (hh : ∀ x y, lpNorm (dualExponent p) (grad x - grad y) ≤
      L * lpNorm p (x-y) ^ (κ-1))
    (hz : ∀ y, f zstar + H zstar ≤ f y + H y) (hd : lpNorm p (center-zstar) ≤ D) :
    let result := (engine.routine H center L μ D δ prox).run grad
    (f result.value + H result.value - (f zstar + H zstar) ≤ μ / p * δ ^ p) ∧
      lpNorm p (result.value-zstar) ≤ δ ∧
      (result.calls : ℝ) ≤ (C + 1) * (1 + compositeStageFactor p κ L μ D δ) := by
  refine ⟨engine.objective_gap H center L μ D δ prox hL hμ hD hδ hδD hH hprox
    f grad zstar hf hg hh hz hd, ?_, ?_⟩
  · exact externalComposite_contraction engine (by linarith) H center prox hL hμ hD hδ hδD
      hH hprox f grad zstar hf hg hh hz hd
  · have hc := engine.calls_le H center L μ D δ prox grad hL hμ hD hδ hδD
    have hcast : (((engine.routine H center L μ D δ prox).run grad).calls : ℝ) ≤
        (compositeQueryBudget C p κ L μ D δ : ℝ) := by exact_mod_cast hc
    exact hcast.trans (compositeQueryBudget_real_le hC hL.le hμ.le hD.le hδ.le)

end P31
