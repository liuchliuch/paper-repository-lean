import P31.NormComparison
import P31.QueryProgram
import P31.Schedule

/-! Equations (7.8)--(7.9).  Programs are actual deterministic local-oracle
gradient-query trees with exact query counts and output values.
The external Hilbert input is only a Euclidean gradient estimate. -/

noncomputable section
open scoped BigOperators
namespace P31.HilbertDiagnostics

abbrev Vec (k : ℕ) := Fin k → ℝ

abbrev Program (k : ℕ) := QueryProgram.Program (Vec k) (Vec k) (Vec k)

/-- A successful execution with its actual number of oracle queries. -/
def Certificate {k : ℕ} (P : Program k) (_f : Vec k → ℝ) (g : Vec k → Vec k)
    (r : ℝ) (N : ℕ) (bound : ℝ) : Prop :=
  ∃x, (P.run g).value=x ∧ (P.run g).calls ≤ N ∧ lpNorm r (g x) ≤ bound

/-- The known Hilbert theorem: `p_src=2`, Corollary 3, Section 4.1,
https://arxiv.org/html/2311.17296v2.  This is the uniform numerical-constant
`N`-query normalization of the source's `2N`-iteration statement.  Only
Euclidean smoothness, Euclidean radius, and Euclidean gradient norm occur. -/
structure EuclideanRateInput (C : ℝ) where
  method : ∀k : ℕ, ℝ → ℝ → Vec k → ℕ → Program k
  rate : ∀ (k : ℕ) (f : Vec k → ℝ) (g : Vec k → Vec k) (x₀ xstar : Vec k)
    (L R₂ : ℝ) (N : ℕ), 0 ≤ L → 0 ≤ R₂ → 0 < N →
    ConvexOn ℝ Set.univ f → (∀x, HasFDerivAt f (coordinateFunctional (g x)) x) →
    (∀x, f xstar ≤ f x) →
    (∀u v, lpNorm 2 (g u-g v) ≤ L*lpNorm 2 (u-v)) →
    lpNorm 2 (x₀-xstar) ≤ R₂ →
    Certificate (method k L R₂ x₀ N) f g 2 N (C*L*R₂/(N:ℝ)^2)

/-- Known support is represented by the actual restricted coordinate space
`Fin k`, as allowed by `f(x)=fbar(x_I)` in the source. -/
def supportFactor (k : ℕ) (p : ℝ) : ℝ := (k:ℝ)^(1/2-1/p)
def hilbertFactor (k : ℕ) (p : ℝ) (N : ℕ) : ℝ := (k:ℝ)^(1-2/p)/(N:ℝ)^2
def continuationFactor (p : ℝ) (N : ℕ) : ℝ := 1/(N:ℝ)^((p+2)/p)

lemma supportFactor_nonneg (k : ℕ) (p : ℝ) : 0 ≤ supportFactor k p :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma supportFactor_sq (k : ℕ) (hk : 0 < k) (p : ℝ) :
    supportFactor k p * supportFactor k p = (k:ℝ)^(1-2/p) := by
  unfold supportFactor
  rw [← Real.rpow_add (Nat.cast_pos.mpr hk)]
  congr 1
  ring

/-- Primal and dual finite-coordinate comparisons turn ℓₚ smoothness into
Euclidean smoothness with the same `L`. -/
theorem restricted_euclidean_smooth {k : ℕ} {p L : ℝ} (hp : 2 ≤ p) (hL : 0 ≤ L)
    (g : Vec k → Vec k)
    (h : ∀u v, lpNorm (dualExponent p) (g u-g v) ≤ L*lpNorm p (u-v)) :
    ∀u v, lpNorm 2 (g u-g v) ≤ L*lpNorm 2 (u-v) := by
  intro u v
  have hc := finite_support_hilbert_comparisons hp (u-v) (g u-g v)
  exact hc.2.2.1.trans ((h u v).trans (mul_le_mul_of_nonneg_left hc.1 hL))

/-- First factor `k^(1/2-1/p)` comes from the initial radius. -/
theorem restricted_radius {k : ℕ} {p R : ℝ} (hp : 2 ≤ p) (x₀ xstar : Vec k)
    (h : lpNorm p (x₀-xstar) ≤ R) :
    lpNorm 2 (x₀-xstar) ≤ supportFactor k p*R := by
  have hc := finite_support_hilbert_comparisons hp (x₀-xstar) (0:Vec k)
  have hbase : lpNorm 2 (x₀-xstar) ≤ supportFactor k p*lpNorm p (x₀-xstar) := by
    simpa only [Fintype.card_fin, supportFactor] using hc.2.1
  exact hbase.trans (mul_le_mul_of_nonneg_left h (supportFactor_nonneg _ _))

/-- Equation (7.8) derived from the external Euclidean rate.  Both factors of
the support loss are proved via actual ℓₚ/ℓ₂/ℓ_q norm comparisons. -/
theorem finite_support_hilbert_rate {k : ℕ} (hk : 0 < k) {p C L R : ℝ}
    (hp : 2 ≤ p) (_hC : 0 ≤ C) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (H : EuclideanRateInput C) (f : Vec k → ℝ) (g : Vec k → Vec k)
    (x₀ xstar : Vec k) (N : ℕ) (hN : 0 < N)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀x, HasFDerivAt f (coordinateFunctional (g x)) x)
    (hmin : ∀x, f xstar ≤ f x)
    (hsmooth : ∀u v, lpNorm (dualExponent p) (g u-g v) ≤ L*lpNorm p (u-v))
    (hradius : lpNorm p (x₀-xstar) ≤ R) :
    Certificate (H.method k L (supportFactor k p*R) x₀ N) f g (dualExponent p) N
      (C*L*R*hilbertFactor k p N) := by
  have hR₂ : 0 ≤ supportFactor k p*R := mul_nonneg (supportFactor_nonneg _ _) hR
  obtain ⟨x, hx, hcalls, hbound⟩ := H.rate k f g x₀ xstar L _ N hL hR₂ hN
    hconvex hgrad hmin (restricted_euclidean_smooth hp hL g hsmooth)
    (restricted_radius hp x₀ xstar hradius)
  refine ⟨x, hx, hcalls, ?_⟩
  have hc := finite_support_hilbert_comparisons hp (0:Vec k) (g x)
  calc
    _ ≤ supportFactor k p*lpNorm 2 (g x) := by simpa only [Fintype.card_fin, supportFactor] using hc.2.2.2
    _ ≤ supportFactor k p*(C*L*(supportFactor k p*R)/(N:ℝ)^2) :=
      mul_le_mul_of_nonneg_left hbound (supportFactor_nonneg _ _)
    _ = C*L*R*hilbertFactor k p N := by
      unfold hilbertFactor
      rw [← mul_div_assoc]
      calc
        _ = C*L*R*(supportFactor k p*supportFactor k p)/(N:ℝ)^2 := by ring
        _ = _ := by rw [supportFactor_sq k hk]; ring

/-- Empty known support returns its unique restricted point without a query. -/
def supportMethod {C : ℝ} (H : EuclideanRateInput C) (k : ℕ)
    (p L R : ℝ) (x₀ : Vec k) (N : ℕ) : Program k :=
  if k=0 then .pure 0 else H.method k L (supportFactor k p*R) x₀ N

/-- Equation (7.8) including the empty-support case. -/
theorem finite_support_hilbert_rate_all {k : ℕ} {p C L R : ℝ}
    (hp : 2 ≤ p) (hC : 0 ≤ C) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (H : EuclideanRateInput C) (f : Vec k → ℝ) (g : Vec k → Vec k)
    (x₀ xstar : Vec k) (N : ℕ) (hN : 0 < N)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀x, HasFDerivAt f (coordinateFunctional (g x)) x)
    (hmin : ∀x, f xstar ≤ f x)
    (hsmooth : ∀u v, lpNorm (dualExponent p) (g u-g v) ≤ L*lpNorm p (u-v))
    (hradius : lpNorm p (x₀-xstar) ≤ R) :
    Certificate (supportMethod H k p L R x₀ N) f g (dualExponent p) N
      (C*L*R*hilbertFactor k p N) := by
  by_cases hk : k=0
  · subst k
    change Certificate (.pure (0:Vec 0)) f g (dualExponent p) N _
    refine ⟨0, rfl, Nat.zero_le _, ?_⟩
    have hnorm : lpNorm (dualExponent p) (g 0)=0 := by
      have hq : 0 < dualExponent p := dualExponent_pos (by linarith)
      simpa [lpNorm, lpPower] using
        (Real.zero_rpow (one_div_ne_zero hq.ne') : (0:ℝ)^(1/dualExponent p)=0)
    rw [hnorm]
    exact mul_nonneg (mul_nonneg (mul_nonneg hC hL) hR)
      (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _))
  · simpa only [supportMethod, if_neg hk] using
      finite_support_hilbert_rate (Nat.pos_of_ne_zero hk) hp hC hL hR H f g x₀ xstar N hN
        hconvex hgrad hmin hsmooth hradius

/-- The method choice inspects only the two known numerical upper bounds. -/
def choose {k : ℕ} (upper₁ upper₂ : ℝ) (P Q : Program k) : Program k :=
  if upper₁ ≤ upper₂ then P else Q

/-- Selecting a geometry preserves its exact execution and query budget. -/
theorem choose_certificate {k : ℕ} {P Q : Program k} {f : Vec k → ℝ}
    {g : Vec k → Vec k} {r upper₁ upper₂ : ℝ} {N : ℕ}
    (hP : Certificate P f g r N upper₁) (hQ : Certificate Q f g r N upper₂) :
    Certificate (choose upper₁ upper₂ P Q) f g r N (min upper₁ upper₂) := by
  by_cases h : upper₁ ≤ upper₂
  · simpa only [choose, if_pos h, min_eq_left h] using hP
  · simpa only [choose, if_neg h, min_eq_right (le_of_not_ge h)] using hQ

lemma min_scaled_bounds {C₁ C₂ L R a b : ℝ} (_hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (hL : 0 ≤ L) (hR : 0 ≤ R) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min (C₁*L*R*a) (C₂*L*R*b) ≤ max C₁ C₂*L*R*min a b := by
  have hLR : 0 ≤ L*R := mul_nonneg hL hR
  by_cases hab : a ≤ b
  · rw [min_eq_left hab]
    exact (min_le_left _ _).trans (by
      nlinarith [mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (mul_nonneg hLR ha)])
  · rw [min_eq_right (le_of_not_ge hab)]
    exact (min_le_right _ _).trans (by
      nlinarith [mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (mul_nonneg hLR hb)])

/-- Equation (7.9).  The continuation hypothesis is the base main-theorem rate
certificate for its actual protocol, not an external Hilbert or envelope input. -/
theorem finite_dimension_envelope {d : ℕ} (hd : 0 < d) {p C_H C_p L R : ℝ}
    (hp : 2 ≤ p) (hCH : 0 ≤ C_H) (hCp : 0 ≤ C_p) (hL : 0 ≤ L) (hR : 0 ≤ R)
    (H : EuclideanRateInput C_H) (f : Vec d → ℝ) (g : Vec d → Vec d)
    (x₀ xstar : Vec d) (N : ℕ) (hN : 0 < N)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀x, HasFDerivAt f (coordinateFunctional (g x)) x)
    (hmin : ∀x, f xstar ≤ f x)
    (hsmooth : ∀u v, lpNorm (dualExponent p) (g u-g v) ≤ L*lpNorm p (u-v))
    (hradius : lpNorm p (x₀-xstar) ≤ R) (P : Program d)
    (hcontinuation : Certificate P f g (dualExponent p) N (C_p*L*R*continuationFactor p N)) :
    Certificate (choose (C_H*L*R*hilbertFactor d p N) (C_p*L*R*continuationFactor p N)
      (H.method d L (supportFactor d p*R) x₀ N) P) f g (dualExponent p) N
      (max C_H C_p*L*R*min (hilbertFactor d p N) (continuationFactor p N)) := by
  obtain ⟨x, hx, hcalls, hbound⟩ := choose_certificate
    (finite_support_hilbert_rate hd hp hCH hL hR H f g x₀ xstar N hN
      hconvex hgrad hmin hsmooth hradius) hcontinuation
  refine ⟨x, hx, hcalls, hbound.trans ?_⟩
  exact min_scaled_bounds hCH hCp hL hR
    (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _))
    (div_nonneg zero_le_one (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- The accuracy-form main-theorem certificate, with its exact real query
upper bound.  This is a certificate of a particular protocol execution. -/
def AccuracyCertificate {k : ℕ} (P : Program k) (_f : Vec k → ℝ) (g : Vec k → Vec k)
    (r K scale β ε : ℝ) : Prop :=
  ∃x, (P.run g).value=x ∧
    ((P.run g).calls:ℝ) ≤ K*(1+(scale/ε)^β) ∧ lpNorm r (g x) ≤ ε

/-- The accuracy chosen when converting the main result to an `N`-query rate. -/
def targetAccuracy (K scale β : ℝ) (N : ℕ) : ℝ :=
  scale / ((N:ℝ)/(2*K))^(1/β)

lemma targetAccuracy_pos {K scale β : ℝ} {N : ℕ}
    (hK : 0 < K) (hs : 0 < scale) (hN : 0 < N) : 0 < targetAccuracy K scale β N := by
  exact div_pos hs (Real.rpow_pos_of_pos (div_pos (Nat.cast_pos.mpr hN) (by linarith)) _)

lemma targetAccuracy_power {K scale β : ℝ} {N : ℕ}
    (hK : 0 < K) (hs : 0 < scale) (hb : 0 < β) (hN : 0 < N) :
    (scale/targetAccuracy K scale β N)^β = (N:ℝ)/(2*K) := by
  have hbase : 0 < (N:ℝ)/(2*K) := div_pos (Nat.cast_pos.mpr hN) (by linarith)
  have hs0 : scale ≠ 0 := hs.ne'
  have hroot : ((N:ℝ)/(2*K))^(1/β) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hbase _)
  have heq : scale/targetAccuracy K scale β N = ((N:ℝ)/(2*K))^(1/β) := by
    unfold targetAccuracy
    field_simp
  rw [heq, ← Real.rpow_mul hbase.le, one_div_mul_cancel hb.ne', Real.rpow_one]

lemma targetAccuracy_rate {K scale β : ℝ} {N : ℕ}
    (hK : 0 < K) (hN : 0 < N) :
    targetAccuracy K scale β N = (2*K)^(1/β)*scale/(N:ℝ)^(1/β) := by
  have hK2 : 0 < 2*K := by linarith
  have hN0 : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hKpow : (2*K)^(1/β) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hK2 _)
  have hNpow : (N:ℝ)^(1/β) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hN0 _)
  unfold targetAccuracy
  rw [Real.div_rpow hN0.le hK2.le]
  field_simp

/-- Own inversion of the original accuracy complexity `K[1+(scale/ε)^β]`.
The only lower threshold on `N` is the explicit parameter-dependent `N≥2K`. -/
theorem accuracy_family_to_rate {k : ℕ} {f : Vec k → ℝ} {g : Vec k → Vec k}
    {r K scale β : ℝ} (hK : 0 < K) (hs : 0 < scale) (hb : 0 < β)
    (family : ℝ → Program k)
    (hfamily : ∀ε : ℝ, 0 < ε → AccuracyCertificate (family ε) f g r K scale β ε)
    (N : ℕ) (hN : 0 < N) (hlarge : 2*K ≤ (N:ℝ)) :
    Certificate (family (targetAccuracy K scale β N)) f g r N
      ((2*K)^(1/β)*scale/(N:ℝ)^(1/β)) := by
  obtain ⟨x, hx, hcalls, hgrad⟩ := hfamily _ (targetAccuracy_pos hK hs hN)
  have hbudget : K*(1+(scale/targetAccuracy K scale β N)^β) ≤ (N:ℝ) := by
    rw [targetAccuracy_power hK hs hb hN]
    have hK0 : K ≠ 0 := hK.ne'
    have heq : K*(1+(N:ℝ)/(2*K)) = K+(N:ℝ)/2 := by field_simp
    rw [heq]
    linarith only [hlarge]
  refine ⟨x, hx, ?_, ?_⟩
  · exact_mod_cast hcalls.trans hbudget
  · simpa only [targetAccuracy_rate hK hN] using hgrad

lemma smooth_inverse_beta {p : ℝ} (hp : 2 ≤ p) :
    1/Schedule.beta p 2 = (p+2)/p := by
  have hp0 : p ≠ 0 := by linarith
  have hd : 2*p+2-p ≠ 0 := by linarith
  unfold Schedule.beta Schedule.deltaDenom
  field_simp
  ring

/-- The continuation rate certificate used in (7.9) is derived from the
main theorem's accuracy family, with no final `N`-rate assumption. -/
theorem accuracy_family_to_smooth_continuation {k : ℕ} {p K L R : ℝ}
    (hp : 2 ≤ p) (hK : 0 < K) (hL : 0 < L) (hR : 0 < R)
    (f : Vec k → ℝ) (g : Vec k → Vec k) (family : ℝ → Program k)
    (hfamily : ∀ε : ℝ, 0 < ε →
      AccuracyCertificate (family ε) f g (dualExponent p) K (L*R) (Schedule.beta p 2) ε)
    (N : ℕ) (hN : 0 < N) (hlarge : 2*K ≤ (N:ℝ)) :
    Certificate (family (targetAccuracy K (L*R) (Schedule.beta p 2) N)) f g (dualExponent p) N
      ((2*K)^((p+2)/p)*L*R*continuationFactor p N) := by
  have h := accuracy_family_to_rate hK (mul_pos hL hR)
    (Schedule.beta_pos hp (by norm_num : (1:ℝ) < 2)) family hfamily N hN hlarge
  have heq : (2*K)^(1/Schedule.beta p 2)*(L*R)/(N:ℝ)^(1/Schedule.beta p 2) =
      (2*K)^((p+2)/p)*L*R*continuationFactor p N := by
    rw [smooth_inverse_beta hp]
    unfold continuationFactor
    ring
  simpa only [heq] using h

/-- Full equation (7.9) from the base accuracy-form continuation guarantee.
Both the inversion to an `N`-rate and the choice between geometries are own
proved steps; the external input remains only the Euclidean Hilbert theorem. -/
theorem finite_dimension_envelope_from_accuracy {d : ℕ} (hd : 0 < d)
    {p C_H K L R : ℝ} (hp : 2 ≤ p) (hCH : 0 ≤ C_H) (hK : 0 < K)
    (hL : 0 < L) (hR : 0 < R) (H : EuclideanRateInput C_H)
    (f : Vec d → ℝ) (g : Vec d → Vec d) (x₀ xstar : Vec d)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀x, HasFDerivAt f (coordinateFunctional (g x)) x)
    (hmin : ∀x, f xstar ≤ f x)
    (hsmooth : ∀u v, lpNorm (dualExponent p) (g u-g v) ≤ L*lpNorm p (u-v))
    (hradius : lpNorm p (x₀-xstar) ≤ R) (family : ℝ → Program d)
    (hfamily : ∀ε : ℝ, 0 < ε →
      AccuracyCertificate (family ε) f g (dualExponent p) K (L*R) (Schedule.beta p 2) ε)
    (N : ℕ) (hN : 0 < N) (hlarge : 2*K ≤ (N:ℝ)) :
    Certificate (choose (C_H*L*R*hilbertFactor d p N)
      ((2*K)^((p+2)/p)*L*R*continuationFactor p N)
      (H.method d L (supportFactor d p*R) x₀ N)
      (family (targetAccuracy K (L*R) (Schedule.beta p 2) N))) f g (dualExponent p) N
      (max C_H ((2*K)^((p+2)/p))*L*R*
        min (hilbertFactor d p N) (continuationFactor p N)) := by
  apply finite_dimension_envelope hd hp hCH (Real.rpow_nonneg (by linarith : 0 ≤ 2*K) _)
    hL.le hR.le H f g x₀ xstar N hN hconvex hgrad hmin hsmooth hradius
  exact accuracy_family_to_smooth_continuation hp hK hL hR f g family hfamily N hN hlarge

end P31.HilbertDiagnostics
