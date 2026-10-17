import Paper29.ScoreMonotonicity
import Paper29.AllScale

noncomputable section
open scoped BigOperators ENNReal
namespace Paper29.Chaining

/-- The two endpoint population geometries; powers are the literal p=1,2. -/
def powerPhi {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (p : ℕ) (h : Fin d → ℝ) : ℝ :=
  ∑ i, |(A.mulVec h) i|^p

abbrev PowerBall {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (p : ℕ) (S : ℝ) :=
  {h : Fin d → ℝ // powerPhi A p h ≤ S}

def powerMetric {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (p : ℕ)
    (ℓ : Fin n → ℝ) (h k : Fin d → ℝ) : ℝ≥0∞ :=
  ⨆ i, ENNReal.ofReal (Real.sqrt (|(A.mulVec (h-k)) i|^p / ℓ i))

/-- Endpoint cover property, kept distinct from the all-radius Huber claim. -/
def EndpointCover {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (p : ℕ)
    (ℓ : Fin n → ℝ) (G : ℝ) : Prop :=
  ∀ S, 0 < S → gamma2 (T := PowerBall A p S) (fun h k => powerMetric A p ℓ h k) ≤
    ENNReal.ofReal (G * Real.sqrt S)

/-- The exact quadratic identity at the sharp Huber threshold. -/
theorem small_huber_ball {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    {R : ℝ} (hR : R ≤ 1/2) (h : Fin d → ℝ) (hh : unshifted A h ≤ R) :
    powerPhi A 2 h = 2 * unshifted A h := by
  have he (i : Fin n) : huber ((A.mulVec h) i) = |(A.mulVec h) i|^2 / 2 := by
    have hi : huber ((A.mulVec h) i) ≤ unshifted A h :=
      Finset.single_le_sum (fun j _ => huber_nonneg _) (Finset.mem_univ i)
    rw [AllScale.huber_quadratic (AllScale.quadratic_of_small_huber ((hi.trans hh).trans hR)), sq_abs]
  unfold powerPhi unshifted
  simp_rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The large-radius l1 containment follows from H(t)>=|t|-1/2. -/
theorem large_huber_ball {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    {R : ℝ} (hR : (n:ℝ)/2 ≤ R) (h : Fin d → ℝ) (hh : unshifted A h ≤ R) :
    powerPhi A 1 h ≤ 2 * R := by
  have hs := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => abs_sub_half_le_huber ((A.mulVec h) i))
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hs
  unfold powerPhi
  simp only [pow_one]
  unfold unshifted at hh
  linarith

theorem huberMetric_le_endpoint_one {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (τ ℓ : Fin n → ℝ) (hℓ : ∀ i, 0 < ℓ i) (hdom : ∀ i, ℓ i ≤ τ i)
    (x y : Fin d → ℝ) : huberMetric A τ x y ≤ powerMetric A 1 ℓ x y := by
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ huber ((A.mulVec (x-y)) i) / ℓ i :=
      div_le_div_of_nonneg_left (huber_nonneg _) (hℓ i) (hdom i)
    _ ≤ _ := by simpa only [pow_one] using
      div_le_div_of_nonneg_right (huber_le_abs _) (hℓ i).le

/-- A harmless universal factor is absorbed later: H(t)<=t²/2<=t². -/
theorem huberMetric_le_endpoint_two {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (τ ℓ : Fin n → ℝ) (hℓ : ∀ i, 0 < ℓ i) (hdom : ∀ i, ℓ i ≤ τ i)
    (x y : Fin d → ℝ) : huberMetric A τ x y ≤ powerMetric A 2 ℓ x y := by
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  apply ENNReal.ofReal_le_ofReal
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ huber ((A.mulVec (x-y)) i) / ℓ i :=
      div_le_div_of_nonneg_left (huber_nonneg _) (hℓ i) (hdom i)
    _ ≤ _ := div_le_div_of_nonneg_right (by
      rw [sq_abs]
      have hs := huber_le_sq ((A.mulVec (x-y)) i)
      nlinarith [sq_nonneg ((A.mulVec (x-y)) i)]) (hℓ i).le

/-- The small-radius part of Lemma3.4 is an own pullback argument from the
quadratic endpoint cover. -/
theorem small_radius_cover {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (τ ℓ : Fin n → ℝ) (hℓ : ∀ i, 0 < ℓ i) (hdom : ∀ i, ℓ i ≤ τ i)
    {G R : ℝ} (hG : 0 ≤ G) (cover : EndpointCover A 2 ℓ G)
    (hR : 0 < R) (hsmall : R ≤ 1/2) :
    gamma2 (T := ProcessTools.Ball A R) (fun x y => huberMetric A τ x y) ≤
      ENNReal.ofReal (2*G*Real.sqrt R) := by
  let f : ProcessTools.Ball A R → PowerBall A 2 (2*R) :=
    fun h => ⟨h, by rw [small_huber_ball A hsmall h h.property]; linarith [h.property]⟩
  have hp := gamma2_pullback f (fun x y => huberMetric A τ x y)
    (fun x y => powerMetric A 2 ℓ x y) (fun x y => huberMetric_le_endpoint_two A τ ℓ hℓ hdom x y)
  apply (hp.trans (cover (2*R) (by positivity))).trans
  apply ENNReal.ofReal_le_ofReal
  have hs : Real.sqrt (2*R) ≤ 2 * Real.sqrt R := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
    rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hR.le]
    nlinarith
  nlinarith

/-- The large-radius part uses the actual l1 containment and metric bound. -/
theorem large_radius_cover {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (τ ℓ : Fin n → ℝ) (hℓ : ∀ i, 0 < ℓ i) (hdom : ∀ i, ℓ i ≤ τ i)
    {G R : ℝ} (hG : 0 ≤ G) (cover : EndpointCover A 1 ℓ G)
    (hR : 0 < R) (hlarge : (n:ℝ)/2 ≤ R) :
    gamma2 (T := ProcessTools.Ball A R) (fun x y => huberMetric A τ x y) ≤
      ENNReal.ofReal (2*G*Real.sqrt R) := by
  let f : ProcessTools.Ball A R → PowerBall A 1 (2*R) :=
    fun h => ⟨h, large_huber_ball A hlarge h h.property⟩
  have hp := gamma2_pullback f (fun x y => huberMetric A τ x y)
    (fun x y => powerMetric A 1 ℓ x y) (fun x y => huberMetric_le_endpoint_one A τ ℓ hℓ hdom x y)
  apply (hp.trans (cover (2*R) (by positivity))).trans
  apply ENNReal.ofReal_le_ofReal
  have hs : Real.sqrt (2*R) ≤ 2 * Real.sqrt R := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
    rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt hR.le]
    nlinarith
  nlinarith

end Paper29.Chaining
