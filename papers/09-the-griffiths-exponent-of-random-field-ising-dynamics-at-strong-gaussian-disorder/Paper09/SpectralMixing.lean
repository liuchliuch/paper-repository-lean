/-
Copyright (c) 2026. The attained heat-bath gap and its actual spectral mode.
-/
import Paper09.Dynamics
import Paper09.Semigroup
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic

open Finset BigOperators Classical Real Metric Set Matrix

noncomputable section
namespace Paper09
namespace SpectralMixing

variable {V : Type*} [Fintype V]

/-- The genuine finite weighted `L²(p)` inner product. -/
def weightedInner {A : Type*} [Fintype A] (p : FinProb A) (f g : A → ℝ) : ℝ :=
  p.expect fun a => f a * g a

/-- The subspace of mean-zero functions, using the actual Gibbs weights. -/
def meanZero {A : Type*} [Fintype A] (p : FinProb A) : Submodule ℝ (A → ℝ) where
  carrier := {f | p.expect f = 0}
  zero_mem' := by simp [FinProb.expect]
  add_mem' := by
    intro f g hf hg
    change p.expect (fun a => f a + g a) = 0
    rw [FinProb.expect_add, hf, hg]; ring
  smul_mem' := by
    intro c f hf
    change p.expect (fun a => c * f a) = 0
    rw [FinProb.expect_smul, hf]; ring

def center {A : Type*} [Fintype A] (p : FinProb A) (f : A → ℝ) : A → ℝ :=
  fun a => f a - p.expect f

@[simp] theorem center_expect {A : Type*} [Fintype A] (p : FinProb A) (f : A → ℝ) :
    p.expect (center p f) = 0 := FinProb.expect_centered p f

@[simp] theorem center_variance {A : Type*} [Fintype A] (p : FinProb A) (f : A → ℝ) :
    p.variance (center p f) = p.variance f := by
  unfold FinProb.variance
  rw [center_expect]
  simp only [center, sub_zero]

@[simp] theorem center_dirichlet (p : FinProb (Config V)) (f : Config V → ℝ) :
    dirichletForm p (center p f) = dirichletForm p f := by
  unfold dirichletForm UpdateGraph.dirichlet
  congr 1
  apply sum_congr rfl; intro a ha
  apply sum_congr rfl; intro b hb
  congr 2
  dsimp [center]
  ring

theorem variance_smul {A : Type*} [Fintype A] (p : FinProb A) (c : ℝ) (f : A → ℝ) :
    p.variance (fun a => c*f a) = c^2 * p.variance f := by
  unfold FinProb.variance
  rw [FinProb.expect_smul]
  convert FinProb.expect_smul p (c^2)
    (fun a => (f a-p.expect f)*(f a-p.expect f)) using 1
  congr 1
  funext a
  ring

theorem dirichlet_smul (p : FinProb (Config V)) (c : ℝ) (f : Config V → ℝ) :
    dirichletForm p (fun a => c*f a) = c^2 * dirichletForm p f := by
  unfold dirichletForm UpdateGraph.dirichlet
  simp only [mul_sum]
  apply sum_congr rfl; intro a ha
  apply sum_congr rfl; intro b hb
  split_ifs <;> ring

theorem variance_pos_of_meanZero {A : Type*} [Fintype A]
    (p : FinProb A) (hp : ∀ a, 0 < p.w a) (f : A → ℝ)
    (hf : p.expect f = 0) (hne : f ≠ 0) : 0 < p.variance f := by
  have hex : ∃ a, f a ≠ 0 := by
    by_contra hh
    push_neg at hh
    apply hne
    funext a
    exact hh a
  obtain ⟨a, ha⟩ := hex
  unfold FinProb.variance FinProb.expect
  change 0 < ∑ b, p.w b * ((f b - p.expect f)*(f b-p.expect f))
  rw [hf]
  simp only [sub_zero]
  exact sum_pos' (fun b hb => mul_nonneg (p.nonneg b) (mul_self_nonneg _))
    ⟨a, mem_univ _, mul_pos (hp a) (mul_self_pos.mpr ha)⟩

theorem continuous_expect {A : Type*} [Fintype A] (p : FinProb A) :
    Continuous (fun f : A → ℝ => p.expect f) := by
  unfold FinProb.expect
  fun_prop

theorem continuous_variance {A : Type*} [Fintype A] (p : FinProb A) :
    Continuous (fun f : A → ℝ => p.variance f) := by
  unfold FinProb.variance FinProb.expect
  fun_prop

theorem continuous_dirichlet (p : FinProb (Config V)) :
    Continuous (fun f : Config V → ℝ => dirichletForm p f) := by
  unfold dirichletForm UpdateGraph.dirichlet
  apply continuous_const.mul
  apply continuous_finset_sum
  intro a ha
  apply continuous_finset_sum
  intro b hb
  split_ifs <;> fun_prop

private theorem normalize_mem {A : Type*} [Fintype A] (p : FinProb A)
    (f : A → ℝ) (hf : p.expect f = 0) (hne : f ≠ 0) :
    ((‖f‖⁻¹ : ℝ) • f) ∈ sphere (0 : A → ℝ) 1 ∩ {g | p.expect g = 0} := by
  have hn : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  constructor
  · simp [mem_sphere, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, hn]
  · change p.expect (fun a => ‖f‖⁻¹ * f a) = 0
    rw [FinProb.expect_smul, hf, mul_zero]

/-- The actual Rayleigh quotient attains the variational gap. -/
theorem gap_attained (p : FinProb (Config V)) (hp : ∀ a, 0 < p.w a) (x : V) :
    ∃ f : Config V → ℝ, p.expect f = 0 ∧ 0 < p.variance f ∧
      dirichletForm p f = spectralGap p * p.variance f := by
  classical
  let S : Set (Config V → ℝ) := sphere 0 1 ∩ {f | p.expect f = 0}
  let R := fun f : Config V → ℝ => dirichletForm p f / p.variance f
  have hc : IsCompact S := (isCompact_sphere (0 : Config V → ℝ) 1).inter_right
    (isClosed_eq (continuous_expect p) continuous_const)
  have hn : S.Nonempty := by
    let f := center p (fun η : Config V => spinVal (η x))
    have hne : f ≠ 0 := by
      intro hh
      have h0 := congrFun hh (fun _ => 0)
      have h1 := congrFun hh (fun _ => 1)
      dsimp [f, center] at h0 h1
      rw [spinVal_zero] at h0
      rw [spinVal_one] at h1
      linarith
    exact ⟨‖f‖⁻¹ • f, normalize_mem p f (center_expect _ _) hne⟩
  have hpos : ∀ f ∈ S, 0 < p.variance f := by
    intro f hf
    apply variance_pos_of_meanZero p hp f hf.2
    intro hz
    have hh : ‖f‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hf.1
    rw [hz, norm_zero] at hh
    norm_num at hh
  have hcont : ContinuousOn R S := (continuous_dirichlet p).continuousOn.div
    (continuous_variance p).continuousOn (fun f hf => ne_of_gt (hpos f hf))
  obtain ⟨f, hf, hmin⟩ := hc.exists_isMinOn hn hcont
  have hfvar := hpos f hf
  have hquot : ∀ g, 0 < p.variance g → R f ≤ R g := by
    intro g hg
    let g₀ := center p g
    have hg0 : g₀ ≠ 0 := by
      intro hh
      have hhvar : p.variance g₀ = 0 := by rw [hh]; simp [FinProb.variance, FinProb.expect]
      have hv : p.variance g₀ = p.variance g := center_variance p g
      linarith
    have hgn := normalize_mem p g₀ (center_expect p g) hg0
    have hh := hmin hgn
    change R f ≤ R ((‖g₀‖⁻¹ : ℝ) • g₀) at hh
    have hnorm : ‖g₀‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hg0)
    have hscale : R ((‖g₀‖⁻¹ : ℝ) • g₀) = R g := by
      change dirichletForm p (fun a => ‖g₀‖⁻¹ * g₀ a) /
        p.variance (fun a => ‖g₀‖⁻¹ * g₀ a) = _
      rw [dirichlet_smul, variance_smul, center_dirichlet, center_variance]
      dsimp [R]
      field_simp [hnorm]
    rwa [hscale] at hh
  have hray : (rayleighValues p).Nonempty := ⟨R f, f, hfvar, rfl⟩
  have hlow : R f ≤ spectralGap p := by
    rw [spectralGap, if_pos hray]
    apply le_csInf hray
    rintro r ⟨g, hg, rfl⟩
    exact hquot g hg
  have heq : R f = spectralGap p :=
    le_antisymm hlow (spectralGap_le_rayleigh p f hfvar)
  refine ⟨f, hf.2, hfvar, ?_⟩
  exact (div_eq_iff (ne_of_gt hfvar)).mp heq

theorem generator_affine (p : FinProb (Config V)) (f g : Config V → ℝ) (t : ℝ)
    (a : Config V) :
    heatBathGenerator p (fun b => f b + t*g b) a =
      heatBathGenerator p f a + t * heatBathGenerator p g a := by
  unfold heatBathGenerator
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl; intro b hb; ring

/-- Stationarity is derived directly from detailed balance. -/
theorem generator_expect_zero (p : FinProb (Config V)) (f : Config V → ℝ) :
    p.expect (heatBathGenerator p f) = 0 := by
  let c := fun a b => p.w a * heatBathRate p a b
  have hsym (a b : Config V) : c a b = c b a := heatBathRate_reversible p a b
  have hswap : (∑ a : Config V, ∑ b : Config V, c a b * f b) =
      ∑ a : Config V, ∑ b : Config V, c a b * f a := by
    rw [sum_comm]
    apply sum_congr rfl; intro a ha
    apply sum_congr rfl; intro b hb
    rw [hsym]
  have hh : p.expect (heatBathGenerator p f) =
      (∑ a : Config V, ∑ b : Config V, c a b * f b) -
      ∑ a : Config V, ∑ b : Config V, c a b * f a := by
    unfold FinProb.expect heatBathGenerator
    simp only [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro a ha
    apply sum_congr rfl; intro b hb
    dsimp [c]
    ring
  rw [hh, hswap, sub_self]

/-- The heat-bath generator is self-adjoint in the actual weighted inner product. -/
theorem generator_selfadjoint (p : FinProb (Config V)) (f g : Config V → ℝ) :
    weightedInner p f (heatBathGenerator p g) =
      weightedInner p (heatBathGenerator p f) g := by
  let c := fun a b => p.w a * heatBathRate p a b
  have hsym (a b : Config V) : c a b = c b a := heatBathRate_reversible p a b
  have hexpand (u v : Config V → ℝ) : weightedInner p u (heatBathGenerator p v) =
      (∑ a : Config V, ∑ b : Config V, c a b * u a * v b) -
      ∑ a : Config V, ∑ b : Config V, c a b * u a * v a := by
    unfold weightedInner FinProb.expect heatBathGenerator
    simp only [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro a ha
    apply sum_congr rfl; intro b hb
    dsimp [c]; ring
  have hswap : (∑ a : Config V, ∑ b : Config V, c a b * f a * g b) =
      ∑ a : Config V, ∑ b : Config V, c a b * g a * f b := by
    rw [sum_comm]
    apply sum_congr rfl; intro a ha
    apply sum_congr rfl; intro b hb
    rw [hsym]
    ring
  have hdiag : (∑ a : Config V, ∑ b : Config V, c a b * f a * g a) =
      ∑ a : Config V, ∑ b : Config V, c a b * g a * f a := by
    apply sum_congr rfl; intro a ha
    apply sum_congr rfl; intro b hb; ring
  have hcomm : weightedInner p (heatBathGenerator p f) g =
      weightedInner p g (heatBathGenerator p f) := by
    unfold weightedInner FinProb.expect
    apply sum_congr rfl; intro a ha; ring
  rw [hcomm, hexpand, hexpand, hswap, hdiag]

private theorem dirichlet_affine (p : FinProb (Config V)) (f g : Config V → ℝ) (t : ℝ) :
    dirichletForm p (fun a => f a+t*g a) = dirichletForm p f -
      2*t*weightedInner p f (heatBathGenerator p g) + t^2*dirichletForm p g := by
  have hs := generator_selfadjoint p f g
  rw [dirichletForm_eq_neg_generator, dirichletForm_eq_neg_generator,
    dirichletForm_eq_neg_generator]
  have hh : (∑ a, p.w a * ((f a+t*g a) * heatBathGenerator p (fun b => f b+t*g b) a)) =
      (∑ a, p.w a * (f a * heatBathGenerator p f a)) +
      t*(weightedInner p f (heatBathGenerator p g) + weightedInner p (heatBathGenerator p f) g) +
      t^2*(∑ a, p.w a*(g a * heatBathGenerator p g a)) := by
    unfold weightedInner FinProb.expect
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro a ha
    rw [generator_affine]
    ring
  change -(∑ a, p.w a * ((f a+t*g a) * heatBathGenerator p (fun b => f b+t*g b) a)) = _
  rw [hh, ← hs]
  dsimp [FinProb.expect]
  ring

private theorem variance_affine (p : FinProb (Config V)) (f g : Config V → ℝ)
    (hf : p.expect f = 0) (hg : p.expect g = 0) (t : ℝ) :
    p.variance (fun a => f a+t*g a) = p.variance f +
      2*t*weightedInner p f g + t^2*p.variance g := by
  have hm : p.expect (fun a => f a+t*g a) = 0 := by
    rw [FinProb.expect_add, FinProb.expect_smul, hf, hg]; ring
  unfold FinProb.variance
  rw [hm, hf, hg]
  unfold weightedInner FinProb.expect
  simp only [sub_zero, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl; intro a ha; ring

/-- Equality in the true Poincaré inequality forces the heat-bath eigen-equation. -/
theorem eigenfunction_of_attained (p : FinProb (Config V)) (hp : ∀ a, 0 < p.w a)
    (f : Config V → ℝ) (hf : p.expect f = 0)
    (heq : dirichletForm p f = spectralGap p * p.variance f) :
    ∀ a, heatBathGenerator p f a = - spectralGap p * f a := by
  have hcross (g : Config V → ℝ) (hg : p.expect g = 0) :
      -weightedInner p f (heatBathGenerator p g) = spectralGap p * weightedInner p f g := by
    have hnonneg : ∀ t : ℝ,
        (dirichletForm p g - spectralGap p * p.variance g) * (t*t) +
          (2*(-weightedInner p f (heatBathGenerator p g) -
            spectralGap p * weightedInner p f g))*t + 0 ≥ 0 := by
      intro t
      have hh := spectralGap_poincare p (fun a => f a+t*g a)
      rw [dirichlet_affine, variance_affine p f g hf hg, heq] at hh
      nlinarith
    have hd := discrim_le_zero hnonneg
    unfold discrim at hd
    nlinarith [sq_nonneg (-weightedInner p f (heatBathGenerator p g) -
      spectralGap p * weightedInner p f g)]
  intro a
  let g := center p (fun b : Config V => if b = a then 1 else 0)
  have hh := hcross g (center_expect _ _)
  rw [generator_selfadjoint] at hh
  have hgen := generator_expect_zero p f
  have hleft : weightedInner p (heatBathGenerator p f) g = p.w a * heatBathGenerator p f a := by
    unfold weightedInner g center FinProb.expect
    simp only [mul_sub, mul_one, mul_zero, mul_ite, sum_sub_distrib, ← mul_assoc, ← sum_mul]
    rw [show (∑ b, p.w b * heatBathGenerator p f b) = 0 from hgen]
    simp
  have hright : weightedInner p f g = p.w a * f a := by
    unfold weightedInner g center FinProb.expect
    simp only [mul_sub, mul_one, mul_zero, mul_ite, sum_sub_distrib, ← mul_assoc, ← sum_mul]
    rw [show (∑ b, p.w b * f b) = 0 from hf]
    simp
  rw [hleft, hright] at hh
  have ha := hp a
  nlinarith

/-- An actual mean-zero gap eigenfunction exists for every strictly positive
finite heat-bath law on a nonempty site set. -/
theorem gap_eigenfunction (p : FinProb (Config V)) (hp : ∀ a, 0 < p.w a) (x : V) :
    ∃ f : Config V → ℝ, p.expect f = 0 ∧ 0 < p.variance f ∧
      ∀ a, heatBathGenerator p f a = -spectralGap p * f a := by
  obtain ⟨f, hf, hv, he⟩ := gap_attained p hp x
  exact ⟨f, hf, hv, eigenfunction_of_attained p hp f hf he⟩

/-- The un-clamped matrix exponential preserves the weighted mean at every
real time; positivity is unnecessary for this algebraic stationary identity. -/
theorem semigroup_expect (p : FinProb (Config V)) (f : Config V → ℝ) (t : ℝ) :
    p.expect (heatBathSemigroup p t *ᵥ f) = p.expect f := by
  unfold FinProb.expect Matrix.mulVec dotProduct
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro b hb
  calc (∑ a, p.w a * (heatBathSemigroup p t a b * f b)) =
      ∑ a, (p.w b * f b) * heatBathSemigroup p t b a := by
        apply sum_congr rfl; intro a ha
        calc p.w a * (heatBathSemigroup p t a b * f b) =
            (p.w a * heatBathSemigroup p t a b) * f b := by ring
          _ = (p.w b * heatBathSemigroup p t b a) * f b := by rw [heatBathSemigroup_reversible]
          _ = _ := by ring
    _ = p.w b * f b := by rw [← mul_sum, heatBathSemigroup_rows, mul_one]

private theorem semigroup_square_hasDerivAt (p : FinProb (Config V))
    (f : Config V → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => weightedInner p (heatBathSemigroup p s *ᵥ f)
      (heatBathSemigroup p s *ᵥ f))
      (-2 * dirichletForm p (heatBathSemigroup p t *ᵥ f)) t := by
  have h (a : Config V) := heatBathSemigroup_hasDerivAt p f t a
  have hd := HasDerivAt.fun_sum (u := univ) (fun a ha => ((h a).mul (h a)).const_mul (p.w a))
  convert hd using 1
  rw [dirichletForm_eq_neg_generator]
  unfold FinProb.expect
  simp only [neg_mul_neg, mul_sum]
  apply sum_congr rfl; intro a ha; ring

/-- The actual heat-bath evolution contracts mean-zero weighted `L²` at the
variational spectral-gap rate. No eigenbasis or decay estimate is assumed. -/
theorem weighted_l2_decay (p : FinProb (Config V)) (f : Config V → ℝ)
    (hf : p.expect f = 0) (t : ℝ) (ht : 0 ≤ t) :
    (∑ a, p.w a * ((heatBathSemigroup p t *ᵥ f) a)^2) ≤
      exp (-2*spectralGap p*t) * (∑ a, p.w a * (f a)^2) := by
  let H := fun s : ℝ => weightedInner p (heatBathSemigroup p s *ᵥ f)
    (heatBathSemigroup p s *ᵥ f)
  let G := fun s : ℝ => exp (2*spectralGap p*s) * H s
  have hH (s : ℝ) : HasDerivAt H (-2*dirichletForm p (heatBathSemigroup p s *ᵥ f)) s :=
    semigroup_square_hasDerivAt p f s
  have hG (s : ℝ) : HasDerivAt G
      (exp (2*spectralGap p*s) * (2*spectralGap p*H s -
        2*dirichletForm p (heatBathSemigroup p s *ᵥ f))) s := by
    have he : HasDerivAt (fun s : ℝ => exp (2*spectralGap p*s))
        (exp (2*spectralGap p*s) * (2*spectralGap p)) s :=
      by simpa only [id_eq, mul_one] using (((hasDerivAt_id s).const_mul (2*spectralGap p)).exp)
    convert he.mul (hH s) using 1 <;> dsimp [G] <;> ring
  have hanti : Antitone G := by
    apply antitone_of_deriv_nonpos (fun s => (hG s).differentiableAt)
    intro s
    rw [(hG s).deriv]
    have hm : p.expect (heatBathSemigroup p s *ᵥ f) = 0 := by rw [semigroup_expect, hf]
    have hv : p.variance (heatBathSemigroup p s *ᵥ f) = H s := by
      unfold FinProb.variance
      rw [hm]
      simp only [sub_zero]
      rfl
    have hp := spectralGap_poincare p (heatBathSemigroup p s *ᵥ f)
    rw [hv] at hp
    exact mul_nonpos_of_nonneg_of_nonpos (exp_nonneg _) (by linarith)
  have hh := hanti ht
  have hzero : G 0 = ∑ a, p.w a * (f a)^2 := by
    simp only [G, H, heatBathSemigroup_zero, Matrix.one_mulVec, mul_zero, exp_zero, one_mul,
      weightedInner, FinProb.expect, ← sq]
  rw [hzero] at hh
  have hpos : 0 < exp (2*spectralGap p*t) := exp_pos _
  have hbound : H t ≤ (∑ a, p.w a*(f a)^2) / exp (2*spectralGap p*t) := by
    rw [le_div_iff₀ hpos]
    simpa only [G, mul_comm] using hh
  have hexp : exp (-2*spectralGap p*t) = (exp (2*spectralGap p*t))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hexp]
  simpa only [H, weightedInner, FinProb.expect, ← sq, div_eq_mul_inv, mul_comm] using hbound

end SpectralMixing
end Paper09
