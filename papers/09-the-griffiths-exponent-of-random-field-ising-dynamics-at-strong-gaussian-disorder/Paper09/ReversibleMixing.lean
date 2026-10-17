/-
Copyright (c) 2026. Appendix A.1 for arbitrary finite irreducible reversible
continuous-time chains. All dynamics are constructed from actual jump rates.
-/
import Paper09.SpectralMixing
import Paper09.MixingTimes
import Mathlib.Logic.Relation

open Finset BigOperators Classical Real Metric Set Matrix
open scoped Matrix.Norms.Operator

noncomputable section
set_option maxHeartbeats 800000
namespace Paper09.ReversibleMixing

/-- The data of a finite reversible continuous-time chain. `R` gives its actual
off-diagonal jump rates; diagonal values are ignored. Irreducibility is
connectivity by finite positive-rate paths, not a spectral assumption. -/
structure Chain (α : Type*) [Fintype α] where
  p : FinProb α
  positive : ∀ a, 0 < p.w a
  R : α → α → ℝ
  offdiag_nonneg : ∀ a b, a ≠ b → 0 ≤ R a b
  balance : ∀ a b, p.w a * R a b = p.w b * R b a
  connected : ∀ a b, Relation.ReflTransGen (fun x y => x ≠ y ∧ 0 < R x y) a b

variable {α : Type*} [Fintype α]

/-- Nonnegative jump-rate matrix with irrelevant diagonal erased. -/
def rate (C : Chain α) (a b : α) : ℝ := if a = b then 0 else C.R a b

theorem rate_nonneg (C : Chain α) (a b : α) : 0 ≤ rate C a b := by
  unfold rate
  split_ifs with h
  · exact le_rfl
  · exact C.offdiag_nonneg a b h

theorem rate_reversible (C : Chain α) (a b : α) : C.p.w a * rate C a b = C.p.w b * rate C b a := by
  by_cases h : a = b
  · subst b; rfl
  · simpa [rate, h, Ne.symm h] using C.balance a b

/-- The backward generator at the chain's actual time normalization. -/
def generator (C : Chain α) (f : α → ℝ) (a : α) : ℝ :=
  ∑ b, rate C a b * (f b - f a)

/-- The continuous-time Dirichlet form with the ordered-edge factor `1/2`. -/
def energy (C : Chain α) (f : α → ℝ) : ℝ :=
  (1/2) * ∑ a, ∑ b, (C.p.w a * rate C a b) * (f a - f b)^2

theorem energy_nonneg (C : Chain α) (f : α → ℝ) : 0 ≤ energy C f := by
  apply mul_nonneg (by norm_num)
  exact sum_nonneg fun a _ => sum_nonneg fun b _ =>
    mul_nonneg (mul_nonneg (C.p.nonneg a) (rate_nonneg C a b)) (sq_nonneg _)

theorem energy_eq_neg_generator (C : Chain α) (f : α → ℝ) :
    energy C f = -C.p.expect (fun a => f a * generator C f a) := by
  let c := fun a b => C.p.w a * rate C a b
  have hsym (a b : α) : c a b = c b a := rate_reversible C a b
  have hswap : (∑ a : α, ∑ b : α, c a b * (f b)^2) = ∑ a : α, ∑ b : α, c a b * (f a)^2 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro a _
    apply sum_congr rfl
    intro b _
    rw [hsym]
  change (1/2:ℝ) * (∑ a : α, ∑ b : α, c a b * (f a-f b)^2) = _
  have halg (a b : α) : c a b * (f a-f b)^2 = c a b*(f a)^2 + c a b*(f b)^2 -2*(c a b*f a*f b) := by ring
  simp_rw [halg, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  rw [hswap]
  unfold FinProb.expect generator
  simp_rw [mul_sum]
  have hp (a b : α) : C.p.w a*(f a*(rate C a b*(f b-f a))) = c a b*f a*f b-c a b*(f a)^2 := by
    dsimp [c]
    ring
  simp_rw [hp, sum_sub_distrib, ← mul_sum]
  ring

def rayleighValues (C : Chain α) : Set ℝ :=
  {r | ∃ f : α → ℝ, 0 < C.p.variance f ∧ r = energy C f / C.p.variance f}

def gap (C : Chain α) : ℝ := if (rayleighValues C).Nonempty then sInf (rayleighValues C) else 0

def relaxationTime (C : Chain α) : ℝ := (gap C)⁻¹

theorem rayleighValues_bddBelow (C : Chain α) : BddBelow (rayleighValues C) := by
  refine ⟨0, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  exact div_nonneg (energy_nonneg C f) hf.le

theorem gap_nonneg (C : Chain α) : 0 ≤ gap C := by
  unfold gap
  split_ifs with h
  · refine le_csInf h ?_
    rintro r ⟨f, hf, rfl⟩
    exact div_nonneg (energy_nonneg C f) hf.le
  · exact le_rfl

theorem gap_le_rayleigh (C : Chain α) (f : α → ℝ) (hf : 0 < C.p.variance f) :
    gap C ≤ energy C f / C.p.variance f := by
  have hm : energy C f / C.p.variance f ∈ rayleighValues C := ⟨f, hf, rfl⟩
  rw [gap, if_pos ⟨_, hm⟩]
  exact csInf_le (rayleighValues_bddBelow C) hm

theorem gap_poincare (C : Chain α) (f : α → ℝ) : gap C * C.p.variance f ≤ energy C f := by
  by_cases hf : 0 < C.p.variance f
  · exact (le_div_iff₀ hf).mp (gap_le_rayleigh C f hf)
  · have hz : C.p.variance f = 0 := le_antisymm (le_of_not_gt hf) (FinProb.variance_nonneg _ _)
    rw [hz, mul_zero]
    exact energy_nonneg C f

/-- The actual rate matrix, with the negative exit-rate diagonal. -/
def matrix (C : Chain α) : Matrix α α ℝ :=
  fun a b => rate C a b - if a = b then ∑ c, rate C a c else 0

theorem matrix_mulVec (C : Chain α) (f : α → ℝ) : matrix C *ᵥ f = generator C f := by
  funext a
  classical
  simp only [Matrix.mulVec, dotProduct, matrix, sub_mul, sum_sub_distrib, ite_mul, zero_mul,
    sum_ite_eq, Finset.mem_univ, if_true]
  unfold generator
  simp only [mul_sub, sum_sub_distrib, sum_mul, Finset.mem_univ, if_true]

theorem matrix_rows (C : Chain α) (a : α) : ∑ b, matrix C a b = 0 := by
  classical
  simp [matrix, sum_sub_distrib]

theorem matrix_reversible (C : Chain α) (a b : α) : C.p.w a * matrix C a b = C.p.w b * matrix C b a := by
  classical
  by_cases h : a = b
  · subst b; rfl
  · simpa only [matrix, if_neg h, if_neg (Ne.symm h), sub_zero] using rate_reversible C a b

def semigroup (C : Chain α) (t : ℝ) : Matrix α α ℝ := NormedSpace.exp ℝ (t • matrix C)

@[simp] theorem semigroup_zero (C : Chain α) : semigroup C 0 = 1 := by simp [semigroup]

theorem semigroup_add (C : Chain α) (s t : ℝ) : semigroup C (s+t) = semigroup C s * semigroup C t := by
  classical
  unfold semigroup
  rw [add_smul]
  apply Matrix.exp_add_of_commute
  change (s • matrix C)*(t • matrix C) = (t • matrix C)*(s • matrix C)
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm s t]

theorem semigroup_rows (C : Chain α) (t : ℝ) (a : α) : ∑ b, semigroup C t a b = 1 := by
  classical
  apply matrix_exp_rows
  intro a
  simp only [Matrix.smul_apply, smul_eq_mul, ← mul_sum, matrix_rows, mul_zero]

theorem semigroup_nonneg (C : Chain α) (t : ℝ) (ht : 0 ≤ t) (a b : α) : 0 ≤ semigroup C t a b := by
  classical
  let R : ℝ := ∑ i : α, ∑ j : α, rate C i j
  apply matrix_exp_nonneg_of_shift (t • matrix C) (t*R)
  intro i j
  have hrow : (∑ k, rate C i k) ≤ R :=
    single_le_sum (fun l _ => sum_nonneg fun k _ => rate_nonneg C l k) (mem_univ i)
  by_cases h : i = j
  · subst j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, matrix,
      Matrix.one_apply_eq, ite_true, mul_one]
    nlinarith [rate_nonneg C i i]
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, matrix, if_neg h,
      sub_zero, Matrix.one_apply_ne h, mul_zero, add_zero]
    exact mul_nonneg ht (rate_nonneg C i j)

theorem semigroup_reversible (C : Chain α) (t : ℝ) (a b : α) :
    C.p.w a * semigroup C t a b = C.p.w b * semigroup C t b a := by
  classical
  apply matrix_exp_reversible
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  calc
    _ = t*(C.p.w i*matrix C i j) := by ring
    _ = t*(C.p.w j*matrix C j i) := by rw [matrix_reversible]
    _ = _ := by ring

def transition (C : Chain α) (t : ℝ) (a : α) : FinProb α where
  w b := semigroup C (max t 0) a b
  nonneg b := semigroup_nonneg C (max t 0) (le_max_right _ _) a b
  sum_one := semigroup_rows C (max t 0) a

theorem transition_w (C : Chain α) (t : ℝ) (ht : 0 ≤ t) (a b : α) :
    (transition C t a).w b = semigroup C t a b := by simp [transition, max_eq_left ht]
/-- The constructed transition kernels satisfy detailed balance and hence
preserve the stationary law. -/
theorem transition_stationary (C : Chain α) (t : ℝ) :
    MarkovKernel.Stationary (transition C t) C.p :=
  MarkovKernel.stationary_of_reversible _ _ (fun a b => semigroup_reversible C (max t 0) a b)


def mixingTime (C : Chain α) (ε : ℝ) : ℝ := tMix C.p (transition C) ε

theorem semigroup_hasDerivAt (C : Chain α) (f : α → ℝ) (t : ℝ) (a : α) :
    HasDerivAt (fun s : ℝ => (semigroup C s *ᵥ f) a) (generator C (semigroup C t *ᵥ f) a) t := by
  classical
  have h (b : α) := (matrix_semigroup_hasDerivAt (matrix C) t a b).mul_const (f b)
  have hh := HasDerivAt.fun_sum (u := univ) (fun b _ => h b)
  change HasDerivAt (fun s : ℝ => (semigroup C s *ᵥ f) a)
    (((matrix C * semigroup C t) *ᵥ f) a) t at hh
  simpa only [← Matrix.mulVec_mulVec, matrix_mulVec] using hh

theorem semigroup_eigenfunction (C : Chain α) (f : α → ℝ) (r t : ℝ)
    (hf : ∀ a, generator C f a = r*f a) :
    semigroup C t *ᵥ f = fun a => Real.exp (t*r)*f a := by
  classical
  apply matrix_exp_mulVec_eigen
  rw [Matrix.smul_mulVec, matrix_mulVec]
  funext a
  simp only [Pi.smul_apply, smul_eq_mul, hf]
  ring



variable [Nontrivial α]

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

@[simp] theorem center_dirichlet (C : Chain α) (f : α → ℝ) :
    energy C (center C.p f) = energy C f := by
  unfold energy
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

theorem dirichlet_smul (C : Chain α) (c : ℝ) (f : α → ℝ) :
    energy C (fun a => c*f a) = c^2 * energy C f := by
  unfold energy
  simp only [mul_sum]
  apply sum_congr rfl; intro a ha
  apply sum_congr rfl; intro b hb
  ring

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

theorem continuous_dirichlet (C : Chain α) :
    Continuous (fun f : α → ℝ => energy C f) := by
  unfold energy
  fun_prop

private theorem normalize_mem {A : Type*} [Fintype A] (p : FinProb A)
    (f : A → ℝ) (hf : p.expect f = 0) (hne : f ≠ 0) :
    ((‖f‖⁻¹ : ℝ) • f) ∈ sphere (0 : A → ℝ) 1 ∩ {g | p.expect g = 0} := by
  have hn : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  constructor
  · simp [mem_sphere, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, hn]
  · change p.expect (fun a => ‖f‖⁻¹ * f a) = 0
    rw [FinProb.expect_smul, hf, mul_zero]

/-- The actual Rayleigh quotient attains the variational gap. -/
theorem gap_attained (C : Chain α)  :
    ∃ f : α → ℝ, C.p.expect f = 0 ∧ 0 < C.p.variance f ∧
      energy C f = gap C * C.p.variance f := by
  classical
  let S : Set (α → ℝ) := sphere 0 1 ∩ {f | C.p.expect f = 0}
  let R := fun f : α → ℝ => energy C f / C.p.variance f
  have hc : IsCompact S := (isCompact_sphere (0 : α → ℝ) 1).inter_right
    (isClosed_eq (continuous_expect C.p) continuous_const)
  have hn : S.Nonempty := by
    obtain ⟨a, b, hab⟩ := exists_pair_ne α
    let f := center C.p (fun c : α => if c = a then 1 else 0)
    have hne : f ≠ 0 := by
      intro hh
      have h0 := congrFun hh a
      have h1 := congrFun hh b
      dsimp [f, center] at h0 h1
      simp only [ite_true] at h0
      simp only [if_neg (Ne.symm hab)] at h1
      linarith
    exact ⟨‖f‖⁻¹ • f, normalize_mem C.p f (center_expect _ _) hne⟩
  have hpos : ∀ f ∈ S, 0 < C.p.variance f := by
    intro f hf
    apply variance_pos_of_meanZero C.p C.positive f hf.2
    intro hz
    have hh : ‖f‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hf.1
    rw [hz, norm_zero] at hh
    norm_num at hh
  have hcont : ContinuousOn R S := (continuous_dirichlet C).continuousOn.div
    (continuous_variance C.p).continuousOn (fun f hf => ne_of_gt (hpos f hf))
  obtain ⟨f, hf, hmin⟩ := hc.exists_isMinOn hn hcont
  have hfvar := hpos f hf
  have hquot : ∀ g, 0 < C.p.variance g → R f ≤ R g := by
    intro g hg
    let g₀ := center C.p g
    have hg0 : g₀ ≠ 0 := by
      intro hh
      have hhvar : C.p.variance g₀ = 0 := by rw [hh]; simp [FinProb.variance, FinProb.expect]
      have hv : C.p.variance g₀ = C.p.variance g := center_variance C.p g
      linarith
    have hgn := normalize_mem C.p g₀ (center_expect C.p g) hg0
    have hh := hmin hgn
    change R f ≤ R ((‖g₀‖⁻¹ : ℝ) • g₀) at hh
    have hnorm : ‖g₀‖⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hg0)
    have hscale : R ((‖g₀‖⁻¹ : ℝ) • g₀) = R g := by
      change energy C (fun a => ‖g₀‖⁻¹ * g₀ a) /
        C.p.variance (fun a => ‖g₀‖⁻¹ * g₀ a) = _
      rw [dirichlet_smul, variance_smul, center_dirichlet, center_variance]
      dsimp [R]
      field_simp [hnorm]
    rwa [hscale] at hh
  have hray : (rayleighValues C).Nonempty := ⟨R f, f, hfvar, rfl⟩
  have hlow : R f ≤ gap C := by
    rw [gap, if_pos hray]
    apply le_csInf hray
    rintro r ⟨g, hg, rfl⟩
    exact hquot g hg
  have heq : R f = gap C :=
    le_antisymm hlow (gap_le_rayleigh C f hfvar)
  refine ⟨f, hf.2, hfvar, ?_⟩
  exact (div_eq_iff (ne_of_gt hfvar)).mp heq

theorem generator_affine (C : Chain α) (f g : α → ℝ) (t : ℝ)
    (a : α) :
    generator C (fun b => f b + t*g b) a =
      generator C f a + t * generator C g a := by
  unfold generator
  rw [mul_sum, ← sum_add_distrib]
  apply sum_congr rfl; intro b hb; ring

/-- Stationarity is derived directly from detailed balance. -/
theorem generator_expect_zero (C : Chain α) (f : α → ℝ) :
    C.p.expect (generator C f) = 0 := by
  let c := fun a b => C.p.w a * rate C a b
  have hsym (a b : α) : c a b = c b a := rate_reversible C a b
  have hswap : (∑ a : α, ∑ b : α, c a b * f b) =
      ∑ a : α, ∑ b : α, c a b * f a := by
    rw [sum_comm]
    apply sum_congr rfl; intro a ha
    apply sum_congr rfl; intro b hb
    rw [hsym]
  have hh : C.p.expect (generator C f) =
      (∑ a : α, ∑ b : α, c a b * f b) -
      ∑ a : α, ∑ b : α, c a b * f a := by
    unfold FinProb.expect generator
    simp only [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro a ha
    apply sum_congr rfl; intro b hb
    dsimp [c]
    ring
  rw [hh, hswap, sub_self]

/-- The actual reversible generator is self-adjoint in the actual weighted inner product. -/
theorem generator_selfadjoint (C : Chain α) (f g : α → ℝ) :
    weightedInner C.p f (generator C g) =
      weightedInner C.p (generator C f) g := by
  let c := fun a b => C.p.w a * rate C a b
  have hsym (a b : α) : c a b = c b a := rate_reversible C a b
  have hexpand (u v : α → ℝ) : weightedInner C.p u (generator C v) =
      (∑ a : α, ∑ b : α, c a b * u a * v b) -
      ∑ a : α, ∑ b : α, c a b * u a * v a := by
    unfold weightedInner FinProb.expect generator
    simp only [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro a ha
    apply sum_congr rfl; intro b hb
    dsimp [c]; ring
  have hswap : (∑ a : α, ∑ b : α, c a b * f a * g b) =
      ∑ a : α, ∑ b : α, c a b * g a * f b := by
    rw [sum_comm]
    apply sum_congr rfl; intro a ha
    apply sum_congr rfl; intro b hb
    rw [hsym]
    ring
  have hdiag : (∑ a : α, ∑ b : α, c a b * f a * g a) =
      ∑ a : α, ∑ b : α, c a b * g a * f a := by
    apply sum_congr rfl; intro a ha
    apply sum_congr rfl; intro b hb; ring
  have hcomm : weightedInner C.p (generator C f) g =
      weightedInner C.p g (generator C f) := by
    unfold weightedInner FinProb.expect
    apply sum_congr rfl; intro a ha; ring
  rw [hcomm, hexpand, hexpand, hswap, hdiag]

private theorem dirichlet_affine (C : Chain α) (f g : α → ℝ) (t : ℝ) :
    energy C (fun a => f a+t*g a) = energy C f -
      2*t*weightedInner C.p f (generator C g) + t^2*energy C g := by
  have hs := generator_selfadjoint C f g
  rw [energy_eq_neg_generator, energy_eq_neg_generator,
    energy_eq_neg_generator]
  have hh : (∑ a, C.p.w a * ((f a+t*g a) * generator C (fun b => f b+t*g b) a)) =
      (∑ a, C.p.w a * (f a * generator C f a)) +
      t*(weightedInner C.p f (generator C g) + weightedInner C.p (generator C f) g) +
      t^2*(∑ a, C.p.w a*(g a * generator C g a)) := by
    unfold weightedInner FinProb.expect
    simp only [mul_sum, ← sum_add_distrib]
    apply sum_congr rfl; intro a ha
    rw [generator_affine]
    ring
  change -(∑ a, C.p.w a * ((f a+t*g a) * generator C (fun b => f b+t*g b) a)) = _
  rw [hh, ← hs]
  dsimp [FinProb.expect]
  ring

private theorem variance_affine (C : Chain α) (f g : α → ℝ)
    (hf : C.p.expect f = 0) (hg : C.p.expect g = 0) (t : ℝ) :
    C.p.variance (fun a => f a+t*g a) = C.p.variance f +
      2*t*weightedInner C.p f g + t^2*C.p.variance g := by
  have hm : C.p.expect (fun a => f a+t*g a) = 0 := by
    rw [FinProb.expect_add, FinProb.expect_smul, hf, hg]; ring
  unfold FinProb.variance
  rw [hm, hf, hg]
  unfold weightedInner FinProb.expect
  simp only [sub_zero, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl; intro a ha; ring

/-- Equality in the true Poincaré inequality forces the actual generator eigen-equation. -/
theorem eigenfunction_of_attained (C : Chain α) (f : α → ℝ) (hf : C.p.expect f = 0)
    (heq : energy C f = gap C * C.p.variance f) :
    ∀ a, generator C f a = - gap C * f a := by
  have hcross (g : α → ℝ) (hg : C.p.expect g = 0) :
      -weightedInner C.p f (generator C g) = gap C * weightedInner C.p f g := by
    have hnonneg : ∀ t : ℝ,
        (energy C g - gap C * C.p.variance g) * (t*t) +
          (2*(-weightedInner C.p f (generator C g) -
            gap C * weightedInner C.p f g))*t + 0 ≥ 0 := by
      intro t
      have hh := gap_poincare C (fun a => f a+t*g a)
      rw [dirichlet_affine, variance_affine C f g hf hg, heq] at hh
      nlinarith
    have hd := discrim_le_zero hnonneg
    unfold discrim at hd
    nlinarith [sq_nonneg (-weightedInner C.p f (generator C g) -
      gap C * weightedInner C.p f g)]
  intro a
  let g := center C.p (fun b : α => if b = a then 1 else 0)
  have hh := hcross g (center_expect _ _)
  rw [generator_selfadjoint] at hh
  have hgen := generator_expect_zero C f
  have hleft : weightedInner C.p (generator C f) g = C.p.w a * generator C f a := by
    unfold weightedInner g center FinProb.expect
    simp only [mul_sub, mul_one, mul_zero, mul_ite, sum_sub_distrib, ← mul_assoc, ← sum_mul]
    rw [show (∑ b, C.p.w b * generator C f b) = 0 from hgen]
    simp
  have hright : weightedInner C.p f g = C.p.w a * f a := by
    unfold weightedInner g center FinProb.expect
    simp only [mul_sub, mul_one, mul_zero, mul_ite, sum_sub_distrib, ← mul_assoc, ← sum_mul]
    rw [show (∑ b, C.p.w b * f b) = 0 from hf]
    simp
  rw [hleft, hright] at hh
  have ha := C.positive a
  nlinarith

/-- An actual mean-zero gap eigenfunction exists for every finite reversible chain
on at least two states with positive stationary weights. -/
theorem gap_eigenfunction (C : Chain α)  :
    ∃ f : α → ℝ, C.p.expect f = 0 ∧ 0 < C.p.variance f ∧
      ∀ a, generator C f a = -gap C * f a := by
  obtain ⟨f, hf, hv, he⟩ := gap_attained C
  exact ⟨f, hf, hv, eigenfunction_of_attained C f hf he⟩

/-- The un-clamped matrix exponential preserves the weighted mean at every
real time; positivity is unnecessary for this algebraic stationary identity. -/
theorem semigroup_expect (C : Chain α) (f : α → ℝ) (t : ℝ) :
    C.p.expect (semigroup C t *ᵥ f) = C.p.expect f := by
  unfold FinProb.expect Matrix.mulVec dotProduct
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro b hb
  calc (∑ a, C.p.w a * (semigroup C t a b * f b)) =
      ∑ a, (C.p.w b * f b) * semigroup C t b a := by
        apply sum_congr rfl; intro a ha
        calc C.p.w a * (semigroup C t a b * f b) =
            (C.p.w a * semigroup C t a b) * f b := by ring
          _ = (C.p.w b * semigroup C t b a) * f b := by rw [semigroup_reversible]
          _ = _ := by ring
    _ = C.p.w b * f b := by rw [← mul_sum, semigroup_rows, mul_one]

private theorem semigroup_square_hasDerivAt (C : Chain α)
    (f : α → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => weightedInner C.p (semigroup C s *ᵥ f)
      (semigroup C s *ᵥ f))
      (-2 * energy C (semigroup C t *ᵥ f)) t := by
  have h (a : α) := semigroup_hasDerivAt C f t a
  have hd := HasDerivAt.fun_sum (u := univ) (fun a ha => ((h a).mul (h a)).const_mul (C.p.w a))
  convert hd using 1
  rw [energy_eq_neg_generator]
  unfold FinProb.expect
  simp only [neg_mul_neg, mul_sum]
  apply sum_congr rfl; intro a ha; ring

/-- The actual reversible-chain evolution contracts mean-zero weighted `L²` at the
variational spectral-gap rate. No eigenbasis or decay estimate is assumed. -/
theorem weighted_l2_decay (C : Chain α) (f : α → ℝ)
    (hf : C.p.expect f = 0) (t : ℝ) (ht : 0 ≤ t) :
    (∑ a, C.p.w a * ((semigroup C t *ᵥ f) a)^2) ≤
      exp (-2*gap C*t) * (∑ a, C.p.w a * (f a)^2) := by
  let H := fun s : ℝ => weightedInner C.p (semigroup C s *ᵥ f)
    (semigroup C s *ᵥ f)
  let G := fun s : ℝ => exp (2*gap C*s) * H s
  have hH (s : ℝ) : HasDerivAt H (-2*energy C (semigroup C s *ᵥ f)) s :=
    semigroup_square_hasDerivAt C f s
  have hG (s : ℝ) : HasDerivAt G
      (exp (2*gap C*s) * (2*gap C*H s -
        2*energy C (semigroup C s *ᵥ f))) s := by
    have he : HasDerivAt (fun s : ℝ => exp (2*gap C*s))
        (exp (2*gap C*s) * (2*gap C)) s :=
      by simpa only [id_eq, mul_one] using (((hasDerivAt_id s).const_mul (2*gap C)).exp)
    convert he.mul (hH s) using 1 <;> dsimp [G] <;> ring
  have hanti : Antitone G := by
    apply antitone_of_deriv_nonpos (fun s => (hG s).differentiableAt)
    intro s
    rw [(hG s).deriv]
    have hm : C.p.expect (semigroup C s *ᵥ f) = 0 := by rw [semigroup_expect, hf]
    have hv : C.p.variance (semigroup C s *ᵥ f) = H s := by
      unfold FinProb.variance
      rw [hm]
      simp only [sub_zero]
      rfl
    have hpoincare := gap_poincare C (semigroup C s *ᵥ f)
    rw [hv] at hpoincare
    exact mul_nonpos_of_nonneg_of_nonpos (exp_nonneg _) (by linarith)
  have hh := hanti ht
  have hzero : G 0 = ∑ a, C.p.w a * (f a)^2 := by
    simp only [G, H, semigroup_zero, Matrix.one_mulVec, mul_zero, exp_zero, one_mul,
      weightedInner, FinProb.expect, ← sq]
  rw [hzero] at hh
  have hpos : 0 < exp (2*gap C*t) := exp_pos _
  have hbound : H t ≤ (∑ a, C.p.w a*(f a)^2) / exp (2*gap C*t) := by
    rw [le_div_iff₀ hpos]
    simpa only [G, mul_comm] using hh
  have hexp : exp (-2*gap C*t) = (exp (2*gap C*t))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hexp]
  simpa only [H, weightedInner, FinProb.expect, ← sq, div_eq_mul_inv, mul_comm] using hbound

/-- Irreducibility forces the attained variational gap to be strictly positive. -/
theorem gap_pos (C : Chain α) : 0 < gap C := by
  by_contra h
  have hg : gap C = 0 := le_antisymm (le_of_not_gt h) (gap_nonneg C)
  obtain ⟨f, hf, hv, he⟩ := gap_attained C
  rw [hg, zero_mul] at he
  let c := fun a b => C.p.w a * rate C a b * (f a-f b)^2
  have hn (a b : α) : 0 ≤ c a b :=
    mul_nonneg (mul_nonneg (C.p.nonneg a) (rate_nonneg C a b)) (sq_nonneg _)
  have hsum : (∑ a : α, ∑ b : α, c a b) = 0 := by
    change (1/2:ℝ) * (∑ a : α, ∑ b : α, c a b) = 0 at he
    linarith
  have hedge (a b : α) (hab : a ≠ b ∧ 0 < C.R a b) : f a = f b := by
    have h1 : c a b ≤ ∑ b : α, c a b := single_le_sum (fun b _ => hn a b) (mem_univ b)
    have h2 : (∑ b : α, c a b) ≤ ∑ a : α, ∑ b : α, c a b :=
      single_le_sum (fun a _ => sum_nonneg fun b _ => hn a b) (mem_univ a)
    rw [hsum] at h2
    have hc : 0 < C.p.w a * rate C a b := by
      rw [rate, if_neg hab.1]
      exact mul_pos (C.positive a) hab.2
    have hle : (C.p.w a * rate C a b) * (f a-f b)^2 ≤ 0 := h1.trans h2
    have hs : (f a-f b)^2 ≤ 0 := nonpos_of_mul_nonpos_right hle hc
    nlinarith [sq_nonneg (f a-f b)]
  have hconstant (a b : α) : f a = f b := by
    have hpath := C.connected a b
    induction hpath with
    | refl => rfl
    | tail _ hbc ih => exact ih.trans (hedge _ _ hbc)
  have hfconst : f = fun _ => f (Classical.arbitrary α) := funext fun a => hconstant a _
  rw [hfconst] at hv
  simp [FinProb.variance, FinProb.expect_const] at hv

def minimumWeightState (C : Chain α) : α :=
  (univ.exists_min_image C.p.w univ_nonempty).choose

def minimumWeight (C : Chain α) : ℝ := C.p.w (minimumWeightState C)

theorem minimumWeight_le (C : Chain α) (a : α) : minimumWeight C ≤ C.p.w a := by
  exact (univ.exists_min_image C.p.w univ_nonempty).choose_spec.2 a (mem_univ a)

theorem minimumWeight_pos (C : Chain α) :
    0 < minimumWeight C := C.positive _

theorem weight_le_one (C : Chain α) (a : α) : C.p.w a ≤ 1 := by
  simpa only [C.p.sum_one] using single_le_sum (fun b _ => C.p.nonneg b) (mem_univ a)

theorem minimumWeight_le_one (C : Chain α) : minimumWeight C ≤ 1 :=
  weight_le_one C _

/-- The mean-zero density of a point mass relative to the actual stationary law. -/
def pointDensity (C : Chain α) (x : α) (y : α) : ℝ :=
  (if y = x then 1 / C.p.w x else 0) - 1

theorem pointDensity_mean (C : Chain α) (x : α) :
    C.p.expect (pointDensity C x) = 0 := by
  classical
  unfold pointDensity
  rw [FinProb.expect_sub, FinProb.expect_const]
  unfold FinProb.expect
  simp only [mul_ite, mul_zero, sum_ite_eq', Finset.mem_univ, if_true]
  field_simp [ne_of_gt (C.positive x)]
  <;> ring

/-- Detailed balance identifies the evolved point density with the row density. -/
theorem pointDensity_evolved (C : Chain α) (t : ℝ) (x y : α) :
    (semigroup C t *ᵥ pointDensity C x) y =
      semigroup C t x y / C.p.w y - 1 := by
  classical
  unfold pointDensity Matrix.mulVec dotProduct
  simp only [mul_sub, sum_sub_distrib, mul_one, semigroup_rows,
    mul_ite, mul_zero, sum_ite_eq', Finset.mem_univ, if_true]
  congr 1
  rw [mul_one_div]
  apply (div_eq_div_iff (ne_of_gt (C.positive x)) (ne_of_gt (C.positive y))).mpr
  simpa [mul_comm] using (semigroup_reversible C t x y).symm

/-- Exact density-square identity for the actual transition law. -/
theorem chiSquare_eq (C : Chain α) (t : ℝ) (ht : 0 ≤ t) (x : α) :
    chiSquare (transition C t x) C.p =
      ∑ y, C.p.w y * ((semigroup C t *ᵥ pointDensity C x) y)^2 := by
  unfold chiSquare
  apply sum_congr rfl
  intro y _
  rw [transition_w C t ht, pointDensity_evolved C]
  field_simp [ne_of_gt (C.positive y)]

/-- The actual `L²` decay and the exact initial density give the chain's
chi-square estimate, with no mixing or spectral-decay hypothesis. -/
theorem chiSquare_le (C : Chain α) (t : ℝ) (ht : 0 ≤ t) (x : α) :
    chiSquare (transition C t x) C.p ≤
      Real.exp (-2 * gap C * t) * (1 / C.p.w x - 1) := by
  rw [chiSquare_eq C t ht]
  have hh := weighted_l2_decay C (pointDensity C x)
    (pointDensity_mean C x) t ht
  have hnorm : (∑ y, C.p.w y * (pointDensity C x y)^2) = 1 / C.p.w x - 1 :=
    point_density_sq C.p C.positive x
  rw [hnorm] at hh
  exact hh

/-- The explicit comparison time from Appendix A.1, using the actual minimum weight. -/
def mixingUpperTime (C : Chain α) (ε : ℝ) : ℝ :=
  Real.log (1 / (ε * minimumWeight C)) / gap C

/-- The comparison time is an actual good time for every starting configuration. -/
theorem good_upper_time (C : Chain α)  (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    0 ≤ mixingUpperTime C ε ∧
      ∀ a, tvDist (transition C (mixingUpperTime C ε) a) C.p ≤ ε := by
  let m := minimumWeight C
  let g := gap C
  let T := mixingUpperTime C ε
  have hm : 0 < m := minimumWeight_pos C
  have hm1 : m ≤ 1 := minimumWeight_le_one C
  have hg : 0 < g := gap_pos C
  have hu : 0 < ε * m := mul_pos hε hm
  have hu1 : ε * m < 1 := by nlinarith
  have hv : 1 < 1 / (ε * m) := (lt_div_iff₀ hu).mpr (by linarith)
  have hT : 0 ≤ T := (div_pos (Real.log_pos hv) hg).le
  refine ⟨hT, ?_⟩
  have hE : Real.exp (-g * T) = ε * m := by
    have he : -g * T = - Real.log (1 / (ε * m)) := by
      change -g * (Real.log (1 / (ε * m)) / g) = -Real.log (1 / (ε * m))
      field_simp [ne_of_gt hg]
      <;> ring
    rw [he, Real.exp_neg, Real.exp_log (one_div_pos.mpr hu)]
    field_simp [ne_of_gt hu]
  have hE2 : Real.exp (-2 * g * T) = (ε * m)^2 := by
    rw [show -2 * g * T = (-g * T) + (-g * T) by ring, Real.exp_add, hE]
    ring
  intro a
  have hma : m ≤ C.p.w a := minimumWeight_le C a
  have hm2 : m^2 ≤ C.p.w a := by nlinarith
  have hi : 0 < 1 / C.p.w a := one_div_pos.mpr (C.positive a)
  have hcancel : C.p.w a * (1 / C.p.w a) = 1 := by field_simp [ne_of_gt (C.positive a)]
  have hcoef : m^2 * (1 / C.p.w a - 1) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hm2 hi.le
    nlinarith [sq_nonneg m]
  have hχ := chiSquare_le C T hT a
  change chiSquare (transition C T a) C.p ≤
    Real.exp (-2 * g * T) * (1 / C.p.w a - 1) at hχ
  rw [hE2] at hχ
  have hχ' : chiSquare (transition C T a) C.p ≤ ε^2 := by
    have hh := mul_le_mul_of_nonneg_left hcoef (sq_nonneg ε)
    nlinarith only [hχ, hh]
  have hTV := tvDist_sq_le_chiSquare (transition C T a) C.p C.positive
  have hn := tvDist_nonneg (transition C T a) C.p
  nlinarith

/-- The mixing upper bound for the actual finite-chain transition laws. -/
theorem mixing_upper (C : Chain α)  (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    tMix C.p (transition C) ε ≤
      (gap C)⁻¹ * Real.log (1 / (ε * minimumWeight C)) := by
  obtain ⟨hT, hgood⟩ := good_upper_time C ε hε (by linarith)
  have hh := tMix_le C.p (transition C) hT hgood
  simpa only [mixingUpperTime, div_eq_mul_inv, mul_comm] using hh

private theorem abs_expect_sub_le_bound {A : Type*} [Fintype A]
    (μ ν : FinProb A) (f : A → ℝ) (M : ℝ) (hf : ∀ a, |f a| ≤ M) :
    |μ.expect f - ν.expect f| ≤ (2 * tvDist μ ν) * M := by
  have he : μ.expect f - ν.expect f = ∑ a, (μ.w a - ν.w a) * f a := by
    simp only [FinProb.expect, sub_mul, sum_sub_distrib]
  rw [he]
  calc
    |∑ a, (μ.w a - ν.w a) * f a| ≤ ∑ a, |(μ.w a - ν.w a) * f a| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, |μ.w a - ν.w a| * M := by
      apply sum_le_sum
      intro a _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hf a) (abs_nonneg _)
    _ = (2 * tvDist μ ν) * M := by rw [← sum_mul]; unfold tvDist; ring

/-- An attained gap eigenfunction gives the worst-start TV lower bound for
this actual semigroup, rather than for an assumed scalar decay profile. -/
theorem tv_lower (C : Chain α)  :
    ∃ a : α, ∀ t : ℝ, 0 ≤ t →
      Real.exp (-gap C * t) / 2 ≤ tvDist (transition C t a) C.p := by
  obtain ⟨f, hf, hvar, heigen⟩ := gap_eigenfunction C
  obtain ⟨a, _, hmax⟩ := univ.exists_max_image (fun a => |f a|) univ_nonempty
  have hmax' : ∀ b, |f b| ≤ |f a| := fun b => hmax b (mem_univ b)
  have hM : 0 < |f a| := by
    by_contra h
    have hzero : f = fun _ => 0 := by
      funext b
      have hb := hmax' b
      have ha := abs_nonneg (f a)
      have hh : |f b| = 0 := le_antisymm (by linarith) (abs_nonneg _)
      exact abs_eq_zero.mp hh
    rw [hzero] at hvar
    simp [FinProb.variance, FinProb.expect_const] at hvar
  refine ⟨a, ?_⟩
  intro t ht
  have hexp := semigroup_eigenfunction C f (-gap C) t heigen
  have hrow : (transition C t a).expect f = Real.exp (-gap C * t) * f a := by
    have hh := congrFun hexp a
    change (∑ b, semigroup C t a b * f b) = _ at hh
    unfold FinProb.expect
    simp_rw [transition_w C t ht]
    simpa only [mul_neg, neg_mul, mul_comm t (gap C)] using hh
  have hd := abs_expect_sub_le_bound (transition C t a) C.p f (|f a|) hmax'
  rw [hf, sub_zero, hrow, abs_mul, abs_of_pos (Real.exp_pos _)] at hd
  have hh : Real.exp (-gap C * t) ≤ 2 * tvDist (transition C t a) C.p :=
    (mul_le_mul_iff_left₀ hM).mp hd
  linarith

/-- The relaxation-to-mixing lower bound for the actual finite irreducible reversible chain. -/
theorem mixing_lower (C : Chain α)  :
    Real.log 2 * (gap C)⁻¹ ≤ tMix C.p (transition C) (1 / 4) := by
  obtain ⟨hT, hgood⟩ := good_upper_time C (1 / 4) (by norm_num) (by norm_num)
  obtain ⟨a, ha⟩ := tv_lower C
  have hg := gap_pos C
  apply le_tMix C.p (transition C) ⟨_, hT, hgood⟩
  intro t ht hmixed
  have he : Real.exp (-gap C * t) ≤ 1 / 2 := by
    have hh := ha t ht
    have hmix := hmixed a
    linarith
  have hlog := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp] at hlog
  have hhalf : Real.log (1 / 2) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
  rw [hhalf] at hlog
  change Real.log 2 / gap C ≤ t
  apply (div_le_iff₀ hg).mpr
  linarith

/-- Both original inequalities of Appendix A.1 for an arbitrary finite
irreducible reversible continuous-time chain on at least two states. -/
theorem lemma_A_1 (C : Chain α)  (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    Real.log 2 * relaxationTime C ≤ mixingTime C (1 / 4) ∧
      mixingTime C ε ≤ relaxationTime C * Real.log (1 / (ε * minimumWeight C)) :=
  ⟨mixing_lower C, mixing_upper C ε hε hε1⟩


end Paper09.ReversibleMixing
