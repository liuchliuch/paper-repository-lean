import Paper09.Dynamics
import Paper09.GibbsShell
import Mathlib.Tactic

open Finset BigOperators Classical Real
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 800000

local instance (priority := 2000) classicalSumDecidableEq {I O : Type*} : DecidableEq (I ⊕ O) :=
  Classical.decEq _

namespace Paper09
namespace FinProb

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The actual exterior marginal of a finite joint probability law. -/
def exteriorMarginal (p : FinProb (α × β)) : FinProb β where
  w b := ∑ a, p.w (a, b)
  nonneg b := sum_nonneg fun a _ => p.nonneg (a, b)
  sum_one := by
    rw [sum_comm]
    simpa only [Fintype.sum_prod_type] using p.sum_one

/-- Conditioning on the exterior. A zero-mass fiber is assigned the arbitrary
reference law `ν`; all disintegration identities are independent of this choice. -/
def interiorConditional (p : FinProb (α × β)) (ν : FinProb α) (b : β) : FinProb α :=
  if hz : (p.exteriorMarginal).w b = 0 then ν else
  { w a := p.w (a, b) / (p.exteriorMarginal).w b
    nonneg a := div_nonneg (p.nonneg _) ((p.exteriorMarginal).nonneg _)
    sum_one := by
      rw [← sum_div]
      exact div_self hz }

theorem joint_eq_marginal_mul_conditional (p : FinProb (α × β))
    (ν : FinProb α) (a : α) (b : β) :
    p.w (a, b) = (p.exteriorMarginal).w b * (p.interiorConditional ν b).w a := by
  by_cases hz : (p.exteriorMarginal).w b = 0
  · have ha : p.w (a, b) = 0 := by
      have hm := single_le_sum (fun x _ => p.nonneg (x, b)) (mem_univ a)
      change p.w (a, b) ≤ (p.exteriorMarginal).w b at hm
      exact le_antisymm (by simpa [hz] using hm) (p.nonneg _)
    simp [ha, hz]
  · simp only [interiorConditional, dif_neg hz]
    exact (mul_div_cancel₀ _ hz).symm

/-- Finite Fubini/disintegration, for a joint statistic. -/
theorem expect_disintegration (p : FinProb (α × β)) (ν : FinProb α)
    (f : α × β → ℝ) :
    p.expect f = (p.exteriorMarginal).expect
      (fun b => (p.interiorConditional ν b).expect (fun a => f (a, b))) := by
  simp only [expect, Fintype.sum_prod_type]
  rw [sum_comm]
  apply sum_congr rfl
  intro b _
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  rw [joint_eq_marginal_mul_conditional p ν a b]
  ring

/-- The total-variance lower bound used in Lemma 2.2, for the actual
conditional laws of the joint law. -/
theorem variance_extend_ge_conditional (p : FinProb (α × β)) (ν : FinProb α)
    (f : α → ℝ) :
    (p.exteriorMarginal).expect (fun b => (p.interiorConditional ν b).variance f)
      ≤ p.variance (fun z => f z.1) := by
  unfold variance
  rw [expect_disintegration p ν]
  apply expect_mono
  intro b
  exact variance_le_expect_sq (p.interiorConditional ν b) f _

theorem expect_pos_of_pos (p : FinProb α) {f : α → ℝ} (hf : ∀ a, 0 < f a) :
    0 < p.expect f := by
  have hn : ∃ a, 0 < p.w a := by
    by_contra h
    have hz : ∀ a, p.w a = 0 := by
      intro a
      exact le_antisymm (le_of_not_gt (fun ha => h ⟨a, ha⟩)) (p.nonneg a)
    have hh := p.sum_one
    simp only [hz, sum_const_zero] at hh
    norm_num at hh
  obtain ⟨a, ha⟩ := hn
  apply lt_of_lt_of_le (mul_pos ha (hf a))
  exact single_le_sum (fun x _ => mul_nonneg (p.nonneg x) (hf x).le) (mem_univ a)

/-- Two positive-mass points separated by a statistic force positive variance. -/
theorem variance_pos_of_two (p : FinProb α) (f : α → ℝ) (a a' : α)
    (ha : 0 < p.w a) (ha' : 0 < p.w a') (hf : f a ≠ f a') :
    0 < p.variance f := by
  by_contra hn
  have hz : p.variance f = 0 :=
    le_antisymm (le_of_not_gt hn) (p.variance_nonneg f)
  have hc (x : α) (hx : 0 < p.w x) : f x = p.expect f := by
    have he : p.w x * ((f x - p.expect f) * (f x - p.expect f)) ≤ p.variance f := by
      simpa only [variance, expect] using
        (single_le_sum (fun y _ => mul_nonneg (p.nonneg y)
          (mul_self_nonneg (f y - p.expect f))) (mem_univ x))
    rw [hz] at he
    have hzero : p.w x * ((f x - p.expect f) * (f x - p.expect f)) = 0 :=
      le_antisymm he (mul_nonneg (p.nonneg x) (mul_self_nonneg _))
    exact sub_eq_zero.mp (mul_self_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hx.ne'))
  exact hf ((hc a ha).trans (hc a' ha').symm)

end FinProb

namespace UpdateGraph

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Independent coordinate updates on a product state space. -/
def product (G : UpdateGraph α) (H : UpdateGraph β) : UpdateGraph (α × β) where
  edge x y := (x.2 = y.2 ∧ G.edge x.1 y.1) ∨ (x.1 = y.1 ∧ H.edge x.2 y.2)
  symm := by
    intro x y h
    rcases h with ⟨he, hg⟩ | ⟨he, hh⟩
    · exact Or.inl ⟨he.symm, G.symm hg⟩
    · exact Or.inr ⟨he.symm, H.symm hh⟩

theorem conductance_same_exterior (p : FinProb (α × β)) (ν : FinProb α)
    (a a' : α) (b : β) :
    conductance p (a, b) (a', b) =
      (p.exteriorMarginal).w b * conductance (p.interiorConditional ν b) a a' := by
  unfold conductance
  rw [FinProb.joint_eq_marginal_mul_conditional p ν a b,
    FinProb.joint_eq_marginal_mul_conditional p ν a' b]
  by_cases hm : (p.exteriorMarginal).w b = 0
  · simp [hm]
  · rw [← mul_add]
    calc
      _ = ((p.exteriorMarginal).w b *
          ((p.exteriorMarginal).w b *
            ((p.interiorConditional ν b).w a * (p.interiorConditional ν b).w a'))) /
          ((p.exteriorMarginal).w b *
            ((p.interiorConditional ν b).w a + (p.interiorConditional ν b).w a')) := by
        congr 1
        ring
      _ = _ := by rw [mul_div_mul_left _ _ hm, mul_div_assoc]

/-- Exterior updates of an extended interior statistic vanish exactly.
The remaining conductances disintegrate against the true exterior marginal. -/
theorem dirichlet_extend_disintegration (G : UpdateGraph α) (H : UpdateGraph β)
    (p : FinProb (α × β)) (ν : FinProb α) (f : α → ℝ) :
    (G.product H).dirichlet p (fun z => f z.1) =
      (p.exteriorMarginal).expect (fun b => G.dirichlet (p.interiorConditional ν b) f) := by
  have he (a a' : α) (b b' : β) :
      (if (G.product H).edge (a,b) (a',b') then
        conductance p (a,b) (a',b') * (f a - f a') ^ 2 else 0) =
      if b' = b then
        (if G.edge a a' then conductance p (a,b) (a',b) * (f a - f a') ^ 2 else 0)
        else 0 := by
    by_cases hb : b' = b
    · subst b'
      by_cases hg : G.edge a a'
      · simp [product, hg]
      · by_cases ha : a = a'
        · subst a'; simp
        · simp [product, hg, ha]
    · by_cases ha : a = a'
      · subst a'; simp
      · have hb' : b ≠ b' := Ne.symm hb
        simp [product, hb, hb', ha]
  simp only [dirichlet, Fintype.sum_prod_type]
  simp_rw [he]
  simp only [sum_ite_eq', mem_univ, if_true]
  rw [sum_comm]
  simp only [FinProb.expect]
  apply sum_congr rfl
  intro b _
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  rw [mul_sum]
  apply sum_congr rfl
  intro a' _
  split_ifs with hg
  · rw [conductance_same_exterior p ν]
    ring
  · ring

/-- The rate-one normalization of an ordered-edge Dirichlet sum. -/
def energy (G : UpdateGraph α) (p : FinProb α) (f : α → ℝ) : ℝ :=
  (1 / 2) * G.dirichlet p f

theorem energy_nonneg (G : UpdateGraph α) (p : FinProb α) (f : α → ℝ) :
    0 ≤ G.energy p f := mul_nonneg (by norm_num) (G.dirichlet_nonneg p f)

theorem energy_extend_disintegration (G : UpdateGraph α) (H : UpdateGraph β)
    (p : FinProb (α × β)) (ν : FinProb α) (f : α → ℝ) :
    (G.product H).energy p (fun z => f z.1) =
      (p.exteriorMarginal).expect (fun b => G.energy (p.interiorConditional ν b) f) := by
  rw [energy, dirichlet_extend_disintegration G H p ν f]
  exact (FinProb.expect_smul _ _ _).symm

/-- Energy comparison after averaging each *actual* conditional density bound. -/
theorem energy_extend_le (G : UpdateGraph α) (H : UpdateGraph β)
    (p : FinProb (α × β)) (ν : FinProb α) (D : β → ℝ)
    (hhi : ∀ b a, (p.interiorConditional ν b).w a ≤ exp (D b) * ν.w a)
    (f : α → ℝ) :
    (G.product H).energy p (fun z => f z.1) ≤
      (p.exteriorMarginal).expect (fun b => exp (D b)) * G.energy ν f := by
  rw [energy_extend_disintegration G H p ν f]
  calc
    _ ≤ (p.exteriorMarginal).expect (fun b => exp (D b) * G.energy ν f) := by
      apply FinProb.expect_mono
      intro b
      have hh := mul_le_mul_of_nonneg_left
        (dirichlet_le_of_density (exp_nonneg _) (hhi b) G f)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
      convert hh using 1
      unfold energy
      ring
    _ = _ := by
      simp only [FinProb.expect]
      rw [sum_mul]
      apply sum_congr rfl
      intro b _
      ring

/-- Variance comparison after averaging each actual conditional density bound. -/
theorem variance_extend_ge (p : FinProb (α × β)) (ν : FinProb α) (D : β → ℝ)
    (hlo : ∀ b a, exp (-D b) * ν.w a ≤ (p.interiorConditional ν b).w a)
    (f : α → ℝ) :
    (p.exteriorMarginal).expect (fun b => exp (-D b)) * ν.variance f ≤
      p.variance (fun z => f z.1) := by
  calc
    _ = (p.exteriorMarginal).expect (fun b => exp (-D b) * ν.variance f) := by
      simp only [FinProb.expect]
      rw [sum_mul]
      apply sum_congr rfl
      intro b _
      ring
    _ ≤ (p.exteriorMarginal).expect (fun b => (p.interiorConditional ν b).variance f) :=
      FinProb.expect_mono (fun b => FinProb.variance_of_density_lower (hlo b) f)
    _ ≤ _ := FinProb.variance_extend_ge_conditional p ν f

/-! The gap below is the same Rayleigh infimum as `spectralGap`, generalized
to a finite update graph so that the interior/exterior product is explicit. -/

def rayleighSet (G : UpdateGraph α) (p : FinProb α) : Set ℝ :=
  {r | ∃ f : α → ℝ, 0 < p.variance f ∧ r = G.energy p f / p.variance f}

def variationalGap (G : UpdateGraph α) (p : FinProb α) : ℝ :=
  if (G.rayleighSet p).Nonempty then sInf (G.rayleighSet p) else 0

theorem rayleighSet_bddBelow (G : UpdateGraph α) (p : FinProb α) :
    BddBelow (G.rayleighSet p) := by
  refine ⟨0, ?_⟩
  rintro r ⟨f, hf, rfl⟩
  exact div_nonneg (G.energy_nonneg p f) hf.le

theorem variationalGap_nonneg (G : UpdateGraph α) (p : FinProb α) :
    0 ≤ G.variationalGap p := by
  unfold variationalGap
  split_ifs with hn
  · apply le_csInf hn
    rintro r ⟨f, hf, rfl⟩
    exact div_nonneg (G.energy_nonneg p f) hf.le
  · exact le_rfl

theorem variationalGap_le (G : UpdateGraph α) (p : FinProb α)
    (f : α → ℝ) (hf : 0 < p.variance f) :
    G.variationalGap p ≤ G.energy p f / p.variance f := by
  have hm : G.energy p f / p.variance f ∈ G.rayleighSet p := ⟨f, hf, rfl⟩
  rw [variationalGap, if_pos ⟨_, hm⟩]
  exact csInf_le (G.rayleighSet_bddBelow p) hm

theorem variationalGap_eq_spectralGap {V : Type*} [Fintype V]
    (p : FinProb (V → Spin)) :
    (heatBathGraph V).variationalGap p = spectralGap p := rfl

/-- A trial function is transferred to the full product system using genuine
disintegration; its variance stays positive because the exponential moment is. -/
theorem rayleigh_extend_le (G : UpdateGraph α) (H : UpdateGraph β)
    (p : FinProb (α × β)) (ν : FinProb α) (D : β → ℝ)
    (hlo : ∀ b a, exp (-D b) * ν.w a ≤ (p.interiorConditional ν b).w a)
    (hhi : ∀ b a, (p.interiorConditional ν b).w a ≤ exp (D b) * ν.w a)
    (f : α → ℝ) (hf : 0 < ν.variance f) :
    (G.product H).variationalGap p ≤
      ((p.exteriorMarginal).expect (fun b => exp (D b)) /
        (p.exteriorMarginal).expect (fun b => exp (-D b))) *
      (G.energy ν f / ν.variance f) := by
  let P := (p.exteriorMarginal).expect (fun b => exp (D b))
  let M := (p.exteriorMarginal).expect (fun b => exp (-D b))
  have hP : 0 < P := FinProb.expect_pos_of_pos _ (fun b => exp_pos _)
  have hM : 0 < M := FinProb.expect_pos_of_pos _ (fun b => exp_pos _)
  have he := energy_extend_le G H p ν D hhi f
  have hv := variance_extend_ge p ν D hlo f
  change (G.product H).energy p (fun z => f z.1) ≤ P * G.energy ν f at he
  change M * ν.variance f ≤ p.variance (fun z => f z.1) at hv
  have hfv : 0 < p.variance (fun z => f z.1) := lt_of_lt_of_le (mul_pos hM hf) hv
  apply le_trans (variationalGap_le _ p _ hfv)
  calc
    _ ≤ (P * G.energy ν f) / (M * ν.variance f) :=
      div_le_div₀ (mul_nonneg hP.le (G.energy_nonneg ν f)) he (mul_pos hM hf) hv
    _ = _ := by dsimp [P, M]; ring

/-- Lemma 2.2's averaged comparison from actual joint and conditional laws.
The only nondegeneracy premise asks that the interior law admit a statistic
with positive variance. No gap eigenfunction, gap bound, or comparison
certificate is assumed: the conclusion follows for the Rayleigh infima. -/
theorem variationalGap_product_le (G : UpdateGraph α) (H : UpdateGraph β)
    (p : FinProb (α × β)) (ν : FinProb α) (D : β → ℝ)
    (hn : (G.rayleighSet ν).Nonempty)
    (hlo : ∀ b a, exp (-D b) * ν.w a ≤ (p.interiorConditional ν b).w a)
    (hhi : ∀ b a, (p.interiorConditional ν b).w a ≤ exp (D b) * ν.w a) :
    (G.product H).variationalGap p ≤ G.variationalGap ν *
      ((p.exteriorMarginal).expect (fun b => exp (D b)) /
        (p.exteriorMarginal).expect (fun b => exp (-D b))) := by
  let K := (p.exteriorMarginal).expect (fun b => exp (D b)) /
    (p.exteriorMarginal).expect (fun b => exp (-D b))
  have hK : 0 < K := div_pos
    (FinProb.expect_pos_of_pos _ (fun b => exp_pos _))
    (FinProb.expect_pos_of_pos _ (fun b => exp_pos _))
  have hbound : (G.product H).variationalGap p / K ≤ G.variationalGap ν := by
    have heq : G.variationalGap ν = sInf (G.rayleighSet ν) := if_pos hn
    rw [heq]
    apply le_csInf hn
    rintro r ⟨f, hf, rfl⟩
    apply (div_le_iff₀ hK).mpr
    simpa only [mul_comm] using rayleigh_extend_le G H p ν D hlo hhi f hf
  exact (div_le_iff₀ hK).mp hbound

/-- The explicit `exp (4 A)` factor in paper (2.2), after the conditional
oscillation bounds have been established for the actual conditional laws. -/
theorem soft_shell_gap_product (G : UpdateGraph α) (H : UpdateGraph β)
    (p : FinProb (α × β)) (ν : FinProb α) (A b : ℝ) (k : β → ℕ)
    (hn : (G.rayleighSet ν).Nonempty)
    (hlo : ∀ τ a, exp (-(2 * A + b * (k τ : ℝ))) * ν.w a ≤
      (p.interiorConditional ν τ).w a)
    (hhi : ∀ τ a, (p.interiorConditional ν τ).w a ≤
      exp (2 * A + b * (k τ : ℝ)) * ν.w a) :
    (G.product H).variationalGap p ≤ G.variationalGap ν * exp (4 * A) *
      ((p.exteriorMarginal).expect (fun τ => exp (b * (k τ : ℝ))) /
        (p.exteriorMarginal).expect (fun τ => exp (-b * (k τ : ℝ)))) := by
  have h := variationalGap_product_le G H p ν (fun τ => 2 * A + b * (k τ : ℝ))
    hn hlo hhi
  have hp : (p.exteriorMarginal).expect (fun τ => exp (2 * A + b * (k τ : ℝ))) =
      exp (2 * A) * (p.exteriorMarginal).expect (fun τ => exp (b * (k τ : ℝ))) := by
    simp_rw [exp_add]
    exact FinProb.expect_smul _ _ _
  have hm : (p.exteriorMarginal).expect (fun τ => exp (-(2 * A + b * (k τ : ℝ)))) =
      exp (-(2 * A)) * (p.exteriorMarginal).expect (fun τ => exp (-b * (k τ : ℝ))) := by
    have he : ∀ τ, -(2 * A + b * (k τ : ℝ)) = -(2 * A) + -b * (k τ : ℝ) := by
      intro τ; ring
    simp_rw [he, exp_add]
    exact FinProb.expect_smul _ _ _
  rw [hp, hm] at h
  have hexp : exp (4 * A) = exp (2 * A) / exp (-(2 * A)) := by
    rw [← exp_sub]
    congr 1
    ring
  rw [hexp]
  convert h using 1
  ring

end UpdateGraph

namespace FinProb

variable {α γ : Type*} [Fintype α] [Fintype γ]

/-- A finite law in equivalent coordinates, with no marginalization. -/
def reindex (p : FinProb α) (e : α ≃ γ) : FinProb γ where
  w y := p.w (e.symm y)
  nonneg y := p.nonneg _
  sum_one := by rw [e.symm.sum_comp]; exact p.sum_one

theorem expect_reindex (p : FinProb α) (e : α ≃ γ) (f : γ → ℝ) :
    (p.reindex e).expect f = p.expect (fun x => f (e x)) := by
  have he := e.symm.sum_comp (fun x => p.w x * f (e x))
  simpa only [expect, reindex, e.apply_symm_apply] using he

theorem variance_reindex (p : FinProb α) (e : α ≃ γ) (f : γ → ℝ) :
    (p.reindex e).variance f = p.variance (fun x => f (e x)) := by
  simp only [variance, expect_reindex]

end FinProb

namespace UpdateGraph

variable {α γ : Type*} [Fintype α] [Fintype γ]

/-- The same update graph in equivalent coordinates. -/
def reindex (G : UpdateGraph α) (e : α ≃ γ) : UpdateGraph γ where
  edge x y := G.edge (e.symm x) (e.symm y)
  symm := G.symm

theorem dirichlet_reindex (G : UpdateGraph α) (p : FinProb α) (e : α ≃ γ)
    (f : γ → ℝ) :
    (G.reindex e).dirichlet (p.reindex e) f = G.dirichlet p (fun x => f (e x)) := by
  unfold dirichlet reindex conductance FinProb.reindex
  have hinner (y : γ) :
      (∑ y' : γ, if G.edge (e.symm y) (e.symm y') then
        (p.w (e.symm y) * p.w (e.symm y') /
          (p.w (e.symm y) + p.w (e.symm y'))) * (f y - f y') ^ 2 else 0) =
      ∑ x' : α, if G.edge (e.symm y) x' then
        (p.w (e.symm y) * p.w x' / (p.w (e.symm y) + p.w x')) *
          (f y - f (e x')) ^ 2 else 0 := by
    simpa only [e.apply_symm_apply] using e.symm.sum_comp (fun x' =>
      if G.edge (e.symm y) x' then
        (p.w (e.symm y) * p.w x' / (p.w (e.symm y) + p.w x')) *
          (f y - f (e x')) ^ 2 else 0)
  simp_rw [hinner]
  simpa only [e.apply_symm_apply] using e.symm.sum_comp (fun x =>
    ∑ x' : α, if G.edge x x' then
      (p.w x * p.w x' / (p.w x + p.w x')) * (f (e x) - f (e x')) ^ 2 else 0)

theorem energy_reindex (G : UpdateGraph α) (p : FinProb α) (e : α ≃ γ)
    (f : γ → ℝ) :
    (G.reindex e).energy (p.reindex e) f = G.energy p (fun x => f (e x)) := by
  rw [energy, dirichlet_reindex]
  rfl

/-- The true Rayleigh set, and hence the gap, is invariant under a bijection. -/
theorem rayleighSet_reindex (G : UpdateGraph α) (p : FinProb α) (e : α ≃ γ) :
    (G.reindex e).rayleighSet (p.reindex e) = G.rayleighSet p := by
  ext r
  constructor
  · rintro ⟨f, hf, hr⟩
    refine ⟨fun x => f (e x), ?_, ?_⟩
    · simpa only [FinProb.variance_reindex] using hf
    · simpa only [energy_reindex, FinProb.variance_reindex] using hr
  · rintro ⟨f, hf, hr⟩
    refine ⟨fun y => f (e.symm y), ?_, ?_⟩
    · simpa only [FinProb.variance_reindex, e.symm_apply_apply] using hf
    · simpa only [energy_reindex, FinProb.variance_reindex, e.symm_apply_apply] using hr

theorem variationalGap_reindex (G : UpdateGraph α) (p : FinProb α) (e : α ≃ γ) :
    (G.reindex e).variationalGap (p.reindex e) = G.variationalGap p := by
  simp only [variationalGap, rayleighSet_reindex]

end UpdateGraph

/-- Lemma 2.2 for an actual finite spin law, expressed using any bijection
which splits its one-site updates into interior and exterior updates. -/
theorem spectralGap_soft_shell_split {V I O : Type*}
    [Fintype V] [Fintype I] [Fintype O]
    (p : FinProb (V → Spin)) (ν : FinProb (I → Spin))
    (e : (V → Spin) ≃ ((I → Spin) × (O → Spin)))
    (he : (heatBathGraph V).reindex e = (heatBathGraph I).product (heatBathGraph O))
    (A b : ℝ) (k : (O → Spin) → ℕ)
    (hn : ((heatBathGraph I).rayleighSet ν).Nonempty)
    (hlo : ∀ τ η, exp (-(2 * A + b * (k τ : ℝ))) * ν.w η ≤
      ((p.reindex e).interiorConditional ν τ).w η)
    (hhi : ∀ τ η, ((p.reindex e).interiorConditional ν τ).w η ≤
      exp (2 * A + b * (k τ : ℝ)) * ν.w η) :
    spectralGap (V := V) p ≤ spectralGap (V := I) ν * exp (4 * A) *
      (p.expect (fun η => exp (b * (k (e η).2 : ℝ))) /
        p.expect (fun η => exp (-b * (k (e η).2 : ℝ)))) := by
  have h := UpdateGraph.soft_shell_gap_product (heatBathGraph I) (heatBathGraph O)
    (p.reindex e) ν A b k hn hlo hhi
  rw [← he, UpdateGraph.variationalGap_reindex,
    UpdateGraph.variationalGap_eq_spectralGap,
    UpdateGraph.variationalGap_eq_spectralGap] at h
  have hm (f : (O → Spin) → ℝ) :
      ((p.reindex e).exteriorMarginal).expect f = p.expect (fun η => f (e η).2) := by
    have hd := FinProb.expect_disintegration (p.reindex e) ν (fun z => f z.2)
    simp only [FinProb.expect_const] at hd
    rw [← hd, FinProb.expect_reindex]
  simpa only [hm] using h

/-- Splitting a site sum splits exactly the one-site update graph, without
any additional graph hypothesis. -/
theorem heatBathGraph_sum_split {I O : Type*} [Fintype I] [Fintype O] :
    (heatBathGraph (I ⊕ O)).reindex (Equiv.sumArrowEquivProdArrow I O Spin) =
      (heatBathGraph I).product (heatBathGraph O) := by
  have hedge (x y : (I → Spin) × (O → Spin)) :
      ((heatBathGraph (I ⊕ O)).reindex (Equiv.sumArrowEquivProdArrow I O Spin)).edge x y ↔
      ((heatBathGraph I).product (heatBathGraph O)).edge x y := by
    change oneSite (Sum.elim x.1 x.2) (Sum.elim y.1 y.2) ↔
      (x.2 = y.2 ∧ oneSite x.1 y.1) ∨ (x.1 = y.1 ∧ oneSite x.2 y.2)
    constructor
    · rintro ⟨i | o, hneq, hrest⟩
      · left
        refine ⟨?_, i, hneq, ?_⟩
        · funext z
          exact hrest (Sum.inr z) (by simp)
        · intro j hj
          exact hrest (Sum.inl j) (by simpa using hj)
      · right
        refine ⟨?_, o, hneq, ?_⟩
        · funext z
          exact hrest (Sum.inl z) (by simp)
        · intro j hj
          exact hrest (Sum.inr j) (by simpa using hj)
    · rintro (⟨heq, i, hneq, hrest⟩ | ⟨heq, o, hneq, hrest⟩)
      · refine ⟨Sum.inl i, hneq, ?_⟩
        intro z hz
        cases z with
        | inl j => exact hrest j (by simpa using hz)
        | inr j => exact congrFun heq j
      · refine ⟨Sum.inr o, hneq, ?_⟩
        intro z hz
        cases z with
        | inl j => exact congrFun heq j
        | inr j => exact hrest j (by simpa using hz)
  cases hG : (heatBathGraph (I ⊕ O)).reindex (Equiv.sumArrowEquivProdArrow I O Spin) with
  | mk edge symm =>
    cases hH : (heatBathGraph I).product (heatBathGraph O) with
    | mk edge' symm' =>
      have he : edge = edge' := by
        funext x y
        have hh := hedge x y
        rw [hG, hH] at hh
        exact propext hh
      cases he
      rfl

/-- A positive finite spin law on a nonempty site set has a nonempty
Rayleigh set. This applies directly to every finite Gibbs law. -/
theorem spin_rayleighSet_nonempty {I : Type*} [Fintype I] [Nonempty I]
    (ν : FinProb (I → Spin)) (hν : ∀ η, 0 < ν.w η) :
    ((heatBathGraph I).rayleighSet ν).Nonempty := by
  let x : I := Classical.choice inferInstance
  let f : (I → Spin) → ℝ := fun η => spinVal (η x)
  have hf : 0 < ν.variance f := FinProb.variance_pos_of_two ν f
    (fun _ => 0) (fun _ => 1) (hν _) (hν _) (by norm_num [f, spinVal])
  exact ⟨_, f, hf, rfl⟩

/-- Paper (2.2), with actual spectral gaps and no structural graph premise,
for a system whose sites are the disjoint sum of interior and exterior. -/
theorem spectralGap_soft_shell_sum {I O : Type*}
    [Fintype I] [Fintype O] [Nonempty I]
    (p : FinProb (I ⊕ O → Spin)) (ν : FinProb (I → Spin))
    (hν : ∀ η, 0 < ν.w η) (A b : ℝ) (k : (O → Spin) → ℕ)
    (hlo : ∀ τ η, exp (-(2 * A + b * (k τ : ℝ))) * ν.w η ≤
      ((p.reindex (Equiv.sumArrowEquivProdArrow I O Spin)).interiorConditional ν τ).w η)
    (hhi : ∀ τ η,
      ((p.reindex (Equiv.sumArrowEquivProdArrow I O Spin)).interiorConditional ν τ).w η ≤
      exp (2 * A + b * (k τ : ℝ)) * ν.w η) :
    spectralGap (V := I ⊕ O) p ≤ spectralGap (V := I) ν * exp (4 * A) *
      (p.expect (fun η => exp (b * (k (fun o => η (Sum.inr o)) : ℝ))) /
        p.expect (fun η => exp (-b * (k (fun o => η (Sum.inr o)) : ℝ)))) := by
  exact spectralGap_soft_shell_split p ν (Equiv.sumArrowEquivProdArrow I O Spin)
    (heatBathGraph_sum_split (I := I) (O := O)) A b k
    (spin_rayleighSet_nonempty ν hν) hlo hhi

namespace Lattice

variable {I O : Type*} [Fintype I] [Fintype O]

/-- The induced interior lattice in a disjoint decomposition of sites. -/
def sumLeft (Λ : Lattice (I ⊕ O)) : Lattice I where
  adj i j := Λ.adj (Sum.inl i) (Sum.inl j)
  symm := Λ.symm
  irrefl i := Λ.irrefl _
  maxDegree := Λ.maxDegree
  degree_le i := by
    apply le_trans (Finset.card_le_card_of_injOn (fun j : I => (Sum.inl j : I ⊕ O)) ?_ ?_)
      (Λ.degree_le (Sum.inl i))
    · intro j hj
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2⟩
    · intro j hj k hk he
      exact Sum.inl.inj he

/-- The induced exterior lattice. -/
def sumRight (Λ : Lattice (I ⊕ O)) : Lattice O where
  adj i j := Λ.adj (Sum.inr i) (Sum.inr j)
  symm := Λ.symm
  irrefl i := Λ.irrefl _
  maxDegree := Λ.maxDegree
  degree_le i := by
    apply le_trans (Finset.card_le_card_of_injOn (fun j : O => (Sum.inr j : I ⊕ O)) ?_ ?_)
      (Λ.degree_le (Sum.inr i))
    · intro j hj
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hj).2⟩
    · intro j hj k hk he
      exact Sum.inr.inj he

/-- Conditioning on the exterior adds exactly its interaction field. -/
def sumConditionalField (Λ : Lattice (I ⊕ O)) (h : I ⊕ O → ℝ)
    (β : ℝ) (τ : O → Spin) (i : I) : ℝ :=
  h (Sum.inl i) + β * ∑ o, if Λ.adj (Sum.inl i) (Sum.inr o) then spinVal (τ o) else 0

/-- Exact decomposition of the Ising Hamiltonian into a conditional interior
Hamiltonian and a term constant in the interior configuration. -/
theorem sum_energy_decomposition (Λ : Lattice (I ⊕ O)) (h : I ⊕ O → ℝ)
    (β : ℝ) (η : I → Spin) (τ : O → Spin) :
    Λ.interaction β univ (Sum.elim η τ) + fieldEnergy h univ (Sum.elim η τ) =
      Λ.sumLeft.interaction β univ η +
        fieldEnergy (Λ.sumConditionalField h β τ) univ η +
      (Λ.sumRight.interaction β univ τ + fieldEnergy (fun o => h (Sum.inr o)) univ τ) := by
  have hadj (i : I) (o : O) :
      Λ.adj (Sum.inr o) (Sum.inl i) ↔ Λ.adj (Sum.inl i) (Sum.inr o) :=
    ⟨Λ.symm, Λ.symm⟩
  have hc :
      (∑ o : O, ∑ i : I, if Λ.adj (Sum.inr o) (Sum.inl i) then
        spinVal (τ o) * spinVal (η i) else 0) =
      ∑ i : I, ∑ o : O, if Λ.adj (Sum.inl i) (Sum.inr o) then
        spinVal (η i) * spinVal (τ o) else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro o _
    simp only [hadj, mul_comm]
  have hf : fieldEnergy (Λ.sumConditionalField h β τ) univ η =
      (∑ i : I, h (Sum.inl i) * spinVal (η i)) +
      β * ∑ i : I, ∑ o : O, if Λ.adj (Sum.inl i) (Sum.inr o) then
        spinVal (η i) * spinVal (τ o) else 0 := by
    simp only [fieldEnergy, sumConditionalField, add_mul, sum_add_distrib]
    congr 1
    rw [mul_sum]
    apply sum_congr rfl
    intro i _
    simp only [mul_sum, sum_mul]
    apply sum_congr rfl
    intro o _
    split_ifs <;> ring
  rw [hf]
  simp only [interaction, fieldEnergy, sumLeft, sumRight, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, sum_add_distrib]
  rw [hc]
  ring

end Lattice

namespace FinProb

theorem conditional_w_of_factorization {α β : Type*} [Fintype α] [Fintype β]
    (p : FinProb (α × β)) (ν q : FinProb α) (b : β) (c : ℝ) (hc : c ≠ 0)
    (h : ∀ a, p.w (a, b) = c * q.w a) (a : α) :
    (p.interiorConditional ν b).w a = q.w a := by
  have hm : p.exteriorMarginal.w b = c := by
    change (∑ a, p.w (a,b)) = c
    simp_rw [h]
    rw [← mul_sum, q.sum_one, mul_one]
  have hz : p.exteriorMarginal.w b ≠ 0 := by rw [hm]; exact hc
  simp only [interiorConditional, dif_neg hz]
  change p.w (a,b) / p.exteriorMarginal.w b = q.w a
  rw [h a, hm]
  exact mul_div_cancel_left₀ _ hc

end FinProb

/-- The finite Gibbs law of the interior under an exterior configuration. -/
def sumInteriorGibbs {I O : Type*} [Fintype I] [Fintype O]
    (Λ : Lattice (I ⊕ O)) (h : I ⊕ O → ℝ) (β : ℝ) (τ : O → Spin) :
    FinProb (I → Spin) :=
  gibbs Λ.sumLeft (Λ.sumConditionalField h β τ) β univ ∅ (fun _ => 0)

/-- Exact conditional identification for an actual full finite-volume Gibbs
law. The exterior Hamiltonian cancels after conditioning and normalization. -/
theorem gibbs_sum_conditional_w {I O : Type*} [Fintype I] [Fintype O]
    (Λ : Lattice (I ⊕ O)) (h : I ⊕ O → ℝ) (β : ℝ)
    (ν : FinProb (I → Spin)) (τ : O → Spin) (η : I → Spin) :
    (((gibbs Λ h β univ ∅ (fun _ => 0)).reindex
        (Equiv.sumArrowEquivProdArrow I O Spin)).interiorConditional ν τ).w η =
      (sumInteriorGibbs Λ h β τ).w η := by
  let C := exp (Λ.sumRight.interaction β univ τ +
    Lattice.fieldEnergy (fun o => h (Sum.inr o)) univ τ)
  let ZI := isingZ Λ.sumLeft (Λ.sumConditionalField h β τ) β univ ∅ (fun _ => 0)
  let Z := isingZ Λ h β univ ∅ (fun _ => 0)
  have hZI : 0 < ZI := isingZ_pos _ _ _ _ _ _
  have hZ : 0 < Z := isingZ_pos _ _ _ _ _ _
  have hC : 0 < C := exp_pos _
  have hw (a : I → Spin) :
      isingWeight Λ h β univ ∅ (fun _ => 0) (Sum.elim a τ) =
      isingWeight Λ.sumLeft (Λ.sumConditionalField h β τ) β univ ∅ (fun _ => 0) a * C := by
    simp only [isingWeight, Lattice.boundEnergy, sum_empty, sum_const_zero, mul_zero, add_zero]
    rw [Lattice.sum_energy_decomposition, exp_add]
  apply FinProb.conditional_w_of_factorization _ ν (sumInteriorGibbs Λ h β τ) τ
    (C * ZI / Z) (ne_of_gt (div_pos (mul_pos hC hZI) hZ))
  intro a
  change isingWeight Λ h β univ ∅ (fun _ => 0) (Sum.elim a τ) / Z =
    (C * ZI / Z) *
      (isingWeight Λ.sumLeft (Λ.sumConditionalField h β τ) β univ ∅ (fun _ => 0) a / ZI)
  rw [hw]
  field_simp

namespace Lattice

variable {I O : Type*} [Fintype I] [Fintype O]

def leftSites : Finset (I ⊕ O) := univ.map ⟨Sum.inl, Sum.inl_injective⟩

def rightShell (S : Finset O) : Finset (I ⊕ O) := S.map ⟨Sum.inr, Sum.inr_injective⟩

/-- The conditioned interaction field is exactly the original field plus
the original boundary Hamiltonian, when the shell contains all cross edges. -/
theorem sumConditionalField_energy (Λ : Lattice (I ⊕ O)) (h : I ⊕ O → ℝ)
    (β : ℝ) (S : Finset O)
    (hS : ∀ i o, Λ.adj (Sum.inl i) (Sum.inr o) → o ∈ S)
    (η : I → Spin) (τ : O → Spin) :
    fieldEnergy (Λ.sumConditionalField h β τ) univ η =
      fieldEnergy h leftSites (Sum.elim η τ) +
        Λ.boundEnergy β leftSites (rightShell S) (Sum.elim (fun _ => 0) τ) (Sum.elim η τ) := by
  have hs (i : I) : (∑ o : O, if Λ.adj (Sum.inl i) (Sum.inr o) then spinVal (τ o) else 0) =
      ∑ o ∈ S, if Λ.adj (Sum.inl i) (Sum.inr o) then spinVal (τ o) else 0 := by
    symm
    apply sum_subset (subset_univ S)
    intro o ho hnot
    exact if_neg (fun ha => hnot (hS i o ha))
  simp only [fieldEnergy, sumConditionalField, leftSites, rightShell, sum_map,
    Function.Embedding.coeFn_mk, Sum.elim_inl, boundEnergy, Sum.elim_inr,
    add_mul, sum_add_distrib]
  simp_rw [hs]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro i _
  simp only [mul_sum, sum_mul]
  apply sum_congr rfl
  intro o ho
  split_ifs <;> ring

/-- The actual logarithmic density tilt of the restricted conditional Gibbs
law agrees with `shellTilt` of the original Hamiltonian. -/
theorem sum_logTilt_eq (Λ : Lattice (I ⊕ O)) (h : I ⊕ O → ℝ)
    (β : ℝ) (S : Finset O)
    (hS : ∀ i o, Λ.adj (Sum.inl i) (Sum.inr o) → o ∈ S)
    (ζ τ : O → Spin) (η : I → Spin) :
    (Λ.sumLeft.interaction β univ η + fieldEnergy (Λ.sumConditionalField h β τ) univ η) -
      (Λ.sumLeft.interaction β univ η +
        fieldEnergy (Λ.sumConditionalField (fun _ => 0) β ζ) univ η) =
      shellTilt Λ h β leftSites (rightShell S)
        (Sum.elim (fun _ => 0) ζ) (Sum.elim (fun _ => 0) τ) (Sum.elim η τ) := by
  rw [sumConditionalField_energy Λ h β S hS η τ,
    sumConditionalField_energy Λ (fun _ => 0) β S hS η ζ]
  have hfield : fieldEnergy (fun _ => 0) leftSites (Sum.elim η ζ) = 0 := by
    simp [fieldEnergy]
  have hbound : Λ.boundEnergy β leftSites (rightShell S)
      (Sum.elim (fun _ => 0) ζ) (Sum.elim η ζ) =
      Λ.boundEnergy β leftSites (rightShell S)
        (Sum.elim (fun _ => 0) ζ) (Sum.elim η τ) := by
    simp [boundEnergy, leftSites]
  rw [hfield, hbound]
  unfold shellTilt
  ring

end Lattice

/-- Density comparison for the actual restricted conditional Gibbs laws,
derived from the original Hamiltonian and its shell-defect oscillation. -/
theorem sumInteriorGibbs_density {I O : Type*} [Fintype I] [Fintype O]
    (Λ : Lattice (I ⊕ O)) (h : I ⊕ O → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset O) (hS : ∀ i o, Λ.adj (Sum.inl i) (Sum.inr o) → o ∈ S)
    (ζ τ : O → Spin) :
    let D := 2 * fieldMass h Lattice.leftSites +
      4 * β * (shellDegree Λ Lattice.leftSites (Lattice.rightShell S) : ℝ) *
        (defectCount S ζ τ : ℝ)
    ∀ η, exp (-D) * (sumInteriorGibbs Λ (fun _ => 0) β ζ).w η ≤
        (sumInteriorGibbs Λ h β τ).w η ∧
      (sumInteriorGibbs Λ h β τ).w η ≤
        exp D * (sumInteriorGibbs Λ (fun _ => 0) β ζ).w η := by
  dsimp only
  let D := 2 * fieldMass h Lattice.leftSites +
    4 * β * (shellDegree Λ Lattice.leftSites (Lattice.rightShell S) : ℝ) *
      (defectCount S ζ τ : ℝ)
  let f := fun η : I → Spin => Λ.sumLeft.interaction β univ η +
    Lattice.fieldEnergy (Λ.sumConditionalField h β τ) univ η
  let g := fun η : I → Spin => Λ.sumLeft.interaction β univ η +
    Lattice.fieldEnergy (Λ.sumConditionalField (fun _ => 0) β ζ) univ η
  have hk : defectCount (Lattice.rightShell S) (Sum.elim (fun _ : I => 0) ζ)
      (Sum.elim (fun _ : I => 0) τ) = defectCount S ζ τ := by
    simp [defectCount, Lattice.rightShell, Finset.filter_map, Function.comp_def]
  have ho : ∀ η ξ, (f η - g η) - (f ξ - g ξ) ≤ D := by
    intro η ξ
    rw [show f η - g η = _ from Lattice.sum_logTilt_eq Λ h β S hS ζ τ η,
      show f ξ - g ξ = _ from Lattice.sum_logTilt_eq Λ h β S hS ζ τ ξ]
    have hh := shellTilt_oscillation Λ h β hβ Lattice.leftSites (Lattice.rightShell S)
      (Sum.elim (fun _ : I => 0) ζ) (Sum.elim (fun _ : I => 0) τ)
      (Sum.elim η τ) (Sum.elim ξ τ)
    simpa only [hk] using hh
  have ho' : ∀ η ξ, (g η - f η) - (g ξ - f ξ) ≤ D := by
    intro η ξ
    have hh := ho ξ η
    linarith
  have hw (h' : I ⊕ O → ℝ) (τ' : O → Spin) (η : I → Spin) :
      (sumInteriorGibbs Λ h' β τ').w η =
        exp (Λ.sumLeft.interaction β univ η +
          Lattice.fieldEnergy (Λ.sumConditionalField h' β τ') univ η) /
        ∑ ξ, exp (Λ.sumLeft.interaction β univ ξ +
          Lattice.fieldEnergy (Λ.sumConditionalField h' β τ') univ ξ) := by
    simp [sumInteriorGibbs, gibbs_w, isingWeight, isingZ, Lattice.boundEnergy]
  intro η
  rw [hw, hw]
  change exp (-D) * (exp (g η) / ∑ ξ, exp (g ξ)) ≤ exp (f η) / ∑ ξ, exp (f ξ) ∧
    exp (f η) / (∑ ξ, exp (f ξ)) ≤ exp D * (exp (g η) / ∑ ξ, exp (g ξ))
  have hu := normalized_exp_density_upper f g D ho η
  have hl := normalized_exp_density_upper g f D ho' η
  constructor
  · have hh := mul_le_mul_of_nonneg_left hl (exp_pos (-D)).le
    rw [← mul_assoc, ← exp_add] at hh
    simpa only [neg_add_cancel, exp_zero, one_mul] using hh
  · exact hu

/-- Lemma 2.2 for the actual finite Ising Gibbs law, with the exact shell
degree and the actual shell moments. Every conditional density comparison
and every gap comparison in the proof is derived, not assumed. -/
theorem gibbs_soft_shell_sum {I O : Type*} [Fintype I] [Fintype O] [Nonempty I]
    (Λ : Lattice (I ⊕ O)) (h : I ⊕ O → ℝ) (β : ℝ) (hβ : 0 ≤ β)
    (S : Finset O) (hS : ∀ i o, Λ.adj (Sum.inl i) (Sum.inr o) → o ∈ S)
    (ζ : O → Spin) :
    let p := gibbs Λ h β univ ∅ (fun _ => 0)
    let ν := sumInteriorGibbs Λ (fun _ => 0) β ζ
    let b := 4 * β * (shellDegree Λ Lattice.leftSites (Lattice.rightShell S) : ℝ)
    spectralGap (V := I ⊕ O) p ≤ spectralGap (V := I) ν *
      exp (4 * fieldMass h Lattice.leftSites) *
        (p.expect (fun η => exp (b * (defectCount S ζ (fun o => η (Sum.inr o)) : ℝ))) /
          p.expect (fun η => exp (-b * (defectCount S ζ (fun o => η (Sum.inr o)) : ℝ)))) := by
  dsimp only
  apply spectralGap_soft_shell_sum
  · intro η
    exact div_pos (isingWeight_pos _ _ _ _ _ _ _) (isingZ_pos _ _ _ _ _ _)
  · intro τ η
    rw [gibbs_sum_conditional_w]
    exact (sumInteriorGibbs_density Λ h β hβ S hS ζ τ η).1
  · intro τ η
    rw [gibbs_sum_conditional_w]
    exact (sumInteriorGibbs_density Λ h β hβ S hS ζ τ η).2

end Paper09
