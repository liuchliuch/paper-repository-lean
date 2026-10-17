import Paper09.BlockMixing
import Paper09.BlockConditional

open Finset BigOperators Classical Real Matrix
open Paper09.BlockKernels Paper09.Disagreement
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1000000

namespace Paper09
namespace ActualBlockMixing

variable {V W : Type*} [Fintype V] [Fintype W]

/-- Changing site coordinates preserves the actual heat-bath generator. -/
theorem generator_relabel (p : FinProb (Config V)) (e : V ≃ W)
    (f : Config V → ℝ) (θ : Config W) :
    heatBathGenerator p f ((Relabel.configEquiv e).symm θ) =
      heatBathGenerator (p.reindex (Relabel.configEquiv e))
        (fun ξ => f ((Relabel.configEquiv e).symm ξ)) θ := by
  let E := Relabel.configEquiv e
  have hr (ξ : Config W) : heatBathRate p (E.symm θ) (E.symm ξ) =
      heatBathRate (p.reindex E) θ ξ := by
    unfold heatBathRate
    rw [Relabel.oneSite_iff e θ ξ]
    rfl
  unfold heatBathGenerator
  have hs := E.symm.sum_comp (fun η => heatBathRate p (E.symm θ) η * (f η-f (E.symm θ)))
  rw [← hs]
  apply sum_congr rfl
  intro ξ hξ
  rw [hr]

/-- The real matrix-exponential transition probabilities are invariant under
site relabeling, including the actual rate-one time normalization. -/
theorem transition_relabel (p : FinProb (Config V)) (e : V ≃ W)
    (t : ℝ) (η : Config V) :
    heatBathTransition (p.reindex (Relabel.configEquiv e)) t ((Relabel.configEquiv e) η) =
      (heatBathTransition p t η).reindex (Relabel.configEquiv e) := by
  let E := Relabel.configEquiv e
  let q := p.reindex E
  have hint : ∀ f a,
      ((max t 0 • heatBathMatrix p)*ᵥf) (E.symm a) =
      ((max t 0 • heatBathMatrix q)*ᵥ(fun b => f (E.symm b))) a := by
    intro f a
    simp only [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, heatBathMatrix_mulVec]
    rw [generator_relabel p e]
  apply FinProb.ext_weights
  intro θ
  let f : Config V → ℝ := fun ξ => if ξ = E.symm θ then 1 else 0
  have hh := matrix_exp_action_intertwine (max t 0 • heatBathMatrix p)
    (max t 0 • heatBathMatrix q) E.symm hint f (E η)
  have htest (ξ : Config W) : f (E.symm ξ) = if ξ = θ then 1 else 0 := by
    dsimp [f]
    simp only [E.symm.injective.eq_iff]
  simp only [E.symm_apply_apply, Matrix.mulVec, dotProduct, htest, f,
    mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true] at hh
  change heatBathSemigroup q (max t 0) (E η) θ = heatBathSemigroup p (max t 0) η (E.symm θ)
  exact hh.symm

theorem tv_reindex {A B : Type*} [Fintype A] [Fintype B]
    (p q : FinProb A) (e : A ≃ B) :
    tvDist (p.reindex e) (q.reindex e) = tvDist p q := by
  unfold tvDist FinProb.reindex
  congr 1
  exact e.symm.sum_comp (fun x => |p.w x-q.w x|)

theorem transition_tv_relabel (p : FinProb (Config V)) (e : V ≃ W)
    (t : ℝ) (η : Config V) :
    tvDist (heatBathTransition (p.reindex (Relabel.configEquiv e)) t ((Relabel.configEquiv e) η))
      (p.reindex (Relabel.configEquiv e)) = tvDist (heatBathTransition p t η) p := by
  rw [transition_relabel, tv_reindex]

private theorem tv_subsingleton {A : Type*} [Fintype A] [Subsingleton A] (p q : FinProb A) :
    tvDist p q = 0 := by
  have hp (a : A) : p.w a = 1 := Fintype.eq_of_subsingleton_of_sum_eq p.sum_one a (mem_univ a)
  have hq (a : A) : q.w a = 1 := Fintype.eq_of_subsingleton_of_sum_eq q.sum_one a (mem_univ a)
  simp only [tvDist, hp, hq, sub_self, abs_zero, sum_const_zero, mul_zero]

end ActualBlockMixing
namespace RFIM

local instance (priority := 2000) actualBlockPointDecEq (d : ℕ) : DecidableEq (Point d) := Classical.decEq _
local instance (priority := 2000) actualBlockSiteDecEq {d : ℕ} (A : Finset (Point d)) : DecidableEq ↥A := Classical.decEq _
local instance (priority := 3000) actualBlockSubtypeDecEq {V : Type*} (B : Finset V) : DecidableEq ↥B := Classical.decEq _

/-- The concrete local-chain replacement estimate in the actual finite-volume
RFIM. The exterior is frozen in the real ambient chain, and the stationary
comparison law is the real conditional block heat-bath update. -/
theorem actual_block_mixing (d : ℕ) (β σ cstar : ℝ) (hd : 2 ≤ d) (hβ : 0 < β)
    (hσ : 0 ≤ σ) (hcstar : 0 < cstar) (hcstar1 : cstar < 1) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ C : ℝ, C₀ ≤ C → ∀ (Ω B : Finset (Point d)), B ⊆ Ω →
      ∀ (h : Point d → ℝ) (L R M N : ℝ),
      1 ≤ L → 1 ≤ R → 1 ≤ M → 2 ≤ N →
      (B.card:ℝ) ≤ M → (B.card:ℝ) ≤ L*R^d →
      (∀ x ∈ Ω, |h x| ≤ σ*sqrt (8*log N)) →
      let p := freeGibbs Ω h β
      let hp := gibbs_positive (domainLattice Ω) (fun x : ↥Ω => h x.val) β univ ∅ (fun _ => 0)
      let U := ambientBlockSites Ω B
      let T := C*exp (C*(R^(d-1)*L^exponentA d)) *
        (M*(1+sqrt (log N))+2*log M+1)
      0 ≤ T ∧ ∀ η, tvDist (Censoring.siteTransition p hp U T η)
        (blockHeatBath p hp U η) ≤ cstar/M^2 := by
  obtain ⟨C₀,hC₀,hbound⟩ := domain_field_block_mixing d β σ cstar hd hβ hσ hcstar hcstar1
  refine ⟨C₀,hC₀,?_⟩
  intro C hCbig Ω B hB h L R M N hL hR hM hN hqM hqvol hh
  let p := freeGibbs Ω h β
  let hp : ∀ η, 0 < p.w η := gibbs_positive _ _ _ _ _ _
  let U := ambientBlockSites Ω B
  have hC : 0 < C := hC₀.trans_le hCbig
  let T₀ := C₀*exp (C₀*(R^(d-1)*L^exponentA d))*(M*(1+sqrt (log N))+2*log M+1)
  let T := C*exp (C*(R^(d-1)*L^exponentA d))*(M*(1+sqrt (log N))+2*log M+1)
  have hlogM : 0 ≤ log M := log_nonneg hM
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hT₀ : 0 ≤ T₀ := by dsimp [T₀]; positivity
  have hTlater : T₀ ≤ T := by
    have hS : 0 ≤ R^(d-1)*L^exponentA d := by positivity
    have he : exp (C₀*(R^(d-1)*L^exponentA d)) ≤ exp (C*(R^(d-1)*L^exponentA d)) :=
      exp_le_exp.mpr (mul_le_mul_of_nonneg_right hCbig hS)
    exact mul_le_mul_of_nonneg_right (mul_le_mul hCbig he (exp_nonneg _) hC.le) (by positivity)
  have hδ : 0 ≤ cstar/M^2 := by positivity
  refine ⟨hT,?_⟩
  intro η
  apply block_ct_mixing_error p hp U η T (cstar/M^2)
  intro ξ
  by_cases hBn : B.Nonempty
  · let e := blockSiteEquiv Ω B hB
    let E := Relabel.configEquiv e
    let q := localConditional p hp U η
    have heq : q.reindex E = blockLocalGibbs Ω B h β η :=
      localConditional_eq_blockLocalGibbs Ω B hB h β η
    have hfield : ∀ x, |blockLocalField Ω B h β η x| ≤ σ*sqrt (8*log N)+2*(d:ℝ)*β :=
      blockLocalField_abs_le Ω B h β _ hβ.le (fun x hx => hh x (hB hx)) η
    have hmix := (hbound B hBn (blockLocalField Ω B h β η) L R M N hL hR hM hN hqM hqvol hfield).2 (E ξ)
    change tvDist (heatBathTransition (blockLocalGibbs Ω B h β η) T₀ (E ξ))
      (blockLocalGibbs Ω B h β η) ≤ _ at hmix
    rw [← heq, ActualBlockMixing.transition_tv_relabel q e T₀ ξ] at hmix
    exact (heatBath_tv_later q T₀ T hT₀ hTlater ξ).trans hmix
  · have hb0 : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hBn
    have hU : U = ∅ := by simp [U, ambientBlockSites, hb0]
    letI : IsEmpty ↥U := ⟨fun x => by simpa only [hU, Finset.not_mem_empty] using x.property⟩
    rw [ActualBlockMixing.tv_subsingleton]
    exact hδ

end RFIM
end Paper09
