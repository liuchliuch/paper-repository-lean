import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Tactic.FunProp
import Lean.Elab.Tactic.Omega

/-!
# Almost-sure affine spanning at the exact sample-size endpoint

This file proves the probabilistic half of Proposition 7.3 for actual product
probability measures with a density. The proof uses Fubini, the openness of
finite affine independence, and the Haar-nullity of proper affine subspaces.
-/
noncomputable section
namespace Paper38.GaussianFullRank

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped ENNReal

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma affineIndependent_cons {n : ℕ} {p : Fin n → V}
    (hp : AffineIndependent ℝ p) {x : V}
    (hx : x ∉ affineSpan ℝ (Set.range p)) :
    AffineIndependent ℝ (Fin.cons x p) := by
  have ha : AffineIndependent ℝ (fun i : {i : Fin (n + 1) // i ≠ 0} =>
      (@Fin.cons n (fun _ => V) x p (i : Fin (n + 1)))) := by
    rw [← affineIndependent_equiv (finSuccAboveEquiv (0 : Fin (n + 1)))]
    simpa only [Function.comp_apply, finSuccAboveEquiv_apply, Fin.succAbove_zero,
      Fin.cons_succ] using hp
  apply ha.affineIndependent_of_notMem_span
  have himage : Fin.cons x p '' {i : Fin (n + 1) | i ≠ 0} = Set.range p := by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      cases i using Fin.cases with
      | zero => exact (hi rfl).elim
      | succ i => exact ⟨i, by simp⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i.succ, Fin.succ_ne_zero i, by simp⟩
  simpa only [Fin.cons_zero, himage] using hx

variable [FiniteDimensional ℝ V] [MeasureSpace V] [BorelSpace V]
  [IsAddHaarMeasure (volume : Measure V)]

lemma density_avoids_proper_affineSubspace {μ : Measure V}
    (hμ : μ ≪ volume) (s : AffineSubspace ℝ V) (hs : s ≠ ⊤) :
    ∀ᵐ x ∂μ, x ∉ s := by
  rw [ae_iff]
  simpa only [not_not, Set.setOf_mem_eq] using hμ (addHaar_affineSubspace volume s hs)

/-- Independent samples from any density are affinely independent up to the
maximal possible family size. -/
theorem ae_affineIndependent {μ : Measure V} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (n : ℕ) (hn : n ≤ Module.finrank ℝ V + 1) :
    ∀ᵐ p : Fin n → V ∂Measure.pi (fun _ => μ), AffineIndependent ℝ p := by
  induction n with
  | zero => exact Filter.Eventually.of_forall (fun p => affineIndependent_of_subsingleton ℝ p)
  | succ n ih =>
    have hn' : n ≤ Module.finrank ℝ V + 1 := by omega
    have hmeas : MeasurableSet {z : V × (Fin n → V) |
        AffineIndependent ℝ (Fin.cons z.1 z.2)} := by
      apply IsOpen.measurableSet
      apply isOpen_setOf_affineIndependent.preimage
      exact continuous_pi fun i => Fin.cases continuous_fst
        (fun k => (continuous_apply k).comp continuous_snd) i
    have hprod : ∀ᵐ z : V × (Fin n → V) ∂μ.prod (Measure.pi (fun _ => μ)),
        AffineIndependent ℝ (Fin.cons z.1 z.2) := by
      apply (ae_prod_iff_ae_ae hmeas).2
      apply (ae_ae_comm hmeas).2
      filter_upwards [ih hn'] with p hp
      have hproper : affineSpan ℝ (Set.range p) ≠ ⊤ := by
        intro htop
        have hc := hp.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp htop
        simp only [Fintype.card_fin] at hc
        omega
      filter_upwards [density_avoids_proper_affineSubspace hμ _ hproper] with x hx
      exact affineIndependent_cons hp hx
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => V) 0
    have he := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0
    have hprod' : ∀ᵐ z : V × (Fin n → V) ∂μ.prod (Measure.pi (fun _ => μ)),
        AffineIndependent ℝ (e.symm z) := by
      simpa only [e, MeasurableEquiv.piFinSuccAbove_symm_apply,
        Fin.insertNthEquiv_zero] using hprod
    have hmap := (ae_map_iff e.symm.measurable.aemeasurable
      isOpen_setOf_affineIndependent.measurableSet).2 hprod'
    rwa [(he.symm).map_eq] at hmap

/-- At exactly d+1 independent samples, a density gives full affine span almost
surely. Combined with the deterministic covariance characterization, this is
positive definiteness at the exact endpoint in Proposition 7.3. -/
theorem ae_affineSpan_eq_top_endpoint {μ : Measure V} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) :
    ∀ᵐ p : Fin (Module.finrank ℝ V + 1) → V ∂Measure.pi (fun _ => μ),
      affineSpan ℝ (Set.range p) = ⊤ := by
  filter_upwards [ae_affineIndependent hμ (Module.finrank ℝ V + 1) le_rfl] with p hp
  exact hp.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simp)

/-- The sufficiency statement of Proposition 7.3 for every N ≥ d+1,
with independent samples under their actual product law. -/
theorem ae_affineSpan_eq_top {μ : Measure V} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) {N : ℕ} (hN : Module.finrank ℝ V + 1 ≤ N) :
    ∀ᵐ p : Fin N → V ∂Measure.pi (fun _ => μ),
      affineSpan ℝ (Set.range p) = ⊤ := by
  let f : Fin (Module.finrank ℝ V + 1) → Fin N := Fin.castLE hN
  have hf : Function.Injective f := Fin.castLE_injective hN
  have hi : iIndepFun (fun i : Fin N => fun p : Fin N → V => p i)
      (Measure.pi (fun _ : Fin N => μ)) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
  have hi' := hi.precomp hf
  have hmap : (Measure.pi (fun _ : Fin N => μ)).map
      (fun p i => p (f i)) = Measure.pi (fun _ : Fin (Module.finrank ℝ V + 1) => μ) := by
    rw [(iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (measurable_pi_apply (f i)).aemeasurable)).1 hi']
    congr 1
    funext i
    exact (measurePreserving_eval (fun _ : Fin N => μ) (f i)).map_eq
  have hae : ∀ᵐ p : Fin N → V ∂Measure.pi (fun _ => μ),
      affineSpan ℝ (Set.range (fun i => p (f i))) = ⊤ := by
    have hendpoint : ∀ᵐ q ∂(Measure.pi (fun _ : Fin N => μ)).map
        (fun p : Fin N → V => fun i => p (f i)),
        affineSpan ℝ (Set.range q) = ⊤ := by
      rw [hmap]
      exact ae_affineSpan_eq_top_endpoint hμ
    exact ae_of_ae_map (measurable_pi_iff.2
      (fun i => measurable_pi_apply (f i))).aemeasurable hendpoint
  filter_upwards [hae] with p hp
  apply le_antisymm le_top
  rw [← hp]
  exact affineSpan_mono ℝ (Set.range_comp_subset_range f p)

end Paper38.GaussianFullRank
