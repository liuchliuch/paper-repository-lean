import Paper29.SeedCompression
import Paper29.DecodingAggregation
import Paper29.HardTranscript

noncomputable section
open scoped BigOperators ENNReal Classical
open MeasureTheory
namespace Paper29.QueryModel

/-- Finite success event retains an original successful seed as its witness. -/
def codeSuccess {Ω R : Type} {n d r : ℕ} (hrd : r ≤ d) (label : R → ℝ)
    (p : Policy Ω n d) (A : Matrix (Fin n) (Fin d) ℝ) (ε : ℝ) (b : Fin n → R)
    (e : PolicyCode n r R) : Prop :=
  ∃ ω,compilePolicy hrd label p ω=e ∧ Successful p A (fun i => label (b i)) ε ω

theorem correct_success_real {Ω : Type} [MeasurableSpace Ω] {n d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : Policy Ω n d)
    (A : Matrix (Fin n) (Fin d) ℝ) (ε : ℝ) (hp : Correct μ p A ε) (b : Fin n → ℝ) :
    (99/100:ℝ) ≤ μ.real {ω | Successful p A b ε ω} := by
  have hh := ENNReal.toReal_mono (measure_ne_top μ _) (hp.2.2 b).2.2
  norm_num only [ENNReal.toReal_div,ENNReal.toReal_ofNat] at hh
  exact hh

/-- The actual success probability survives measurable finite seed compression. -/
theorem codeSuccess_probability {Ω R : Type} [MeasurableSpace Ω] [Fintype R]
    {n d r : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hrd : r ≤ d) (label : R → ℝ) (p : Policy Ω n d)
    (A : Matrix (Fin n) (Fin d) ℝ) (ε : ℝ) (hp : Correct μ p A ε) (b : Fin n → R) :
    (99/100:ℝ) ≤ Sampling.eventMass (ProcessTools.seedCodeMass μ (compilePolicy hrd label p))
      (Finset.univ.filter (codeSuccess hrd label p A ε b)) := by
  apply (correct_success_real μ p A ε hp (fun i => label (b i))).trans
  apply ProcessTools.seedCodeMass_success μ _ (measurable_compilePolicy hrd label p hp.2.1)
  intro ω hω
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨ω,rfl,hω⟩⟩

/-- At a successful code, the causal compressed decoder equals a real
successful output's decoded coordinates. -/
theorem codeSuccess_decoder {Ω R : Type} [Nonempty Ω] {n d r : ℕ}
    (hrd : r ≤ d) (label : R → ℝ) (p : Policy Ω n d) (hfresh : Fresh p)
    (A : Matrix (Fin n) (Fin d) ℝ) (ε : ℝ) (b : Fin n → R) (e : PolicyCode n r R)
    (he : codeSuccess hrd label p A ε b e) :
    let rep := ProcessTools.seedRepresentative (compilePolicy hrd label p)
    ∃ x : Fin d → ℝ,
      Transcript.representativeDecoder rep label p hrd n
        ((Transcript.representativePolicy rep label p hfresh).history e b n) =
          (fun j => HardDistribution.decode (x (Fin.castLE hrd j))) ∧
      ∀ y,Real.sqrt (objective A (fun i => label (b i)) x) ≤
        (1+ε)*Real.sqrt (objective A (fun i => label (b i)) y) := by
  obtain ⟨ω,hcode,x,h,hrun,hgood⟩ := he
  subst e
  exact ⟨x,compressed_decoder_returned hrd label p hfresh ω b x h hrun,hgood⟩

end Paper29.QueryModel
namespace Paper29.HardDistribution
open Transcript

/-- Averaging an event over the exact hard source/response distribution and an
independent finite seed. -/
theorem hardSeedLaw_event_ge {E : Type} [Fintype E] {r N : ℕ}
    (q : E → ℝ) (hq : ∀ e,0 ≤ q e) (hsq : ∑ e,q e=1)
    (β : ℝ) (hβ : 0 ≤ β) (hβhi : β ≤ 1/2)
    (F : Signs r × (Bits r N × E) → Prop) [DecidablePred F] (a : ℝ)
    (hF : ∀ s y,a ≤ Sampling.eventMass q (Finset.univ.filter (fun e => F (s,(y,e))))) :
    a ≤ Sampling.eventMass (hardSeedLaw q hq hsq β hβ hβhi).weight (Finset.univ.filter F) := by
  have hnonneg := hardMass_nonneg (r:=r) (N:=N) β hβ hβhi
  calc
    a = ∑ s : Signs r, ∑ y : Bits r N, hardMass β s y*a := by
      simp only [← Finset.sum_mul,hardMass_total,one_mul]
    _ ≤ ∑ s : Signs r, ∑ y : Bits r N, hardMass β s y*
        Sampling.eventMass q (Finset.univ.filter (fun e => F (s,(y,e)))) := by
      exact Finset.sum_le_sum (fun s _ => Finset.sum_le_sum
        (fun y _ => mul_le_mul_of_nonneg_left (hF s y) (hnonneg s y)))
    _ = _ := by
      simp only [Sampling.eventMass,Finset.sum_filter,Fintype.sum_prod_type,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro e _
      change hardMass β s y*(if F (s,(y,e)) then q e else 0) =
        if F (s,(y,e)) then hardMass β s y*q e else 0
      split_ifs <;> ring

end Paper29.HardDistribution
