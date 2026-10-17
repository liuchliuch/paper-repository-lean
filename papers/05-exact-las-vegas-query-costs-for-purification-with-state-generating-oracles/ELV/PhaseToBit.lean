import ELV.Hadamard
import ELV.ReflectionCompile
import ELV.UnrestrictedWitness

/-! The two Hadamards act only on the public register. The private catalyst
is scaled once and returned; every phase-query amplitude is scaled by 1/sqrt 2. -/
noncomputable section
namespace ELV.Query
open ELV.Stabilize ELV.Hilbert
variable {L N Q : Type*}
  [NormedAddCommGroup L] [InnerProductSpace ℂ L]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N]
  [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]

/-- Regroup the two public amplitudes while leaving the private summand intact. -/
def publicHadamard : HilbertPair ℂ (HilbertPair ℂ L) ≃ₗᵢ[ℂ] HilbertPair ℂ (HilbertPair ℂ L) :=
  pairAssoc.symm.trans ((pairCongr hadamard (LinearIsometryEquiv.refl ℂ L)).trans pairAssoc)

lemma publicHadamard_apply (a b : ℂ) (w : L) :
    publicHadamard (WithLp.toLp 2 (a,WithLp.toLp 2 (b,w))) =
      WithLp.toLp 2 ((halfAmplitude : ℂ)*(a+b),WithLp.toLp 2 ((halfAmplitude : ℂ)*(a-b),w)) := rfl

/-- Known H, the fixed phase circuit in the second public branch, then known H. -/
def phaseToBit (c : Circuit (HilbertPair ℂ L) N Q) :
    Circuit (HilbertPair ℂ (HilbertPair ℂ L)) (HilbertPair ℂ N) Q :=
  [.work publicHadamard] ++ parallel c ++ [.work publicHadamard]

lemma phaseToBit_run (c : Circuit (HilbertPair ℂ L) N Q) (O : Q ≃ₗᵢ[ℂ] Q)
    (ζ : ℂ) (w : L)
    (he : run O c (WithLp.toLp 2 ((1 : ℂ),w)) = WithLp.toLp 2 (ζ,w)) :
    run O (phaseToBit c) (WithLp.toLp 2 ((1 : ℂ),WithLp.toLp 2 ((0 : ℂ),(halfAmplitude : ℂ) • w))) =
      WithLp.toLp 2 ((halfAmplitude : ℂ)^2*(1+ζ),
        WithLp.toLp 2 ((halfAmplitude : ℂ)^2*(1-ζ),(halfAmplitude : ℂ) • w)) := by
  rw [phaseToBit,run_append,run_append]
  simp only [run,Gate.unitary,publicHadamard_apply,add_zero,sub_zero,mul_one]
  have hm : WithLp.toLp 2 ((halfAmplitude : ℂ),(halfAmplitude : ℂ) • w) =
      (halfAmplitude : ℂ) • WithLp.toLp 2 ((1 : ℂ),w) := by
    apply (WithLp.equiv 2 (_ × _)).injective
    apply Prod.ext
    · change (halfAmplitude : ℂ) = (halfAmplitude : ℂ)*1
      ring
    · rfl
  rw [run_parallel,hm,run_smul,he]
  change publicHadamard (WithLp.toLp 2 ((halfAmplitude : ℂ),
    WithLp.toLp 2 ((halfAmplitude : ℂ)*ζ,(halfAmplitude : ℂ) • w))) = _
  rw [publicHadamard_apply]
  apply (WithLp.equiv 2 (_ × _)).injective
  apply Prod.ext
  · change (halfAmplitude : ℂ)*((halfAmplitude : ℂ)+(halfAmplitude : ℂ)*ζ) = (halfAmplitude : ℂ)^2*(1+ζ)
    ring
  · apply (WithLp.equiv 2 (_ × _)).injective
    apply Prod.ext
    · change (halfAmplitude : ℂ)*((halfAmplitude : ℂ)-(halfAmplitude : ℂ)*ζ) = (halfAmplitude : ℂ)^2*(1-ζ)
      ring
    · rfl

lemma phaseToBit_cost (c : Circuit (HilbertPair ℂ L) N Q) (O : Q ≃ₗᵢ[ℂ] Q) (w : L) :
    cost O (phaseToBit c) (WithLp.toLp 2 ((1 : ℂ),WithLp.toLp 2 ((0 : ℂ),(halfAmplitude : ℂ) • w))) =
      (1/2 : ℝ)*cost O c (WithLp.toLp 2 ((1 : ℂ),w)) := by
  rw [phaseToBit,cost_append,cost_append]
  simp only [cost_cons,cost_nil,Gate.queried,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),
    add_zero,zero_add,run,Gate.unitary,publicHadamard_apply,add_zero,sub_zero,mul_one]
  rw [cost_parallel]
  have hm : WithLp.toLp 2 ((halfAmplitude : ℂ),(halfAmplitude : ℂ) • w) =
      (halfAmplitude : ℂ) • WithLp.toLp 2 ((1 : ℂ),w) := by
    apply (WithLp.equiv 2 (_ × _)).injective
    apply Prod.ext
    · change (halfAmplitude : ℂ) = (halfAmplitude : ℂ)*1
      ring
    · rfl
  rw [hm,cost_smul,amplitude_norm_sq]

lemma phaseToBit_catalyst_norm (w : L) :
    ‖(halfAmplitude : ℂ) • w‖^2 = (1/2 : ℝ)*‖w‖^2 := by
  rw [norm_smul,mul_pow,amplitude_norm_sq]

end ELV.Query
