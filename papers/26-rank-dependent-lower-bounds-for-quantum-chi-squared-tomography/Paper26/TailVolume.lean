import Paper26.TailGeometry
import Paper26.VolumeSymmetry
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Lemma 2.3's actual Lebesgue-volume argument, relative only to classical
Brunn--Minkowski, unitary invariance of Lebesgue measure, and the generic
Lyapunov positivity input used by the proved joint-convexity theorem.
Neither input asserts a tail-body volume inequality.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.TailVolume

open TailConvexity VolumeSymmetry

local instance matrixMeasurableSpace (m : Type*) (n : Type*) :
    MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

abbrev μ : Measure (Matrix ι κ ℂ) := TailGeometry.matrixLebesgue

def exponent : ℝ := 1 / ((2 * Fintype.card ι * Fintype.card κ : ℕ) : ℝ)

def volumeRoot (K : ℝ) (A : Matrix ι ι ℂ) : ℝ :=
  (μ (body A K : Set (Matrix ι κ ℂ))).toReal ^ (exponent (ι := ι) (κ := κ))

def minkowskiMix (t : ℝ) (S T : Set (Matrix ι κ ℂ)) : Set (Matrix ι κ ℂ) :=
  {Z | ∃ X ∈ S, ∃ Y ∈ T, Z = mix t X Y}

/-- Classical Brunn--Minkowski on the actual real `2*s*r`-dimensional matrix
space, for arbitrary nonempty compact sets. Gardner (2002), Theorem 4.1.
This exact external input is explicit and is never installed as an axiom. -/
structure BrunnMinkowskiInput (ι κ : Type*) [Fintype ι] [Fintype κ] : Prop where
  compact_sets : ∀ (S T : Set (Matrix ι κ ℂ)), IsCompact S → IsCompact T →
    S.Nonempty → T.Nonempty → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    (1 - t) * (μ S).toReal ^ (exponent (ι := ι) (κ := κ)) +
      t * (μ T).toReal ^ (exponent (ι := ι) (κ := κ)) ≤
      (μ (minkowskiMix t S T)).toReal ^ (exponent (ι := ι) (κ := κ))

/-- Ordinary invariance of Lebesgue outer measure under complex unitary row
rotations. It quantifies over all sets, independently of the loss or `A`. -/
structure UnitaryLebesgueInput (ι κ : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype κ] : Prop where
  image_measure : ∀ (U : Matrix ι ι ℂ), Uᴴ * U = 1 → U * Uᴴ = 1 →
    ∀ S : Set (Matrix ι κ ℂ), μ ((fun Z => U * Z) '' S) = μ S

lemma body_isCompact (A : Matrix ι ι ℂ) (hA : A.PosDef) (K : ℝ) :
    IsCompact (body A K : Set (Matrix ι κ ℂ)) := by
  exact TailGeometry.tail_sublevel_isCompact A hA K

lemma body_volume_ne_top (A : Matrix ι ι ℂ) (hA : A.PosDef) (K : ℝ) :
    μ (body A K : Set (Matrix ι κ ℂ)) ≠ ∞ := by
  exact ne_of_lt (TailGeometry.tail_sublevel_volume_lt_top A hA K)

lemma body_nonempty (A : Matrix ι ι ℂ) (K : ℝ) (hK : 0 ≤ K) :
    (body A K : Set (Matrix ι κ ℂ)).Nonempty := by
  refine ⟨0, ?_⟩
  simpa [body, H, Q, pairing] using hK

/-- The new loss-specific inclusion follows from the proved joint convexity,
before any external volume theorem is invoked. -/
theorem bodies_mix_subset (L : LyapunovPositivityInput ι)
    (A B : Matrix ι ι ℂ) (hA : A.PosDef) (hB : B.PosDef) (K t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    minkowskiMix t (body A K) (body B K) ⊆
      (body (mix t A B) K : Set (Matrix ι κ ℂ)) := by
  rintro Z ⟨X, hX, Y, hY, rfl⟩
  have hc := H_jointConvex L A B X Y hA hB ht ht1
  have hx := mul_le_mul_of_nonneg_left hX (sub_nonneg.mpr ht1)
  have hy := mul_le_mul_of_nonneg_left hY ht
  change H (mix t A B) (mix t X Y) ≤ K
  nlinarith

lemma convex_posDef : Convex ℝ {A : Matrix ι ι ℂ | A.PosDef} := by
  intro A hA B hB a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  have haeq : 1 - b = a := by linarith
  simpa [mix, haeq] using mix_posDef A B hA hB hb hb1

/-- Brunn--Minkowski and the actual sublevel inclusion imply concavity of the
`1/(2*s*r)`-power of the body's Lebesgue volume. -/
theorem volumeRoot_concave (L : LyapunovPositivityInput ι)
    (BM : BrunnMinkowskiInput ι κ) (K : ℝ) (hK : 0 ≤ K) :
    ConcaveOn ℝ {A : Matrix ι ι ℂ | A.PosDef} (volumeRoot (κ := κ) K) := by
  refine ⟨convex_posDef, ?_⟩
  intro A hA B hB a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  have haeq : 1 - b = a := by linarith
  have hm := mix_posDef A B hA hB hb hb1
  have hbm := BM.compact_sets (body A K) (body B K)
    (body_isCompact A hA K) (body_isCompact B hB K)
    (body_nonempty A K hK) (body_nonempty B K hK) b hb hb1
  have hmeasure := measure_mono (μ := μ (ι := ι) (κ := κ))
    (bodies_mix_subset (κ := κ) L A B hA hB K b hb hb1)
  have hr := ENNReal.toReal_mono (body_volume_ne_top (κ := κ) (mix b A B) hm K) hmeasure
  have hpow := Real.rpow_le_rpow ENNReal.toReal_nonneg hr
    (show 0 ≤ exponent (ι := ι) (κ := κ) by unfold exponent; positivity)
  have h := hbm.trans hpow
  simpa only [volumeRoot, haeq, mix, smul_eq_mul] using h

theorem volumeRoot_unitary (UL : UnitaryLebesgueInput ι κ) (K : ℝ) :
    UnitaryInvariantOnPosDef (volumeRoot (ι := ι) (κ := κ) K) := by
  intro U A hU₁ hU₂ hA
  unfold volumeRoot
  rw [body_conjugate U A K hU₁ hU₂ hA, UL.image_measure U hU₁ hU₂]

lemma scalar_posDef [Nonempty ι] (A : Matrix ι ι ℂ) (hA : A.PosDef) :
    ((((Matrix.trace A).re / Fintype.card ι : ℝ) : ℂ) •
      (1 : Matrix ι ι ℂ)).PosDef := by
  obtain ⟨U, a, hU₁, _hU₂, ha, heq⟩ :=
    Normalization.exists_positive_spectral_representation A hA
  have ht : (Matrix.trace A).re = ∑ i, a i := by
    rw [heq, Normalization.trace_conjugate_diagonal U a hU₁]
  have hp : 0 < (Matrix.trace A).re / Fintype.card ι := by
    rw [ht]
    exact div_pos (Normalization.spectrum_trace_pos a ha)
      (Nat.cast_pos.mpr Fintype.card_pos)
  exact Matrix.PosDef.one.smul (RCLike.ofReal_pos.mpr hp)

/-- Lemma 2.3: the uniform tail spectrum maximizes the actual Lebesgue volume
at fixed trace. Cyclic labels cover every positive integer dimension, for
example by using `ZMod s` as the row index type. The only unformalized inputs
are the three explicitly named general external theorems. -/
theorem uniform_tail_maximizes_volume [AddCommGroup ι] [Nonempty ι] [Nonempty κ]
    (L : LyapunovPositivityInput ι) (BM : BrunnMinkowskiInput ι κ)
    (UL : UnitaryLebesgueInput ι κ) (A : Matrix ι ι ℂ) (hA : A.PosDef)
    (K : ℝ) (hK : 0 < K) :
    μ (body A K : Set (Matrix ι κ ℂ)) ≤
      μ (body ((((Matrix.trace A).re / Fintype.card ι : ℝ) : ℂ) • 1) K :
        Set (Matrix ι κ ℂ)) := by
  have h := uniform_matrix_maximal_of_concavity (volumeRoot (κ := κ) K)
    (volumeRoot_concave L BM K hK.le) (volumeRoot_unitary UL K) A hA
  have he : 0 < exponent (ι := ι) (κ := κ) := by
    unfold exponent
    positivity
  unfold volumeRoot at h
  have hh := (Real.rpow_le_rpow_iff ENNReal.toReal_nonneg ENNReal.toReal_nonneg he).mp h
  exact (ENNReal.toReal_le_toReal (body_volume_ne_top A hA K)
    (body_volume_ne_top _ (scalar_posDef A hA) K)).mp hh

end Paper26.TailVolume
