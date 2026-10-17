import Paper35.GaussianWinner
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Explicit classical curve-calculus inputs, independent of random networks

The external propositions here concern arbitrary AC curves and finite scalar
families. They contain no network, Gaussian law, selected-weight moment, A, D,
Q, or expected-length estimate. Tonelli and the finite maximizing selector are
proved separately below. Specializations to the paper's source maps are proved
in LayerMoment and GaussianLayer.
-/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
namespace Paper35.CurveCalculus
open Paper35.GaussianWinner
abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)

def finiteSup {K : ℕ} (hK : 0 < K) (x : Fin K → ℝ) : ℝ :=
  Finset.univ.sup' ⟨⟨0,hK⟩,Finset.mem_univ _⟩ x

def winner {K : ℕ} (hK : 0 < K) (x : Fin K → ℝ) : Fin K :=
  Fin.cast (Nat.sub_add_cancel hK) (finiteWinner (K-1)
    (fun j => x (Fin.cast (Nat.sub_add_cancel hK) j)))

lemma measurable_winner {K : ℕ} (hK : 0 < K) : Measurable (winner hK) := by
  unfold winner
  exact (measurable_of_countable (Fin.cast (Nat.sub_add_cancel hK))).comp
    ((measurable_finiteWinner (K-1)).comp
      (measurable_pi_lambda _ (fun j => measurable_pi_apply _)))

lemma winner_is_max {K : ℕ} (hK : 0 < K) (x : Fin K → ℝ) (j : Fin K) :
    x j ≤ x (winner hK x) := by
  unfold winner
  rw [finiteWinner_value (K-1) (fun i => x (Fin.cast (Nat.sub_add_cancel hK) i))]
  simpa only [Fin.cast_cast, Fin.cast_refl] using
    le_finiteMax (K-1) (fun i => x (Fin.cast (Nat.sub_add_cancel hK) i))
      (Fin.cast (Nat.sub_add_cancel hK).symm j)

lemma winner_value {K : ℕ} (hK : 0 < K) (x : Fin K → ℝ) :
    x (winner hK x) = finiteSup hK x := by
  apply le_antisymm
  · exact Finset.le_sup' x (Finset.mem_univ _)
  · exact Finset.sup'_le _ _ (fun j _ => winner_is_max hK x j)

lemma finiteMax_eq_finiteSup (n : ℕ) (x : Fin (n+1) → ℝ) :
    finiteMax n x = finiteSup (Nat.succ_pos n) x := by
  apply le_antisymm
  · rw [← finiteWinner_value n x]
    exact Finset.le_sup' x (Finset.mem_univ _)
  · exact Finset.sup'_le _ _ (fun j _ => le_finiteMax n x j)

lemma measurable_finite_selection {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (d : ℕ) (f : ι → Ω → Space d) (hf : ∀ i, Measurable (f i))
    (J : Ω → ι) (hJ : Measurable J) : Measurable (fun ω => f (J ω) ω) := by
  classical
  have H := Finset.measurable_sum Finset.univ (fun i _ =>
    (hf i).indicator (hJ (measurableSet_singleton i)))
  convert H using 1
  ext ω
  simp only [Set.indicator_apply, Set.mem_preimage, Set.mem_singleton_iff]
  simp

/-- Finite scalar maxima preserve a common Lipschitz constant. -/
lemma lipschitz_finiteSup {X : Type*} [PseudoMetricSpace X] {K : ℕ}
    (hK : 0 < K) (C : ℝ≥0) (f : Fin K → X → ℝ)
    (hf : ∀ j, LipschitzWith C (f j)) :
    LipschitzWith C (fun x => finiteSup hK (fun j => f j x)) := by
  have H := Finset.sup'_induction
    (s := (Finset.univ : Finset (Fin K))) ⟨⟨0,hK⟩,Finset.mem_univ _⟩ f
    (p := fun g : X → ℝ => LipschitzWith C g)
    (fun a ha b hb => by simpa only [max_self] using ha.max hb)
    (fun j _ => hf j)
  convert H using 1
  funext x
  exact (Finset.sup'_apply _ f x).symm

/-- An actual finite affine-max vector map is globally Lipschitz. The proof
uses the candidate linear-functional norms and finite supremum calculus. -/
theorem affineMax_lipschitz (d q : ℕ) (K : Fin q → ℕ) (hK : ∀ r, 0 < K r)
    (W : (r : Fin q) → Fin (K r) → Space d) (b : (r : Fin q) → Fin (K r) → ℝ) :
    ∃ C : ℝ≥0, LipschitzWith C (fun x : Space d =>
      WithLp.toLp 2 (fun r => finiteSup (hK r) (fun j => inner ℝ (W r j) x+b r j))) := by
  let C : ℝ≥0 := ∑ r, ∑ j, ‖innerSL ℝ (W r j)‖₊
  have hC (r : Fin q) (j : Fin (K r)) : ‖innerSL ℝ (W r j)‖₊ ≤ C :=
    (Finset.single_le_sum (fun k _ => zero_le ‖innerSL ℝ (W r k)‖₊) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => zero_le (∑ j, ‖innerSL ℝ (W k j)‖₊)) (Finset.mem_univ r))
  have hj (r : Fin q) (j : Fin (K r)) :
      LipschitzWith C (fun x : Space d => inner ℝ (W r j) x + b r j) := by
    have H := ((innerSL ℝ (W r j)).lipschitz.add (LipschitzWith.const (b r j)))
    simp only [add_zero] at H
    exact H.weaken (hC r j)
  have hr (r : Fin q) := lipschitz_finiteSup (hK r) C _ (hj r)
  have hp : LipschitzWith C (fun x : Space d => fun r =>
      finiteSup (hK r) (fun j => inner ℝ (W r j) x+b r j)) := by
    intro x y
    exact edist_pi_le_iff.mpr (fun r => hr r x y)
  exact ⟨_, (PiLp.lipschitzWith_toLp 2 (fun _ : Fin q => ℝ)).comp hp⟩

/-- Classical arclength representation of an arbitrary continuous rectifiable
curve. The same representation preserves variation after every Lipschitz map.
The factorization is Burago--Burago--Ivanov, A Course in Metric Geometry
(2001), Proposition 2.5.9, p.46; Euclidean unit velocity follows from the
AC metric-speed theorem (AGS, Gradient Flows, 2nd ed., Theorem 1.1.2). The velocity is modified on a null
set to a fixed unit vector; this explains the dimension >0 hypothesis. -/
def ArclengthRepresentationInput : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (η : ℝ → Space d) (L : ℝ),
    ContinuousOn η (Icc 0 L) → eVariationOn η (Icc 0 L) ≠ ∞ →
    ∃ (x u : ℝ → Space d),
      LipschitzWith 1 x ∧ Measurable u ∧ (∀ s, ‖u s‖=1) ∧
      (∀ᵐ s ∂volume.restrict (Icc 0 (eVariationOn η (Icc 0 L)).toReal), HasDerivAt x (u s) s) ∧
      ∀ (q : ℕ) (F : Space d → Space q) (C : ℝ≥0), LipschitzWith C F →
        eVariationOn (F ∘ η) (Icc 0 L) =
          eVariationOn (F ∘ x) (Icc 0 (eVariationOn η (Icc 0 L)).toReal)

/-- Original monotone arclength factorization, including its time-change map.
The image-surjectivity and factorization are exactly the arclength
parametrization statement (Burago--Burago--Ivanov, Proposition 2.5.9, p.46).
Its unit-velocity clause uses the AC metric-speed theorem, with a null-set
modification; it contains no switch-count or post-composition variation estimate. -/
def ArclengthFactorizationInput : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (η : ℝ → Space d) (L : ℝ), 0 ≤ L →
    ContinuousOn η (Icc 0 L) → eVariationOn η (Icc 0 L) ≠ ∞ →
    ∃ (x u : ℝ → Space d) (σ : ℝ → ℝ),
      LipschitzWith 1 x ∧ Measurable u ∧ (∀ s, ‖u s‖=1) ∧
      (∀ᵐ s ∂volume.restrict (Icc 0 (eVariationOn η (Icc 0 L)).toReal), HasDerivAt x (u s) s) ∧
      ContinuousOn σ (Icc 0 L) ∧ MonotoneOn σ (Icc 0 L) ∧
      σ '' Icc 0 L = Icc 0 (eVariationOn η (Icc 0 L)).toReal ∧
      EqOn η (x ∘ σ) (Icc 0 L)

/-- Post-composition variation preservation is proved from the monotone
factorization, using mathlib's variation theorem for arbitrary monotone maps. -/
theorem arclengthRepresentation_of_factorization (hf : ArclengthFactorizationInput) :
    ArclengthRepresentationInput := by
  intro d hd η L hcont hfinite
  by_cases hL : 0 ≤ L
  · obtain ⟨x,u,σ,hx,hmu,hu,hderiv,hσcont,hσmono,himage,hfactor⟩ := hf d hd η L hL hcont hfinite
    refine ⟨x,u,hx,hmu,hu,hderiv,?_⟩
    intro q F C hF
    calc
      eVariationOn (F ∘ η) (Icc 0 L) = eVariationOn ((F ∘ x) ∘ σ) (Icc 0 L) :=
        eVariationOn.eq_of_eqOn (fun t ht => congrArg F (hfactor ht))
      _ = _ := by rw [eVariationOn.comp_eq_of_monotoneOn _ _ hσmono,himage]
  · have hempty : Icc 0 L = ∅ := Icc_eq_empty hL
    let v : Space d := EuclideanSpace.single ⟨0,hd⟩ 1
    refine ⟨fun _ => 0,fun _ => v,(LipschitzWith.const 0).weaken (by norm_num),measurable_const,?_,?_,?_⟩
    · intro s; simp [v,EuclideanSpace.norm_single]
    · simp [hempty,Real.volume_Icc]
    · intro q F C hF
      simp [hempty,eVariationOn.subsingleton _ (Set.subsingleton_singleton)]

/-- Standard AC differentiability and stability under continuous linear
functionals followed by a constant translation. This is the ordinary Banach
space AC chain rule in finite dimension, with its original arbitrary-curve
quantifiers; no finite maximum appears. -/
def LinearACCalculusInput : Prop :=
  ∀ (d : ℕ) (T : ℝ) (η : ℝ → Space d),
    AbsolutelyContinuousOnInterval η 0 T →
      (∀ᵐ s ∂volume.restrict (Icc 0 T), HasDerivAt η (deriv η s) s) ∧
      (∀ (ℓ : Space d →L[ℝ] ℝ) (b : ℝ),
        AbsolutelyContinuousOnInterval (fun s => ℓ (η s)+b) 0 T)

/-- Finite-maximum chain rule and the variation formula for arbitrary scalar
AC functions. An arbitrary active selector has the correct derivative almost
everywhere, since derivatives agree almost everywhere on equality sets.
This is the classical AC finite-max/variation corollary, combining stability
under finite Lipschitz maxima, equality-set derivative agreement, and the AC
metric-speed/variation theorem (AGS Theorem 1.1.2). Rockafellar--Wets,
Variational Analysis, Theorem 10.31 supplies related smooth finite-max
calculus; it is not cited as a verbatim arbitrary-AC theorem. This deterministic
statement has no probability measure or source model. -/
def FiniteMaxACCalculusInput : Prop :=
  ∀ (q : ℕ) (K : Fin q → ℕ) (hK : ∀ r, 0 < K r) (T : ℝ)
    (f a : (r : Fin q) → Fin (K r) → ℝ → ℝ)
    (J : (s : ℝ) → (r : Fin q) → Fin (K r)),
    (∀ r j, AbsolutelyContinuousOnInterval (f r j) 0 T) →
    (∀ r j, ∀ᵐ s ∂volume.restrict (Icc 0 T), HasDerivAt (f r j) (a r j s) s) →
    (∀ s r j, f r j s ≤ f r (J s r) s) →
    eVariationOn (fun s => WithLp.toLp 2 (fun r => finiteSup (hK r) (fun j => f r j s)))
      (Icc 0 T) =
      ∫⁻ s in Icc 0 T, ENNReal.ofReal ‖WithLp.toLp 2 (fun r => a r (J s r) s)‖

/-- Tonelli and conversion of a nonnegative Bochner first moment, proved for
arbitrary random vector fields. -/
theorem expected_variation_from_derivative {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (q : ℕ) (T : ℝ)
    (f : Ω → ℝ → Space q) (B : ℝ → Ω → Space q)
    (hB : AEMeasurable (fun p : ℝ × Ω => B p.1 p.2)
      ((volume.restrict (Icc 0 T)).prod μ))
    (hBi : ∀ s, Integrable (fun ω => ‖B s ω‖) μ)
    (hvar : ∀ ω, eVariationOn (f ω) (Icc 0 T) =
      ∫⁻ s in Icc 0 T, ENNReal.ofReal ‖B s ω‖) :
    (∫⁻ ω, eVariationOn (f ω) (Icc 0 T) ∂μ) =
      ∫⁻ s in Icc 0 T, ENNReal.ofReal (∫ ω, ‖B s ω‖ ∂μ) := by
  simp_rw [hvar]
  rw [lintegral_lintegral_swap hB.prod_swap.norm.ennreal_ofReal]
  apply lintegral_congr
  intro s
  exact (ofReal_integral_eq_lintegral_ofReal (hBi s) (Filter.Eventually.of_forall (fun ω => norm_nonneg _))).symm

end Paper35.CurveCalculus
