import Paper29.SumMeasurableSingleton
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! General Shannon information and disclosed standard information-theory
inputs. Source: R. M. Gray, Entropy and Information Theory, corrected first
edition (3 June 2023), §§5.3,5.5, in particular the general chain rule (5.28),
Corollary5.5.3 and Lemma5.5.7. https://ee.stanford.edu/~gray/it1_corrected_6-23.pdf
These generic Prop inputs have no inhabitants or axioms in this project. They
contain no adaptive algorithm, stopping, activity probability or query bound. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Classical
namespace Paper29.GeneralInformation

/-- KL divergence of probability laws, using the nonnegative convex density
integrand u log u-u+1 and ∞ for failure of absolute continuity. -/
def klDiv {X : Type} [MeasurableSpace X] (μ ν : Measure X) : ℝ≥0∞ :=
  if μ ≪ ν then ∫⁻ x,ENNReal.ofReal
    ((μ.rnDeriv ν x).toReal*Real.log (μ.rnDeriv ν x).toReal-(μ.rnDeriv ν x).toReal+1) ∂ν else ⊤

def information {Ω S T : Type} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure Ω) (X : Ω → S) (Y : Ω → T) : ℝ≥0∞ :=
  klDiv (μ.map (fun ω => (X ω,Y ω))) ((μ.map X).prod (μ.map Y))

/-- Actual regular conditional laws of U given H: measurable probability
kernel and disintegration on all measurable rectangles. -/
def ConditionalLaw {Ω U H : Type} [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace H]
    (μ : Measure Ω) (Urv : Ω → U) (Hrv : Ω → H) (K : H → Measure U) : Prop :=
  (∀ A,MeasurableSet A → Measurable (fun h => K h A)) ∧
  (∀ h,IsProbabilityMeasure (K h)) ∧
  ∀ A D,MeasurableSet A → MeasurableSet D →
    μ {ω | Urv ω∈A ∧ Hrv ω∈D} = ∫⁻ h in D,K h A ∂μ.map Hrv

def ConditionalChainRule : Prop :=
  ∀ {Ω S B H Z : Type} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace B]
    [MeasurableSpace H] [MeasurableSpace Z] [StandardBorelSpace S] [StandardBorelSpace B]
    [StandardBorelSpace Z] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Bsrc : Ω → B) (Hrv : Ω → H) (Zrv : Ω → Z)
    (K : H → Measure (S × B)) (f : H → (S × B) → Z),
    Measurable X → Measurable Bsrc → Measurable Hrv → Measurable Zrv →
    Measurable (Function.uncurry f) → ConditionalLaw μ (fun ω => (X ω,Bsrc ω)) Hrv K →
    (∀ ω,Zrv ω=f (Hrv ω) (X ω,Bsrc ω)) →
    information μ X (fun ω => (Hrv ω,Zrv ω)) = information μ X Hrv +
      ∫⁻ h,information (K h) Prod.fst (f h) ∂μ.map Hrv

def IndependentInformation : Prop :=
  ∀ {Ω S T : Type} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Y : Ω → T),
    Measurable X → Measurable Y → ProbabilityTheory.IndepFun X Y μ → information μ X Y=0

def ReversibleRelabeling : Prop :=
  ∀ {Ω S T Z : Type} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace Z]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Y : Ω → T) (f : T → Z) (g : Z → T),
    Measurable X → Measurable Y → Measurable f → Measurable g → Function.LeftInverse g f →
    information μ X (fun ω => f (Y ω))=information μ X Y

def ConstantInformation : Prop :=
  ∀ {Ω S Z : Type} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace Z]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (z : Z),
    Measurable X → information μ X (fun _ => z)=0

/-- Quantization characterization of general-alphabet mutual information. -/
def SourceQuantization : Prop :=
  ∀ {Ω S T : Type} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Y : Ω → T),
    Measurable X → Measurable Y → information μ X Y =
      ⨆ (m : ℕ) (f : S → Fin m) (_ : Measurable f),information μ (fun ω => f (X ω)) Y

def SourceDataProcessing : Prop :=
  ∀ {Ω S T Z : Type} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace Z]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → S) (Y : Ω → T) (f : S → Z),
    Measurable X → Measurable Y → Measurable f → information μ (fun ω => f (X ω)) Y ≤ information μ X Y

structure StandardRules : Prop where
  chain : ConditionalChainRule
  independent : IndependentInformation
  relabel : ReversibleRelabeling
  constant : ConstantInformation
  quantization : SourceQuantization
  dataProcessing : SourceDataProcessing

end Paper29.GeneralInformation
