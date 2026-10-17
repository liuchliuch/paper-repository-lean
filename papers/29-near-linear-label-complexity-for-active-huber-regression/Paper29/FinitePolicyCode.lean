import Paper29.QueryModel
import Paper29.AmbientDecoding
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

noncomputable section
open MeasureTheory
namespace Paper29.QueryModel

/-- Only the decoder, next fresh index, or divergence flag is needed for the
lower bound. These values form a finite alphabet even for exact-real outputs. -/
abbrev ActionCode (n r : ℕ) := RateDistortion.Cube r ⊕ (Fin n ⊕ Unit)

def codeDecision {n d r : ℕ} (hrd : r ≤ d) : Decision n d → ActionCode n r
  | .output x => Sum.inl (fun j => HardDistribution.decode (x (Fin.castLE hrd j)))
  | .query i => Sum.inr (Sum.inl i)
  | .diverge => Sum.inr (Sum.inr ())

theorem measurable_decoder {d r : ℕ} (hrd : r ≤ d) :
    Measurable (fun x : Fin d → ℝ => fun j : Fin r => HardDistribution.decode (x (Fin.castLE hrd j))) := by
  apply measurable_pi_lambda
  intro j
  have hh : Measurable (fun x : Fin d → ℝ => if (1/2:ℝ)<x (Fin.castLE hrd j) then true else false) := Measurable.ite (measurableSet_lt (measurable_const : Measurable (fun _ : Fin d → ℝ => (1/2:ℝ))) (measurable_pi_apply (Fin.castLE hrd j)))
    (measurable_const : Measurable (fun _ : Fin d → ℝ => true))
    (measurable_const : Measurable (fun _ : Fin d → ℝ => false))
  convert hh using 1

theorem measurable_codeDecision {n d r : ℕ} (hrd : r ≤ d) :
    Measurable (codeDecision (n:=n) hrd) := by
  let f : ((Fin d → ℝ) ⊕ (Fin n ⊕ Unit)) → ActionCode n r :=
    Sum.elim (fun x => Sum.inl (fun j => HardDistribution.decode (x (Fin.castLE hrd j)))) Sum.inr
  have hf : Measurable f := by
    apply measurable_fun_sum
    · exact measurable_inl.comp (measurable_decoder hrd)
    · exact measurable_inr
  have he : Measurable (Decision.encode : Decision n d → ((Fin d → ℝ) ⊕ (Fin n ⊕ Unit))) :=
    comap_measurable _
  have hcomp : codeDecision (n:=n) hrd = f ∘ Decision.encode := by
    funext a
    cases a <;> rfl
  rw [hcomp]
  exact hf.comp he

/-- All possible finite label histories of length at most n over a given
finite response alphabet. This set is finite independently of the seed. -/
abbrev AlphabetHistory (n : ℕ) (R : Type) := Σ k : Fin (n+1), Fin k.val → (Fin n × R)

def AlphabetHistory.toHistory {n : ℕ} {R : Type} (label : R → ℝ) (h : AlphabetHistory n R) : History n :=
  (List.ofFn h.2).map (fun a => (a.1,label a.2))

/-- Finite table of all possible discrete decisions at every finite alphabet
history. Its entries are measurable seed slices from the original policy. -/
abbrev PolicyCode (n r : ℕ) (R : Type) := AlphabetHistory n R → ActionCode n r

/-- Opaque finite enumeration avoids expanding the decision-table universe.
The mathematical code, decoder and cost remain unchanged. -/
@[irreducible] def policyCodeFintype {n r : ℕ} {R : Type} [Fintype R] :
    Fintype (PolicyCode n r R) := by
  classical
  exact inferInstance

attribute [instance 2000] policyCodeFintype

def compilePolicy {Ω R : Type} {n d r : ℕ} (hrd : r ≤ d) (label : R → ℝ)
    (p : Policy Ω n d) (ω : Ω) : PolicyCode n r R :=
  fun h => codeDecision hrd (p ω (h.toHistory label))

theorem measurable_compilePolicy {Ω R : Type} [MeasurableSpace Ω] [Fintype R]
    {n d r : ℕ} (hrd : r ≤ d) (label : R → ℝ) (p : Policy Ω n d)
    (hp : ∀ h,Measurable (fun ω => p ω h)) : Measurable (compilePolicy hrd label p) := by
  apply measurable_pi_lambda
  intro h
  exact (measurable_codeDecision hrd).comp (hp (h.toHistory label))

end Paper29.QueryModel
