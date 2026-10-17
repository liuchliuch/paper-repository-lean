import ELV.LineParameters
import ELV.CircuitTransforms

/-! Lemma 3.1, from the unknown invariant-plane matrix to an actual fixed
query circuit with an explicit returned catalyst and exact executed cost. -/
noncomputable section
namespace ELV.Line
open ELV.Stabilize ELV.Query
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

def knownLine (s : E) : Submodule ℂ E := Submodule.span ℂ {s}
instance knownLine_complete (s : E) : CompleteSpace (knownLine s) := by
  change CompleteSpace (Submodule.span ℂ {s})
  infer_instance

/-- Both required eigen-relations follow from the actual invariant-plane matrix. -/
lemma plane_eigen (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hne : p ≠ 1/2)
    (s t : E) (R : E ≃ₗᵢ[ℂ] E)
    (hRs : R s = (matrixMean p : ℂ) • s + (matrixOff p : ℂ) • t)
    (hRt : R t = (matrixOff p : ℂ) • s - (matrixMean p : ℂ) • t) :
    R (s + (ratio p : ℂ) • t) = phaseSign p • (s + (ratio p : ℂ) • t) ∧
    R (-(ratio p : ℂ)^2 • s + (ratio p : ℂ) • t) =
      -phaseSign p • (-(ratio p : ℂ)^2 • s + (ratio p : ℂ) • t) := by
  have hh := ratio_spectral p hp0 hp1 hne
  constructor
  · calc
      _ = ((matrixMean p : ℂ) + (ratio p : ℂ)*(matrixOff p : ℂ)) • s +
        ((matrixOff p : ℂ) - (ratio p : ℂ)*(matrixMean p : ℂ)) • t := by
          rw [map_add,map_smul,hRs,hRt]
          module
      _ = _ := by rw [hh.1,hh.2]; module
  · calc
      _ = ((ratio p : ℂ)*((matrixOff p : ℂ)-(ratio p : ℂ)*(matrixMean p : ℂ))) • s +
        (-(ratio p : ℂ)*((matrixMean p : ℂ)+(ratio p : ℂ)*(matrixOff p : ℂ))) • t := by
          rw [map_add,map_smul,map_smul,hRs,hRt]
          module
      _ = _ := by rw [hh.1,hh.2]; module

/-- Full nonendpoint conclusion of Lemma 3.1. The circuit is the explicit
`phaseCircuit (knownLine s)`, which depends on s alone and is fixed before p,t,R. -/
theorem line_purifier (s : E) (hs : ‖s‖ = 1) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) (hne : p ≠ 1/2) (t : E) (ht : ‖t‖ = 1) (hst : inner ℂ s t = 0)
    (R : E ≃ₗᵢ[ℂ] E)
    (hRs : R s = (matrixMean p : ℂ) • s + (matrixOff p : ℂ) • t)
    (hRt : R t = (matrixOff p : ℂ) • s - (matrixMean p : ℂ) • t) :
    ∃ v : LineSpace E,
      inner ℂ (origin s) v = 0 ∧
      Query.run (lpCongr R) (phaseCircuit (knownLine s)) (origin s+v) = phaseSign p • origin s+v ∧
      Query.cost (lpCongr R) (phaseCircuit (knownLine s)) (origin s+v) = 1/|1-2*p| ∧
      ‖v‖ ^ 2 = min p (1-p)/|1-2*p| := by
  let ss : knownLine s := ⟨s,Submodule.mem_span_singleton_self s⟩
  let tt : (knownLine s)ᗮ := ⟨t,Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hst⟩
  have hq := ratio_lt_one p hp0.le hp1.le hne
  let v := catalyst (ratio p) hq s t
  have he := plane_eigen p hp0.le hp1.le hne s t R hRs hRt
  have hcosts := ratio_costs p hp0.le hp1.le hne
  refine ⟨v,catalyst_orthogonal _ _ _ _ hs,?_,?_,?_⟩
  · exact phaseCircuit_exact (ratio p) hq ss tt R (phaseSign p) (phaseSign_sq p) he.1 he.2
  · rw [phaseCircuit_cost (ratio p) hq ss tt hs ht R (phaseSign p) (phaseSign_sq p) he.1]
    exact hcosts.1
  · rw [catalyst_norm_sq _ _ s t hs ht]
    exact hcosts.2

/-- The very same circuit has zero catalyst and cost one at both endpoints. -/
theorem line_purifier_endpoint (s : E) (hs : ‖s‖ = 1) (R : E ≃ₗᵢ[ℂ] E)
    (ζ : ℂ) (hζ : ζ^2 = 1) (hRs : R s = ζ • s) :
    Query.run (lpCongr R) (phaseCircuit (knownLine s)) (origin s) = ζ • origin s ∧
    Query.cost (lpCongr R) (phaseCircuit (knownLine s)) (origin s) = 1 := by
  let ss : knownLine s := ⟨s,Submodule.mem_span_singleton_self s⟩
  exact phaseCircuit_endpoint ss hs R ζ hζ hRs

end ELV.Line
