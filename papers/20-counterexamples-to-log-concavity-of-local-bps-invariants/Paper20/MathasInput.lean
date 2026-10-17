import Paper20.SchurNormalization
import Paper20.HilbertHeckeBridge
import Paper20.QuantumEigenvalues
import Mathlib.LinearAlgebra.Trace

/-!
Exact external type-A character input.  These are explicit parameters,
not axioms or admitted production declarations.  The representation is the
actual standard-filling representation constructed from the original
canonical polynomial Hecke algebra.  In particular no BPS, Q-polynomial,
positivity, or partition-trace identity is a field of this interface.

The source and the conversion G_i=v T_i, q=v² are registered in
EXTERNAL_DEPENDENCIES.md.  Schur normalization and every consequence below
are proved internally.
-/
namespace Paper20.ExternalInput
open Polynomial Paper20.YoungShapes Paper20.Seminormal
open Paper20.HeckeTraceAlgebra Paper20.ExternalNormalization
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

section Field
variable {K : Type*} [Field K] [CharZero K]

/-- Mathas's canonical Schur trace decomposition and full-twist content
eigenvalue, in explicitly fixed conventions and on the genuine blocks. -/
structure MathasAt (r : ℕ) (v : K) (hv : v≠0)
    (hp : Function.Injective (fun d : ℤ => v^d)) : Prop where
  schur_trace : ∀ a : algebra r,
    (canonicalTrace r a).eval₂ (Int.castRingHom K) (v-v⁻¹)=
      ∑ p : Part r,
        LinearMap.trace K (StandardFilling (⟨p.diagram,p.diagram_card⟩ : Shape r) → K)
          (FieldHecke.originalRepresentation v hv hp ⟨p.diagram,p.diagram_card⟩ a) /
          schurElement (v^2) p.parts
  full_twist : ∀ p : Part r,
    FieldHecke.originalRepresentation v hv hp (⟨p.diagram,p.diagram_card⟩ : Shape r)
      (omega r)=(v^2)^(contentOf p.parts) • 1

lemma shape_dimension {r : ℕ} (p : Part r) :
    dimension p.diagram=dimOf r p.parts := by
  rw [dimension,p.diagram_card,p.diagram_rowLens]

lemma twist_trace {r k : ℕ} {v : K} {hv : v≠0}
    {hp : Function.Injective (fun d : ℤ => v^d)} (input : MathasAt r v hv hp)
    (p : Part r) :
    LinearMap.trace K (StandardFilling (⟨p.diagram,p.diagram_card⟩ : Shape r) → K)
      (FieldHecke.originalRepresentation v hv hp ⟨p.diagram,p.diagram_card⟩
        (omega r^(k+1)))=
      ((v^2)^(contentOf p.parts))^(k+1)*(dimOf r p.parts:K) := by
  rw [map_pow,input.full_twist,_root_.smul_pow,one_pow,map_smul,LinearMap.trace_one,
    block_dimension,shape_dimension,smul_eq_mul]

/-- The paper's normalized character formula is a proved consequence of
the original q-Schur trace input; its hook/content conversion is internal. -/
theorem partition_trace {r k : ℕ} {v : K} {hv : v≠0}
    {hp : Function.Injective (fun d : ℤ => v^d)} (input : MathasAt r v hv hp)
    (hz : v-v⁻¹≠0) :
    quantumPartitionTrace r k v=
      (canonicalTrace r (omega r^(k+1))).eval₂ (Int.castRingHom K) (v-v⁻¹) := by
  rw [input.schur_trace]
  apply Finset.sum_congr rfl
  intro p _
  rw [twist_trace input,schurElement_quantum p v hv hz]
  unfold quantumTerm
  have he : ((v^2)^(contentOf p.parts))^(k+1)=
      v^(contentOf p.parts)*v^(((2*k+1:ℕ):ℤ)*contentOf p.parts) := by
    rw [← zpow_natCast _ (k+1),← zpow_natCast v 2,← zpow_mul,
      ← zpow_mul,← zpow_add₀ hv]
    congr 1
    push_cast
    ring
  rw [he]
  field_simp [zpow_ne_zero _ hv]
  <;> ring

end Field

/-- The two faithful coordinates required by the independent original
Hilbert extraction and Q-series expansion. -/
structure MathasInputs : Prop where
  at_origin : ∀ r, 2 ≤ r → MathasAt r HilbertAtZero.v HilbertAtZero.v_ne_zero
    hilbert_origin_parameter_injective
  at_unit : ∀ r, 2 ≤ r → MathasAt r QuantumSeriesCoordinates.v
    QuantumSeriesCoordinates.v_ne_zero hilbert_unit_parameter_injective

theorem character_origin (input : MathasInputs) (r k : ℕ) (hr : 2 ≤ r) :
    HilbertHeckeBridge.CharacterFormulaAt r k HilbertAtZero.v := by
  apply partition_trace (input.at_origin r hr)
  intro h
  have he : HilbertAtZero.v^2=1 := by
    have hv := HilbertAtZero.v_ne_zero
    have he := sub_eq_zero.mp h
    calc
      HilbertAtZero.v^2=HilbertAtZero.v*HilbertAtZero.v := pow_two _
      _=HilbertAtZero.v*HilbertAtZero.v⁻¹ := congrArg (HilbertAtZero.v*·) he
      _=1 := mul_inv_cancel₀ hv
  have hn := hilbert_origin_parameter_injective (by simpa only [zpow_ofNat,zpow_zero,pow_zero] using he :
    HilbertAtZero.v^(2:ℤ)=HilbertAtZero.v^(0:ℤ))
  omega

theorem character_unit (input : MathasInputs) (r k : ℕ) (hr : 2 ≤ r) :
    HilbertHeckeBridge.CharacterFormulaAt r k QuantumSeriesCoordinates.v :=
  partition_trace (input.at_unit r hr) QuantumSeriesCoordinates.quantum_difference_ne_zero

end
end Paper20.ExternalInput
