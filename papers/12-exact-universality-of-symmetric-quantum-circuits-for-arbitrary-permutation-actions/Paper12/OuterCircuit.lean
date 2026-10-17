import Paper12.FixedRotations
import Paper12.Amplify

noncomputable section
namespace Paper12
open Matrix Classical
variable {X W : Type*} [Fintype X] [Fintype W]

def outerT (A : Circuit (X ⊕ W)) (p : ℝ) : Circuit (X ⊕ (W ⊕ Fin 1)) :=
  (A.onLeft.mul ((singleCircuit (ryGate (0 : Fin 1) (ampZeta p))).onRight (J := X ⊕ W))).rewire
    (Equiv.sumAssoc X W (Fin 1))

def workspaceControls (X W : Type*) [Fintype W] : Finset (X ⊕ W) :=
  Finset.univ.map Function.Embedding.inr

def outerF (p : ℝ) : Circuit ((X ⊕ (W ⊕ Fin 1)) ⊕ Fin 1) :=
  equalityCircuit (flagEquality (workspaceControls X (W ⊕ Fin 1)) 0)

def outerIteration (A : Circuit (X ⊕ W)) (p : ℝ) : Circuit ((X ⊕ (W ⊕ Fin 1)) ⊕ Fin 1) :=
  (outerT A p).onLeft.mul ((outerF (X := X) (W := W) p).mul
    ((outerT A p).onLeft.adjoint.mul (outerF (X := X) (W := W) p)))

theorem sign_phase_unitary (k : ℕ) : star ((-1 : ℂ) ^ k) * (-1 : ℂ) ^ k = 1 := by
  change starRingEnd ℂ ((-1 : ℂ) ^ k) * (-1 : ℂ) ^ k = 1
  rw [map_pow]
  simp only [map_neg, map_one]
  rw [← mul_pow]
  norm_num

def outerRaw (A : Circuit (X ⊕ W)) (p : ℝ) : Circuit ((X ⊕ (W ⊕ Fin 1)) ⊕ Fin 1) :=
  (singleCircuit (phaseGate (Sum.inl (Sum.inr (Sum.inr (0 : Fin 1))))
    ((-1 : ℂ) ^ ampK p) (sign_phase_unitary (ampK p)))).mul
    (((singleCircuit (ryGate (0 : Fin 1) (Real.pi / 2))).onRight (J := X ⊕ (W ⊕ Fin 1))).mul
      (((outerIteration A p).power (ampK p)).mul
        ((outerT A p).onLeft.mul
          ((singleCircuit (ryGate (0 : Fin 1) (-Real.pi / 2))).onRight (J := X ⊕ (W ⊕ Fin 1))))))

def outerWireEquiv : ((X ⊕ (W ⊕ Fin 1)) ⊕ Fin 1) ≃ (X ⊕ (W ⊕ Fin 2)) :=
  (Equiv.sumAssoc X (W ⊕ Fin 1) (Fin 1)).trans
    (((Equiv.refl X).sumCongr (Equiv.sumAssoc W (Fin 1) (Fin 1))).trans
      ((Equiv.refl X).sumCongr ((Equiv.refl W).sumCongr finSumFinEquiv)))

/-- The complete literal oblivious-amplification circuit, including phase correction. -/
def obliviousCircuit (A : Circuit (X ⊕ W)) (p : ℝ) : Circuit (X ⊕ (W ⊕ Fin 2)) :=
  (outerRaw A p).rewire outerWireEquiv

theorem outerT_size (A : Circuit (X ⊕ W)) (p : ℝ) : (outerT A p).size = A.size + 1 := by
  simp [outerT]

theorem obliviousCircuit_size (A : Circuit (X ⊕ W)) (p : ℝ) :
    (obliviousCircuit A p).size ≤ 32 * (A.size + 1) * (ampK p + 1) := by
  simp only [obliviousCircuit, Circuit.rewire_size, outerRaw, outerIteration, outerF,
    Circuit.mul_size, Circuit.adjoint_size, Circuit.power_size, Circuit.onLeft_size,
    Circuit.onRight_size, singleCircuit_size, equalityCircuit_size, outerT_size]
  nlinarith [Nat.zero_le (A.size * ampK p)]
end Paper12
