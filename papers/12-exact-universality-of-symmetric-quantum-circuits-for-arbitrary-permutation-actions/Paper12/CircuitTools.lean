import Paper12.Necessity

/-! Elementary circuit constructors and their exact semantics. -/
noncomputable section
namespace Paper12
open Matrix Complex Classical

@[ext] theorem Layer.ext {J : Type*} [Fintype J] {L K : Layer J}
    (h : L.gates = K.gates) : L = K := by
  cases L; cases K; simp_all

def singletonLayer {J : Type*} [Fintype J] (g : Gate J) : Layer J where
  gates := {g}
  commute := by
    intro a ha b hb
    simp only [Finset.mem_singleton] at ha hb
    subst a; subst b; rfl

@[simp] theorem singletonLayer_unitary {J : Type*} [Fintype J] (g : Gate J) :
    (singletonLayer g).unitary = g.unitary := by
  unfold Layer.unitary
  rw [dif_pos (pairwiseCommute_to_set _ (singletonLayer g).commute)]
  exact Finset.noncommProd_singleton _ _

def singleCircuit {J : Type*} [Fintype J] (g : Gate J) : Circuit J :=
  ⟨[singletonLayer g]⟩

@[simp] theorem singleCircuit_unitary {J : Type*} [Fintype J] (g : Gate J) :
    (singleCircuit g).unitary = g.unitary := by
  simp [Circuit.unitary, singleCircuit]

@[simp] theorem singleCircuit_size {J : Type*} [Fintype J] (g : Gate J) :
    (singleCircuit g).size = 1 := by simp [Circuit.size, singleCircuit, singletonLayer]

/-- A scalar one-qubit unitary on any chosen wire supplies the exact global phase. -/
def phaseGate {J : Type*} (head : J) (z : ℂ) (hz : star z * z = 1) : Gate J :=
  .one ⟨head, z • (1 : Matrix (Fin 2) (Fin 2) ℂ), by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, hz, one_smul]⟩

@[simp] theorem phaseGate_unitary {J : Type*} (head : J) (z : ℂ)
    (hz : star z * z = 1) : (phaseGate head z hz).unitary = z • (1 : Op J) := by
  ext i j
  change (if ∀ w, w ≠ head → i w = j w then
    (z • (1 : Matrix (Fin 2) (Fin 2) ℂ)) (i head) (j head) else 0) = _
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  by_cases hij : i = j
  · subst j; simp
  · rw [if_neg hij, mul_zero]
    split_ifs with hoff hhead
    · exfalso
      apply hij
      funext w
      by_cases hw : w = head
      · simpa [hw] using hhead
      · exact hoff w hw
    · simp
    · rfl

@[simp] theorem applyOp_one {X : Type*} [Fintype X] (ψ : Vec X) :
    applyOp (1 : Op X) ψ = ψ := by
  funext b
  simp [applyOp, Matrix.one_apply]

theorem applyOp_smul {X : Type*} [Fintype X] (z : ℂ) (U : Op X) (ψ : Vec X) :
    applyOp (z • U) ψ = z • applyOp U ψ := by
  funext b
  simp only [applyOp, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply]
  simp_rw [mul_assoc]
  exact (Finset.mul_sum _ _ _).symm

theorem embedZero_smul {X W : Type*} (z : ℂ) (ψ : Vec X) :
    embedZero (W := W) (z • ψ) = z • embedZero ψ := by
  funext b
  simp only [embedZero, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

def phaseCircuit {X : Type*} [Fintype X] (z : ℂ) (hz : star z * z = 1) :
    Circuit (X ⊕ Fin 1) := singleCircuit (phaseGate (Sum.inr 0) z hz)

theorem phaseCircuit_clean {X : Type*} [Fintype X] (z : ℂ) (hz : star z * z = 1) :
    CleanImplements (phaseCircuit (X := X) z hz) (z • 1) := by
  intro ψ
  simp [phaseCircuit, applyOp_smul, embedZero_smul]

theorem phaseCircuit_symmetric {X : Type*} [Fintype X] (Γ : Subgroup (X ≃ X))
    (z : ℂ) (hz : star z * z = 1) :
    Nonempty (Symmetric Γ (phaseCircuit z hz)) := by
  refine ⟨⟨fun γ => liftFixW γ.val, (fun _ _ => rfl), ?_⟩⟩
  intro γ L hL
  simp only [phaseCircuit, singleCircuit, List.mem_singleton] at hL
  subst L
  apply Layer.ext
  simp only [Layer.map, singletonLayer, relabelGates, Finset.map_singleton]
  rfl

end Paper12
