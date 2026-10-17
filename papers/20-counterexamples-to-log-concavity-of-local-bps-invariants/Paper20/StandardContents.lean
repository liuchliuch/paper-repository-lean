import Paper20.StandardExchange
import Paper20.QuantumEigenvalues

namespace Paper20.YoungShapes
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- The content of the actual cell carrying a given label in a genuine
standard Young filling. -/
def fillingContent {n : ℕ} {μ : Shape n} (t : StandardFilling μ) (i : Fin n) : ℤ :=
  cellContent (t.val i).val

lemma fillingPath_position {n : ℕ} {μ : Shape n} (t : StandardFilling μ) (i : Fin n) :
    position (fillingPath n μ t) i=(t.val i).val :=
  congrArg (fun s : StandardFilling μ => (s.val i).val) (pathFilling_fillingPath n μ t)

lemma fillingPath_content {n : ℕ} {μ : Shape n} (t : StandardFilling μ) (i : Fin n) :
    pathContent (fillingPath n μ t) i=fillingContent t i :=
  congrArg cellContent (fillingPath_position t i)

theorem filling_adjacent_content_ne {n : ℕ} {μ : Shape n} (t : StandardFilling μ)
    (i j : Fin n) (hij : j.val=i.val+1) : fillingContent t i≠fillingContent t j := by
  simpa only [fillingPath_content] using adjacent_content_ne (fillingPath n μ t) i j hij

def Exchangeable {n : ℕ} {μ : Shape n} (t : StandardFilling μ) (i j : Fin n) : Prop :=
  ¬t.val i≤t.val j ∧ ¬t.val j≤t.val i

/-- A forbidden exchange of adjacent labels has the precise content
boundary value 1 or -1 on actual standard fillings. -/
theorem nonexchangeable_content {n : ℕ} {μ : Shape n} (t : StandardFilling μ)
    (i j : Fin n) (hij : j.val=i.val+1) (hn : ¬Exchangeable t i j) :
    fillingContent t j-fillingContent t i=1 ∨ fillingContent t j-fillingContent t i= -1 := by
  classical
  have hrev : ¬t.val j≤t.val i := by
    have he := position_not_reverse (fillingPath n μ t) i j
      (show i < j from by change i.val < j.val; omega)
    simpa only [fillingPath_position] using he
  have hle : t.val i≤t.val j := by
    by_contra h
    exact hn ⟨h,hrev⟩
  have hp : position (fillingPath n μ t) i≤position (fillingPath n μ t) j := by
    rw [fillingPath_position,fillingPath_position]
    exact hle
  simpa only [fillingPath_content] using
    adjacent_comparable_content (fillingPath n μ t) i j hij hp

@[simp] theorem exchange_content {n : ℕ} {μ : Shape n} (t : StandardFilling μ)
    (i j : Fin n) (hij : j.val=i.val+1) (h : Exchangeable t i j) (k : Fin n) :
    fillingContent (exchange t i j hij h) k=fillingContent t (Equiv.swap i j k) := rfl

/-- Quantum eigenvalues attached to actual adjacent standard-tableau
cells are distinct under the actual faithful integer-power parameter. -/
theorem filling_adjacent_eigenvalues_ne {F : Type*} [Field F] (v : F)
    (hv : Function.Injective (fun d : ℤ => v^d))
    {n : ℕ} {μ : Shape n} (t : StandardFilling μ) (i j : Fin n) (hij : j.val=i.val+1) :
    v^(2*fillingContent t i)≠v^(2*fillingContent t j) := by
  intro he
  have hc := hv he
  have hc' : fillingContent t i=fillingContent t j := by omega
  exact filling_adjacent_content_ne t i j hij hc'

end
end Paper20.YoungShapes
