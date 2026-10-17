import Paper12.IncidenceSymmetry
import Paper12.PauliChanges

noncomputable section
namespace Paper12
open Matrix Classical
variable {X Q : Type*} [Fintype X] [Fintype Q]

def symbolCircuit (w : Q → PWord X) (s : PSym) : Circuit (X ⊕ Q) :=
  ((uniformChange (X := X) s).onLeft (K := Q)).mul
    ((incidenceCircuit w s).mul ((uniformChange (X := X) s).adjoint.onLeft (K := Q)))

theorem symbolCircuit_size (w : Q → PWord X) (s : PSym) :
    (symbolCircuit w s).size ≤ Fintype.card Q * Fintype.card X + 2 * Fintype.card X := by
  simp only [symbolCircuit, Circuit.mul_size, Circuit.onLeft_size,
    Circuit.adjoint_size, uniformChange, parallelCircuit_size]
  have h := incidenceCircuit_size w s
  omega

theorem symbolCircuit_sector (w : Q → PWord X) (s : PSym) (hs : s ≠ .I) (q : Q) :
    SectorSimulates (oneHot q) (symbolCircuit w s).unitary
      (tensorOp (fun x => if w q x = s then pmat s else 1)) := by
  have hc : SectorSimulates (oneHot q) (symbolCircuit w s).unitary
      ((uniformChange (X := X) s).unitary *
        (tensorOp (fun x => if w q x = s then pmat .X else 1) *
          (uniformChange (X := X) s).unitaryᴴ)) := by
    simp only [symbolCircuit, Circuit.mul_unitary, Circuit.onLeft_unitary,
      Circuit.adjoint_unitary]
    exact (SectorSimulates.extendLeft _ _).mul
      ((incidenceCircuit_sector w s q).mul (SectorSimulates.extendLeft _ _))
  have he : (uniformChange (X := X) s).unitary *
      (tensorOp (fun x => if w q x = s then pmat .X else 1) *
        (uniformChange (X := X) s).unitaryᴴ) =
      tensorOp (fun x => if w q x = s then pmat s else 1) := by
    simp only [uniformChange, parallelCircuit_unitary, tensorOp_adjoint,
      ← tensorOp_mul]
    congr 1
    funext x
    change basisChange s * ((if w q x = s then pmat .X else 1) * (basisChange s)ᴴ) = _
    by_cases hx : w q x = s
    · simp only [if_pos hx]
      rw [← mul_assoc, basisChange_conj_X s hs]
    · simp only [if_neg hx, one_mul]
      exact unitary_mul_adj _ (basisChange_unitary s)
  rw [he] at hc
  exact hc

theorem symbolCircuit_preserved (w : Q → PWord X) (s : PSym)
    (γ : X ≃ X) (τ : Q ≃ Q) (hw : ∀ q x, w (τ q) (γ x) = w q x) :
    (symbolCircuit w s).Preserved (γ.sumCongr τ) :=
  Circuit.preserved_mul
    (Circuit.preserved_onLeft τ (uniformChange_preserved s γ))
    (Circuit.preserved_mul (incidenceCircuit_preserved w s γ τ hw)
      (Circuit.preserved_onLeft τ (Circuit.preserved_adjoint (uniformChange_preserved s γ))))

def pauliSelection (w : Q → PWord X) : Circuit (X ⊕ Q) :=
  (symbolCircuit w .Y).mul ((symbolCircuit w .Z).mul (symbolCircuit w .X))

theorem pauliSelection_size (w : Q → PWord X) :
    (pauliSelection w).size ≤ 3 * Fintype.card Q * Fintype.card X + 6 * Fintype.card X := by
  simp only [pauliSelection, Circuit.mul_size]
  have hX := symbolCircuit_size w .X
  have hY := symbolCircuit_size w .Y
  have hZ := symbolCircuit_size w .Z
  nlinarith [hX, hY, hZ]

theorem pauliSelection_sector (w : Q → PWord X) (q : Q) :
    SectorSimulates (oneHot q) (pauliSelection w).unitary (pop X (w q)) := by
  have hc := (symbolCircuit_sector w .Y (by decide) q).mul
    ((symbolCircuit_sector w .Z (by decide) q).mul (symbolCircuit_sector w .X (by decide) q))
  have he : tensorOp (fun x => if w q x = .Y then pmat .Y else 1) *
      (tensorOp (fun x => if w q x = .Z then pmat .Z else 1) *
        tensorOp (fun x => if w q x = .X then pmat .X else 1)) = pop X (w q) := by
    rw [← tensorOp_mul, ← tensorOp_mul]
    have hh : (fun x => if w q x = .Y then pmat .Y else (1 : QMat)) *
        ((fun x => if w q x = .Z then pmat .Z else (1 : QMat)) *
          (fun x => if w q x = .X then pmat .X else (1 : QMat))) = fun x => pmat (w q x) := by
      funext x
      cases h : w q x <;> simp [h, pmat]
    rw [hh]
    rfl
  rw [he] at hc
  simpa only [pauliSelection, Circuit.mul_unitary] using hc

theorem pauliSelection_preserved (w : Q → PWord X)
    (γ : X ≃ X) (τ : Q ≃ Q) (hw : ∀ q x, w (τ q) (γ x) = w q x) :
    (pauliSelection w).Preserved (γ.sumCongr τ) :=
  Circuit.preserved_mul (symbolCircuit_preserved w .Y γ τ hw)
    (Circuit.preserved_mul (symbolCircuit_preserved w .Z γ τ hw)
      (symbolCircuit_preserved w .X γ τ hw))
end Paper12
