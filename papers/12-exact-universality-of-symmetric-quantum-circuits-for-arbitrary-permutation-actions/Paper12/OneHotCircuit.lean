import Paper12.Rotations
import Paper12.Kickback
import Paper12.OneHotCombinatorics
import Paper12.StateRewire

noncomputable section
namespace Paper12
open Matrix Classical
variable {X : Type*} [Fintype X]

abbrev SelectorWire (α : Coeffs X) := {w : PWord X // w ∈ coeffSupport α}

def selectorD (α : Coeffs X) (q : SelectorWire α) : ℝ := selectorAmp α q.val

def prepLocal (α : Coeffs X) : SelectorWire α ⊕ Fin 2 → QMat :=
  Sum.elim (fun q => productRotation (selectorD α q))
    (fun r => if r = 0 then 1 else realRotation (Real.cos (beta0 α / 2)) (Real.sin (beta0 α / 2)))

theorem prepLocal_unitary (α : Coeffs X) (x : SelectorWire α ⊕ Fin 2) :
    (prepLocal α x)ᴴ * prepLocal α x = 1 := by
  cases x with
  | inl q => exact productRotation_unitary _
  | inr r =>
    fin_cases r
    · simp [prepLocal]
    · change (realRotation (Real.cos (beta0 α / 2)) (Real.sin (beta0 α / 2)))ᴴ *
        realRotation (Real.cos (beta0 α / 2)) (Real.sin (beta0 α / 2)) = 1
      exact realRotation_unitary (by nlinarith [Real.sin_sq_add_cos_sq (beta0 α / 2)])

def prepT (α : Coeffs X) : Circuit (SelectorWire α ⊕ Fin 2) :=
  parallelCircuit (prepLocal α) (prepLocal_unitary α)

def prepWeightTest (α : Coeffs X) : Threshold (SelectorWire α ⊕ Fin 2) where
  head := Sum.inr 0
  controls := Finset.univ.map Function.Embedding.inl
  threshold := 1
  head_not := by simp

def prepD (α : Coeffs X) := equalityCircuit (prepWeightTest α)

def prepFG (α : Coeffs X) : Circuit ((SelectorWire α ⊕ Fin 2) ⊕ Fin 1) :=
  (prepD α).onLeft.mul
    ((equalityCircuit (flagEquality ({Sum.inr 0, Sum.inr 1} : Finset (SelectorWire α ⊕ Fin 2)) 2)).mul
      (prepD α).onLeft)

def prepF0 (α : Coeffs X) : Circuit ((SelectorWire α ⊕ Fin 2) ⊕ Fin 1) :=
  equalityCircuit (flagEquality Finset.univ 0)

def prepIteration (α : Coeffs X) : Circuit ((SelectorWire α ⊕ Fin 2) ⊕ Fin 1) :=
  (prepT α).onLeft.mul ((prepF0 α).mul ((prepT α).onLeft.adjoint.mul (prepFG α)))

def prepRaw (α : Coeffs X) : Circuit ((SelectorWire α ⊕ Fin 2) ⊕ Fin 1) :=
  (singleCircuit (.one ⟨Sum.inr 1, pmat .X, pmat_unitary .X⟩)).onLeft.mul
    ((singleCircuit (ryGate (0 : Fin 1) (Real.pi / 2))).onRight.mul
      (((prepIteration α).power 2).mul
        ((prepT α).onLeft.mul (singleCircuit (ryGate (0 : Fin 1) (-Real.pi / 2))).onRight)))

def prepWireEquiv (α : Coeffs X) :
    ((SelectorWire α ⊕ Fin 2) ⊕ Fin 1) ≃ (SelectorWire α ⊕ Fin 3) :=
  (Equiv.sumAssoc (SelectorWire α) (Fin 2) (Fin 1)).trans
    ((Equiv.refl (SelectorWire α)).sumCongr (finSumFinEquiv))

/-- The literal five-product-layer, two-reflection-step preparation circuit. -/
def oneHotCircuit (α : Coeffs X) : Circuit (SelectorWire α ⊕ Fin 3) :=
  (prepRaw α).rewire (prepWireEquiv α)

theorem selectorWire_card (α : Coeffs X) : Fintype.card (SelectorWire α) = coeffCard α := by
  exact Fintype.card_coe (coeffSupport α)

theorem oneHotCircuit_size (α : Coeffs X) :
    (oneHotCircuit α).size ≤ 40 * (coeffCard α + 1) := by
  simp only [oneHotCircuit, Circuit.rewire_size, prepRaw, prepIteration, prepFG, prepF0,
    prepD, prepT, Circuit.mul_size, Circuit.adjoint_size, Circuit.power_size,
    Circuit.onLeft_size, Circuit.onRight_size, singleCircuit_size,
    equalityCircuit_size, parallelCircuit_size, Fintype.card_sum, Fintype.card_fin,
    selectorWire_card]
  omega

theorem selectorD_sq (α : Coeffs X) (hmass : 0 < coeffMass α) :
    (∑ q : SelectorWire α, (selectorD α q) ^ 2) = 1 := by
  rw [show (∑ q : SelectorWire α, (selectorD α q) ^ 2) =
    ∑ w ∈ coeffSupport α, (selectorAmp α w) ^ 2 from Finset.sum_coe_sort (coeffSupport α) (fun w => (selectorAmp α w) ^ 2)]
  exact selector_amp_sq α hmass

theorem selector_productC (α : Coeffs X) (hmass : 0 < coeffMass α) :
    productC (selectorD α) = Real.sqrt (prepP0 α) := by
  have hs : productC (selectorD α) ^ 2 = prepP0 α := by
    rw [productC_sq]
    congr 1
    exact Finset.prod_coe_sort (coeffSupport α) (fun w => 1 + (selectorAmp α w) ^ 2)
  rw [← hs, Real.sqrt_sq (productC_pos _).le]
end Paper12
