import Paper20.FillingPaths
import Paper20.YoungAdjacentGeometry

namespace Paper20.YoungShapes
open Finset
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- Swapping adjacent labels preserves their order on every ordered pair
except the pair being reversed by that swap. -/
lemma adjacent_swap_lt {n : ℕ} (i j a b : Fin n) (hij : j.val=i.val+1)
    (hab : a < b) (hne : ¬(a=i ∧ b=j)) : Equiv.swap i j a < Equiv.swap i j b := by
  simp only [Equiv.swap_apply_def]
  split_ifs <;> simp only [Fin.lt_def,← Fin.val_inj] at * <;> omega

def exchangeEquiv {n : ℕ} {μ : Shape n} (t : StandardFilling μ) (i j : Fin n) :
    Fin n ≃ Cells μ.val := (Equiv.swap i j).trans t.val

/-- An adjacent exchange gives another genuine standard filling whenever
the two actual cells are incomparable in the cell partial order. -/
theorem exchange_standard {n : ℕ} {μ : Shape n} (t : StandardFilling μ)
    (i j : Fin n) (hij : j.val=i.val+1)
    (hincomp : ¬t.val i≤t.val j ∧ ¬t.val j≤t.val i) :
    StrictMono (exchangeEquiv t i j).symm := by
  intro a b hab
  let u := t.val.symm a
  let v := t.val.symm b
  have huv : u < v := t.property hab
  have hpair : ¬(u=i ∧ v=j) := by
    rintro ⟨hui,hvj⟩
    apply hincomp.1
    have ha : t.val i=a := by rw [← hui]; exact t.val.apply_symm_apply a
    have hb : t.val j=b := by rw [← hvj]; exact t.val.apply_symm_apply b
    rw [ha,hb]
    exact hab.le
  have he := adjacent_swap_lt i j u v hij huv hpair
  simpa only [exchangeEquiv,Equiv.symm_trans_apply,Equiv.symm_swap,Equiv.trans_apply] using he

/-- The actual exchanged standard filling, with validity proved from
incomparability of the actual two cells. -/
def exchange {n : ℕ} {μ : Shape n} (t : StandardFilling μ)
    (i j : Fin n) (hij : j.val=i.val+1)
    (hincomp : ¬t.val i≤t.val j ∧ ¬t.val j≤t.val i) : StandardFilling μ :=
  ⟨exchangeEquiv t i j,exchange_standard t i j hij hincomp⟩

@[simp] theorem exchange_apply {n : ℕ} {μ : Shape n} (t : StandardFilling μ)
    (i j : Fin n) (hij : j.val=i.val+1)
    (hincomp : ¬t.val i≤t.val j ∧ ¬t.val j≤t.val i) (k : Fin n) :
    (exchange t i j hij hincomp).val k=t.val (Equiv.swap i j k) := rfl

theorem exchange_incomparable {n : ℕ} {μ : Shape n} (t : StandardFilling μ)
    (i j : Fin n) (hij : j.val=i.val+1)
    (hincomp : ¬t.val i≤t.val j ∧ ¬t.val j≤t.val i) :
    ¬(exchange t i j hij hincomp).val i≤(exchange t i j hij hincomp).val j ∧
      ¬(exchange t i j hij hincomp).val j≤(exchange t i j hij hincomp).val i := by
  simpa only [exchange_apply,Equiv.swap_apply_left,Equiv.swap_apply_right] using hincomp.symm

/-- The actual valid adjacent exchange is an involution on genuine
standard fillings, including all labels and cells. -/
theorem exchange_exchange {n : ℕ} {μ : Shape n} (t : StandardFilling μ)
    (i j : Fin n) (hij : j.val=i.val+1)
    (hincomp : ¬t.val i≤t.val j ∧ ¬t.val j≤t.val i) :
    exchange (exchange t i j hij hincomp) i j hij (exchange_incomparable t i j hij hincomp)=t := by
  apply Subtype.ext
  apply Equiv.ext
  intro k
  simp only [exchange_apply,Equiv.swap_apply_self]

end
end Paper20.YoungShapes
