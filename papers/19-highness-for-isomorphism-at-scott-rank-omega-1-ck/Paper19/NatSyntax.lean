import Paper19.NatModel
import Paper19.Infinitary

namespace Paper19.Infinitary
open Paper19

def Term.evalNat (M : NatModel) (e : ℕ → ℕ) : Term → ℕ
  | .var i => e i
  | .zero => M.zero
  | .named => M.named
  | .succ t => M.succ (t.evalNat M e)
  | .proj t => M.proj (t.evalNat M e)
  | .level t => M.level (t.evalNat M e)

def Formula.RealizeNat (M : NatModel) (e : ℕ → ℕ) : Formula → Prop
  | .top => True
  | .eq a b => a.evalNat M e = b.evalNat M e
  | .index a => M.index (a.evalNat M e) = true
  | .rel a b c => M.rel (a.evalNat M e,b.evalNat M e,c.evalNat M e) = true
  | .neg a => ¬a.RealizeNat M e
  | .and a b => a.RealizeNat M e ∧ b.RealizeNat M e
  | .all a => ∀ i, (a i).RealizeNat M e
  | .ex v a => ∃ y, a.RealizeNat M (Function.update e v y)

theorem term_nat_transfer (T : Tree) (tag : Bool) (e : ℕ → Carrier T) (t : Term) :
    t.evalNat (natModel T tag) (fun i => carrierEquivNat T (e i)) =
      carrierEquivNat T (t.eval tag e) := by
  induction t <;> simp_all [Term.evalNat,Term.eval]

theorem update_equiv {α β : Type} (E : α ≃ β) (e : ℕ → α) (v : ℕ) (x : α) :
    Function.update (fun i => E (e i)) v (E x) = fun i => E (Function.update e v x i) := by
  funext i
  by_cases hi : i=v <;> simp [Function.update_apply,hi]

theorem formula_nat_transfer (T : Tree) (tag : Bool) (e : ℕ → Carrier T) (φ : Formula) :
    φ.RealizeNat (natModel T tag) (fun i => carrierEquivNat T (e i)) ↔ φ.Realize tag e := by
  induction φ generalizing e with
  | top => rfl
  | eq a b =>
    simp only [Formula.RealizeNat,Formula.Realize,term_nat_transfer]
    exact (carrierEquivNat T).injective.eq_iff
  | index a =>
    simp only [Formula.RealizeNat,Formula.Realize,term_nat_transfer,natModel_index]
  | rel a b c =>
    simp only [Formula.RealizeNat,Formula.Realize,term_nat_transfer,natModel_rel]
  | neg a ih => exact not_congr (ih e)
  | and a b iha ihb => exact and_congr (iha e) (ihb e)
  | all a ih => exact forall_congr' (fun i => ih i e)
  | ex v a ih =>
    constructor
    · rintro ⟨y,hy⟩
      let x := (carrierEquivNat T).symm y
      have hx : carrierEquivNat T x = y := (carrierEquivNat T).apply_symm_apply y
      have hu := update_equiv (carrierEquivNat T) e v x
      rw [hx] at hu
      rw [hu] at hy
      exact ⟨x,(ih (Function.update e v x)).mp hy⟩
    · rintro ⟨x,hx⟩
      refine ⟨carrierEquivNat T x,?_⟩
      rw [update_equiv]
      exact (ih (Function.update e v x)).mpr hx

end Paper19.Infinitary
