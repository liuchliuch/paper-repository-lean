import CounterFreeHDA.Realization

namespace CounterFreeHDA.FirstOrder
universe u

/-- The event signature used by the paper: equality, precedence, event order,
labels, and the two distinguished interfaces, with genuine quantification. -/
inductive Formula (Lab : Type u) : ℕ → Type u where
  | bot {n} : Formula Lab n
  | equal {n} : Fin n → Fin n → Formula Lab n
  | prec {n} : Fin n → Fin n → Formula Lab n
  | eord {n} : Fin n → Fin n → Formula Lab n
  | label {n} : Lab → Fin n → Formula Lab n
  | source {n} : Fin n → Formula Lab n
  | target {n} : Fin n → Formula Lab n
  | neg {n} : Formula Lab n → Formula Lab n
  | conj {n} : Formula Lab n → Formula Lab n → Formula Lab n
  | existsE {n} : Formula Lab (n+1) → Formula Lab n

namespace Formula
variable {Lab : Type u}

def Holds (P : PomsetData Lab) : {n : ℕ} → Formula Lab n → (Fin n → Fin P.n) → Prop
  | _,.bot,_ => False
  | _,.equal i j,ρ => ρ i = ρ j
  | _,.prec i j,ρ => P.prec (ρ i) (ρ j)
  | _,.eord i j,ρ => P.eord (ρ i) (ρ j)
  | _,.label a i,ρ => P.lab (ρ i) = a
  | _,.source i,ρ => P.inSrc (ρ i)
  | _,.target i,ρ => P.inTgt (ρ i)
  | _,.neg φ,ρ => ¬ φ.Holds P ρ
  | _,.conj φ ψ,ρ => φ.Holds P ρ ∧ ψ.Holds P ρ
  | _,.existsE φ,ρ => ∃ e : Fin P.n, φ.Holds P (Fin.cases e ρ)

def Models (φ : Formula Lab 0) (P : PomsetData Lab) : Prop := φ.Holds P Fin.elim0

/-- Formula semantics retains the complete actual event and interface data. -/
theorem holds_iso {P Q : PomsetData Lab} (e : PomsetIso P Q) {n : ℕ} (φ : Formula Lab n)
    (ρ : Fin n → Fin P.n) : φ.Holds Q (e.toEquiv ∘ ρ) ↔ φ.Holds P ρ := by
  induction φ with
  | bot => exact Iff.rfl
  | equal i j => exact e.toEquiv.injective.eq_iff
  | prec i j => exact e.prec_iff _ _
  | eord i j => exact e.eord_iff _ _
  | label a i => exact (congrArg (fun a => a = _) (e.lab_eq _)).to_iff
  | source i => exact e.inSrc_image_iff _
  | target i => exact e.inTgt_image_iff _
  | neg φ ih => exact not_congr (ih ρ)
  | conj φ ψ ihφ ihψ => exact and_congr (ihφ ρ) (ihψ ρ)
  | existsE φ ih =>
    constructor
    · rintro ⟨q,hq⟩
      obtain ⟨p,rfl⟩ := e.toEquiv.surjective q
      refine ⟨p,(ih (Fin.cases p ρ)).mp ?_⟩
      have he : e.toEquiv ∘ Fin.cases p ρ = Fin.cases (e.toEquiv p) (e.toEquiv ∘ ρ) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      simpa only [he] using hq
    · rintro ⟨p,hp⟩
      refine ⟨e.toEquiv p,?_⟩
      have he : e.toEquiv ∘ Fin.cases p ρ = Fin.cases (e.toEquiv p) (e.toEquiv ∘ ρ) := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i <;> rfl
      simpa only [he] using (ih (Fin.cases p ρ)).mpr hp

end Formula

/-- Definability relative to the actual bounded-width interval-pomset source. -/
def Definable {Lab : Type u} (k : ℕ) (L : Set (IntervalPom Lab)) : Prop :=
  ∃ φ : Formula Lab 0, ∀ P : IntervalPom Lab, P.val.WidthLE k → (P ∈ L ↔ φ.Models P.val)

end CounterFreeHDA.FirstOrder
