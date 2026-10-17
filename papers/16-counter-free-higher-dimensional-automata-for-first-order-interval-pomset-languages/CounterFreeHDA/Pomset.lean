/-
Copyright (c) 2026. Counter-Free Higher-Dimensional Automata formalisation.
Interval pomsets with interfaces: data, well-formedness, subsumption, gluing,
powers and corners.  Event sets are `Fin n`.
-/
import CounterFreeHDA.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic

/-!
# Interval pomsets

An interval pomset `P : U → V` consists of a finite event set `Fin n`, a strict
interval precedence order `prec`, an event order `eord` recorded on
precedence-incomparable pairs, a labelling `lab : Fin n → Lab`, and ordered
source and target interfaces `src : Fin srcLen → Fin n`, `tgt : Fin tgtLen → Fin n`.

We separate *data* from *well-formedness* so that constructions are total on data
and theorems assume only `IsIntervalPom`.
-/

namespace CounterFreeHDA

universe u v w

/-! ## Data and well-formedness -/

/-- Raw data of an interval pomset with event set `Fin n`. -/
structure PomsetData (Lab : Type u) where
  /-- Number of events. -/
  n : ℕ
  /-- Labelling of events. -/
  lab : Fin n → Lab
  /-- Strict interval precedence order. -/
  prec : Fin n → Fin n → Prop
  /-- Event order, recorded on precedence-incomparable pairs. -/
  eord : Fin n → Fin n → Prop
  /-- Size of the source interface. -/
  srcLen : ℕ
  /-- Size of the target interface. -/
  tgtLen : ℕ
  /-- Source interface, an ordered list of distinct events. -/
  src : Fin srcLen → Fin n
  /-- Target interface, an ordered list of distinct events. -/
  tgt : Fin tgtLen → Fin n
  src_inj : Function.Injective src
  tgt_inj : Function.Injective tgt

namespace PomsetData

variable {Lab : Type u}

/-- Source conclist labels. -/
def srcConclist (P : PomsetData Lab) : Conclist Lab :=
  List.ofFn (P.lab ∘ P.src)

/-- Target conclist labels. -/
def tgtConclist (P : PomsetData Lab) : Conclist Lab :=
  List.ofFn (P.lab ∘ P.tgt)

theorem srcConclist_length (P : PomsetData Lab) :
    P.srcConclist.length = P.srcLen := by
  simp [srcConclist]

theorem tgtConclist_length (P : PomsetData Lab) :
    P.tgtConclist.length = P.tgtLen := by
  simp [tgtConclist]

theorem srcConclist_get (P : PomsetData Lab) (i : Fin P.srcLen) :
    P.srcConclist.get (Fin.cast (P.srcConclist_length).symm i) = P.lab (P.src i) := by
  simp [srcConclist, List.get_ofFn, Fin.cast]

theorem tgtConclist_get (P : PomsetData Lab) (i : Fin P.tgtLen) :
    P.tgtConclist.get (Fin.cast (P.tgtConclist_length).symm i) = P.lab (P.tgt i) := by
  simp [tgtConclist, List.get_ofFn, Fin.cast]

/-- Membership of an event in the source interface. -/
def inSrc (P : PomsetData Lab) (e : Fin P.n) : Prop := e ∈ Set.range P.src

/-- Membership of an event in the target interface. -/
def inTgt (P : PomsetData Lab) (e : Fin P.n) : Prop := e ∈ Set.range P.tgt

theorem inSrc_iff (P : PomsetData Lab) (e : Fin P.n) :
    P.inSrc e ↔ ∃ i : Fin P.srcLen, P.src i = e := Iff.rfl

theorem inTgt_iff (P : PomsetData Lab) (e : Fin P.n) :
    P.inTgt e ↔ ∃ i : Fin P.tgtLen, P.tgt i = e := Iff.rfl

end PomsetData

/-- Well-formedness of interval-pomset data (paper §2). -/
structure IsIntervalPom {Lab : Type u} (P : PomsetData Lab) : Prop where
  /-- `prec` is irreflexive. -/
  prec_irrefl : ∀ e, ¬ P.prec e e
  /-- `prec` is transitive. -/
  prec_trans : ∀ {e f g}, P.prec e f → P.prec f g → P.prec e g
  /-- `eord` is irreflexive. -/
  eord_irrefl : ∀ e, ¬ P.eord e e
  /-- Event order is acyclic, as in the source; it need not be globally transitive. -/
  eord_acyclic : ∀ e, ¬ Relation.TransGen P.eord e e
  /-- For distinct events exactly one of `e≺f`, `f≺e`, `e↣f`, `f↣e` holds. -/
  trichotomy : ∀ e f : Fin P.n, e ≠ f →
    (P.prec e f ∨ P.prec f e ∨ P.eord e f ∨ P.eord f e) ∧
    (P.prec e f → ¬ P.prec f e ∧ ¬ P.eord e f ∧ ¬ P.eord f e) ∧
    (P.prec f e → ¬ P.prec e f ∧ ¬ P.eord e f ∧ ¬ P.eord f e) ∧
    (P.eord e f → ¬ P.prec e f ∧ ¬ P.prec f e ∧ ¬ P.eord f e) ∧
    (P.eord f e → ¬ P.prec e f ∧ ¬ P.prec f e ∧ ¬ P.eord e f)
  /-- Source events are precedence-minimal. -/
  src_minimal : ∀ e, P.inSrc e → ∀ f, ¬ P.prec f e
  /-- Target events are precedence-maximal. -/
  tgt_maximal : ∀ e, P.inTgt e → ∀ f, ¬ P.prec e f
  /-- Event order on the source interface agrees with index order. -/
  src_eord : ∀ i j : Fin P.srcLen, (P.eord (P.src i) (P.src j) ↔ (i : ℕ) < (j : ℕ))
  /-- Event order on the target interface agrees with index order. -/
  tgt_eord : ∀ i j : Fin P.tgtLen, (P.eord (P.tgt i) (P.tgt j) ↔ (i : ℕ) < (j : ℕ))
  /-- Interval-order condition: `prec` is an interval order. -/
  interval_rep : ∃ s t : Fin P.n → ℝ, ∀ e f, P.prec e f ↔ t e < s f

/-- A well-formed interval pomset. -/
def IntervalPom (Lab : Type u) : Type _ := { P : PomsetData Lab // IsIntervalPom P }

namespace IntervalPom

variable {Lab : Type u}

/-- Underlying data. -/
def toData (P : IntervalPom Lab) : PomsetData Lab := P.1

instance : CoeOut (IntervalPom Lab) (PomsetData Lab) := ⟨toData⟩

/-- Number of events. -/
abbrev n (P : IntervalPom Lab) : ℕ := (P : PomsetData Lab).n
/-- Labelling. -/
abbrev lab (P : IntervalPom Lab) : Fin P.n → Lab := (P : PomsetData Lab).lab
/-- Precedence. -/
abbrev prec (P : IntervalPom Lab) : Fin P.n → Fin P.n → Prop := (P : PomsetData Lab).prec
/-- Event order. -/
abbrev eord (P : IntervalPom Lab) : Fin P.n → Fin P.n → Prop := (P : PomsetData Lab).eord
/-- Source interface size. -/
abbrev srcLen (P : IntervalPom Lab) : ℕ := (P : PomsetData Lab).srcLen
/-- Target interface size. -/
abbrev tgtLen (P : IntervalPom Lab) : ℕ := (P : PomsetData Lab).tgtLen
/-- Source interface. -/
abbrev src (P : IntervalPom Lab) : Fin P.srcLen → Fin P.n := (P : PomsetData Lab).src
/-- Target interface. -/
abbrev tgt (P : IntervalPom Lab) : Fin P.tgtLen → Fin P.n := (P : PomsetData Lab).tgt
/-- Well-formedness. -/
abbrev wf (P : IntervalPom Lab) : IsIntervalPom (P : PomsetData Lab) := P.2

/-- Source conclist. -/
abbrev srcConclist (P : IntervalPom Lab) : Conclist Lab := (P : PomsetData Lab).srcConclist
/-- Target conclist. -/
abbrev tgtConclist (P : IntervalPom Lab) : Conclist Lab := (P : PomsetData Lab).tgtConclist

/-- A pomset is *discrete* when no precedence holds. -/
def IsDiscrete (P : IntervalPom Lab) : Prop := ∀ e f : Fin P.n, ¬ P.prec e f

/-- A pomset is a *starter* when every event is in the target interface. -/
def IsStarter (P : IntervalPom Lab) : Prop :=
  ∀ e : Fin P.n, (P : PomsetData Lab).inTgt e

/-- A pomset is a *terminator* when every event is in the source interface. -/
def IsTerminator (P : IntervalPom Lab) : Prop :=
  ∀ e : Fin P.n, (P : PomsetData Lab).inSrc e

/-- An *elementary* starter or terminator starts/terminates exactly one event. -/
def IsElementary (P : IntervalPom Lab) : Prop :=
  (P.IsStarter ∧ P.tgtLen = P.srcLen + 1) ∨
  (P.IsTerminator ∧ P.srcLen = P.tgtLen + 1)

end IntervalPom

/-! ## Isomorphism -/

/-- Label- and interface-preserving isomorphism of interval-pomset data.
Interface lengths are matched by order-preserving equivalences, so no `Fin.cast`
is needed in the commuting triangles. -/
structure PomsetIso {Lab : Type u} (P Q : PomsetData Lab) where
  toEquiv : Fin P.n ≃ Fin Q.n
  lab_eq : ∀ e, Q.lab (toEquiv e) = P.lab e
  srcEquiv : Fin P.srcLen ≃ Fin Q.srcLen
  tgtEquiv : Fin P.tgtLen ≃ Fin Q.tgtLen
  src_mono : ∀ i j : Fin P.srcLen,
    ((srcEquiv i : ℕ) < (srcEquiv j : ℕ)) ↔ ((i : ℕ) < (j : ℕ))
  tgt_mono : ∀ i j : Fin P.tgtLen,
    ((tgtEquiv i : ℕ) < (tgtEquiv j : ℕ)) ↔ ((i : ℕ) < (j : ℕ))
  src_eq : ∀ i : Fin P.srcLen, toEquiv (P.src i) = Q.src (srcEquiv i)
  tgt_eq : ∀ i : Fin P.tgtLen, toEquiv (P.tgt i) = Q.tgt (tgtEquiv i)
  prec_iff : ∀ e f, Q.prec (toEquiv e) (toEquiv f) ↔ P.prec e f
  eord_iff : ∀ e f, Q.eord (toEquiv e) (toEquiv f) ↔ P.eord e f

/-- Isomorphism of interval pomsets. -/
def IntervalPomIso {Lab : Type u} (P Q : IntervalPom Lab) : Prop :=
  Nonempty (PomsetIso (P : PomsetData Lab) (Q : PomsetData Lab))

infix:50 " ≅ " => IntervalPomIso

namespace PomsetIso

variable {Lab : Type u}

/-- Isomorphisms are reflexive. -/
def refl (P : PomsetData Lab) : PomsetIso P P where
  toEquiv := Equiv.refl _
  lab_eq := fun _ => rfl
  srcEquiv := Equiv.refl _
  tgtEquiv := Equiv.refl _
  src_mono := fun _ _ => Iff.rfl
  tgt_mono := fun _ _ => Iff.rfl
  src_eq := fun _ => rfl
  tgt_eq := fun _ => rfl
  prec_iff := fun _ _ => Iff.rfl
  eord_iff := fun _ _ => Iff.rfl

/-- Isomorphisms are symmetric. -/
def symm {P Q : PomsetData Lab} (φ : PomsetIso P Q) : PomsetIso Q P where
  toEquiv := φ.toEquiv.symm
  lab_eq := by
    intro e
    have h := φ.lab_eq (φ.toEquiv.symm e)
    simpa using h.symm
  srcEquiv := φ.srcEquiv.symm
  tgtEquiv := φ.tgtEquiv.symm
  src_mono := by
    intro i j
    have h := φ.src_mono (φ.srcEquiv.symm i) (φ.srcEquiv.symm j)
    simpa using h.symm
  tgt_mono := by
    intro i j
    have h := φ.tgt_mono (φ.tgtEquiv.symm i) (φ.tgtEquiv.symm j)
    simpa using h.symm
  src_eq := by
    intro i
    have h := φ.src_eq (φ.srcEquiv.symm i)
    simp only [Equiv.apply_symm_apply] at h
    have h2 := congrArg φ.toEquiv.symm h
    simpa using h2.symm
  tgt_eq := by
    intro i
    have h := φ.tgt_eq (φ.tgtEquiv.symm i)
    simp only [Equiv.apply_symm_apply] at h
    have h2 := congrArg φ.toEquiv.symm h
    simpa using h2.symm
  prec_iff := by
    intro e f
    have h := φ.prec_iff (φ.toEquiv.symm e) (φ.toEquiv.symm f)
    simpa using h.symm
  eord_iff := by
    intro e f
    have h := φ.eord_iff (φ.toEquiv.symm e) (φ.toEquiv.symm f)
    simpa using h.symm

/-- Isomorphisms are transitive. -/
def trans {P Q R : PomsetData Lab} (φ : PomsetIso P Q) (ψ : PomsetIso Q R) :
    PomsetIso P R where
  toEquiv := φ.toEquiv.trans ψ.toEquiv
  lab_eq := fun e => (ψ.lab_eq (φ.toEquiv e)).trans (φ.lab_eq e)
  srcEquiv := φ.srcEquiv.trans ψ.srcEquiv
  tgtEquiv := φ.tgtEquiv.trans ψ.tgtEquiv
  src_mono := by
    intro i j
    have h1 := φ.src_mono i j
    have h2 := ψ.src_mono (φ.srcEquiv i) (φ.srcEquiv j)
    simpa using h2.trans h1
  tgt_mono := by
    intro i j
    have h1 := φ.tgt_mono i j
    have h2 := ψ.tgt_mono (φ.tgtEquiv i) (φ.tgtEquiv j)
    simpa using h2.trans h1
  src_eq := by
    intro i
    simp only [Equiv.trans_apply]
    rw [φ.src_eq, ψ.src_eq]
  tgt_eq := by
    intro i
    simp only [Equiv.trans_apply]
    rw [φ.tgt_eq, ψ.tgt_eq]
  prec_iff := by
    intro e f
    have h1 := φ.prec_iff e f
    have h2 := ψ.prec_iff (φ.toEquiv e) (φ.toEquiv f)
    simpa using h2.trans h1
  eord_iff := by
    intro e f
    have h1 := φ.eord_iff e f
    have h2 := ψ.eord_iff (φ.toEquiv e) (φ.toEquiv f)
    simpa using h2.trans h1

/-- `IsIntervalPom` is invariant under isomorphism. -/
theorem iso_isIntervalPom {P Q : PomsetData Lab} (φ : PomsetIso P Q)
    (h : IsIntervalPom P) : IsIntervalPom Q := by
  have inv := φ.toEquiv.symm
  have inv_src := φ.srcEquiv.symm
  have inv_tgt := φ.tgtEquiv.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- prec_irrefl
    intro e
    obtain ⟨a, rfl⟩ := φ.toEquiv.surjective e
    intro hh
    exact h.prec_irrefl a (φ.prec_iff a a |>.mp hh)
  · -- prec_trans
    intro e f g hef hfg
    obtain ⟨a, rfl⟩ := φ.toEquiv.surjective e
    obtain ⟨b, rfl⟩ := φ.toEquiv.surjective f
    obtain ⟨c, rfl⟩ := φ.toEquiv.surjective g
    exact φ.prec_iff a c |>.mpr (h.prec_trans (φ.prec_iff a b |>.mp hef)
      (φ.prec_iff b c |>.mp hfg))
  · -- eord_irrefl
    intro e
    obtain ⟨a, rfl⟩ := φ.toEquiv.surjective e
    intro hh
    exact h.eord_irrefl a (φ.eord_iff a a |>.mp hh)
  · -- eord_acyclic
    intro e hp
    have lift : ∀ {a b}, Relation.TransGen Q.eord a b →
        Relation.TransGen P.eord (φ.toEquiv.symm a) (φ.toEquiv.symm b) := by
      intro a b hab
      induction hab with
      | single hab => exact .single ((φ.symm.eord_iff _ _).mpr hab)
      | tail _ hbc ih => exact ih.tail ((φ.symm.eord_iff _ _).mpr hbc)
    exact h.eord_acyclic _ (lift hp)
  · -- trichotomy
    intro e f hne
    obtain ⟨a, rfl⟩ := φ.toEquiv.surjective e
    obtain ⟨b, rfl⟩ := φ.toEquiv.surjective f
    have hne' : a ≠ b := fun hab => hne (hab ▸ rfl)
    rcases h.trichotomy a b hne' with ⟨hex, hpq, hqp, hef, hfe⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact hex.imp (φ.prec_iff a b |>.mpr)
        (fun h => h.imp (φ.prec_iff b a |>.mpr)
          (fun h => h.imp (φ.eord_iff a b |>.mpr) (φ.eord_iff b a |>.mpr)))
    · intro h1
      rcases hpq (φ.prec_iff a b |>.mp h1) with ⟨h2, h3, h4⟩
      exact ⟨(φ.prec_iff b a).not.mpr h2, (φ.eord_iff a b).not.mpr h3,
        (φ.eord_iff b a).not.mpr h4⟩
    · intro h1
      rcases hqp (φ.prec_iff b a |>.mp h1) with ⟨h2, h3, h4⟩
      exact ⟨(φ.prec_iff a b).not.mpr h2, (φ.eord_iff a b).not.mpr h3,
        (φ.eord_iff b a).not.mpr h4⟩
    · intro h1
      rcases hef (φ.eord_iff a b |>.mp h1) with ⟨h2, h3, h4⟩
      exact ⟨(φ.prec_iff a b).not.mpr h2, (φ.prec_iff b a).not.mpr h3,
        (φ.eord_iff b a).not.mpr h4⟩
    · intro h1
      rcases hfe (φ.eord_iff b a |>.mp h1) with ⟨h2, h3, h4⟩
      exact ⟨(φ.prec_iff a b).not.mpr h2, (φ.prec_iff b a).not.mpr h3,
        (φ.eord_iff a b).not.mpr h4⟩
  · -- src_minimal
    intro e he f hf
    obtain ⟨a, rfl⟩ := φ.toEquiv.surjective e
    have hin : P.inSrc a := by
      obtain ⟨j, hj⟩ := he
      obtain ⟨i, hi⟩ := φ.srcEquiv.surjective j
      subst hi
      have hsrc := φ.src_eq i
      have hEq : toEquiv φ (P.src i) = toEquiv φ a := hsrc.trans hj
      have hInj := φ.toEquiv.injective hEq
      exact ⟨i, hInj⟩
    set b := φ.toEquiv.symm f with hb
    have hf' : Q.prec (φ.toEquiv b) (φ.toEquiv a) := by
      simp only [hb, Equiv.apply_symm_apply]
      exact hf
    exact h.src_minimal a hin b (φ.prec_iff b a |>.mp hf')
  · -- tgt_maximal
    intro e he f hf
    obtain ⟨a, rfl⟩ := φ.toEquiv.surjective e
    have hin : P.inTgt a := by
      obtain ⟨j, hj⟩ := he
      obtain ⟨i, hi⟩ := φ.tgtEquiv.surjective j
      subst hi
      have htgt := φ.tgt_eq i
      have hEq : toEquiv φ (P.tgt i) = toEquiv φ a := htgt.trans hj
      have hInj := φ.toEquiv.injective hEq
      exact ⟨i, hInj⟩
    set b := φ.toEquiv.symm f with hb
    have hf' : Q.prec (φ.toEquiv a) (φ.toEquiv b) := by
      simp only [hb, Equiv.apply_symm_apply]
      exact hf
    exact h.tgt_maximal a hin b (φ.prec_iff a b |>.mp hf')
  · -- src_eord
    intro i j
    have h1 : Q.src i = φ.toEquiv (P.src (φ.srcEquiv.symm i)) := by
      have := φ.src_eq (φ.srcEquiv.symm i)
      simpa using this.symm
    have h2 : Q.src j = φ.toEquiv (P.src (φ.srcEquiv.symm j)) := by
      have := φ.src_eq (φ.srcEquiv.symm j)
      simpa using this.symm
    have hP := h.src_eord (φ.srcEquiv.symm i) (φ.srcEquiv.symm j)
    have hIff := φ.eord_iff (P.src (φ.srcEquiv.symm i)) (P.src (φ.srcEquiv.symm j))
    rw [← h1, ← h2] at hIff
    have hMono : ((i : ℕ) < (j : ℕ)) ↔
        ((φ.srcEquiv.symm i : ℕ) < (φ.srcEquiv.symm j : ℕ)) := by
      have hM := φ.src_mono (φ.srcEquiv.symm i) (φ.srcEquiv.symm j)
      simpa using hM
    constructor <;> intro hh
    · exact hMono.mpr (hP.mp (hIff.mp hh))
    · exact hIff.mpr (hP.mpr (hMono.mp hh))
  · -- tgt_eord
    intro i j
    have h1 : Q.tgt i = φ.toEquiv (P.tgt (φ.tgtEquiv.symm i)) := by
      have := φ.tgt_eq (φ.tgtEquiv.symm i)
      simpa using this.symm
    have h2 : Q.tgt j = φ.toEquiv (P.tgt (φ.tgtEquiv.symm j)) := by
      have := φ.tgt_eq (φ.tgtEquiv.symm j)
      simpa using this.symm
    have hP := h.tgt_eord (φ.tgtEquiv.symm i) (φ.tgtEquiv.symm j)
    have hIff := φ.eord_iff (P.tgt (φ.tgtEquiv.symm i)) (P.tgt (φ.tgtEquiv.symm j))
    rw [← h1, ← h2] at hIff
    have hMono : ((i : ℕ) < (j : ℕ)) ↔
        ((φ.tgtEquiv.symm i : ℕ) < (φ.tgtEquiv.symm j : ℕ)) := by
      have hM := φ.tgt_mono (φ.tgtEquiv.symm i) (φ.tgtEquiv.symm j)
      simpa using hM
    constructor <;> intro hh
    · exact hMono.mpr (hP.mp (hIff.mp hh))
    · exact hIff.mpr (hP.mpr (hMono.mp hh))
  · -- interval_rep
    obtain ⟨s, t, hrep⟩ := h.interval_rep
    refine ⟨fun e => s (φ.toEquiv.symm e), fun e => t (φ.toEquiv.symm e), ?_⟩
    intro e f
    obtain ⟨a, rfl⟩ := φ.toEquiv.surjective e
    obtain ⟨b, rfl⟩ := φ.toEquiv.surjective f
    simp only [Equiv.symm_apply_apply]
    have h1 := hrep a b
    have h2 := φ.prec_iff a b
    exact ⟨fun hh => h1.mp (h2.mp hh), fun hh => h2.mpr (h1.mpr hh)⟩

end PomsetIso

/-! ## Identity, elementary starters and terminators -/

/-- Helper: for `Fin (n+1)` and distinct events, exactly one of the four
orderings holds, when `prec` is empty and `eord` is index order. -/
private theorem fin_trichotomy {n : ℕ} (e f : Fin (n + 1)) (hne : e ≠ f) :
    ((e : ℕ) < (f : ℕ) ∨ (f : ℕ) < (e : ℕ)) ∧
    ((e : ℕ) < (f : ℕ) → ¬ (f : ℕ) < (e : ℕ)) ∧
    ((f : ℕ) < (e : ℕ) → ¬ (e : ℕ) < (f : ℕ)) := by
  by_cases h : (e : ℕ) < (f : ℕ)
  · refine ⟨Or.inl h, ?_, ?_⟩
    · intro _ hf; omega
    · intro hf; omega
  · have hlt : (f : ℕ) < (e : ℕ) := by
      by_contra hlt
      push_neg at hlt h
      exact hne (Fin.eq_of_val_eq (Nat.le_antisymm hlt h))
    refine ⟨Or.inr hlt, ?_, ?_⟩
    · intro he; omega
    · intro _ he; omega

/-- Helper: the 4-way trichotomy when `prec` is empty and `eord` is `(· < ·)` on `Fin`. -/
private theorem empty_prec_trichotomy {n : ℕ}
    (prec eord : Fin n → Fin n → Prop)
    (hprec : ∀ e f, ¬ prec e f)
    (heord : ∀ e f, eord e f ↔ (e : ℕ) < (f : ℕ)) :
    ∀ e f : Fin n, e ≠ f →
      (prec e f ∨ prec f e ∨ eord e f ∨ eord f e) ∧
      (prec e f → ¬ prec f e ∧ ¬ eord e f ∧ ¬ eord f e) ∧
      (prec f e → ¬ prec e f ∧ ¬ eord e f ∧ ¬ eord f e) ∧
      (eord e f → ¬ prec e f ∧ ¬ prec f e ∧ ¬ eord f e) ∧
      (eord f e → ¬ prec e f ∧ ¬ prec f e ∧ ¬ eord e f) := by
  intro e f hne
  by_cases h : (e : ℕ) < (f : ℕ)
  · refine ⟨Or.inr (Or.inr (Or.inl ((heord e f).mpr h))), ?_, ?_, ?_, ?_⟩
    · intro hh; exact absurd hh (hprec _ _)
    · intro hh; exact absurd hh (hprec _ _)
    · intro hh
      refine ⟨hprec e f, hprec f e, ?_⟩
      intro h'
      have h1 : (f : ℕ) < (e : ℕ) := (heord f e).mp h'
      omega
    · intro hh
      refine ⟨hprec e f, hprec f e, ?_⟩
      intro h'
      have h1 : (e : ℕ) < (f : ℕ) := (heord e f).mp h'
      have h2 : (f : ℕ) < (e : ℕ) := (heord f e).mp hh
      omega
  · have hlt : (f : ℕ) < (e : ℕ) := by
      by_contra hlt
      push_neg at hlt h
      exact hne (Fin.eq_of_val_eq (Nat.le_antisymm hlt h))
    refine ⟨Or.inr (Or.inr (Or.inr ((heord f e).mpr hlt))), ?_, ?_, ?_, ?_⟩
    · intro hh; exact absurd hh (hprec _ _)
    · intro hh; exact absurd hh (hprec _ _)
    · intro hh
      refine ⟨hprec e f, hprec f e, ?_⟩
      intro h'
      have h1 : (f : ℕ) < (e : ℕ) := (heord f e).mp h'
      have h2 : (e : ℕ) < (f : ℕ) := (heord e f).mp hh
      omega
    · intro hh
      refine ⟨hprec e f, hprec f e, ?_⟩
      intro h'
      have h1 : (e : ℕ) < (f : ℕ) := (heord e f).mp h'
      omega

private theorem fin_lt_acyclic {n : ℕ} (e : Fin n) :
    ¬ Relation.TransGen (fun a b : Fin n => a.val < b.val) e e := by
  intro h
  have key : ∀ {a b : Fin n},
      Relation.TransGen (fun x y : Fin n => x.val < y.val) a b → a.val < b.val := by
    intro a b h
    induction h with
    | single h => exact h
    | tail _ h ih => exact Nat.lt_trans ih h
  exact Nat.lt_irrefl _ (key h)

/-- Identity pomset on a conclist `lab : Fin n → Lab`: all events in both
interfaces, no precedence, event order = index order. -/
def identityPom (Lab : Type u) (n : ℕ) (lab : Fin n → Lab) : IntervalPom Lab where
  val := {
    n := n
    lab := lab
    prec := fun _ _ => False
    eord := fun e f => (e : ℕ) < (f : ℕ)
    srcLen := n
    tgtLen := n
    src := id
    tgt := id
    src_inj := Function.injective_id
    tgt_inj := Function.injective_id
  }
  property := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e h; exact h
    · intro e f g h1 _; exact absurd h1 (by simp)
    · intro e h; exact Nat.lt_irrefl _ h
    · exact fin_lt_acyclic
    · exact empty_prec_trichotomy (fun _ _ => False) (fun e f => (e : ℕ) < (f : ℕ))
        (fun _ _ h => h) (fun _ _ => Iff.rfl)
    · intro e _ f h; exact absurd h (by simp)
    · intro e _ f h; exact absurd h (by simp)
    · intro i j; exact Iff.rfl
    · intro i j; exact Iff.rfl
    · exact ⟨fun _ => 0, fun _ => 0, fun e f => by simp⟩

/-- SuccAbove is order-preserving as a map on `Fin` values. -/
theorem succAbove_val_mono {n : ℕ} (i : Fin (n + 1)) (a b : Fin n) :
    ((i.succAbove a : Fin (n + 1)) : ℕ) < ((i.succAbove b : Fin (n + 1)) : ℕ) ↔
      (a : ℕ) < (b : ℕ) := by
  have key : ∀ x : Fin n, ((i.succAbove x : Fin (n+1)) : ℕ)
      = if (x : ℕ) < (i : ℕ) then (x : ℕ) else (x : ℕ) + 1 := by
    intro x
    by_cases h : (x : ℕ) < (i : ℕ)
    · have hs : i.succAbove x = x.castSucc := by
        apply Fin.succAbove_of_castSucc_lt
        rw [Fin.lt_def, Fin.coe_castSucc]
        exact h
      rw [hs, Fin.coe_castSucc]
      simp [h]
    · have hs : i.succAbove x = x.succ := by
        apply Fin.succAbove_of_le_castSucc
        rw [Fin.le_def, Fin.coe_castSucc]
        omega
      rw [hs, Fin.val_succ]
      simp [h]
  rw [key a, key b]
  split_ifs with ha hb
  · exact Iff.rfl
  · constructor <;> intro h <;> omega
  · constructor <;> intro h <;> omega
  · constructor <;> intro h <;> omega

/-- Elementary starter at position `i` of `lab : Fin (n+1) → Lab`: starts event
`i`, keeping the other events as a shared interface. -/
def elemStart (Lab : Type u) {n : ℕ} (lab : Fin (n + 1) → Lab) (i : Fin (n + 1)) :
    IntervalPom Lab where
  val := {
    n := n + 1
    lab := lab
    prec := fun _ _ => False
    eord := fun e f => (e : ℕ) < (f : ℕ)
    srcLen := n
    tgtLen := n + 1
    src := i.succAbove
    tgt := id
    src_inj := i.succAbove_right_injective
    tgt_inj := Function.injective_id
  }
  property := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e h; exact h
    · intro e f g h1 _; exact absurd h1 (by simp)
    · intro e h; exact Nat.lt_irrefl _ h
    · exact fin_lt_acyclic
    · exact empty_prec_trichotomy (fun _ _ => False) (fun e f => (e : ℕ) < (f : ℕ))
        (fun _ _ h => h) (fun _ _ => Iff.rfl)
    · intro e _ f h; exact absurd h (by simp)
    · intro e _ f h; exact absurd h (by simp)
    · intro a b
      exact succAbove_val_mono i a b
    · intro a b; exact Iff.rfl
    · exact ⟨fun _ => 0, fun _ => 0, fun e f => by simp⟩

/-- Elementary terminator at position `i` of `lab : Fin (n+1) → Lab`: terminates
event `i`, keeping the other events as a shared interface. -/
def elemStop (Lab : Type u) {n : ℕ} (lab : Fin (n + 1) → Lab) (i : Fin (n + 1)) :
    IntervalPom Lab where
  val := {
    n := n + 1
    lab := lab
    prec := fun _ _ => False
    eord := fun e f => (e : ℕ) < (f : ℕ)
    srcLen := n + 1
    tgtLen := n
    src := id
    tgt := i.succAbove
    src_inj := Function.injective_id
    tgt_inj := i.succAbove_right_injective
  }
  property := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e h; exact h
    · intro e f g h1 _; exact absurd h1 (by simp)
    · intro e h; exact Nat.lt_irrefl _ h
    · exact fin_lt_acyclic
    · exact empty_prec_trichotomy (fun _ _ => False) (fun e f => (e : ℕ) < (f : ℕ))
        (fun _ _ h => h) (fun _ _ => Iff.rfl)
    · intro e _ f h; exact absurd h (by simp)
    · intro e _ f h; exact absurd h (by simp)
    · intro a b; exact Iff.rfl
    · intro a b
      exact succAbove_val_mono i a b
    · exact ⟨fun _ => 0, fun _ => 0, fun e f => by simp⟩

/-! ## Subsumption -/

/-- A subsumption `P ⊑ Q` is a label- and interface-preserving bijection of
events under which every precedence of `Q` holds in `P`, and event orders agree
on pairs incomparable in `P`. -/
def Subsumption {Lab : Type u} (P Q : IntervalPom Lab) : Prop :=
  ∃ (φ : Fin P.n ≃ Fin Q.n) (hs : P.srcLen = Q.srcLen) (ht : P.tgtLen = Q.tgtLen),
    (∀ e, P.lab e = Q.lab (φ e)) ∧
    (∀ i : Fin P.srcLen, φ (P.src i) = Q.src (Fin.cast hs i)) ∧
    (∀ i : Fin P.tgtLen, φ (P.tgt i) = Q.tgt (Fin.cast ht i)) ∧
    (∀ e f, Q.prec (φ e) (φ f) → P.prec e f) ∧
    (∀ e f, ¬ P.prec e f → ¬ P.prec f e → (P.eord e f ↔ Q.eord (φ e) (φ f)))

infix:50 " ⊑ₛ " => Subsumption

/-- Every pomset subsumes itself. -/
theorem subsumption_refl {Lab : Type u} (P : IntervalPom Lab) : P ⊑ₛ P := by
  refine ⟨Equiv.refl _, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro e; rfl
  · intro i; simp
  · intro i; simp
  · intro e f h; exact h
  · intro e f _ _; exact Iff.rfl

/-- Subsumption is transitive. -/
theorem subsumption_trans {Lab : Type u} {P Q R : IntervalPom Lab}
    (hPQ : P ⊑ₛ Q) (hQR : Q ⊑ₛ R) : P ⊑ₛ R := by
  obtain ⟨φ, hs1, ht1, hl1, hsrc1, htgt1, hprec1, heord1⟩ := hPQ
  obtain ⟨ψ, hs2, ht2, hl2, hsrc2, htgt2, hprec2, heord2⟩ := hQR
  refine ⟨φ.trans ψ, hs1.trans hs2, ht1.trans ht2, ?_, ?_, ?_, ?_, ?_⟩
  · intro e; exact (hl1 e).trans (hl2 (φ e))
  · intro i
    simp only [Equiv.trans_apply]
    rw [hsrc1 i, hsrc2]
    simp
  · intro i
    simp only [Equiv.trans_apply]
    rw [htgt1 i, htgt2]
    simp
  · intro e f h; exact hprec1 e f (hprec2 (φ e) (φ f) h)
  · intro e f h1 h2
    have h3 : ¬ Q.prec (φ e) (φ f) := fun h => h1 (hprec1 e f h)
    have h4 : ¬ Q.prec (φ f) (φ e) := fun h => h2 (hprec1 f e h)
    exact (heord1 e f h1 h2).trans (heord2 (φ e) (φ f) h3 h4)

/-! ## Gluing (composition)

Gluing `P : U → V` to `Q : V → W` identifies corresponding ordered events of
`T_P` and `S_Q`.  We use disjoint copies of the non-interface events and a single copy of
the common interface. Thus no interface event is duplicated.
-/

/-- Events of the glued pomset `P * Q`. -/
inductive GluedE {Lab : Type u} (P Q : PomsetData Lab) : Type _ where
  | left (e : {e : Fin P.n // ¬ P.inTgt e})
  | right (e : {e : Fin Q.n // ¬ Q.inSrc e})
  | mid (i : Fin P.tgtLen)

/-- Auxiliary injection of `GluedE` into a finite sum of `Fin`s. -/
def GluedE.toSum {Lab : Type u} (P Q : PomsetData Lab) :
    GluedE P Q → ({e : Fin P.n // ¬ P.inTgt e} ⊕ {e : Fin Q.n // ¬ Q.inSrc e}) ⊕ Fin P.tgtLen
  | .left e => Sum.inl (Sum.inl e)
  | .right e => Sum.inl (Sum.inr e)
  | .mid i => Sum.inr i

theorem GluedE.toSum_inj {Lab : Type u} (P Q : PomsetData Lab) :
    Function.Injective (GluedE.toSum P Q) := by
  rintro (e | e | i) (e' | e' | j) h
  · simp only [GluedE.toSum] at h; cases h; rfl
  · simp only [GluedE.toSum] at h; exact absurd h (by simp)
  · simp only [GluedE.toSum] at h; exact absurd h (by simp)
  · simp only [GluedE.toSum] at h; exact absurd h (by simp)
  · simp only [GluedE.toSum] at h; cases h; rfl
  · simp only [GluedE.toSum] at h; exact absurd h (by simp)
  · simp only [GluedE.toSum] at h; exact absurd h (by simp)
  · simp only [GluedE.toSum] at h; exact absurd h (by simp)
  · simp only [GluedE.toSum] at h; cases h; rfl

instance {Lab : Type u} (P Q : PomsetData Lab) : Finite (GluedE P Q) :=
  Finite.of_injective _ (GluedE.toSum_inj P Q)

noncomputable instance {Lab : Type u} (P Q : PomsetData Lab) :
    Fintype (GluedE P Q) :=
  Fintype.ofFinite _

/-- Gluing hypothesis: interface lengths match and labels agree. -/
structure GlueMatch {Lab : Type u} (P Q : PomsetData Lab) where
  len_eq : P.tgtLen = Q.srcLen
  lab_eq : ∀ i : Fin P.tgtLen,
    P.lab (P.tgt i) = Q.lab (Q.src (Fin.cast len_eq i))

namespace GluedE

/-- Canonical embedding of the left factor, identifying its target events. -/
noncomputable def leftMap {Lab : Type u} (P Q : PomsetData Lab) (e : Fin P.n) : GluedE P Q := by
  classical
  exact if h : P.inTgt e then .mid (Classical.choose h) else .left ⟨e,h⟩

/-- Canonical embedding of the right factor, identifying its source events. -/
noncomputable def rightMap {Lab : Type u} (P Q : PomsetData Lab)
    (len : P.tgtLen = Q.srcLen) (e : Fin Q.n) : GluedE P Q := by
  classical
  exact if h : Q.inSrc e then .mid (Fin.cast len.symm (Classical.choose h)) else .right ⟨e,h⟩

def leftProjection {Lab : Type u} (P Q : PomsetData Lab) : GluedE P Q → Option (Fin P.n)
  | .left e => some e.val
  | .right _ => none
  | .mid i => some (P.tgt i)

def rightProjection {Lab : Type u} (P Q : PomsetData Lab)
    (len : P.tgtLen = Q.srcLen) : GluedE P Q → Option (Fin Q.n)
  | .left _ => none
  | .right e => some e.val
  | .mid i => some (Q.src (Fin.cast len i))

theorem leftProjection_leftMap {Lab : Type u} (P Q : PomsetData Lab) (e : Fin P.n) :
    leftProjection P Q (leftMap P Q e) = some e := by
  unfold leftMap
  split_ifs with h
  · exact congrArg some (Classical.choose_spec h)
  · rfl

theorem rightProjection_rightMap {Lab : Type u} (P Q : PomsetData Lab)
    (len : P.tgtLen = Q.srcLen) (e : Fin Q.n) :
    rightProjection P Q len (rightMap P Q len e) = some e := by
  unfold rightMap
  split_ifs with h
  · simpa only [rightProjection, Fin.cast_trans, Fin.cast_refl] using
      congrArg some (Classical.choose_spec h)
  · rfl

theorem leftMap_inj {Lab : Type u} (P Q : PomsetData Lab) : Function.Injective (leftMap P Q) := by
  intro e f h
  have h' := congrArg (leftProjection P Q) h
  simpa only [leftProjection_leftMap, Option.some.injEq] using h'

theorem rightMap_inj {Lab : Type u} (P Q : PomsetData Lab) (len : P.tgtLen = Q.srcLen) :
    Function.Injective (rightMap P Q len) := by
  intro e f h
  have h' := congrArg (rightProjection P Q len) h
  simpa only [rightProjection_rightMap, Option.some.injEq] using h'

theorem leftMap_tgt {Lab : Type u} (P Q : PomsetData Lab) (i : Fin P.tgtLen) :
    leftMap P Q (P.tgt i) = .mid i := by
  unfold leftMap
  have h : P.inTgt (P.tgt i) := ⟨i,rfl⟩
  rw [dif_pos h]
  exact congrArg GluedE.mid (P.tgt_inj (Classical.choose_spec h))

theorem rightMap_src {Lab : Type u} (P Q : PomsetData Lab)
    (len : P.tgtLen = Q.srcLen) (i : Fin Q.srcLen) :
    rightMap P Q len (Q.src i) = .mid (Fin.cast len.symm i) := by
  unfold rightMap
  have h : Q.inSrc (Q.src i) := ⟨i,rfl⟩
  rw [dif_pos h]
  exact congrArg (fun j => GluedE.mid (Fin.cast len.symm j))
    (Q.src_inj (Classical.choose_spec h))

/-- The two interface embeddings agree exactly on the identified positions. -/
theorem identified {Lab : Type u} (P Q : PomsetData Lab)
    (len : P.tgtLen = Q.srcLen) (i : Fin P.tgtLen) :
    leftMap P Q (P.tgt i) = rightMap P Q len (Q.src (Fin.cast len i)) := by
  rw [leftMap_tgt, rightMap_src]
  simp

end GluedE

/-- Internal precedence plus the cross-factor order on non-interface events. -/
def gluePrec {Lab : Type u} {P Q : PomsetData Lab} (len : P.tgtLen = Q.srcLen) :
    GluedE P Q → GluedE P Q → Prop
  | .left e, .left f => P.prec e.val f.val
  | .left e, .mid i => P.prec e.val (P.tgt i)
  | .left _, .right _ => True
  | .mid _, .left _ => False
  | .mid _, .mid _ => False
  | .mid i, .right f => Q.prec (Q.src (Fin.cast len i)) f.val
  | .right _, .left _ => False
  | .right _, .mid _ => False
  | .right e, .right f => Q.prec e.val f.val

/-- Event orders are inherited from the factors on incomparable pairs. -/
def glueEord {Lab : Type u} {P Q : PomsetData Lab} (len : P.tgtLen = Q.srcLen) :
    GluedE P Q → GluedE P Q → Prop
  | .left e, .left f => P.eord e.val f.val
  | .left e, .mid i => P.eord e.val (P.tgt i)
  | .left _, .right _ => False
  | .mid i, .left f => P.eord (P.tgt i) f.val
  | .mid i, .mid j => P.eord (P.tgt i) (P.tgt j)
  | .mid i, .right f => Q.eord (Q.src (Fin.cast len i)) f.val
  | .right _, .left _ => False
  | .right e, .mid j => Q.eord e.val (Q.src (Fin.cast len j))
  | .right e, .right f => Q.eord e.val f.val

def glueLab {Lab : Type u} {P Q : PomsetData Lab} (_m : GlueMatch P Q) : GluedE P Q → Lab
  | .left e => P.lab e.val
  | .right e => Q.lab e.val
  | .mid i => P.lab (P.tgt i)

/-- Glued pomset data with event set `Fin (card)`. -/
noncomputable def glueData {Lab : Type u} (P Q : PomsetData Lab)
    (m : GlueMatch P Q) : PomsetData Lab where
  n := Fintype.card (GluedE P Q)
  lab := fun e => glueLab m ((Fintype.equivFin (GluedE P Q)).symm e)
  prec := fun e f =>
    gluePrec m.len_eq ((Fintype.equivFin (GluedE P Q)).symm e)
      ((Fintype.equivFin (GluedE P Q)).symm f)
  eord := fun e f =>
    glueEord m.len_eq ((Fintype.equivFin (GluedE P Q)).symm e)
      ((Fintype.equivFin (GluedE P Q)).symm f)
  srcLen := P.srcLen
  tgtLen := Q.tgtLen
  src := fun i => (Fintype.equivFin (GluedE P Q)) (GluedE.leftMap P Q (P.src i))
  tgt := fun j => (Fintype.equivFin (GluedE P Q)) (GluedE.rightMap P Q m.len_eq (Q.tgt j))
  src_inj := (Fintype.equivFin (GluedE P Q)).injective.comp
    ((GluedE.leftMap_inj P Q).comp P.src_inj)
  tgt_inj := (Fintype.equivFin (GluedE P Q)).injective.comp
    ((GluedE.rightMap_inj P Q m.len_eq).comp Q.tgt_inj)

theorem glueData_tgtLen {Lab : Type u} (P Q : PomsetData Lab) (m : GlueMatch P Q) :
    (glueData P Q m).tgtLen = Q.tgtLen := rfl

theorem glueData_srcLen {Lab : Type u} (P Q : PomsetData Lab) (m : GlueMatch P Q) :
    (glueData P Q m).srcLen = P.srcLen := rfl

/-! ## Powers of endomorphisms -/

/-- `P` is an endomorphism when source and target have the same length and
matching labels. -/
structure IsEndo {Lab : Type u} (P : PomsetData Lab) : Prop where
  len_eq : P.srcLen = P.tgtLen
  lab_eq : ∀ i : Fin P.srcLen,
    P.lab (P.src i) = P.lab (P.tgt (Fin.cast len_eq i))

/-- Identity pomset data. -/
def idData {Lab : Type u} (n : ℕ) (lab : Fin n → Lab) : PomsetData Lab where
  n := n
  lab := lab
  prec := fun _ _ => False
  eord := fun e f => (e : ℕ) < (f : ℕ)
  srcLen := n
  tgtLen := n
  src := id
  tgt := id
  src_inj := Function.injective_id
  tgt_inj := Function.injective_id

/-- Event count of the `k`-th power of an endomorphism: `|P⁰| = r`,
`|P^{k+1}| = |P^k| + |P| - r` (see also `PomCounted` in `Iterate`). -/
def powCard {Lab : Type u} (P : PomsetData Lab) (h : IsEndo P) : ℕ → ℕ
  | 0 => P.srcLen
  | k + 1 => powCard P h k + P.n - P.srcLen

/-! ## Corners -/

/-- Compatibility of a face pair for `P`: shared interface positions satisfy
`α ≤ β` in the status order. -/
def CompatibleFor {Lab : Type u} (P : PomsetData Lab)
    (α : Fin P.srcLen → Status) (β : Fin P.tgtLen → Status) : Prop :=
  ∀ i : Fin P.srcLen, ∀ j : Fin P.tgtLen,
    P.src i = P.tgt j → α i ≤ β j

/-- Deleted events of a corner. -/
def CornerDeleted {Lab : Type u} (P : PomsetData Lab)
    (α : Fin P.srcLen → Status) (β : Fin P.tgtLen → Status) : Set (Fin P.n) :=
  { e | (∃ i : Fin P.srcLen, P.src i = e ∧ α i = Status.one) ∨
        (∃ j : Fin P.tgtLen, P.tgt j = e ∧ β j = Status.zero) }

/-- Retained events of a corner. -/
def CornerKept {Lab : Type u} (P : PomsetData Lab)
    (α : Fin P.srcLen → Status) (β : Fin P.tgtLen → Status) : Type _ :=
  { e : Fin P.n // e ∉ CornerDeleted P α β }

end CounterFreeHDA
