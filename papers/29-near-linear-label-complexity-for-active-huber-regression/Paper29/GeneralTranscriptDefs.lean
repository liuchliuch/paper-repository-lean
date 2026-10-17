import Paper29.GeneralInformation
import Paper29.SeedNonempty

noncomputable section
open MeasureTheory
open scoped ENNReal Classical BigOperators
namespace Paper29.GeneralTranscript

abbrev Slot (n : ℕ) (R : Type) := (Fin n × R) ⊕ Unit

def History (E : Type) (n : ℕ) (R : Type) : ℕ → Type
  | 0 => E
  | t+1 => History E n R t × Slot n R

instance historyMeasurableSpace {E R : Type} [MeasurableSpace E] [MeasurableSpace R] {n : ℕ} :
    (t : ℕ) → MeasurableSpace (History E n R t)
  | 0 => inferInstanceAs (MeasurableSpace E)
  | t+1 => @Prod.instMeasurableSpace (History E n R t) (Slot n R) (historyMeasurableSpace t) inferInstance

abbrev Choices (E : Type) (n : ℕ) (R : Type) := (t : ℕ) → History E n R t → (Fin n ⊕ Unit)

def fixedSlot {E R S : Type} {n : ℕ} (p : Choices E n R) (t : ℕ) (h : History E n R t)
    (sb : S × (Fin n → R)) : Slot n R :=
  match p t h with
  | .inl j => .inl (j,sb.2 j)
  | .inr _ => .inr ()

def history {Ω E R : Type} {n : ℕ} (p : Choices E n R) (seed : Ω → E) (responses : Ω → Fin n → R)
    (ω : Ω) : (t : ℕ) → History E n R t
  | 0 => seed ω
  | t+1 => (history p seed responses ω t,fixedSlot p t (history p seed responses ω t) ((),responses ω))

def active {E R : Type} {n : ℕ} (p : Choices E n R) (t : ℕ) (h : History E n R t) : ℕ :=
  if p t h=Sum.inr () then 0 else 1

def queryCount {Ω E R : Type} {n : ℕ} (p : Choices E n R) (seed : Ω → E)
    (responses : Ω → Fin n → R) (ω : Ω) : ℕ :=
  ∑ t∈Finset.range n,active p t (history p seed responses ω t)

def History.queried {E R : Type} {n : ℕ} : (t : ℕ) → History E n R t → List (Fin n)
  | 0,_ => []
  | t+1,h => History.queried t h.1 ++ match h.2 with
    | .inl z => [z.1]
    | .inr _ => []

def Fresh {E R : Type} {n : ℕ} (p : Choices E n R) : Prop :=
  ∀ t h j,p t h=Sum.inl j → j∉History.queried t h

def Absorbing {E R : Type} {n : ℕ} (p : Choices E n R) : Prop :=
  ∀ t h,p (t+1) (h,Sum.inr ())=Sum.inr ()

theorem measurable_fixedSlot {E R S : Type} [MeasurableSpace E] [MeasurableSpace R] [MeasurableSpace S]
    {n : ℕ} (p : Choices E n R) (t : ℕ) (h : History E n R t) :
    Measurable (fixedSlot (S:=S) p t h) := by
  unfold fixedSlot
  cases hp : p t h with
  | inl j =>
    exact measurable_inl.comp (measurable_const.prodMk
      ((measurable_pi_apply j : Measurable (fun b : Fin n → R => b j)).comp measurable_snd))
  | inr u => exact measurable_const

theorem measurable_joint_fixedSlot {E R S : Type} [MeasurableSpace E] [MeasurableSpace R] [MeasurableSpace S]
    {n : ℕ} (p : Choices E n R) (t : ℕ) (hp : Measurable (p t)) :
    Measurable (Function.uncurry (fixedSlot (S:=S) p t)) := by
  let f : (Fin n ⊕ Unit) × (S × (Fin n → R)) → Slot n R := fun z =>
    match z.1 with
    | .inl j => .inl (j,z.2.2 j)
    | .inr _ => .inr ()
  have hf : Measurable f := by
    apply measurable_from_prod_countable_right
    intro c
    dsimp only [f]
    cases c with
    | inl j => exact measurable_inl.comp (measurable_const.prodMk
        ((measurable_pi_apply j : Measurable (fun b : Fin n → R => b j)).comp measurable_snd))
    | inr u => exact measurable_const
  exact hf.comp ((hp.comp measurable_fst).prodMk measurable_snd)

theorem measurable_history {Ω E R : Type} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace R]
    {n : ℕ} (p : Choices E n R) (hp : ∀ t,Measurable (p t)) (seed : Ω → E)
    (responses : Ω → Fin n → R) (hs : Measurable seed) (hb : Measurable responses) (t : ℕ) :
    Measurable (fun ω => history p seed responses ω t) := by
  induction t with
  | zero => exact hs
  | succ t ih =>
    exact ih.prodMk ((measurable_joint_fixedSlot (S:=Unit) p t (hp t)).comp
      (ih.prodMk (measurable_const.prodMk hb)))

theorem measurable_active {E R : Type} [MeasurableSpace E] [MeasurableSpace R]
    {n : ℕ} (p : Choices E n R) (t : ℕ) (hp : Measurable (p t)) :
    Measurable (fun h => (active p t h : ℝ≥0∞)) := by
  have hs := hp (measurableSet_singleton (Sum.inr ()))
  have hh : Measurable (fun h => if p t h=Sum.inr () then (0:ℝ≥0∞) else 1) :=
    Measurable.ite hs measurable_const measurable_const
  simpa only [active,Nat.cast_ite,Nat.cast_zero,Nat.cast_one] using hh

/-- Activity counts the actual number of observed coordinate slots. -/
theorem queryCount_eq_history_length {Ω E R : Type} {n : ℕ} (p : Choices E n R)
    (seed : Ω → E) (responses : Ω → Fin n → R) (ω : Ω) (t : ℕ) :
    (∑ k∈Finset.range t,active p k (history p seed responses ω k)) =
      (History.queried t (history p seed responses ω t)).length := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Finset.sum_range_succ,ih]
    cases hp : p t (history p seed responses ω t) <;>
      simp [history,History.queried,fixedSlot,active,hp]

theorem history_nodup {Ω E R : Type} {n : ℕ} (p : Choices E n R) (hfresh : Fresh p)
    (seed : Ω → E) (responses : Ω → Fin n → R) (ω : Ω) (t : ℕ) :
    (History.queried t (history p seed responses ω t)).Nodup := by
  induction t with
  | zero => exact List.nodup_nil
  | succ t ih =>
    cases hp : p t (history p seed responses ω t) with
    | inl j =>
      have hh := ih.concat (hfresh t _ j hp)
      simpa only [history,History.queried,fixedSlot,hp,List.concat_eq_append] using hh
    | inr u => simpa [history,History.queried,fixedSlot,hp] using ih

/-- With freshness, the charged active slots are exactly the distinct rows. -/
theorem queryCount_eq_distinct {Ω E R : Type} {n : ℕ} (p : Choices E n R) (hfresh : Fresh p)
    (seed : Ω → E) (responses : Ω → Fin n → R) (ω : Ω) :
    queryCount p seed responses ω = (History.queried n (history p seed responses ω n)).toFinset.card := by
  rw [List.toFinset_card_of_nodup (history_nodup p hfresh seed responses ω n)]
  exact queryCount_eq_history_length p seed responses ω n

end Paper29.GeneralTranscript
