import Paper02.UpdateMachine
import Paper02.AmplifiedDecoderMachine

/-! # Sequential execution of an incoming update on every sketch copy -/
set_option synthInstance.maxSize 1024
noncomputable section

namespace Paper02.ReplicatedUpdateMachine
open Streaming

structure State (d R J ℓ K q : ℕ) [NeZero q] where
  index : Fin (R + 1)
  buffers : Fin R → CopyState J K q
  work : UpdateMachine.State d J ℓ K q
  deriving Fintype

variable {d R J ℓ K q : ℕ} [Fact q.Prime]

def step (seeds : Fin R → CopySeed J ℓ q) (i : Fin d) (δ : ZMod q)
    (s : State d R J ℓ K q) : State d R J ℓ K q :=
  if hi : s.index.val < R then
    if s.work.phase.val = 4 then
      let buffers := Function.update s.buffers ⟨s.index.val, hi⟩ s.work.buffer
      { index := ⟨s.index.val + 1, by omega⟩
        buffers := buffers
        work := if hn : s.index.val + 1 < R then UpdateMachine.initial (buffers ⟨s.index.val + 1, hn⟩) else s.work }
    else { s with work := UpdateMachine.step (seeds ⟨s.index.val, hi⟩) i δ s.work }
  else s

def initial (hR : 0 < R) (buffers : Fin R → CopyState J K q) : State d R J ℓ K q :=
  ⟨0, buffers, UpdateMachine.initial (buffers ⟨0, hR⟩)⟩

def Reaches (seeds : Fin R → CopySeed J ℓ q) (i : Fin d) (δ : ZMod q)
    (s t : State d R J ℓ K q) : Prop := Relation.ReflTransGen (fun a b => step seeds i δ a = b) s t

def prefixBuffers (before after : Fin R → CopyState J K q) (n : ℕ) : Fin R → CopyState J K q :=
  fun r => if r.val < n then after r else before r

lemma prefix_update (before after : Fin R → CopyState J K q) (r : Fin R) :
    Function.update (prefixBuffers before after r.val) r (after r) = prefixBuffers before after (r.val + 1) := by
  funext k
  by_cases hkr : k = r
  · subst k; simp [prefixBuffers]
  · rw [Function.update_of_ne hkr]
    have he : (k.val < r.val + 1) = (k.val < r.val) := propext (by
      have hne : k.val ≠ r.val := fun h => hkr (Fin.ext h)
      omega)
    simp only [prefixBuffers, he]

lemma lift_update (seeds : Fin R → CopySeed J ℓ q) (i : Fin d) (δ : ZMod q)
    (r : Fin R) (buffers : Fin R → CopyState J K q)
    {a c : UpdateMachine.State d J ℓ K q} (h : UpdateMachine.Reaches (seeds r) i δ a c) :
    Reaches seeds i δ ⟨⟨r.val, by omega⟩, buffers, a⟩ ⟨⟨r.val, by omega⟩, buffers, c⟩ := by
  apply Relation.ReflTransGen.lift' (fun w => State.mk ⟨r.val, by omega⟩ buffers w) _ h
  intro x y hxy
  by_cases hx : x.phase.val = 4
  · have he : x = y := by
      have hnot0 : ¬ x.phase.val = 0 := by omega
      have hnot1 : ¬ x.phase.val = 1 := by omega
      have hnot2 : ¬ x.phase.val = 2 := by omega
      have hnot3 : ¬ x.phase.val = 3 := by omega
      simpa only [UpdateMachine.step, if_neg hnot0, if_neg hnot1, if_neg hnot2, if_neg hnot3] using hxy
    rw [← he]
  · exact Relation.ReflTransGen.single (by
      simpa only [step, dif_pos r.isLt, if_neg hx] using congrArg (fun w => State.mk ⟨r.val, by omega⟩ buffers w) hxy)

/-- All copies process the update through the actual finite-register program;
only the updated persistent summary is then committed to its array slot. -/
theorem machine_correct (hR : 0 < R) (seeds : Fin R → CopySeed J ℓ q)
    (i : Fin d) (δ : ZMod q) (buffers : Fin R → CopyState J K q) :
    ∃ finish : State d R J ℓ K q,
      Reaches seeds i δ (initial hR buffers) finish ∧ finish.index.val = R ∧
      finish.buffers = (fun r => UpdateMachine.fieldUpdate (seeds r) i δ (buffers r)) := by
  let updated : Fin R → CopyState J K q := fun r => UpdateMachine.fieldUpdate (seeds r) i δ (buffers r)
  have walk : ∀ n (hn : n ≤ R), ∃ s : State d R J ℓ K q,
      Reaches seeds i δ (initial hR buffers) s ∧ s.index.val = n ∧
        s.buffers = prefixBuffers buffers updated n ∧
        (∀ h : n < R, s.work = UpdateMachine.initial (buffers ⟨n, h⟩)) := by
    intro n
    induction n with
    | zero =>
      intro hn
      refine ⟨initial hR buffers, Relation.ReflTransGen.refl, rfl, ?_, ?_⟩
      · funext r; simp [initial, prefixBuffers]
      · intro h; rfl
    | succ n ih =>
      intro hn
      have hnt : n < R := by omega
      obtain ⟨s, hr, hi, hb, hw⟩ := ih hnt.le
      let r : Fin R := ⟨n, hnt⟩
      have hu := lift_update seeds i δ r (prefixBuffers buffers updated n)
        (UpdateMachine.machine_correct (seeds r) i δ (buffers r)).1
      have hs : s = ⟨⟨n, by omega⟩, prefixBuffers buffers updated n, UpdateMachine.initial (buffers r)⟩ := by
        have hidx : s.index = ⟨n, by omega⟩ := Fin.ext hi
        cases s
        simp only [State.mk.injEq]
        exact ⟨hidx, hb, hw hnt⟩
      rw [hs] at hr
      have hp := hr.trans hu
      let t : State d R J ℓ K q :=
        step seeds i δ ⟨⟨n, by omega⟩, prefixBuffers buffers updated n, UpdateMachine.finish (updated r)⟩
      refine ⟨t, hp.tail rfl, ?_, ?_, ?_⟩
      · simp [t, step, hnt, UpdateMachine.finish]
      · simp only [t, step, dif_pos hnt, UpdateMachine.finish, if_pos rfl]
        exact prefix_update buffers updated r
      · intro hnext
        simp only [t, step, dif_pos hnt, UpdateMachine.finish, if_pos rfl, dif_pos hnext]
        congr 1
        rw [show Function.update (prefixBuffers buffers updated n) ⟨n, hnt⟩ (updated r) =
          prefixBuffers buffers updated (n + 1) from prefix_update buffers updated r]
        simp [prefixBuffers]
  obtain ⟨finish, hr, hi, hb, _⟩ := walk R (le_refl _)
  refine ⟨finish, hr, hi, ?_⟩
  rw [hb]
  funext r
  simp [prefixBuffers, r.isLt, updated]

open StreamingSpace WeightEval

def machineBits (d R J ℓ K q : ℕ) : ℕ :=
  registerBits (R + 1) + R * ((J + 1) * (2 * K + 1) * registerBits q) + UpdateMachine.machineBits d J ℓ K q

theorem machine_fits : FitsBits (State d R J ℓ K q) (machineBits d R J ℓ K q) := by
  let e : State d R J ℓ K q ≃ Fin (R + 1) × (Fin R → CopyState J K q) × UpdateMachine.State d J ℓ K q :=
    { toFun := fun s => (s.index, s.buffers, s.work)
      invFun := fun s => ⟨s.1, s.2.1, s.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcopy : FitsBits (CopyState J K q) ((J + 1) * (2 * K + 1) * registerBits q) := by
    have h := array_fits (J + 1) (summary_fits K q)
    simpa only [CopyState, Nat.mul_assoc] using h
  have hh := prod_fits (fin_fits (R + 1))
    (prod_fits (array_fits R hcopy) (UpdateMachine.machine_fits (d := d) (J := J) (ℓ := ℓ) (K := K) (q := q)))
  unfold FitsBits at *
  rw [Fintype.card_congr e]
  apply hh.trans_eq
  congr 1
  unfold machineBits
  omega

end Paper02.ReplicatedUpdateMachine
