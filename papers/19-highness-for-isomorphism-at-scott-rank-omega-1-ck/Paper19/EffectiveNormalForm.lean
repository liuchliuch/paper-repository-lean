import Paper19.NormalForm
import Mathlib.Computability.Halting

namespace Paper19

/-- Finite conjunctions with arbitrary fixed constants preserve primitive
recursiveness. The constants need not be uniformly obtainable. -/
theorem primrec_finset_all {α ι : Type} [Primcodable α] (s : Finset ι)
    (p : ι → α → Prop) (h : ∀ i ∈ s, PrimrecPred (p i)) :
    PrimrecPred (fun a => ∀ i ∈ s, p i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨inferInstance, by simpa using (Primrec.const true : Primrec (fun _ : α => true))⟩
  | @insert i s hi ih =>
    exact ((h i (by simp)).and (ih (fun j hj => h j (by simp [hj])))).of_eq (by simp)

theorem primrec_finset_any {α ι : Type} [Primcodable α] (s : Finset ι)
    (p : ι → α → Prop) (h : ∀ i ∈ s, PrimrecPred (p i)) :
    PrimrecPred (fun a => ∃ i ∈ s, p i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨inferInstance, by simpa using (Primrec.const false : Primrec (fun _ : α => false))⟩
  | @insert i s hi ih =>
    exact ((h i (by simp)).or (ih (fun j hj => h j (by simp [hj])))).of_eq (by simp)

/-- The finite arithmetic test associated to a basis vector. -/
def PatternTest {n : ℕ} (ρ : BinVec n) (v : BoundVec n) (σ : Node) : Prop :=
  σ.length = n ∧ ∀ i : Fin n,
    σ.getD i 0 % 2 = (if ρ i then 1 else 0) ∧ v i ≤ σ.getD i 0 / 2

theorem pattern_primrec {n : ℕ} (ρ : BinVec n) (v : BoundVec n) :
    PrimrecPred (PatternTest ρ v) := by
  have hlen : PrimrecPred (fun σ : Node => σ.length = n) :=
    Primrec.eq.comp Primrec.list_length (Primrec.const n)
  have hall : PrimrecPred (fun σ : Node => ∀ i : Fin n,
      σ.getD i 0 % 2 = (if ρ i then 1 else 0) ∧ v i ≤ σ.getD i 0 / 2) := by
    apply (primrec_finset_all (Finset.univ : Finset (Fin n))
      (fun i (σ : Node) => σ.getD i 0 % 2 = (if ρ i then 1 else 0) ∧
        v i ≤ σ.getD i 0 / 2) ?_).of_eq (by simp)
    intro i _
    have hg : Primrec (fun σ : Node => σ.getD i 0) :=
      (Primrec.list_getD 0).comp Primrec.id (Primrec.const i.val)
    exact (Primrec.eq.comp (Primrec.nat_mod.comp hg (Primrec.const 2))
      (Primrec.const (if ρ i then 1 else 0))).and
      (Primrec.nat_le.comp (Primrec.const (v i)) (Primrec.nat_div.comp hg (Primrec.const 2)))
  exact hlen.and hall

/-- This is actual primitive-recursive levelwise extendibility, rather than
mere classical decidability of an arbitrary set. -/
theorem lemma2_ext_primrec (T : Tree) (n : ℕ) :
    PrimrecPred (fun σ : Node => σ ∈ extLevel (STree T) n) := by
  classical
  choose M hM using (fun ρ : BinVec n => Urho_basis T ρ)
  have hp : PrimrecPred (fun σ : Node =>
      ∃ ρ ∈ (Finset.univ : Finset (BinVec n)), ∃ v ∈ M ρ, PatternTest ρ v σ) :=
    primrec_finset_any Finset.univ _ (fun ρ _ =>
      primrec_finset_any (M ρ) _ (fun v _ => pattern_primrec ρ v))
  apply hp.of_eq
  intro σ
  constructor
  · rintro ⟨ρ, _, v, hv, hlen, htest⟩
    let u : BoundVec n := fun i => σ.getD i 0 / 2
    have hu : u ∈ Urho T ρ := (hM ρ u).mpr ⟨v, hv, fun i => (htest i).2⟩
    have henc : encodeBound ρ u = σ := by
      apply List.ext_getElem
      · simpa using hlen.symm
      · intro i hi hi'
        have hin : i < n := by simpa [encodeBound] using hi
        have hd : σ.getD i 0 = σ[i] := List.getD_eq_getElem _ 0 hi'
        have ht := (htest ⟨i, hin⟩).1
        simp only [encodeBound, List.getElem_ofFn, u]
        rw [hd] at ht ⊢
        omega
    have hex : (STree T).IsExtendible σ := by simpa [Urho, henc] using hu
    refine ⟨?_, hlen, hex⟩
    obtain ⟨f, hf, heq⟩ := hex
    rw [heq]; exact hf σ.length
  · rintro ⟨hm, hlen, hex⟩
    let ρ : BinVec n := fun i => decide (σ.getD i 0 % 2 = 1)
    let u : BoundVec n := fun i => σ.getD i 0 / 2
    have hbit (i : Fin n) : σ.getD i 0 % 2 = (if ρ i then 1 else 0) := by
      have ht := Nat.mod_lt (σ.getD i 0) (by decide : 0 < 2)
      simp only [ρ]
      split_ifs <;> simp_all <;> omega
    have henc : encodeBound ρ u = σ := by
      apply List.ext_getElem
      · simpa using hlen.symm
      · intro i hi hi'
        have hin : i < n := by simpa [encodeBound] using hi
        have hd : σ.getD i 0 = σ[i] := List.getD_eq_getElem _ 0 hi'
        have ht := hbit ⟨i, hin⟩
        simp only [encodeBound, List.getElem_ofFn, u]
        rw [hd] at ht ⊢
        omega
    have hu : u ∈ Urho T ρ := by simpa [Urho, henc] using hex
    obtain ⟨v, hv, hvu⟩ := (hM ρ u).mp hu
    exact ⟨ρ, Finset.mem_univ _, v, hv, hlen, fun i => ⟨hbit i, hvu i⟩⟩

end Paper19
