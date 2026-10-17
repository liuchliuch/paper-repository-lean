import Paper19.Coding
import Mathlib.Order.WellFoundedSet
import Mathlib.Order.Minimal

/-!
# Lemma 2: Dickson bases and levelwise decidability of `Ext(S)_n`
-/

namespace Paper19

open scoped symmDiff

/-- Upward closure of `U_ρ`. -/
theorem Urho_upward (T : Tree) {n : ℕ} (ρ : BinVec n) :
    ∀ ⦃u v : BoundVec n⦄, u ∈ Urho T ρ → u ≤ v → v ∈ Urho T ρ := by
  intro u v hu hv
  obtain ⟨g, hg, heq⟩ := hu
  have heq : encodeBound ρ u = List.ofFn (fun j : Fin n => g j) := by
    simpa using heq
  have hcoord (i : Fin n) : 2 * u i + (if ρ i then 1 else 0) = g i := by
    have h := congrArg (fun l : List ℕ => l.getD i 0) heq
    simpa [encodeBound, List.getD_eq_getElem, i.is_lt] using h
  let b : Stream := fun i => if hi : i < n then v ⟨i, hi⟩ else streamBounds g i
  have hQT := isQT_of_STree_path hg
  have hb : ∀ i, streamBounds g i ≤ b i := by
    intro i
    by_cases hi : i < n
    · have hc := hcoord ⟨i, hi⟩
      have hu : streamBounds g i = u ⟨i, hi⟩ := by
        dsimp [streamBounds]
        rw [← hc]
        cases hr : ρ ⟨i, hi⟩ <;> simp [hr] <;> omega
      simpa [b, hi, hu] using hv ⟨i, hi⟩
    · simp [b, hi]
  have hnew : IsQT T (streamBits g) b := by
    intro i
    exact RT.monotone (ofFn_isPrefix (hb i)) (hQT i)
  refine ⟨pairStream (streamBits g) b, pairStream_path hnew, ?_⟩
  simp only [encodeBound_length]
  apply List.ext_getElem
  · simp [encodeBound]
  · intro i hi hi'
    have hi : i < n := by simpa using hi'
    have hc := hcoord ⟨i, hi⟩
    have hr : streamBits g i = ρ ⟨i, hi⟩ := by
      dsimp [streamBits]
      rw [← hc]
      cases hr : ρ ⟨i, hi⟩ <;> simp [hr] <;> omega
    simp [encodeBound, pairStream, b, hi, hr]

/-- Minimal elements of a PWO set form a finite set. -/
theorem minimal_finite {α : Type*} [PartialOrder α] {s : Set α} (hpwo : Set.IsPWO s) :
    Set.Finite {m | Minimal (· ∈ s) m} := by
  classical
  by_contra hi
  have hiInf : Set.Infinite {m | Minimal (· ∈ s) m} := by
    intro hf; exact hi hf
  let e : ℕ ↪ {m | Minimal (· ∈ s) m} := hiInf.natEmbedding _
  set f : ℕ → α := fun k => (e k : α) with hfdef
  have hmem : ∀ k : ℕ, f k ∈ s := by
    intro k
    show ((e k : α) ∈ s)
    exact (e k).2.1
  obtain ⟨g, hg⟩ := hpwo.exists_monotone_subseq (f := f) hmem
  have hle : f (g 0) ≤ f (g 1) := hg (Nat.zero_le 1)
  have hmin0 : Minimal (· ∈ s) (f (g 0)) := by
    rw [hfdef]; exact (e (g 0)).2
  have hmin1 : Minimal (· ∈ s) (f (g 1)) := by
    rw [hfdef]; exact (e (g 1)).2
  have hbeq : f (g 1) = f (g 0) := hmin1.eq_of_ge hmin0.1 hle
  have hcon : e (g 0) = e (g 1) := by
    have h0 : f (g 0) = (e (g 0) : α) := by rw [hfdef]
    have h1 : f (g 1) = (e (g 1) : α) := by rw [hfdef]
    rw [h0, h1] at hbeq
    exact Subtype.ext hbeq.symm
  have hidx : g 0 = g 1 := e.injective hcon
  exact absurd (g.injective hidx) (by decide : (0:ℕ) ≠ 1)

/-- Dickson's lemma for `ω^n` in finite-basis form. -/
theorem dickson_basis {n : ℕ} (s : Set (BoundVec n))
    (hup : ∀ ⦃u v : BoundVec n⦄, u ∈ s → u ≤ v → v ∈ s) :
    ∃ M : Finset (BoundVec n), ∀ u, u ∈ s ↔ ∃ v ∈ M, v ≤ u := by
  classical
  have hpwo : Set.IsPWO s := Pi.isPWO s
  by_cases hs : s.Nonempty
  · have hmins_fin := minimal_finite hpwo
    refine ⟨hmins_fin.toFinset, fun u => ⟨fun hu => ?_, ?_⟩⟩
    · obtain ⟨v, hvle, hvmin⟩ := hpwo.exists_le_minimal hu
      exact ⟨v, hmins_fin.mem_toFinset.2 hvmin, hvle⟩
    · intro hex
      obtain ⟨v, hv, hle⟩ := hex
      have hvm : Minimal (· ∈ s) v := hmins_fin.mem_toFinset.1 hv
      exact hup hvm.1 hle
  · refine ⟨∅, fun u => ⟨fun hu => ?_, fun hex => ?_⟩⟩
    · exact absurd (⟨u, hu⟩ : s.Nonempty) hs
    · obtain ⟨v, hv, _⟩ := hex
      simp at hv

/-- Finite-basis characterization of `U_ρ` (Equation (2)). -/
theorem Urho_basis (T : Tree) {n : ℕ} (ρ : BinVec n) :
    ∃ M : Finset (BoundVec n),
      ∀ u, u ∈ Urho T ρ ↔ ∃ v ∈ M, ∀ j : Fin n, v j ≤ u j := by
  obtain ⟨M, hM⟩ := dickson_basis (Urho T ρ) (Urho_upward T ρ)
  exact ⟨M, fun u => by simpa [BoundVec.le_def] using hM u⟩

/-- For each fixed `n`, `Ext(S)_n` is decidable (nonuniformly in `n`). -/
theorem lemma2_ext_decidable (T : Tree) (n : ℕ) :
    ∃ dec : Node → Bool,
      ∀ σ, σ ∈ extLevel (STree T) n ↔ dec σ = true := by
  classical
  choose M hM using (fun ρ : BinVec n => Urho_basis T ρ)
  let dec : Node → Bool := fun σ =>
    if hlen : σ.length = n then
      decide (∃ v ∈ M (fun j => bitsOf σ ⟨j, by omega⟩),
        ∀ j : Fin n, v j ≤ quotsOf σ ⟨j, by omega⟩)
    else false
  refine ⟨dec, ?_⟩
  intro σ
  by_cases hlen : σ.length = n
  · have henc : encodeBound (fun j : Fin n => bitsOf σ ⟨j, by omega⟩)
        (fun j : Fin n => quotsOf σ ⟨j, by omega⟩) = σ := by
      apply List.ext_getElem
      · simpa using hlen.symm
      · intro i hi hi'
        simp only [encodeBound, List.getElem_ofFn, bitsOf, quotsOf,
          List.get_eq_getElem]
        have hm := Nat.mod_lt σ[i] (by decide : 0 < 2)
        by_cases hp : σ[i] % 2 = 1 <;> simp [hp] <;> omega
    have hiff := hM (fun j : Fin n => bitsOf σ ⟨j, by omega⟩)
      (fun j : Fin n => quotsOf σ ⟨j, by omega⟩)
    change Tree.IsExtendible (STree T) _ ↔ _ at hiff
    rw [henc] at hiff
    simp only [dec, dif_pos hlen, decide_eq_true_eq]
    rw [← hiff]
    constructor
    · exact fun h => h.2.2
    · intro h
      refine ⟨?_, hlen, h⟩
      obtain ⟨f, hf, heq⟩ := h
      rw [heq]
      exact hf σ.length
  · simp [dec, hlen, extLevel]

end Paper19
