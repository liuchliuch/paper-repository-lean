import Paper19.Core

/-!
# Boolean groups `G_n` and the projection `π_n` (Section 3, Equation (3))
-/

namespace Paper19

open scoped symmDiff

variable {T : Tree}

/-! ## Boolean group operations -/

theorem symmDiff_cancel (F H : Finset Node) : (F ∆ H) ∆ H = F := by
  rw [symmDiff_assoc, symmDiff_self, symmDiff_bot]

theorem symmDiff_left_cancel (F G H : Finset Node) :
    F ∆ H = G ∆ H ↔ F = G := by
  constructor
  · intro h
    have h2 := congrArg (fun X : Finset Node => X ∆ H) h
    simpa [symmDiff_cancel] using h2
  · intro h
    rw [h]

theorem empty_symmDiff_fin (H : Finset Node) : (∅ : Finset Node) ∆ H = H := by
  ext a
  simp [Finset.mem_symmDiff]

theorem symmDiff_involutive (H : Finset Node) :
    Function.Involutive (fun F : Finset Node => F ∆ H) :=
  fun F => symmDiff_cancel F H

def GMem (T : Tree) (n : ℕ) (F : Finset Node) : Prop :=
  ∀ σ ∈ F, σ ∈ level (STree T) n

theorem GMem_empty (T : Tree) (n : ℕ) : GMem T n ∅ :=
  fun σ hσ => absurd hσ (Finset.notMem_empty σ)

theorem GMem_symmDiff {T : Tree} {n : ℕ} {F G : Finset Node}
    (hF : GMem T n F) (hG : GMem T n G) : GMem T n (F ∆ G) := by
  intro σ hσ
  rcases Finset.mem_symmDiff.1 hσ with h | h
  · exact hF σ h.1
  · exact hG σ h.1

theorem GMem_singleton {T : Tree} {n : ℕ} {σ : Node}
    (h : σ ∈ level (STree T) n) : GMem T n ({σ} : Finset Node) := by
  intro τ hτ
  have : τ = σ := by simpa using hτ
  rw [this]
  exact h

def LenN1 (n : ℕ) (F : Finset Node) : Prop :=
  ∀ τ ∈ F, τ.length = n + 1

theorem LenN1_empty (n : ℕ) : LenN1 n (∅ : Finset Node) :=
  fun τ hτ => absurd hτ (Finset.notMem_empty τ)

theorem LenN1_symmDiff {n : ℕ} {F G : Finset Node}
    (hF : LenN1 n F) (hG : LenN1 n G) : LenN1 n (F ∆ G) := by
  intro τ hτ
  rcases Finset.mem_symmDiff.1 hτ with h | h
  · exact hF τ h.1
  · exact hG τ h.1

theorem GMem_len_succ {T : Tree} {n : ℕ} {F : Finset Node}
    (h : GMem T (n + 1) F) : LenN1 n F := by
  intro τ hτ
  exact (h τ hτ).2

/-! ## Parity of symmetric difference -/

theorem filter_symmDiff {α : Type} [DecidableEq α] (F G : Finset α)
    (p : α → Prop) [DecidablePred p] :
    (F ∆ G).filter p = (F.filter p) ∆ (G.filter p) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_symmDiff]
  by_cases hp : p a <;> simp [hp] <;> tauto

theorem odd_card_symmDiff {α : Type} [DecidableEq α] (F G : Finset α) :
    Odd (F ∆ G).card ↔ (Odd F.card ↔ Even G.card) := by
  have hEq : (F ∆ G : Finset α) = (F ∪ G) \ (F ∩ G) := by
    ext a
    simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_inter,
      Finset.mem_sdiff]
    tauto
  have hcard : (F ∆ G).card = F.card + G.card - 2 * (F ∩ G).card := by
    have h2 : (F ∪ G).card = F.card + G.card - (F ∩ G).card := by
      have := Finset.card_union_add_card_inter F G
      omega
    have h3 : F ∩ G ∩ (F ∪ G) = F ∩ G := by
      ext a; simp
    rw [hEq, Finset.card_sdiff, h3, h2]
    omega
  rw [hcard]
  have hpar : Odd (F.card + G.card - 2 * (F ∩ G).card) ↔ Odd (F.card + G.card) := by
    have hle : 2 * (F ∩ G).card ≤ F.card + G.card := by
      have h := Finset.card_union_add_card_inter F G
      have hsub : (F ∩ G).card ≤ (F ∪ G).card :=
        Finset.card_le_card (show (F ∩ G : Finset α) ⊆ F ∪ G from
          Finset.inter_subset_union)
      omega
    have heq : F.card + G.card - 2 * (F ∩ G).card + 2 * (F ∩ G).card
        = F.card + G.card := Nat.sub_add_cancel hle
    have he : Even (2 * (F ∩ G).card) := even_two_mul _
    rw [← heq, Nat.odd_add]
    simp [he]
  rw [hpar, Nat.odd_add]

theorem odd_card_symmDiff_xor {α : Type} [DecidableEq α] (F G : Finset α) :
    Odd (F ∆ G).card ↔
      (Odd F.card ∧ ¬ Odd G.card) ∨ (Odd G.card ∧ ¬ Odd F.card) := by
  rw [odd_card_symmDiff, Nat.not_odd_iff_even]
  constructor
  · intro h
    by_cases hF : Odd F.card
    · left
      exact ⟨hF, h.1 hF⟩
    · right
      have hG : Odd G.card := by
        by_contra hG
        exact hF (h.2 (Nat.not_odd_iff_even.1 hG))
      exact ⟨hG, hF⟩
  · rintro h
    rcases h with h | h
    · exact ⟨fun _ => h.2, fun _ => h.1⟩
    · exact ⟨fun hF => absurd hF h.2,
        fun hE => absurd h.1 (Nat.not_odd_iff_even.2 hE)⟩

/-! ## The projection `π_n = proj` -/

@[simp] theorem proj_empty (T : Tree) (n : ℕ) : proj T n ∅ = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro σ hσ
  have h1 : σ ∈ ((∅ : Finset Node).filter (fun τ => τ.length = n + 1)).image
      (fun τ => τ.take n) ∧
      Odd (((∅ : Finset Node).filter (fun τ => τ.take n = σ)).card) :=
    Finset.mem_filter.1 hσ
  have himg := h1.1
  obtain ⟨τ, hτ, _⟩ := Finset.mem_image.1 himg
  exact absurd hτ (Finset.notMem_empty τ)

theorem mem_proj_of_mem {T : Tree} {n : ℕ} {F : Finset Node} {σ : Node}
    (hσ : σ ∈ proj T n F) :
    σ.length = n ∧ Odd ((F.filter (fun τ => τ.take n = σ)).card) := by
  have h1 : σ ∈ ((F.filter (fun τ => τ.length = n + 1)).image (fun τ => τ.take n)) ∧
      Odd ((F.filter (fun τ => τ.take n = σ)).card) :=
    Finset.mem_filter.1 hσ
  have himg := h1.1
  have hodd := h1.2
  obtain ⟨τ, hτF, hτσ⟩ := Finset.mem_image.1 himg
  have hlenτ : τ.length = n + 1 := (Finset.mem_filter.1 hτF).2
  have htake : (τ.take n).length = n := by
    rw [List.length_take, hlenτ]
    omega
  subst hτσ
  exact ⟨htake, hodd⟩

theorem mem_proj_iff_odd {T : Tree} {n : ℕ} {F : Finset Node} {σ : Node}
    (hF : LenN1 n F) (hlen : σ.length = n) :
    σ ∈ proj T n F ↔ Odd ((F.filter (fun τ => τ.take n = σ)).card) := by
  constructor
  · intro h
    exact (mem_proj_of_mem h).2
  · intro hodd
    have hne : (F.filter (fun τ => τ.take n = σ)).Nonempty := by
      by_contra hempty
      have h0 : (F.filter (fun τ => τ.take n = σ)).card = 0 :=
        Finset.card_eq_zero.2 (by simpa using hempty)
      rw [h0] at hodd
      exact absurd hodd (by simp)
    obtain ⟨τ, hτ⟩ := hne
    have hτF : τ ∈ F := (Finset.mem_filter.1 hτ).1
    have hτσ : τ.take n = σ := (Finset.mem_filter.1 hτ).2
    have hlenτ : τ.length = n + 1 := hF τ hτF
    exact Finset.mem_filter.2
      ⟨Finset.mem_image.2 ⟨τ, Finset.mem_filter.2 ⟨hτF, hlenτ⟩, hτσ⟩, hodd⟩

theorem proj_symmDiff_of_len {T : Tree} {n : ℕ} {F G : Finset Node}
    (hF : LenN1 n F) (hG : LenN1 n G) :
    proj T n (F ∆ G) = proj T n F ∆ proj T n G := by
  have hD : LenN1 n (F ∆ G) := LenN1_symmDiff hF hG
  ext σ
  by_cases hlen : σ.length = n
  · have h1 : σ ∈ proj T n (F ∆ G) ↔
        Odd ((F ∆ G).filter (fun τ => τ.take n = σ)).card :=
      mem_proj_iff_odd hD hlen
    have h2 : σ ∈ proj T n F ↔
        Odd (F.filter (fun τ => τ.take n = σ)).card :=
      mem_proj_iff_odd hF hlen
    have h3 : σ ∈ proj T n G ↔
        Odd (G.filter (fun τ => τ.take n = σ)).card :=
      mem_proj_iff_odd hG hlen
    rw [h1, Finset.mem_symmDiff, h2, h3]
    have hfs : (F ∆ G).filter (fun τ => τ.take n = σ) =
        (F.filter (fun τ => τ.take n = σ)) ∆ (G.filter (fun τ => τ.take n = σ)) :=
      filter_symmDiff F G (fun τ => τ.take n = σ)
    rw [hfs, odd_card_symmDiff_xor]
  · rw [Finset.mem_symmDiff]
    constructor
    · intro h
      exact absurd (mem_proj_of_mem h).1 hlen
    · rintro (h | h)
      · exact absurd (mem_proj_of_mem h.1).1 hlen
      · exact absurd (mem_proj_of_mem h.1).1 hlen

theorem proj_hom {T : Tree} {n : ℕ} {F G : Finset Node}
    (hF : LenN1 n F) (hG : LenN1 n G) :
    proj T n (F ∆ G) = proj T n F ∆ proj T n G :=
  proj_symmDiff_of_len hF hG

theorem proj_singleton {T : Tree} {n : ℕ} {τ : Node}
    (hlen : τ.length = n + 1) :
    proj T n ({τ} : Finset Node) = {τ.take n} := by
  have htakeLen : (τ.take n).length = n := by
    rw [List.length_take, hlen]
    omega
  have h1 : LenN1 n ({τ} : Finset Node) := by
    intro ρ hρ
    have : ρ = τ := by simpa using hρ
    rw [this]
    exact hlen
  ext σ
  by_cases hσ : σ = τ.take n
  · subst hσ
    rw [Finset.mem_singleton]
    constructor
    · intro _; rfl
    · intro _
      have hfilter : (({τ} : Finset Node).filter (fun ρ => ρ.take n = τ.take n)) = {τ} := by
        ext ρ
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨rfl, _⟩; rfl
        · intro h
          have : ρ = τ := h
          subst this
          exact ⟨rfl, by simp⟩
      have hodd : Odd (({τ} : Finset Node).filter (fun ρ => ρ.take n = τ.take n)).card := by
        rw [hfilter, Finset.card_singleton]
        decide
      exact (mem_proj_iff_odd h1 htakeLen).2 hodd
  · rw [Finset.mem_singleton]
    constructor
    · intro h
      have hodd := (mem_proj_of_mem h).2
      have hfilter : (({τ} : Finset Node).filter (fun ρ => ρ.take n = σ)) = ∅ := by
        ext ρ
        simp only [Finset.mem_filter, Finset.mem_singleton, Finset.notMem_empty,
          iff_false, and_imp]
        rintro ⟨hρ, hρσ⟩
        have : ρ = τ := hρ
        subst this
        exact hσ hρσ.symm
      rw [hfilter] at hodd
      exact absurd hodd (by simp)
    · intro h
      exact absurd h (by simp [hσ])

theorem proj_trunc_succ {T : Tree} {f : Stream} {n : ℕ} :
    proj T n ({List.ofFn (fun i : Fin (n + 1) => f i)} : Finset Node) =
      {List.ofFn (fun i : Fin n => f i)} := by
  have hlen : (List.ofFn (fun i : Fin (n + 1) => f i)).length = n + 1 :=
    List.length_ofFn
  have htake : (List.ofFn (fun i : Fin (n + 1) => f i)).take n
      = List.ofFn (fun i : Fin n => f i) := by
    apply List.ext_getElem
    · rw [List.length_take, List.length_ofFn, List.length_ofFn]
      omega
    · intro i hi hi'
      rw [List.getElem_take, List.getElem_ofFn, List.getElem_ofFn]
  rw [proj_singleton hlen, htake]

/-! ## Coherent sequences -/

theorem CoherentIso.act_self {T : Tree} (c : CoherentIso T) (n : ℕ) (F : Finset Node) :
    c.act n (c.act n F) = F := by
  unfold CoherentIso.act
  rw [symmDiff_cancel]

theorem CoherentAut.act_self {T : Tree} (c : CoherentAut T) (n : ℕ) (F : Finset Node) :
    c.act n (c.act n F) = F := by
  unfold CoherentAut.act
  rw [symmDiff_cancel]

theorem CoherentIso.act_proj {T : Tree} (c : CoherentIso T) (n : ℕ)
    {F : Finset Node} (hF : LenN1 n F) (hh : LenN1 n (c.h (n + 1))) :
    proj T n (c.act (n + 1) F) = c.act n (proj T n F) := by
  unfold CoherentIso.act
  rw [proj_symmDiff_of_len hF hh, c.coherence n]

theorem CoherentIso.mem_length {T : Tree} (c : CoherentIso T) (n : ℕ)
    {σ : Node} (hσ : σ ∈ c.h n) : σ.length = n := by
  rcases n with _ | m
  · rw [c.root] at hσ
    have : σ = [] := by simpa using hσ
    rw [this]
    rfl
  · have h : c.h (m + 1) = proj T (m + 1) (c.h (m + 2)) := by
      rw [c.coherence (m + 1)]
    rw [h] at hσ
    exact (mem_proj_of_mem hσ).1

theorem CoherentAut.mem_length {T : Tree} (c : CoherentAut T) (n : ℕ)
    {σ : Node} (hσ : σ ∈ c.h n) : σ.length = n := by
  rcases n with _ | m
  · rw [c.root] at hσ
    exact absurd hσ (by simp)
  · have h : c.h (m + 1) = proj T (m + 1) (c.h (m + 2)) := by
      rw [c.coherence (m + 1)]
    rw [h] at hσ
    exact (mem_proj_of_mem hσ).1

end Paper19
