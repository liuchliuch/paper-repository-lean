import Paper19.BooleanGroup
import Paper19.Chains

namespace Paper19

open scoped symmDiff
open Finset

variable {T : Tree}

/-! Groups `G_n` are those of `Paper19.BooleanGroup`. -/

theorem GMem_of_subset_ext {T : Tree} {n : ℕ} {F : Finset Node}
    (h : ∀ σ ∈ F, σ ∈ extLevel (STree T) n) : GMem T n F := by
  intro σ hσ
  obtain ⟨hmem, hlen, _⟩ := h σ hσ
  exact ⟨hmem, hlen⟩

/-! `proj` lemmas are those of `Paper19.BooleanGroup`. -/

theorem mem_proj_iff {T : Tree} {n : ℕ} {F : Finset Node} {σ : Node} :
    σ ∈ proj T n F ↔
      (∃ τ ∈ F, τ.length = n + 1 ∧ τ.take n = σ) ∧
        Odd ((F.filter (fun τ => τ.take n = σ)).card) := by
  simp only [proj, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨τ, hτ, htake⟩, hodd⟩
    obtain ⟨hτF, hlen⟩ := hτ
    exact ⟨⟨τ, hτF, hlen, htake⟩, hodd⟩
  · rintro ⟨⟨τ, hτF, hlen, htake⟩, hodd⟩
    exact ⟨⟨τ, ⟨hτF, hlen⟩, htake⟩, hodd⟩


/-! ## Stream prefixes -/

def streamPrefix (f : Stream) (m : ℕ) : Node :=
  List.ofFn (fun i : Fin m => f i)

@[simp] theorem streamPrefix_length (f : Stream) (m : ℕ) :
    (streamPrefix f m).length = m := by simp [streamPrefix]

theorem streamPrefix_take (f : Stream) (m k : ℕ) (h : m ≤ k) :
    (streamPrefix f k).take m = streamPrefix f m := by
  apply List.ext_getElem
  · simp [List.length_take, streamPrefix, min_eq_left h]
  · intro i hi1 hi2
    rw [List.getElem_take]
    simp [streamPrefix]

theorem streamPrefix_prefix (f : Stream) {m k : ℕ} (h : m ≤ k) :
    streamPrefix f m <+: streamPrefix f k := by
  have htake := streamPrefix_take f m k h
  rw [← htake]
  exact List.take_prefix m (streamPrefix f k)

theorem isPath_streamPrefix {T : Tree} {f : Stream} (hf : Tree.IsPath T f) (m : ℕ) :
    T.mem (streamPrefix f m) := by
  simpa [streamPrefix] using hf m

theorem isExtendible_of_eq_prefix {T : Tree} {f : Stream} (hf : Tree.IsPath T f)
    {σ : Node} (hσ : σ = streamPrefix f σ.length) :
    Tree.IsExtendible T σ := ⟨f, hf, by simpa [streamPrefix] using hσ⟩

/-! ## Child relation on `G_n` and lift sequences -/

def IsChildG {T : Tree} (x y : Dom T) : Prop :=
  ∃ (n : ℕ) (F E : Finset Node),
    x = Dom.vec n F ∧ y = Dom.vec (n + 1) E ∧ proj T n E = F ∧
      GMem T n F ∧ GMem T (n + 1) E

def HasInfiniteLiftG {T : Tree} (F : Dom T) : Prop :=
  ∃ g : ℕ → Dom T, g 0 = F ∧ ∀ k : ℕ, IsChildG (g k) (g (k + 1))

/-- An infinite lift of `F ∈ G_n` as a sequence of group elements (Eq. (3) coherence). -/
def LiftSeq (T : Tree) (n : ℕ) (F : Finset Node) : Prop :=
  ∃ E : ℕ → Finset Node, E 0 = F ∧
    (∀ k, proj T (n + k) (E (k + 1)) = E k) ∧
    (∀ k, GMem T (n + k) (E k))

theorem liftSeq_of_hasInfiniteLiftG {T : Tree} {n : ℕ} {F : Finset Node}
    (h : HasInfiniteLiftG (Dom.vec n F : Dom T)) : LiftSeq T n F := by
  obtain ⟨g, hg0, hg⟩ := h
  have isVec : ∀ k, ∃ (H : Finset Node), g k = Dom.vec (n + k) H := by
    intro k
    induction k with
    | zero =>
      refine ⟨F, ?_⟩
      rw [hg0]
      simp
    | succ k ih =>
      obtain ⟨H, hH⟩ := ih
      obtain ⟨n', F', E', hx, hy, _, _, _⟩ := hg k
      refine ⟨E', ?_⟩
      rw [hy]
      have hlevel : n' + 1 = n + (k + 1) := by
        rw [hH] at hx
        cases hx
        omega
      rw [hlevel]
  choose! H hH using isVec
  refine ⟨H, ?_, ?_, ?_⟩
  · have h0 := hH 0
    rw [hg0] at h0
    cases h0
    rfl
  · intro k
    obtain ⟨n', F', E', hx, hy, hproj, _, _⟩ := hg k
    have hk := hH k
    rw [hx] at hk
    cases hk
    have hk1 := hH (k + 1)
    rw [hy] at hk1
    cases hk1
    exact hproj
  · intro k
    by_cases hk : k = 0
    · subst hk
      obtain ⟨n', F', E', hx, hy, _, hGF, _⟩ := hg 0
      have h0 := hH 0
      -- h0 : g 0 = Dom.vec (n+0) (H 0)
      -- hx : g 0 = Dom.vec n' F'
      have key : Dom.vec (n + 0) (H 0) = Dom.vec n' F' := h0.symm.trans hx
      cases key
      -- goal: GMem T (n+0) F'; hGF : GMem T n' F' with n' = n+0
      simpa using hGF
    · rcases hg (k - 1) with ⟨nb, Fb, Eb, hxb, hyb, _, _, hGEb⟩
      have hshape := hH (k - 1)
      rw [hxb] at hshape
      cases hshape
      have hk1 : (k - 1) + 1 = k := by omega
      rw [hk1] at hyb
      have hk' := hH k
      rw [hyb] at hk'
      -- hk' : Dom.vec (n+(k-1)+1) Eb = Dom.vec (n+k) (H k)
      have hFE : Eb = H k ∧ n + (k - 1) + 1 = n + k := by
        injection hk' with hlev hfin
        exact ⟨hfin, hlev⟩
      rw [hFE.1, hFE.2] at hGEb
      exact hGEb

theorem hasInfiniteLiftG_of_liftSeq {T : Tree} {n : ℕ} {F : Finset Node}
    (h : LiftSeq T n F) : HasInfiniteLiftG (Dom.vec n F : Dom T) := by
  obtain ⟨E, h0, hp, hg⟩ := h
  refine ⟨fun k => Dom.vec (n + k) (E k), ?_, ?_⟩
  · show Dom.vec (n + 0) (E 0) = Dom.vec n F
    rw [h0]
    simp
  · intro k
    exact ⟨n + k, E k, E (k + 1), rfl, rfl, hp k, hg k, hg (k + 1)⟩

theorem exists_child_of_mem_proj {T : Tree} {n : ℕ} {E F : Finset Node}
    (hproj : proj T n E = F) (hGE : GMem T (n + 1) E)
    {τ : Node} (hτ : τ ∈ F) :
    ∃ ρ, ρ ∈ E ∧ ρ.length = n + 1 ∧ τ <+: ρ ∧ (STree T).mem ρ := by
  have h : τ ∈ proj T n E := by rw [hproj]; exact hτ
  obtain ⟨⟨ρ, hρE, hlen, htake⟩, _⟩ := mem_proj_iff.1 h
  refine ⟨ρ, hρE, hlen, ?_, (hGE ρ hρE).1⟩
  have : τ = ρ.take n := htake.symm
  rw [this]
  exact List.take_prefix n ρ


/-! ## Lemma 6 ⇒: extendible support yields an infinite lift -/

theorem liftSeq_of_subset_ext {T : Tree} {n : ℕ} {F : Finset Node}
    (hF : ∀ σ ∈ F, σ ∈ extLevel (STree T) n) :
    LiftSeq T n F := by
  classical
  have path : ∀ σ ∈ F, {f : Stream // Tree.IsPath (STree T) f ∧ σ = streamPrefix f σ.length} := by
    intro σ hσF
    have hex := (hF σ hσF).2.2
    refine ⟨Classical.choose hex, (Classical.choose_spec hex).1, ?_⟩
    have hσeq := (Classical.choose_spec hex).2
    simpa [streamPrefix] using hσeq
  let s : Node → Stream := fun σ => if h : σ ∈ F then (path σ h).1 else fun _ => 0
  have s_path : ∀ σ ∈ F, Tree.IsPath (STree T) (s σ) := by
    intro σ hσF
    have h : s σ = (path σ hσF).1 := by simp [s, hσF]
    rw [h]; exact (path σ hσF).2.1
  have s_prefix : ∀ σ ∈ F, σ = streamPrefix (s σ) σ.length := by
    intro σ hσF
    have h : s σ = (path σ hσF).1 := by simp [s, hσF]
    rw [h]; exact (path σ hσF).2.2
  have s_len : ∀ σ ∈ F, σ.length = n := fun σ hσF => (hF σ hσF).2.1
  let E : ℕ → Finset Node := fun k => F.image (fun σ => streamPrefix (s σ) (n + k))
  refine ⟨E, ?_, ?_, ?_⟩
  · -- E 0 = F
    ext ρ
    show ρ ∈ F.image (fun σ => streamPrefix (s σ) (n + 0)) ↔ ρ ∈ F
    constructor
    · intro hρ
      obtain ⟨σ, hσF, hσρ⟩ := Finset.mem_image.1 hρ
      have e1 : streamPrefix (s σ) (n + 0) = streamPrefix (s σ) n := by simp
      have e2 : streamPrefix (s σ) n = σ := by
        have h := s_prefix σ hσF
        have hl := s_len σ hσF
        conv_lhs => rw [← hl]
        exact h.symm
      have e3 : σ = ρ := by
        rw [e1, e2] at hσρ
        exact hσρ
      rw [← e3]
      exact hσF
    · intro hρF
      apply Finset.mem_image.2
      refine ⟨ρ, hρF, ?_⟩
      show streamPrefix (s ρ) (n + 0) = ρ
      have e1 : streamPrefix (s ρ) (n + 0) = streamPrefix (s ρ) n := by simp
      have e2 : streamPrefix (s ρ) n = streamPrefix (s ρ) ρ.length := by
        rw [← s_len ρ hρF]
      rw [e1, e2]
      exact (s_prefix ρ hρF).symm
  · -- proj coherence
    intro k
    ext ρ
    have hmem : ρ ∈ proj T (n + k) (E (k + 1)) ↔
        (∃ τ ∈ E (k + 1), τ.length = n + k + 1 ∧ τ.take (n + k) = ρ) ∧
          Odd ((E (k + 1)).filter (fun τ => τ.take (n + k) = ρ)).card :=
      mem_proj_iff
    rw [hmem]
    constructor
    · rintro ⟨⟨τ, hτ, hlenτ, htake⟩, _⟩
      simp only [E, mem_image] at hτ
      obtain ⟨σ, hσF, rfl⟩ := hτ
      have hρ : streamPrefix (s σ) (n + k) = ρ := by
        rw [← htake]
        exact (streamPrefix_take (s σ) (n + k) (n + (k + 1)) (by omega)).symm
      apply Finset.mem_image.2
      exact ⟨σ, hσF, hρ⟩
    · intro hρk
      obtain ⟨σ, hσF, hσρ⟩ := Finset.mem_image.1 hρk
      refine ⟨⟨streamPrefix (s σ) (n + (k + 1)), ?_, streamPrefix_length _ _, ?_⟩, ?_⟩
      · apply Finset.mem_image.2
        exact ⟨σ, hσF, rfl⟩
      · have ht := streamPrefix_take (s σ) (n + k) (n + (k + 1)) (by omega)
        rw [ht, hσρ]
      · have hinj : ∀ σ' ∈ F,
            streamPrefix (s σ') (n + k) = streamPrefix (s σ) (n + k) → σ' = σ := by
          intro σ' hσ' heq
          have hpre : streamPrefix (s σ') n = streamPrefix (s σ) n := by
            have a : streamPrefix (s σ') n <+: streamPrefix (s σ') (n + k) :=
              streamPrefix_prefix (s σ') (by omega)
            have b : streamPrefix (s σ) n <+: streamPrefix (s σ) (n + k) :=
              streamPrefix_prefix (s σ) (by omega)
            have a' : streamPrefix (s σ') n <+: streamPrefix (s σ) (n + k) := by
              rw [← heq]; exact a
            have ha : streamPrefix (s σ') n = (streamPrefix (s σ) (n + k)).take n := by
              simpa [streamPrefix] using List.prefix_iff_eq_take.1 a'
            have hb : streamPrefix (s σ) n = (streamPrefix (s σ) (n + k)).take n := by
              simpa [streamPrefix] using List.prefix_iff_eq_take.1 b
            exact ha.trans hb.symm
          have e1 : σ' = streamPrefix (s σ') n := by
            have h := s_prefix σ' hσ'
            have hl := s_len σ' hσ'
            conv_rhs => rw [← hl]
            exact h
          have e2 : σ = streamPrefix (s σ) n := by
            have h := s_prefix σ hσF
            have hl := s_len σ hσF
            conv_rhs => rw [← hl]
            exact h
          rw [e1, e2, hpre]
        have hfib : (E (k + 1)).filter (fun η => η.take (n + k) = ρ) =
            {streamPrefix (s σ) (n + (k + 1))} := by
          ext η
          simp only [E, mem_filter, mem_image, mem_singleton]
          constructor
          · rintro ⟨⟨σ', hσ', rfl⟩, htake'⟩
            have hpr : streamPrefix (s σ') (n + k) = ρ := by
              rwa [streamPrefix_take (s σ') (n + k) (n + (k + 1)) (by omega)] at htake'
            have hσeq : σ' = σ := hinj σ' hσ' (by rw [hpr, hσρ])
            subst hσeq
            rfl
          · rintro rfl
            exact ⟨⟨σ, hσF, rfl⟩,
              (streamPrefix_take (s σ) (n + k) (n + (k + 1)) (by omega)).trans hσρ⟩
        have hcard : ((E (k + 1)).filter (fun η => η.take (n + k) = ρ)).card = 1 := by
          rw [hfib]; simp
        rw [hcard]; decide
  · intro k ρ hρ
    obtain ⟨σ, hσF, hσρ⟩ := Finset.mem_image.1 hρ
    subst hσρ
    exact ⟨isPath_streamPrefix (s_path σ hσF) (n + k), streamPrefix_length _ _⟩

theorem hasInfiniteLiftG_of_subset_ext {T : Tree} {n : ℕ} {F : Finset Node}
    (hF : ∀ σ ∈ F, σ ∈ extLevel (STree T) n) :
    HasInfiniteLiftG (Dom.vec n F : Dom T) :=
  hasInfiniteLiftG_of_liftSeq (liftSeq_of_subset_ext hF)

/-- Lemma 6 (⇒), as in Spec, for the paper's lift relation. -/
theorem lemma6_infiniteLift_of_ext {T : Tree} {n : ℕ} {F : Finset Node}
    (hF : ∀ σ ∈ F, σ ∈ extLevel (STree T) n) :
    HasInfiniteLiftG (Dom.vec n F : Dom T) :=
  hasInfiniteLiftG_of_subset_ext hF

/-- Extract an infinite path of `S` through `σ` from a lift sequence. -/
theorem ext_of_liftSeq {T : Tree} {n : ℕ} {F : Finset Node}
    (h : LiftSeq T n F) {σ : Node} (hσ : σ ∈ F) :
    Tree.IsExtendible (STree T) σ := by
  classical
  obtain ⟨E, h0, hp, hG⟩ := h
  have hσ0 : σ ∈ E 0 := by rwa [h0]
  have step (k : ℕ) (τ : {τ : Node // τ ∈ E k}) :
      ∃ ρ : {ρ : Node // ρ ∈ E (k + 1)}, τ.val <+: ρ.val := by
    obtain ⟨ρ, hρ, hlen, hpre, hm⟩ :=
      exists_child_of_mem_proj (hp k) (hG (k + 1)) τ.property
    exact ⟨⟨ρ, hρ⟩, hpre⟩
  let a : (k : ℕ) → {τ : Node // τ ∈ E k} := fun k =>
    Nat.rec (motive := fun k => {τ : Node // τ ∈ E k})
      ⟨σ, hσ0⟩ (fun k τ => Classical.choose (step k τ)) k
  have ha (k : ℕ) : (a k).val <+: (a (k + 1)).val :=
    Classical.choose_spec (step k (a k))
  have hlen (k : ℕ) : (a k).val.length = n + k := (hG k _ (a k).property).2
  have hm (k : ℕ) : (STree T).mem (a k).val := (hG k _ (a k).property).1
  refine ⟨chainStream (fun k => (a k).val),
    chainStream_path (STree T) _ hlen ha hm, ?_⟩
  have hn : σ.length = n := by simpa [a] using hlen 0
  simpa [a, hn] using (chainStream_prefix (fun k => (a k).val) hlen ha 0).symm

/-- Lemma 6 (⇐): an infinite lift forces every member of `F` to be extendible. -/
theorem lemma6_ext_of_infiniteLift {T : Tree} {n : ℕ} {F : Finset Node}
    (h : HasInfiniteLiftG (Dom.vec n F : Dom T)) :
    ∀ σ ∈ F, σ ∈ extLevel (STree T) n := by
  intro σ hσ
  have hseq := liftSeq_of_hasInfiniteLiftG h
  refine ⟨?_, ?_, ext_of_liftSeq hseq hσ⟩
  · obtain ⟨E, h0, _, hG⟩ := hseq
    exact (hG 0 σ (by rw [h0]; exact hσ)).1
  · obtain ⟨E, h0, _, hG⟩ := hseq
    exact (hG 0 σ (by rw [h0]; exact hσ)).2

end Paper19
