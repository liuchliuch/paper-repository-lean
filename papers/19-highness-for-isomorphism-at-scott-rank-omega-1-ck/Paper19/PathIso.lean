import Paper19.IsoChar
import Paper19.FiniteOperations

/-!
# Lemma 5: paths and isomorphisms compute one another (Section 3)
-/

namespace Paper19

open scoped symmDiff

variable {T : Tree}

/-! ## Truncations of a stream -/

def trunc (f : Stream) (n : ℕ) : Node :=
  List.ofFn (fun i : Fin n => f i)

@[simp] theorem trunc_zero (f : Stream) : trunc f 0 = [] :=
  List.ofFn_zero

theorem trunc_length (f : Stream) (n : ℕ) : (trunc f n).length = n :=
  List.length_ofFn

theorem trunc_take (f : Stream) (n : ℕ) : (trunc f (n + 1)).take n = trunc f n := by
  apply List.ext_getElem
  · rw [List.length_take, trunc_length, trunc_length]
    omega
  · intro i hi hi'
    rw [List.getElem_take]
    unfold trunc
    rw [List.getElem_ofFn, List.getElem_ofFn]

theorem trunc_prefix (f : Stream) (n : ℕ) : trunc f n <+: trunc f (n + 1) := by
  rw [← trunc_take]
  exact List.take_prefix _ _

/-! ## Path → coherent singleton sequence -/

def coherentOfPath {T : Tree} (f : Stream) (_hf : Tree.IsPath (STree T) f) :
    CoherentIso T where
  h := fun n => ({trunc f n} : Finset Node)
  coherence := by
    intro n
    have hlen : (trunc f (n + 1)).length = n + 1 := trunc_length _ _
    rw [proj_singleton hlen, trunc_take]
  root := by
    show ({trunc f 0} : Finset Node) = {[]}
    rw [trunc_zero]

theorem coherentOfPath_h {T : Tree} {f : Stream}
    (hf : Tree.IsPath (STree T) f) (n : ℕ) :
    (coherentOfPath f hf).h n = ({trunc f n} : Finset Node) :=
  rfl

theorem coherentOfPath_GMem {T : Tree} {f : Stream}
    (hf : Tree.IsPath (STree T) f) (n : ℕ) :
    GMem T n ((coherentOfPath f hf).h n) := by
  intro σ hσ
  have hmem : σ ∈ ({trunc f n} : Finset Node) := hσ
  have : σ = trunc f n := by simpa using hmem
  rw [this]
  exact ⟨hf n, trunc_length f n⟩

theorem lemma5_pathToIso {T : Tree} {f : Stream} (hf : Tree.IsPath (STree T) f) :
    ∃ c : CoherentIso T, (∀ n, c.h n = ({trunc f n} : Finset Node)) ∧
      c.h 0 = {[]} ∧ ∀ n, GMem T n (c.h n) :=
  ⟨coherentOfPath f hf, fun n => rfl, by
    show ({trunc f 0} : Finset Node) = {[]}
    rw [trunc_zero], coherentOfPath_GMem hf⟩

/-! ## Coherent sequence → path via least-code children -/

def childFibre (h : ℕ → Finset Node) (n : ℕ) (σ : Node) : Finset Node :=
  (h (n + 1)).filter (fun τ => τ.take n = σ)

def leastChild (h : ℕ → Finset Node) (n : ℕ) (σ : Node) : Node :=
  FiniteCoding.childPick (n,h (n+1),σ)

theorem leastChild_mem {h : ℕ → Finset Node} {n : ℕ} {σ : Node}
    (hex : (childFibre h n σ).Nonempty) :
    leastChild h n σ ∈ childFibre h n σ := by
  have hm (τ : Node) : τ ∈ FiniteCoding.fibre (n,h (n+1),σ) ↔ τ ∈ childFibre h n σ := by
    simp [FiniteCoding.fibre, childFibre]
  cases hl : FiniteCoding.fibre (n,h (n+1),σ) with
  | nil =>
    obtain ⟨τ,hτ⟩ := hex
    have hh := (hm τ).mpr hτ
    simp [hl] at hh
  | cons τ rest =>
    change (FiniteCoding.fibre (n,h (n+1),σ)).getD 0 [] ∈ childFibre h n σ
    rw [hl]
    exact (hm τ).mp (by rw [hl]; simp)

theorem leastChild_parent {h : ℕ → Finset Node} {n : ℕ} {σ : Node}
    (hex : (childFibre h n σ).Nonempty) :
    (leastChild h n σ).take n = σ :=
  (Finset.mem_filter.1 (leastChild_mem hex)).2

theorem leastChild_in {h : ℕ → Finset Node} {n : ℕ} {σ : Node}
    (hex : (childFibre h n σ).Nonempty) :
    leastChild h n σ ∈ h (n + 1) :=
  (Finset.mem_filter.1 (leastChild_mem hex)).1

def nodeSeq {T : Tree} (c : CoherentIso T) : ℕ → Node
  | 0 => []
  | n + 1 => leastChild c.h n (nodeSeq c n)

theorem childFibre_nonempty {T : Tree} (c : CoherentIso T) (n : ℕ)
    (hn : nodeSeq c n ∈ c.h n) :
    (childFibre c.h n (nodeSeq c n)).Nonempty := by
  have hproj : nodeSeq c n ∈ proj T n (c.h (n + 1)) := by
    rw [c.coherence n]
    exact hn
  have hodd := (mem_proj_of_mem hproj).2
  by_contra hempty
  have h0 : (childFibre c.h n (nodeSeq c n)).card = 0 :=
    Finset.card_eq_zero.2 (by simpa using hempty)
  have heq : childFibre c.h n (nodeSeq c n) =
      (c.h (n + 1)).filter (fun τ => τ.take n = nodeSeq c n) := rfl
  rw [heq] at h0
  rw [h0] at hodd
  exact absurd hodd (by simp)

theorem nodeSeq_mem {T : Tree} (c : CoherentIso T) (n : ℕ) :
    nodeSeq c n ∈ c.h n := by
  induction n with
  | zero =>
    show ([] : Node) ∈ c.h 0
    rw [c.root]
    simp
  | succ m ih =>
    show leastChild c.h m (nodeSeq c m) ∈ c.h (m + 1)
    exact leastChild_in (childFibre_nonempty c m ih)

theorem nodeSeq_parent {T : Tree} (c : CoherentIso T) (n : ℕ) :
    (nodeSeq c (n + 1)).take n = nodeSeq c n :=
  leastChild_parent (childFibre_nonempty c n (nodeSeq_mem c n))

theorem nodeSeq_length {T : Tree} (c : CoherentIso T)
    (hG : ∀ n, GMem T n (c.h n)) (n : ℕ) :
    (nodeSeq c n).length = n := by
  induction n with
  | zero => rfl
  | succ m ih =>
    have hGm := hG (m + 1) (nodeSeq c (m + 1)) (nodeSeq_mem c (m + 1))
    have hp := nodeSeq_parent c m
    have hlen : ((nodeSeq c (m + 1)).take m).length = (nodeSeq c m).length :=
      congrArg List.length hp
    rw [List.length_take, ih] at hlen
    have h1 : (nodeSeq c (m + 1)).length = m + 1 := hGm.2
    omega

theorem nodeSeq_prefix {T : Tree} (c : CoherentIso T)
    (hG : ∀ n, GMem T n (c.h n)) (n : ℕ) :
    nodeSeq c n <+: nodeSeq c (n + 1) := by
  rw [← nodeSeq_parent c n]
  exact List.take_prefix _ _

def pathOfCoherent {T : Tree} (c : CoherentIso T)
    (hG : ∀ n, GMem T n (c.h n)) : Stream :=
  fun i => (nodeSeq c (i + 1)).getD i 0

theorem getElem_of_prefix {α : Type} {l₁ l₂ : List α} (h : l₁ <+: l₂)
    {i : ℕ} (hi : i < l₁.length) :
    l₁[i]'hi = l₂[i]'(hi.trans_le (List.IsPrefix.length_le h)) := by
  obtain ⟨t, rfl⟩ := h
  exact List.getElem_append_left' hi t

theorem nodeSeq_prefix_iter {T : Tree} (c : CoherentIso T)
    (hG : ∀ n, GMem T n (c.h n)) (k : ℕ) :
    ∀ m, k ≤ m → nodeSeq c k <+: nodeSeq c m := by
  intro m hkm
  induction' hm : m - k with d ih generalizing m
  · have : m = k := by omega
    subst this
    exact ⟨[], by simp⟩
  · have hlt : k < m := by omega
    have h1 : nodeSeq c k <+: nodeSeq c (m - 1) := by
      have hk' : k ≤ m - 1 := by omega
      have hmk : m - 1 - k = d := by omega
      exact ih (m - 1) hk' hmk
    have h2 : nodeSeq c (m - 1) <+: nodeSeq c m := by
      have hstep := nodeSeq_prefix c hG (m - 1)
      have : m - 1 + 1 = m := by omega
      rw [this] at hstep
      exact hstep
    exact h1.trans h2

theorem trunc_pathOfCoherent {T : Tree} (c : CoherentIso T)
    (hG : ∀ n, GMem T n (c.h n)) (n : ℕ) :
    trunc (pathOfCoherent c hG) n = nodeSeq c n := by
  unfold trunc
  apply List.ext_getElem
  · rw [List.length_ofFn, nodeSeq_length c hG n]
  · intro i hi hi'
    rw [List.getElem_ofFn]
    have hlen : (nodeSeq c (i + 1)).length = i + 1 := nodeSeq_length c hG (i + 1)
    have hlt : i < (nodeSeq c (i + 1)).length := by omega
    show (nodeSeq c (i + 1)).getD i 0 = (nodeSeq c n)[i]
    have hget : (nodeSeq c (i + 1)).getD i 0 = (nodeSeq c (i + 1))[i] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
      simp
    rw [hget]
    have hL : (nodeSeq c n).length = n := nodeSeq_length c hG n
    have hF : (List.ofFn fun i : Fin n => pathOfCoherent c hG i).length = n :=
      List.length_ofFn
    have hstep : i + 1 ≤ n := by omega
    have hp : nodeSeq c (i + 1) <+: nodeSeq c n := nodeSeq_prefix_iter c hG (i + 1) n hstep
    exact getElem_of_prefix hp hlt

theorem isPath_of_coherent {T : Tree} (c : CoherentIso T)
    (hG : ∀ n, GMem T n (c.h n)) :
    Tree.IsPath (STree T) (pathOfCoherent c hG) := by
  intro n
  have hmem := hG n (nodeSeq c n) (nodeSeq_mem c n)
  have h : trunc (pathOfCoherent c hG) n = nodeSeq c n :=
    trunc_pathOfCoherent c hG n
  have h2 : (List.ofFn fun i : Fin n => pathOfCoherent c hG i) = nodeSeq c n := by
    simpa [trunc] using h
  rw [h2]
  exact hmem.1

theorem pathOfCoherent_mem {T : Tree} (c : CoherentIso T)
    (hG : ∀ n, GMem T n (c.h n)) (n : ℕ) :
    trunc (pathOfCoherent c hG) n ∈ c.h n := by
  rw [trunc_pathOfCoherent]
  exact nodeSeq_mem c n

theorem lemma5_isoToPath {T : Tree} (c : CoherentIso T)
    (hG : ∀ n, GMem T n (c.h n)) :
    ∃ f : Stream, Tree.IsPath (STree T) f ∧ ∀ n, trunc f n ∈ c.h n :=
  ⟨pathOfCoherent c hG, isPath_of_coherent c hG, pathOfCoherent_mem c hG⟩

end Paper19
