import Paper19.LiftTree

namespace Paper19

/-- Projection from level n to level k (only k ≤ n is used). -/
def projectTo (T : Tree) : ℕ → Finset Node → ℕ → Finset Node
  | 0, F, _ => F
  | n + 1, F, k => if k < n + 1 then projectTo T n (proj T n F) k else F

@[simp] theorem projectTo_self (T : Tree) (n : ℕ) (F : Finset Node) :
    projectTo T n F n = F := by cases n <;> simp [projectTo]

theorem projectTo_coherence (T : Tree) {n k : ℕ} (F : Finset Node) (hk : k < n) :
    proj T k (projectTo T n F (k + 1)) = projectTo T n F k := by
  induction n generalizing F with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k = n
    · subst k; simp [projectTo]
    · have hlt : k < n := by omega
      simpa [projectTo, show k < n + 1 by omega, show k + 1 < n + 1 by omega]
        using ih (proj T n F) hlt

theorem GMem_proj {T : Tree} {n : ℕ} {F : Finset Node} (hF : GMem T (n + 1) F) :
    GMem T n (proj T n F) := by
  intro σ hσ
  obtain ⟨⟨τ, hτ, hlen, htake⟩, _⟩ := mem_proj_iff.mp hσ
  refine ⟨?_, ?_⟩
  · rw [← htake]; exact (STree T).mem_prefix (hF τ hτ).1 (List.take_prefix _ _)
  · rw [← htake, List.length_take, hlen]; omega

theorem GMem_projectTo {T : Tree} {n k : ℕ} {F : Finset Node}
    (hF : GMem T n F) (hk : k ≤ n) : GMem T k (projectTo T n F k) := by
  induction n generalizing F with
  | zero =>
    have : k = 0 := by omega
    subst k
    exact hF
  | succ n ih =>
    by_cases hkn : k = n + 1
    · subst k; simpa using hF
    · simpa [projectTo, show k < n + 1 by omega] using ih (GMem_proj hF) (by omega)

/-- A lift whose root projects to zero extends to a zero-root translation. -/
theorem extend_lift {T : Tree} {n : ℕ} {F : Finset Node}
    (h : LiftSeq T n F) (hroot : projectTo T n F 0 = ∅) :
    ∃ c : CoherentAut T, c.h n = F ∧ ∀ k, GMem T k (c.h k) := by
  obtain ⟨E, h0, hp, hG⟩ := h
  let H : ℕ → Finset Node := fun k =>
    if k ≤ n then projectTo T n F k else E (k - n)
  have hn : H n = F := by simp [H]
  have hbelow (k : ℕ) (hk : k ≤ n) : H k = projectTo T n F k := by simp [H, hk]
  have habove (k : ℕ) (hk : n ≤ k) : H k = E (k - n) := by
    by_cases hkn : k = n
    · subst k; simp [H, h0]
    · simp [H, show ¬k ≤ n by omega]
  have hcoh (k : ℕ) : proj T k (H (k + 1)) = H k := by
    by_cases hk : k < n
    · rw [hbelow (k + 1) (by omega), hbelow k (by omega)]
      exact projectTo_coherence T F hk
    · rw [habove (k + 1) (by omega), habove k (by omega)]
      have hh := hp (k - n)
      have he : n + (k - n) = k := by omega
      have he' : k + 1 - n = k - n + 1 := by omega
      simpa [he, he'] using hh
  refine ⟨⟨H, hcoh, ?_⟩, hn, ?_⟩
  · simpa [H] using hroot
  · intro k
    change GMem T k (H k)
    by_cases hk : k ≤ n
    · rw [hbelow k hk]
      have hF : GMem T n F := by simpa [h0] using hG 0
      exact GMem_projectTo hF hk
    · rw [habove k (by omega)]
      have hh := hG (k - n)
      simpa [show n + (k - n) = k by omega] using hh

theorem coherent_projectTo {T : Tree} (c : CoherentAut T) {n k : ℕ} (hk : k ≤ n) :
    projectTo T n (c.h n) k = c.h k := by
  induction n with
  | zero =>
    have : k = 0 := by omega
    subst k
    rfl
  | succ n ih =>
    by_cases hkn : k = n + 1
    · subst k; simp
    · simp only [projectTo, if_pos (show k < n + 1 by omega), c.coherence n]
      exact ih (by omega)

end Paper19
