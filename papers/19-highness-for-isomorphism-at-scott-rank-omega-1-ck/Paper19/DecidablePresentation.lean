import Paper19.Presentation

namespace Paper19
open scoped symmDiff

instance GMem.decidable (T : Tree) (n : ℕ) (F : Finset Node) : Decidable (GMem T n F) := by
  unfold GMem level
  infer_instance

instance GoodDom.decidable {T : Tree} (x : Dom T) : Decidable (GoodDom x) := by
  cases x with
  | idx k => exact isTrue trivial
  | vec n F => exact GMem.decidable T n F

/-- An actual finite decision procedure for the translation relation. It
only calls membership in S on the finitely many members of the decoded H. -/
def DAlgorithm (T : Tree) (k x y : Dom T) : Bool :=
  match k, x, y with
  | .idx code, .vec n F, .vec m G =>
    let (n', H) := decodeIndex code
    decide (n' = n ∧ m = n ∧ GMem T n H ∧ G = F ∆ H)
  | _, _, _ => false

theorem DAlgorithm_correct (T : Tree) (k x y : Dom T) :
    DAlgorithm T k x y = true ↔ isD k x y := by
  constructor
  · intro h
    cases k with
    | vec n F => simp [DAlgorithm] at h
    | idx code =>
      cases x with
      | idx n => simp [DAlgorithm] at h
      | vec n F =>
        cases y with
        | idx m => simp [DAlgorithm] at h
        | vec m G =>
          change decide ((decodeIndex code).1 = n ∧ m = n ∧
            GMem T n (decodeIndex code).2 ∧ G = F ∆ (decodeIndex code).2) = true at h
          obtain ⟨hn, hm, hH, hdiff⟩ := of_decide_eq_true h
          subst m
          refine ⟨code, n, n, F, G, (decodeIndex code).2, rfl, rfl, rfl, rfl, ?_, hH, hdiff⟩
          rw [← hn, encIndex_decodeIndex]
  · rintro ⟨code, n, m, F, G, H, rfl, rfl, rfl, hnm, hc, hH, hdiff⟩
    subst m
    rw [hc]
    simp only [DAlgorithm, decodeIndex_encIndex, decide_eq_true_eq]
    exact ⟨trivial, trivial, hH, hdiff⟩

instance isD.decidable {T : Tree} (k x y : Dom T) : Decidable (isD k x y) :=
  decidable_of_iff (DAlgorithm T k x y = true) (DAlgorithm_correct T k x y)

end Paper19
