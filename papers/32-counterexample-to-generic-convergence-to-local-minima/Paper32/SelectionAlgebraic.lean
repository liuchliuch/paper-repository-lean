import Paper32.BorelSelection

/-! Polynomial graph certificate for the minimum-Euclidean-norm selection.
The finite eligibility-mask argument also makes the original semialgebraic
claim independent of any unavailable quantifier-elimination library.
-/

open Set

noncomputable section
namespace Paper32

private def formulaAll {n : ℕ} : List (PolynomialFormula n) → PolynomialFormula n
  | [] => .truth
  | p :: ps => .conj p (formulaAll ps)

private def formulaAny {n : ℕ} : List (PolynomialFormula n) → PolynomialFormula n
  | [] => .compl .truth
  | p :: ps => .disj p (formulaAny ps)

@[simp] private lemma holds_formulaAll {n : ℕ} (ps : List (PolynomialFormula n)) (q) :
    (formulaAll ps).Holds q ↔ ∀ p ∈ ps, p.Holds q := by
  induction ps with
  | nil => simp [formulaAll, PolynomialFormula.Holds]
  | cons p ps ih => simp [formulaAll, PolynomialFormula.Holds, ih]

@[simp] private lemma holds_formulaAny {n : ℕ} (ps : List (PolynomialFormula n)) (q) :
    (formulaAny ps).Holds q ↔ ∃ p ∈ ps, p.Holds q := by
  induction ps with
  | nil => simp [formulaAny, PolynomialFormula.Holds]
  | cons p ps ih => simp [formulaAny, PolynomialFormula.Holds, ih]

private def allFormulas {n : ℕ} {ι : Type} [Fintype ι]
    (p : ι → PolynomialFormula n) : PolynomialFormula n := by
  classical
  exact formulaAll (Finset.univ.toList.map p)

private def anyFormulas {n : ℕ} {ι : Type} [Fintype ι]
    (p : ι → PolynomialFormula n) : PolynomialFormula n := by
  classical
  exact formulaAny (Finset.univ.toList.map p)

@[simp] private lemma holds_allFormulas {n : ℕ} {ι : Type} [Fintype ι]
    (p : ι → PolynomialFormula n) (q) : (allFormulas p).Holds q ↔ ∀ i, (p i).Holds q := by
  classical
  simp [allFormulas]

@[simp] private lemma holds_anyFormulas {n : ℕ} {ι : Type} [Fintype ι]
    (p : ι → PolynomialFormula n) (q) : (anyFormulas p).Holds q ↔ ∃ i, (p i).Holds q := by
  classical
  simp [anyFormulas]

lemma IsSemialgebraic.compl {n : ℕ} {s : Set (Fin n → ℝ)} (hs : IsSemialgebraic s) :
    IsSemialgebraic sᶜ := by
  obtain ⟨p,rfl⟩ := hs
  exact ⟨.compl p,rfl⟩

lemma IsSemialgebraic.inter {n : ℕ} {s t : Set (Fin n → ℝ)}
    (hs : IsSemialgebraic s) (ht : IsSemialgebraic t) : IsSemialgebraic (s ∩ t) := by
  obtain ⟨p,rfl⟩ := hs
  obtain ⟨q,rfl⟩ := ht
  exact ⟨.conj p q,rfl⟩

lemma IsSemialgebraic.iInter {n : ℕ} {ι : Type} [Fintype ι]
    {s : ι → Set (Fin n → ℝ)} (hs : ∀ i, IsSemialgebraic (s i)) :
    IsSemialgebraic (⋂ i, s i) := by
  classical
  choose p hp using hs
  refine ⟨allFormulas p, ?_⟩
  ext q
  simp [hp]

lemma IsSemialgebraic.iUnion {n : ℕ} {ι : Type} [Fintype ι]
    {s : ι → Set (Fin n → ℝ)} (hs : ∀ i, IsSemialgebraic (s i)) :
    IsSemialgebraic (⋃ i, s i) := by
  classical
  choose p hp using hs
  refine ⟨anyFormulas p, ?_⟩
  ext q
  simp [hp]

lemma isSemialgebraic_empty (n : ℕ) : IsSemialgebraic (∅ : Set (Fin n → ℝ)) := by
  refine ⟨.compl .truth, ?_⟩
  ext q
  simp [PolynomialFormula.Holds]

private def affinePolynomial {n : ℕ} (a : AffineForm) (i j : Fin n) : MvPolynomial (Fin n) ℝ :=
  MvPolynomial.C a.x * MvPolynomial.X i +
    MvPolynomial.C a.y * MvPolynomial.X j + MvPolynomial.C a.c

@[simp] private lemma eval_affinePolynomial {n : ℕ} (a : AffineForm) (i j : Fin n) (q) :
    MvPolynomial.eval q (affinePolynomial a i j) = a.eval (q i, q j) := by
  simp [affinePolynomial, AffineForm.eval]

lemma IsPolyhedron.semialgebraic_lift {n : ℕ} {s : Set Point} (hs : IsPolyhedron s) (i j : Fin n) :
    IsSemialgebraic {q : Fin n → ℝ | (q i, q j) ∈ s} := by
  obtain ⟨N,a,rfl⟩ := hs
  refine ⟨allFormulas (fun k : Fin N => .nonneg (affinePolynomial (a k) i j)), ?_⟩
  ext q
  simp [PolynomialFormula.Holds]

/-- An eligible polyhedral piece is either its entire closed cell or empty.
This argument also covers degenerate cells without enumerating geometric cases. -/
lemma eligibleCell_semialgebraic_lift {n : ℕ} (r : AffineRegion) (i j : Fin n) :
    IsSemialgebraic {q : Fin n → ℝ | (q i, q j) ∈ eligibleCell r} := by
  by_cases h : (interior (regionCell r)).Nonempty
  · have heq : eligibleCell r = regionCell r := by
      unfold eligibleCell
      rw [(regionCell_polyhedron r).convex.closure_interior_eq_closure_of_nonempty_interior h,
        (regionCell_polyhedron r).isClosed.closure_eq]
    rw [heq]
    exact (regionCell_polyhedron r).semialgebraic_lift i j
  · have hi : interior (regionCell r) = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simpa only [eligibleCell, hi, closure_empty, Set.mem_empty_iff_false, Set.setOf_false] using
      isSemialgebraic_empty n

private def maskLift (m : Set AffineRegion) : Set (Fin 4 → ℝ) :=
  {q | eligibilityMask (q 0, q 1) = m}

private lemma maskLift_semialgebraic (m : Set AffineRegion) : IsSemialgebraic (maskLift m) := by
  classical
  have heq : maskLift m = ⋂ r : AffineRegion,
      if r ∈ m then {q : Fin 4 → ℝ | (q 0, q 1) ∈ eligibleCell r}
      else {q : Fin 4 → ℝ | (q 0, q 1) ∈ eligibleCell r}ᶜ := by
    ext q
    change (eligibilityMask (q 0, q 1) = m) ↔ _
    rw [Set.ext_iff]
    simp only [Set.mem_iInter, eligibilityMask, Set.mem_setOf_eq]
    apply forall_congr'
    intro r
    by_cases hr : r ∈ m <;> simp [hr]
  rw [heq]
  apply IsSemialgebraic.iInter
  intro r
  split
  · exact eligibleCell_semialgebraic_lift r 0 1
  · exact (eligibleCell_semialgebraic_lift r 0 1).compl

lemma isSemialgebraic_coordinate_eq {n : ℕ} (k : Fin n) (c : ℝ) :
    IsSemialgebraic {q : Fin n → ℝ | q k = c} := by
  refine ⟨.conj (.nonneg (MvPolynomial.X k - MvPolynomial.C c))
    (.nonneg (MvPolynomial.C c - MvPolynomial.X k)), ?_⟩
  ext q
  simp only [Set.mem_setOf_eq, PolynomialFormula.Holds, MvPolynomial.eval_sub,
    MvPolynomial.eval_X, MvPolynomial.eval_C]
  constructor <;> intro h
  · simp [h]
  · linarith [h.1,h.2]

private lemma outputPoint_semialgebraic (u : Point) :
    IsSemialgebraic {q : Fin 4 → ℝ | (q 2, q 3) = u} := by
  have hi := (isSemialgebraic_coordinate_eq (n := 4) 2 u.1).inter
    (isSemialgebraic_coordinate_eq (n := 4) 3 u.2)
  convert hi using 1
  ext q
  simp [Prod.ext_iff]

private def algebraicMaskRepresentative (m : Set AffineRegion) : Point := by
  classical
  exact if hm : ∃ z : Point, eligibilityMask z = m then Classical.choose hm else 0

private lemma algebraicMaskRepresentative_mask (z : Point) :
    eligibilityMask (algebraicMaskRepresentative (eligibilityMask z)) = eligibilityMask z := by
  classical
  simp only [algebraicMaskRepresentative,
    dif_pos (show ∃ u : Point, eligibilityMask u = eligibilityMask z from ⟨z,rfl⟩)]
  exact Classical.choose_spec (show ∃ u : Point, eligibilityMask u = eligibilityMask z from ⟨z,rfl⟩)

private lemma minimumNormSelection_algebraicMask (v z : Point) :
    minimumNormSelection v (algebraicMaskRepresentative (eligibilityMask z)) = minimumNormSelection v z := by
  have heq := clarke_tilt_eq_of_mask_eq (v := v) (algebraicMaskRepresentative_mask z)
  apply minimumNormSelection_unique_norm v z
  · rw [← heq]
    exact minimumNormSelection_mem _ _
  · intro w hw
    apply minimumNormSelection_min_norm
    rwa [heq]

/-- Semialgebraicity for a plane-to-plane map means semialgebraicity of its
complete four-variable real graph. -/
def SemialgebraicPointMap (s : Point → Point) : Prop :=
  IsSemialgebraic {q : Fin 4 → ℝ | (q 2, q 3) = s (q 0, q 1)}

/-- The graph assertion accompanying (2.11), proved by finite polynomial
Boolean formulas for the eligibility masks and constant output coordinates. -/
theorem semialgebraic_minimumNormSelection (v : Point) :
    SemialgebraicPointMap (minimumNormSelection v) := by
  classical
  let cells : Set AffineRegion → Set (Fin 4 → ℝ) := fun m =>
    maskLift m ∩ {q | (q 2, q 3) = minimumNormSelection v (algebraicMaskRepresentative m)}
  have hc : ∀ m, IsSemialgebraic (cells m) := fun m =>
    (maskLift_semialgebraic m).inter (outputPoint_semialgebraic _)
  have hu := IsSemialgebraic.iUnion hc
  have heq : {q : Fin 4 → ℝ | (q 2, q 3) = minimumNormSelection v (q 0, q 1)} = ⋃ m, cells m := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, cells, Set.mem_inter_iff, maskLift]
    constructor
    · intro h
      exact ⟨eligibilityMask (q 0,q 1),rfl,
        h.trans (minimumNormSelection_algebraicMask v (q 0,q 1)).symm⟩
    · rintro ⟨m,hm,hout⟩
      rw [← hm] at hout
      exact hout.trans (minimumNormSelection_algebraicMask v (q 0,q 1))
  unfold SemialgebraicPointMap
  rw [heq]
  exact hu

end Paper32
