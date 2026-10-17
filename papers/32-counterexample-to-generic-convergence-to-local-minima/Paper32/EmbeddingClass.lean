import Paper32.FunctionClass
import Paper32.Extensions

/-! The literal finite-dimensional function classes in Corollary 7.2.
The domain is the paper's two base coordinates together with an arbitrary
finite family of extra real coordinates. Polyhedra are finite intersections
of real affine halfspaces. Semialgebraicity uses finite Boolean combinations
of genuine multivariate-polynomial inequalities on all graph coordinates.
-/

open Set BigOperators
open scoped NNReal

noncomputable section
namespace Paper32.EmbeddingClass

abbrev Space (ι : Type*) := Point × (ι → ℝ)

/-- A coefficient form on all `2 + card ι` input coordinates. -/
structure AffineForm (ι : Type*) where
  base : Paper32.AffineForm
  extra : ι → ℝ

def AffineForm.eval {ι : Type*} [Fintype ι] (a : AffineForm ι) (z : Space ι) : ℝ :=
  a.base.eval z.1 + ∑ i, a.extra i * z.2 i

lemma AffineForm.affineCombination {ι : Type*} [Fintype ι] (a : AffineForm ι)
    (z w : Space ι) (t : ℝ) :
    a.eval (t • z + (1-t) • w) = t * a.eval z + (1-t) * a.eval w := by
  have he : (∑ i, a.extra i * (t * z.2 i + (1-t) * w.2 i)) =
      t * (∑ i, a.extra i * z.2 i) + (1-t) * (∑ i, a.extra i * w.2 i) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [eval, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, Paper32.AffineForm.affineCombination, he]
  ring

/-- A finite intersection of closed affine halfspaces. -/
def IsPolyhedron {ι : Type*} [Fintype ι] (s : Set (Space ι)) : Prop :=
  ∃ a : Finset (AffineForm ι), s = {z | ∀ b ∈ a, 0 ≤ b.eval z}

/-- A finite closed polyhedral cover carrying actual affine coefficient forms. -/
def FinitePiecewiseAffine {ι : Type*} [Fintype ι] (f : Space ι → ℝ) : Prop :=
  ∃ pieces : Finset (Set (Space ι) × AffineForm ι),
    (∀ p ∈ pieces, IsPolyhedron p.1) ∧
    (∀ z, ∃ p ∈ pieces, z ∈ p.1) ∧
    ∀ p ∈ pieces, ∀ z ∈ p.1, f z = p.2.eval z

def ContinuousPiecewiseAffine {ι : Type*} [Fintype ι] (f : Space ι → ℝ) : Prop :=
  Continuous f ∧ FinitePiecewiseAffine f

private lemma polyhedron_of_halfspaces {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : κ → AffineForm ι) : IsPolyhedron {z | ∀ k, 0 ≤ (a k).eval z} := by
  classical
  refine ⟨Finset.univ.image a, ?_⟩
  ext z
  simp

private lemma IsPolyhedron.inter {ι : Type*} [Fintype ι] {s t : Set (Space ι)}
    (hs : IsPolyhedron s) (ht : IsPolyhedron t) : IsPolyhedron (s ∩ t) := by
  classical
  obtain ⟨a,rfl⟩ := hs
  obtain ⟨b,rfl⟩ := ht
  refine ⟨a ∪ b, ?_⟩
  ext z
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_union]
  constructor
  · rintro ⟨ha,hb⟩ c (hc | hc)
    · exact ha c hc
    · exact hb c hc
  · intro h
    exact ⟨fun c hc => h c (Or.inl hc),fun c hc => h c (Or.inr hc)⟩

private lemma finitePiecewiseAffine_of_cover {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : Space ι → ℝ) (cell : κ → Set (Space ι)) (a : κ → AffineForm ι)
    (hpoly : ∀ k, IsPolyhedron (cell k)) (hcover : ∀ z, ∃ k, z ∈ cell k)
    (hform : ∀ k z, z ∈ cell k → f z = (a k).eval z) : FinitePiecewiseAffine f := by
  classical
  refine ⟨Finset.univ.image (fun k => (cell k,a k)), ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hp
    exact hpoly k
  · intro z
    obtain ⟨k,hk⟩ := hcover z
    exact ⟨(cell k,a k),Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩,hk⟩
  · intro p hp z hz
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hp
    exact hform k z hz

private def signed (b : Bool) : ℝ := if b then 1 else -1

private lemma abs_eq_signed {b : Bool} {x : ℝ} (h : 0 ≤ signed b * x) :
    |x| = signed b * x := by
  cases b <;> simp only [signed, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul] at *
  · exact abs_of_nonpos (by linarith)
  · exact abs_of_nonneg h

private lemma decide_signed (x : ℝ) : 0 ≤ signed (decide (0 ≤ x)) * x := by
  classical
  by_cases h : 0 ≤ x
  · simp [signed,h]
  · simp [signed,h]
    linarith

private def liftBase {ι : Type*} (a : Paper32.AffineForm) : AffineForm ι := ⟨a,fun _ => 0⟩

@[simp] private lemma eval_liftBase {ι : Type*} [Fintype ι] (a : Paper32.AffineForm) (z : Space ι) :
    (liftBase a).eval z = a.eval z.1 := by simp [liftBase, AffineForm.eval]

private def coordinateForm {ι : Type*} (i : ι) (b : Bool) : AffineForm ι := by
  classical
  exact ⟨⟨0,0,0⟩,fun j => if j = i then signed b else 0⟩

@[simp] private lemma eval_coordinateForm {ι : Type*} [Fintype ι] (i : ι) (b : Bool) (z : Space ι) :
    (coordinateForm i b).eval z = signed b * z.2 i := by
  classical
  simp [coordinateForm, AffineForm.eval, Paper32.AffineForm.eval]

private def pieceCell {ι : Type*} [Fintype ι] (r : AffineRegion) (s : ι → Bool) : Set (Space ι) :=
  {z | z.1 ∈ regionCell r ∧ ∀ i, 0 ≤ signed (s i) * z.2 i}

private def pieceAffine {ι : Type*} (r : AffineRegion) (s : ι → Bool) : AffineForm ι :=
  ⟨regionAffine r,fun i => 2 * signed (s i)⟩

private lemma pieceCell_polyhedron {ι : Type*} [Fintype ι] (r : AffineRegion) (s : ι → Bool) :
    IsPolyhedron (pieceCell r s) := by
  obtain ⟨n,a,ha⟩ := regionCell_polyhedron r
  have hb : IsPolyhedron {z : Space ι | z.1 ∈ regionCell r} := by
    have hh := polyhedron_of_halfspaces (fun k : Fin n => (liftBase (a k) : AffineForm ι))
    simpa only [eval_liftBase,ha,Set.mem_setOf_eq] using hh
  have he : IsPolyhedron {z : Space ι | ∀ i, 0 ≤ signed (s i) * z.2 i} := by
    simpa only [eval_coordinateForm] using
      polyhedron_of_halfspaces (fun i => coordinateForm i (s i))
  exact hb.inter he

/-- Literal finite piecewise-affine structure for every finite number of extra coordinates. -/
theorem embeddedObjective_finitePiecewiseAffine {ι : Type*} [Fintype ι] :
    FinitePiecewiseAffine (embeddedObjective (ι := ι)) := by
  classical
  apply finitePiecewiseAffine_of_cover _
    (fun rs : AffineRegion × (ι → Bool) => pieceCell rs.1 rs.2)
    (fun rs : AffineRegion × (ι → Bool) => pieceAffine rs.1 rs.2)
  · intro rs
    exact pieceCell_polyhedron rs.1 rs.2
  · intro z
    obtain ⟨r,hr⟩ := regionCells_cover z.1
    exact ⟨(r,fun i => decide (0 ≤ z.2 i)),hr,fun i => decide_signed (z.2 i)⟩
  · rintro ⟨r,s⟩ z ⟨hr,hs⟩
    have he : (∑ i, (2 * signed (s i)) * z.2 i) = 2 * ∑ i, |z.2 i| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_eq_signed (hs i)]
      ring
    simp only [embeddedObjective, pieceAffine, AffineForm.eval, he, F_eq_regionAffine hr]

/-- Continuity is on the full real product, not merely on individual pieces. -/
theorem embeddedObjective_continuous {ι : Type*} [Fintype ι] :
    Continuous (embeddedObjective (ι := ι)) := by
  unfold embeddedObjective
  exact (continuous_F.comp continuous_fst).add (by fun_prop)

theorem embeddedObjective_continuousPiecewiseAffine {ι : Type*} [Fintype ι] :
    ContinuousPiecewiseAffine (embeddedObjective (ι := ι)) :=
  ⟨embeddedObjective_continuous,embeddedObjective_finitePiecewiseAffine⟩

/-- A uniform global bound on the full product space, valid also with no extra coordinates. -/
theorem embeddedObjective_lipschitz {ι : Type*} [Fintype ι] :
    LipschitzWith (8 + 2 * (Fintype.card ι : ℝ≥0)) (embeddedObjective (ι := ι)) := by
  classical
  have hcoord (i : ι) : LipschitzWith 1 (fun z : Space ι => |z.2 i|) := by
    simpa using (lipschitzWith_one_norm (E := ℝ)).comp
      ((LipschitzWith.eval i).comp (LipschitzWith.prod_snd (α := Point) (β := ι → ℝ)))
  have hsum (s : Finset ι) : LipschitzWith (s.card : ℝ≥0)
      (fun z : Space ι => ∑ i ∈ s, |z.2 i|) := by
    induction s using Finset.induction_on with
    | empty => simpa using (LipschitzWith.const (0 : ℝ) : LipschitzWith 0 (fun _ : Space ι => (0 : ℝ)))
    | @insert i s hi ih =>
      simpa [Finset.sum_insert hi,Finset.card_insert_of_notMem hi,add_comm] using (hcoord i).add ih
  have hbase : LipschitzWith 8 (fun z : Space ι => F z.1) := by
    simpa using lipschitz_F.comp (LipschitzWith.prod_fst (α := Point) (β := ι → ℝ))
  have hextra : LipschitzWith (2 * (Fintype.card ι : ℝ≥0))
      (fun z : Space ι => 2 * ∑ i, |z.2 i|) := by
    simpa using (lipschitzWith_smul (2 : ℝ) (β := ℝ)).comp (hsum Finset.univ)
  exact hbase.add hextra

/-- Polynomial Boolean formulas on any finite family of real coordinates. -/
inductive PolynomialFormula (κ : Type*) where
  | nonneg (p : MvPolynomial κ ℝ)
  | truth
  | compl (p : PolynomialFormula κ)
  | conj (p q : PolynomialFormula κ)
  | disj (p q : PolynomialFormula κ)

def PolynomialFormula.Holds {κ : Type*} : PolynomialFormula κ → (κ → ℝ) → Prop
  | .nonneg p, q => 0 ≤ MvPolynomial.eval q p
  | .truth, _ => True
  | .compl p, q => ¬ p.Holds q
  | .conj p r, q => p.Holds q ∧ r.Holds q
  | .disj p r, q => p.Holds q ∨ r.Holds q

def IsSemialgebraic {κ : Type*} [Fintype κ] (s : Set (κ → ℝ)) : Prop :=
  ∃ p : PolynomialFormula κ, s = {q | p.Holds q}

/-- Two inputs, one graph output, and every extra input: `3 + card ι` real coordinates. -/
abbrev GraphCoord (ι : Type*) := Fin 3 ⊕ ι

@[simp] theorem graphCoord_card {ι : Type*} [Fintype ι] :
    Fintype.card (GraphCoord ι) = 3 + Fintype.card ι := by
  simp [GraphCoord]

def graphInput {ι : Type*} (q : GraphCoord ι → ℝ) : Space ι :=
  ((q (.inl 0),q (.inl 1)),fun i => q (.inr i))

def SemialgebraicFunction {ι : Type*} [Fintype ι] (f : Space ι → ℝ) : Prop :=
  IsSemialgebraic {q : GraphCoord ι → ℝ | q (.inl 2) = f (graphInput q)}

private def formulaAll {κ : Type*} : List (PolynomialFormula κ) → PolynomialFormula κ
  | [] => .truth
  | p :: ps => .conj p (formulaAll ps)

private def formulaAny {κ : Type*} : List (PolynomialFormula κ) → PolynomialFormula κ
  | [] => .compl .truth
  | p :: ps => .disj p (formulaAny ps)

@[simp] private lemma holds_formulaAll {κ : Type*} (ps : List (PolynomialFormula κ)) (q) :
    (formulaAll ps).Holds q ↔ ∀ p ∈ ps, p.Holds q := by
  induction ps with
  | nil => simp [formulaAll, PolynomialFormula.Holds]
  | cons p ps ih => simp [formulaAll, PolynomialFormula.Holds, ih]

@[simp] private lemma holds_formulaAny {κ : Type*} (ps : List (PolynomialFormula κ)) (q) :
    (formulaAny ps).Holds q ↔ ∃ p ∈ ps, p.Holds q := by
  induction ps with
  | nil => simp [formulaAny, PolynomialFormula.Holds]
  | cons p ps ih => simp [formulaAny, PolynomialFormula.Holds, ih]

private def allFormulas {κ τ : Type*} [Fintype τ] (p : τ → PolynomialFormula κ) : PolynomialFormula κ := by
  classical
  exact formulaAll (Finset.univ.toList.map p)

private def anyFormulas {κ τ : Type*} [Fintype τ] (p : τ → PolynomialFormula κ) : PolynomialFormula κ := by
  classical
  exact formulaAny (Finset.univ.toList.map p)

@[simp] private lemma holds_allFormulas {κ τ : Type*} [Fintype τ] (p : τ → PolynomialFormula κ) (q) :
    (allFormulas p).Holds q ↔ ∀ i, (p i).Holds q := by
  classical
  simp [allFormulas]

@[simp] private lemma holds_anyFormulas {κ τ : Type*} [Fintype τ] (p : τ → PolynomialFormula κ) (q) :
    (anyFormulas p).Holds q ↔ ∃ i, (p i).Holds q := by
  classical
  simp [anyFormulas]

private def substitutePlanar {κ : Type*} (σ : Fin 3 → MvPolynomial κ ℝ) :
    Paper32.PolynomialFormula 3 → PolynomialFormula κ
  | .nonneg p => .nonneg (MvPolynomial.eval₂Hom MvPolynomial.C σ p)
  | .truth => .truth
  | .compl p => .compl (substitutePlanar σ p)
  | .conj p q => .conj (substitutePlanar σ p) (substitutePlanar σ q)
  | .disj p q => .disj (substitutePlanar σ p) (substitutePlanar σ q)

private lemma eval_substitution {κ : Type*} (σ : Fin 3 → MvPolynomial κ ℝ)
    (p : MvPolynomial (Fin 3) ℝ) (q : κ → ℝ) :
    MvPolynomial.eval q (MvPolynomial.eval₂Hom MvPolynomial.C σ p) =
      MvPolynomial.eval (fun j => MvPolynomial.eval q (σ j)) p := by
  rw [MvPolynomial.map_eval₂Hom]
  have he : (MvPolynomial.eval q).comp MvPolynomial.C = RingHom.id ℝ := by ext r; simp
  rw [he]
  rfl

private lemma holds_substitutePlanar {κ : Type*} (σ : Fin 3 → MvPolynomial κ ℝ)
    (p : Paper32.PolynomialFormula 3) (q : κ → ℝ) :
    (substitutePlanar σ p).Holds q ↔ p.Holds (fun j => MvPolynomial.eval q (σ j)) := by
  induction p with
  | nonneg p => simp only [substitutePlanar,PolynomialFormula.Holds,Paper32.PolynomialFormula.Holds,eval_substitution]
  | truth => rfl
  | compl p ih => simp only [substitutePlanar,PolynomialFormula.Holds,Paper32.PolynomialFormula.Holds,ih]
  | conj p r ihp ihr => simp only [substitutePlanar,PolynomialFormula.Holds,Paper32.PolynomialFormula.Holds,ihp,ihr]
  | disj p r ihp ihr => simp only [substitutePlanar,PolynomialFormula.Holds,Paper32.PolynomialFormula.Holds,ihp,ihr]

private def extraPolynomial {ι : Type*} [Fintype ι] (s : ι → Bool) : MvPolynomial (GraphCoord ι) ℝ :=
  MvPolynomial.C 2 * ∑ i, MvPolynomial.C (signed (s i)) * MvPolynomial.X (.inr i)

private def graphSubstitution {ι : Type*} [Fintype ι] (s : ι → Bool) (j : Fin 3) :
    MvPolynomial (GraphCoord ι) ℝ :=
  if j = 2 then MvPolynomial.X (.inl 2) - extraPolynomial s else MvPolynomial.X (.inl j)

private def signedGraphFormula {ι : Type*} [Fintype ι] (p : Paper32.PolynomialFormula 3)
    (s : ι → Bool) : PolynomialFormula (GraphCoord ι) :=
  .conj (allFormulas (fun i : ι => .nonneg
      (MvPolynomial.C (signed (s i)) * MvPolynomial.X (.inr i))))
    (substitutePlanar (graphSubstitution s) p)

private lemma signedGraphFormula_iff {ι : Type*} [Fintype ι] (p : Paper32.PolynomialFormula 3)
    (hp : {q : Fin 3 → ℝ | q 2 = F (q 0,q 1)} = {q | p.Holds q})
    (s : ι → Bool) (q : GraphCoord ι → ℝ) :
    (signedGraphFormula p s).Holds q ↔
      (∀ i, 0 ≤ signed (s i) * q (.inr i)) ∧
      q (.inl 2) - 2 * ∑ i, signed (s i) * q (.inr i) = F (q (.inl 0),q (.inl 1)) := by
  have hbase (q' : Fin 3 → ℝ) : p.Holds q' ↔ q' 2 = F (q' 0,q' 1) :=
    (Set.ext_iff.mp hp q').symm
  simp only [signedGraphFormula,PolynomialFormula.Holds,holds_allFormulas,
    MvPolynomial.eval_mul,MvPolynomial.eval_C,MvPolynomial.eval_X,holds_substitutePlanar,hbase]
  simp [graphSubstitution,extraPolynomial,MvPolynomial.eval_mul,MvPolynomial.eval_C]

/-- A polynomial Boolean formula for the entire graph in `3 + card ι` real coordinates. -/
theorem embeddedObjective_semialgebraic {ι : Type*} [Fintype ι] :
    SemialgebraicFunction (embeddedObjective (ι := ι)) := by
  classical
  obtain ⟨p,hp⟩ := Paper32.semialgebraic_F
  refine ⟨anyFormulas (signedGraphFormula (ι := ι) p), ?_⟩
  ext q
  simp only [Set.mem_setOf_eq,holds_anyFormulas,signedGraphFormula_iff p hp]
  constructor
  · intro h
    let s : ι → Bool := fun i => decide (0 ≤ q (.inr i))
    have hs : ∀ i, 0 ≤ signed (s i) * q (.inr i) := fun i => decide_signed _
    refine ⟨s,hs,?_⟩
    have he : (∑ i, signed (s i) * q (.inr i)) = ∑ i, |q (.inr i)| := by
      apply Finset.sum_congr rfl
      intro i _
      exact (abs_eq_signed (hs i)).symm
    rw [he]
    change q (.inl 2) = F (q (.inl 0),q (.inl 1)) + 2 * ∑ i, |q (.inr i)| at h
    linarith
  · rintro ⟨s,hs,h⟩
    have he : (∑ i, signed (s i) * q (.inr i)) = ∑ i, |q (.inr i)| := by
      apply Finset.sum_congr rfl
      intro i _
      exact (abs_eq_signed (hs i)).symm
    rw [he] at h
    change q (.inl 2) = F (q (.inl 0),q (.inl 1)) + 2 * ∑ i, |q (.inr i)|
    linarith

end Paper32.EmbeddingClass
