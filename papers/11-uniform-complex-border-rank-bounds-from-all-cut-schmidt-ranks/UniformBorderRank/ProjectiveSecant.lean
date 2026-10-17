import UniformBorderRank.RankOps
import Mathlib.LinearAlgebra.Projectivization.Subspace
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Projective Segre secants

The projective points in this file are mathlib's projectivization of the actual
coefficient vector space.  The Segre set consists of projective classes of
nonzero decomposable coefficient tensors.  The secant is defined by homogeneous
polynomial equations vanishing on the union of spans of at most `b` Segre
points.  No rank predicate occurs in any of these geometric definitions.
-/
noncomputable section
namespace UniformBorderRank

open scoped LinearAlgebra.Projectivization Topology
open Filter

abbrev ProjectiveTensor {N : ℕ} (d : Fin N → ℕ) := Projectivization ℂ (Coeffs d)
abbrev TensorPolynomial {N : ℕ} (d : Fin N → ℕ) :=
  MvPolynomial (∀ i : Fin N, Fin (d i)) ℂ

/-- The Segre set in the projectivization of the coefficient tensor space. -/
def projectiveSegre {N : ℕ} (d : Fin N → ℕ) : Set (ProjectiveTensor d) :=
  {p | ∃ (T : Coeffs d) (hT : T ≠ 0), isProduct T ∧ Projectivization.mk ℂ T hT = p}

/-- The union of the actual projective linear spans of at most `b` Segre points. -/
def projectiveSecantSpans {N : ℕ} (d : Fin N → ℕ) (b : ℕ) :
    Set (ProjectiveTensor d) :=
  {p | ∃ S : Finset (ProjectiveTensor d), S.card ≤ b ∧
    (∀ q ∈ S, q ∈ projectiveSegre d) ∧
    p ∈ Projectivization.Subspace.span (S : Set (ProjectiveTensor d))}

/-- A polynomial zero locus on projective points.  Vanishing is required on
all nonzero representatives; for homogeneous polynomials this is the usual
well-defined projective zero locus. -/
def projectiveZeroLocus {N : ℕ} {d : Fin N → ℕ} (f : TensorPolynomial d) :
    Set (ProjectiveTensor d) :=
  {p | ∀ (T : Coeffs d) (hT : T ≠ 0),
    Projectivization.mk ℂ T hT = p → MvPolynomial.eval T f = 0}

/-- The projective Zariski closure: intersection of all homogeneous polynomial
zero loci containing the given set. -/
def projectiveZariskiClosure {N : ℕ} {d : Fin N → ℕ}
    (S : Set (ProjectiveTensor d)) : Set (ProjectiveTensor d) :=
  {p | ∀ (f : TensorPolynomial d) (n : ℕ), f.IsHomogeneous n →
    S ⊆ projectiveZeroLocus f → p ∈ projectiveZeroLocus f}

/-- The `b`th Segre secant, defined by its geometric span-and-closure construction. -/
def projectiveSecant {N : ℕ} (d : Fin N → ℕ) (b : ℕ) : Set (ProjectiveTensor d) :=
  projectiveZariskiClosure (projectiveSecantSpans d b)

lemma subset_projectiveZariskiClosure {N : ℕ} {d : Fin N → ℕ}
    (S : Set (ProjectiveTensor d)) : S ⊆ projectiveZariskiClosure S := by
  intro p hp f n hf hS
  exact hS hp

lemma projectiveZariskiClosure_mono {N : ℕ} {d : Fin N → ℕ}
    {S U : Set (ProjectiveTensor d)} (h : S ⊆ U) :
    projectiveZariskiClosure S ⊆ projectiveZariskiClosure U := by
  intro p hp f n hf hU
  exact hp f n hf (h.trans hU)

lemma projectiveZariskiClosure_idem {N : ℕ} {d : Fin N → ℕ}
    (S : Set (ProjectiveTensor d)) :
    projectiveZariskiClosure (projectiveZariskiClosure S) = projectiveZariskiClosure S := by
  apply Set.Subset.antisymm
  · intro p hp f n hf hS
    exact hp f n hf (fun q hq => hq f n hf hS)
  · exact subset_projectiveZariskiClosure _

/-- A nonzero sum of `b` product tensors belongs to a genuine projective span
of at most `b` nonzero Segre points; zero summands are discarded. -/
theorem cpRankLe_mem_projectiveSecantSpans {N : ℕ} {d : Fin N → ℕ}
    {T : Coeffs d} {b : ℕ} (hT : T ≠ 0) (h : cpRankLe T b) :
    Projectivization.mk ℂ T hT ∈ projectiveSecantSpans d b := by
  classical
  obtain ⟨k, hk, hsum⟩ := h
  let q : Fin b → ProjectiveTensor d := fun j =>
    if hj : k j ≠ 0 then Projectivization.mk ℂ (k j) hj else Projectivization.mk ℂ T hT
  let J : Finset (Fin b) := Finset.univ.filter (fun j => k j ≠ 0)
  let S : Finset (ProjectiveTensor d) := J.image q
  refine ⟨S, (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans ?_, ?_, ?_⟩
  · simp
  · intro p hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hp
    have hj' : k j ≠ 0 := (Finset.mem_filter.mp hj).2
    exact ⟨k j, hj', hk j, by simp only [q, dif_pos hj']⟩
  · let W := Projectivization.Subspace.span (S : Set (ProjectiveTensor d))
    apply (Projectivization.Subspace.mem_submodule_iff W hT).mp
    have hsum' : T = ∑ j : Fin b, k j := by
      funext idx
      simpa using hsum idx
    rw [hsum']
    apply Submodule.sum_mem
    intro j hj
    by_cases hkj : k j = 0
    · rw [hkj]
      exact Submodule.zero_mem _
    · apply (Projectivization.Subspace.mem_submodule_iff W hkj).mpr
      apply Projectivization.Subspace.subset_span
      change Projectivization.mk ℂ (k j) hkj ∈ S
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hkj⟩, ?_⟩
      simp only [q, dif_pos hkj]

/-- Polynomial evaluation commutes with coefficientwise tensor limits. -/
lemma tendsto_tensorPolynomial_eval {N : ℕ} {d : Fin N → ℕ}
    (f : TensorPolynomial d) {s : ℕ → Coeffs d} {T : Coeffs d}
    (hs : ∀ idx, Tendsto (fun n => s n idx) atTop (nhds (T idx))) :
    Tendsto (fun n => MvPolynomial.eval (s n) f) atTop
      (nhds (MvPolynomial.eval T f)) := by
  exact (MvPolynomial.continuous_eval f).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hs)

/-- The Euclidean border-rank predicate implies the projective secant condition.
This direction only uses continuity of polynomial evaluation; no comparison
between the Euclidean and Zariski closures in the opposite direction is used. -/
theorem borderRankLe_mem_projectiveSecant {N : ℕ} {d : Fin N → ℕ}
    (hN : 0 < N) {T : Coeffs d} {b : ℕ} (hT : T ≠ 0)
    (h : borderRankLe T b) :
    Projectivization.mk ℂ T hT ∈ projectiveSecant d b := by
  obtain ⟨s, hs, hlim⟩ := h
  intro f degree hf hvan U hU hUT
  obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ U T hU hT).mp hUT
  have hclim : ∀ idx, Tendsto (fun n => (c • s n) idx) atTop (nhds (U idx)) := by
    intro idx
    simpa only [Pi.smul_apply, smul_eq_mul, ← hc] using (hlim idx).const_mul c
  have hUne : ∀ᶠ n in atTop, c • s n ≠ (0 : Coeffs d) :=
    (tendsto_pi_nhds.mpr hclim).eventually_ne hU
  have hzero : ∀ᶠ n in atTop, MvPolynomial.eval (c • s n) f = 0 := by
    filter_upwards [hUne] with n hn
    exact hvan (cpRankLe_mem_projectiveSecantSpans hn (cpRankLe_smul hN c (hs n)))
      (c • s n) hn rfl
  exact tendsto_nhds_unique (tendsto_tensorPolynomial_eval f hclim)
    (tendsto_const_nhds.congr' (hzero.mono (fun _ hn => hn.symm)))

/-- The usual homogeneous scaling law in the tensor coefficient variables. -/
lemma eval_homogeneous_smul {N : ℕ} {d : Fin N → ℕ}
    {f : TensorPolynomial d} {degree : ℕ} (hf : f.IsHomogeneous degree)
    (c : ℂ) (T : Coeffs d) :
    MvPolynomial.eval (c • T) f = c ^ degree * MvPolynomial.eval T f := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro mon hmon
  have hd := hf.degree_eq_sum_deg_support hmon
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum, ← hd]
  ring

/-- For a homogeneous polynomial, universal representative vanishing agrees
with ordinary evaluation at any one representative. -/
lemma mk_mem_projectiveZeroLocus_iff {N : ℕ} {d : Fin N → ℕ}
    {f : TensorPolynomial d} {degree : ℕ} (hf : f.IsHomogeneous degree)
    (T : Coeffs d) (hT : T ≠ 0) :
    Projectivization.mk ℂ T hT ∈ projectiveZeroLocus f ↔ MvPolynomial.eval T f = 0 := by
  constructor
  · intro h
    exact h T hT rfl
  · intro h U hU hUT
    obtain ⟨c, rfl⟩ := (Projectivization.mk_eq_mk_iff' ℂ U T hU hT).mp hUT
    rw [eval_homogeneous_smul hf, h, mul_zero]

lemma mem_projectiveZeroLocus_iff {N : ℕ} {d : Fin N → ℕ}
    {f : TensorPolynomial d} {degree : ℕ} (hf : f.IsHomogeneous degree)
    (p : ProjectiveTensor d) :
    p ∈ projectiveZeroLocus f ↔ MvPolynomial.eval p.rep f = 0 := by
  conv_lhs => rw [← p.mk_rep]
  exact mk_mem_projectiveZeroLocus_iff hf p.rep p.rep_nonzero

lemma projectiveZeroLocus_mul {N : ℕ} {d : Fin N → ℕ}
    {f g : TensorPolynomial d} {m n : ℕ}
    (hf : f.IsHomogeneous m) (hg : g.IsHomogeneous n) :
    projectiveZeroLocus (f * g) = projectiveZeroLocus f ∪ projectiveZeroLocus g := by
  ext p
  rw [mem_projectiveZeroLocus_iff (hf.mul hg), MvPolynomial.eval_mul, mul_eq_zero]
  simp only [Set.mem_union, mem_projectiveZeroLocus_iff hf, mem_projectiveZeroLocus_iff hg]

/-- An algebraic projective set is one whose missing points are separated by
homogeneous polynomial equations.  Equivalently, it is the common zero locus
of a family of homogeneous polynomials. -/
def projectiveAlgebraicSet {N : ℕ} {d : Fin N → ℕ}
    (S : Set (ProjectiveTensor d)) : Prop :=
  ∀ p, p ∉ S → ∃ (f : TensorPolynomial d) (degree : ℕ),
    f.IsHomogeneous degree ∧ S ⊆ projectiveZeroLocus f ∧ p ∉ projectiveZeroLocus f

lemma projectiveAlgebraicSet_empty {N : ℕ} {d : Fin N → ℕ} :
    projectiveAlgebraicSet (∅ : Set (ProjectiveTensor d)) := by
  intro p hp
  refine ⟨1, 0, MvPolynomial.isHomogeneous_one _ _, Set.empty_subset _, ?_⟩
  rw [mem_projectiveZeroLocus_iff (MvPolynomial.isHomogeneous_one _ _) p]
  simp

lemma projectiveAlgebraicSet_sInter {N : ℕ} {d : Fin N → ℕ}
    (A : Set (Set (ProjectiveTensor d)))
    (hA : ∀ S ∈ A, projectiveAlgebraicSet S) : projectiveAlgebraicSet (⋂₀ A) := by
  classical
  intro p hp
  obtain ⟨S, hSA, hpS⟩ : ∃ S ∈ A, p ∉ S := by
    by_contra! hall
    exact hp (fun S hSA => hall S hSA)
  obtain ⟨f, degree, hf, hS, hpf⟩ := hA S hSA p hpS
  exact ⟨f, degree, hf, (Set.sInter_subset_of_mem hSA).trans hS, hpf⟩

lemma projectiveAlgebraicSet_union {N : ℕ} {d : Fin N → ℕ}
    {S U : Set (ProjectiveTensor d)}
    (hS : projectiveAlgebraicSet S) (hU : projectiveAlgebraicSet U) :
    projectiveAlgebraicSet (S ∪ U) := by
  intro p hp
  have hpS : p ∉ S := fun h => hp (Or.inl h)
  have hpU : p ∉ U := fun h => hp (Or.inr h)
  obtain ⟨f, m, hf, hSf, hpf⟩ := hS p hpS
  obtain ⟨g, n, hg, hUg, hpg⟩ := hU p hpU
  refine ⟨f * g, m + n, hf.mul hg, ?_, ?_⟩
  · rw [projectiveZeroLocus_mul hf hg]
    exact Set.union_subset_union hSf hUg
  · rw [projectiveZeroLocus_mul hf hg]
    exact fun h => h.elim hpf hpg

/-- The projective Zariski topology given by homogeneous polynomial equations. -/
@[reducible] def projectiveZariskiTopology {N : ℕ} (d : Fin N → ℕ) : TopologicalSpace (ProjectiveTensor d) :=
  TopologicalSpace.ofClosed {S | projectiveAlgebraicSet S}
    projectiveAlgebraicSet_empty
    (fun A hA => projectiveAlgebraicSet_sInter A hA)
    (fun _ hS _ hU => projectiveAlgebraicSet_union hS hU)

lemma isClosed_projectiveZariski_iff {N : ℕ} {d : Fin N → ℕ}
    (S : Set (ProjectiveTensor d)) :
    IsClosed[projectiveZariskiTopology d] S ↔ projectiveAlgebraicSet S := by
  letI := projectiveZariskiTopology d
  rw [← isOpen_compl_iff]
  change projectiveAlgebraicSet Sᶜᶜ ↔ projectiveAlgebraicSet S
  rw [compl_compl]

lemma isClosed_projectiveZeroLocus {N : ℕ} {d : Fin N → ℕ}
    {f : TensorPolynomial d} {degree : ℕ} (hf : f.IsHomogeneous degree) :
    IsClosed[projectiveZariskiTopology d] (projectiveZeroLocus f) := by
  rw [isClosed_projectiveZariski_iff]
  intro p hp
  exact ⟨f, degree, hf, Set.Subset.rfl, hp⟩

/-- The homogeneous-equation closure is exactly closure in the projective
Zariski topology, so the secant definition is an actual topological closure. -/
lemma projectiveZariskiClosure_eq_closure {N : ℕ} {d : Fin N → ℕ}
    (S : Set (ProjectiveTensor d)) :
    projectiveZariskiClosure S = closure[projectiveZariskiTopology d] S := by
  letI := projectiveZariskiTopology d
  apply Set.Subset.antisymm
  · intro p hp
    by_contra hpc
    have hclosed := (isClosed_projectiveZariski_iff (closure S)).mp isClosed_closure
    obtain ⟨f, degree, hf, hc, hpf⟩ := hclosed p hpc
    exact hpf (hp f degree hf (subset_closure.trans hc))
  · intro p hp f degree hf hS
    exact closure_minimal hS (isClosed_projectiveZeroLocus hf) hp

lemma projectiveSecant_eq_closure {N : ℕ} (d : Fin N → ℕ) (b : ℕ) :
    projectiveSecant d b = closure[projectiveZariskiTopology d] (projectiveSecantSpans d b) :=
  projectiveZariskiClosure_eq_closure _

end UniformBorderRank
