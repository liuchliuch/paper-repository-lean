import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Topology.Constructions
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Defs.Induced

/-!
# Lemma 2.1, step 1–2: synthesis isometry and span embedding
-/

noncomputable section

namespace ELV

namespace Gram

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {ι : Type*}

/-- Equal Gram matrices of two families. -/
def EqualGram (a b : ι → V) : Prop :=
  ∀ x y : ι, inner ℂ (a x) (a y) = inner ℂ (b x) (b y)

/-- Synthesis as a linear map on finitely supported coefficients. -/
def synthLM (a : ι → V) : (ι →₀ ℂ) →ₗ[ℂ] V :=
  Finsupp.lsum ℂ fun x => (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (a x)

/-- Synthesis of a finitely supported coefficient family. -/
def synth (a : ι → V) (α : ι →₀ ℂ) : V := synthLM a α

theorem synth_eq_sum (a : ι → V) (α : ι →₀ ℂ) :
    synth a α = ∑ x ∈ α.support, α x • a x := by
  rw [synth, synthLM, Finsupp.lsum_apply]
  simp [Finsupp.sum, LinearMap.smulRight_apply]

theorem synth_single (a : ι → V) (x : ι) :
    synth a (Finsupp.single x (1 : ℂ)) = a x := by
  rw [synth, synthLM, Finsupp.lsum_single]
  simp

/-- Expanded formula for the inner product of two syntheses. -/
theorem synth_inner_expanded (a : ι → V) (α β : ι →₀ ℂ) :
    inner ℂ (synth a α) (synth a β)
      = ∑ y ∈ β.support, β y * ∑ x ∈ α.support,
          starRingEnd ℂ (α x) * inner ℂ (a x) (a y) := by
  rw [synth_eq_sum, synth_eq_sum]
  simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right]

/-- Inner products of syntheses are determined by the Gram matrix. -/
theorem synth_inner_eq {a b : ι → V} (h : EqualGram a b)
    (α β : ι →₀ ℂ) :
    inner ℂ (synth a α) (synth a β) = inner ℂ (synth b α) (synth b β) := by
  rw [synth_inner_expanded a α β, synth_inner_expanded b α β]
  have hx : ∀ x y : ι, inner ℂ (a x) (a y) = inner ℂ (b x) (b y) := h
  simp only [hx]

/-- Norms of syntheses agree. -/
theorem synth_norm_eq {a b : ι → V} (h : EqualGram a b) (α : ι →₀ ℂ) :
    ‖synth a α‖ = ‖synth b α‖ := by
  have hinner : inner ℂ (synth a α) (synth a α)
      = inner ℂ (synth b α) (synth b α) := synth_inner_eq h α α
  have au : ‖inner ℂ (synth a α) (synth a α)‖ = ‖synth a α‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    simp
  have av : ‖inner ℂ (synth b α) (synth b α)‖ = ‖synth b α‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    simp
  have h1 : ‖synth a α‖ ^ 2 = ‖synth b α‖ ^ 2 := by
    rw [← au, ← av, hinner]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num)).mp h1

/-- Kernel consistency: zero synthesis in `a` forces zero synthesis in `b`. -/
theorem synth_eq_zero_of {a b : ι → V} (h : EqualGram a b) (α : ι →₀ ℂ)
    (hz : synth a α = 0) : synth b α = 0 := by
  have hn := synth_norm_eq h α
  rw [hz, norm_zero] at hn
  exact norm_eq_zero.mp hn.symm

/-- Synthesis of any coefficients lies in the span of the family. -/
theorem synth_mem_span (a : ι → V) (α : ι →₀ ℂ) :
    synth a α ∈ Submodule.span ℂ (Set.range a) := by
  rw [synth_eq_sum]
  exact Submodule.sum_mem _ fun x _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self x))

/-- Each generator is a synthesis of `single x 1`. -/
theorem mem_span_single (a : ι → V) (x : ι) :
    a x = synth a (Finsupp.single x (1 : ℂ)) :=
  (synth_single a x).symm

/-- Equal Gram families have equal synthesis kernels. -/
theorem synth_ker_eq {a b : ι → V} (h : EqualGram a b) :
    LinearMap.ker (synthLM a) = LinearMap.ker (synthLM b) := by
  ext α
  constructor
  · intro hα
    have hz : synth a α = 0 := by
      have := LinearMap.mem_ker.mp hα
      simpa [synth] using this
    have := synth_eq_zero_of h α hz
    exact LinearMap.mem_ker.mpr (by simpa [synth] using this)
  · intro hα
    have hz : synth b α = 0 := by
      have := LinearMap.mem_ker.mp hα
      simpa [synth] using this
    have h' : EqualGram b a := fun x y => (h x y).symm
    have := synth_eq_zero_of h' α hz
    exact LinearMap.mem_ker.mpr (by simpa [synth] using this)

/-- Mapping generators: synthesis of `single x 1` is `a x` resp `b x`. -/
theorem synth_single_pair {a b : ι → V} (h : EqualGram a b) (x : ι) :
    synth a (Finsupp.single x (1 : ℂ)) = a x ∧
    synth b (Finsupp.single x (1 : ℂ)) = b x :=
  ⟨synth_single a x, synth_single b x⟩

/-- Bidirectional kernel consistency. -/
theorem synth_eq_zero_iff {a b : ι → V} (h : EqualGram a b) (α : ι →₀ ℂ) :
    synth a α = 0 ↔ synth b α = 0 := by
  constructor
  · exact synth_eq_zero_of h α
  · intro hz
    have h' : EqualGram b a := fun x y => (h x y).symm
    exact synth_eq_zero_of h' α hz

/-- Equal Gram families: syntheses have equal pairwise inner products of
    any two coefficient families (the full content needed for the span
    isometry). -/
theorem synth_cross_eq {a b : ι → V} (h : EqualGram a b)
    (α β : ι →₀ ℂ) :
    inner ℂ (synth a α) (synth a β) = inner ℂ (synth b α) (synth b β) :=
  synth_inner_eq h α β

/-- Generators lie in the range of synthesis. -/
theorem mem_range_single (a : ι → V) (x : ι) :
    a x ∈ LinearMap.range (synthLM a) := by
  refine ⟨Finsupp.single x (1 : ℂ), ?_⟩
  rw [← synth, synth_single]

/-- Range of synthesis equals the span of the family. -/
theorem range_synthLM_eq_span (a : ι → V) :
    LinearMap.range (synthLM a) = Submodule.span ℂ (Set.range a) := by
  apply le_antisymm
  · intro v hv
    obtain ⟨α, rfl⟩ := LinearMap.mem_range.mp hv
    exact synth_mem_span a α
  · rw [Submodule.span_le]
    intro y hy
    obtain ⟨x, rfl⟩ := Set.mem_range.mp hy
    exact mem_range_single a x

/-- Induced linear equivalence of the two synthesis ranges, from the
    first isomorphism theorem and equality of kernels. -/
noncomputable def rangeEquiv {a b : ι → V} (h : EqualGram a b) :
    LinearMap.range (synthLM a) ≃ₗ[ℂ] LinearMap.range (synthLM b) :=
  (LinearMap.quotKerEquivRange (synthLM a)).symm.trans
    ((Submodule.quotEquivOfEq _ _ (synth_ker_eq h)).trans
      (LinearMap.quotKerEquivRange (synthLM b)))

/-- Membership of a synthesis in its range. -/
theorem mem_range_synth (a : ι → V) (α : ι →₀ ℂ) :
    synthLM a α ∈ LinearMap.range (synthLM a) :=
  LinearMap.mem_range.mpr ⟨α, rfl⟩

/-- The range equivalence maps a synthesis of `a` to the corresponding
    synthesis of `b`, as ambient vectors. -/
theorem rangeEquiv_coe (h : EqualGram a b) (α : ι →₀ ℂ) :
    (rangeEquiv h ⟨synthLM a α, mem_range_synth a α⟩ : V) = synthLM b α := by
  have hsymm :
      (LinearMap.quotKerEquivRange (synthLM a)).symm
          ⟨synthLM a α, mem_range_synth a α⟩
        = (LinearMap.ker (synthLM a)).mkQ α :=
    LinearMap.quotKerEquivRange_symm_apply_image (synthLM a) α (mem_range_synth a α)
  unfold rangeEquiv
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hsymm]
  rfl

/-- Norm preservation of the range equivalence. -/
theorem rangeEquiv_norm {a b : ι → V} (h : EqualGram a b)
    (x : LinearMap.range (synthLM a)) :
    ‖(rangeEquiv h x : V)‖ = ‖(x : V)‖ := by
  obtain ⟨α, hα⟩ := LinearMap.mem_range.mp x.2
  have hxeq : (x : V) = synthLM a α := hα.symm
  have hco : (rangeEquiv h x : V) = synthLM b α := by
    have hx' : x = ⟨synthLM a α, mem_range_synth a α⟩ := by
      apply Subtype.ext; exact hα.symm
    rw [hx']
    exact rangeEquiv_coe h α
  rw [hxeq, hco]
  exact (synth_norm_eq h α).symm

/-- Range equivalence is isometric. -/
noncomputable def rangeIsometry {a b : ι → V} (h : EqualGram a b) :
    LinearMap.range (synthLM a) ≃ₗᵢ[ℂ] LinearMap.range (synthLM b) where
  toLinearEquiv := rangeEquiv h
  norm_map' := fun x => rangeEquiv_norm h x

/-- Transport the range isometry along `range = span` to a linear isometry
    of the spans of the two families. -/
noncomputable def spanIsometry {a b : ι → V} (h : EqualGram a b) :
    Submodule.span ℂ (Set.range a) ≃ₗᵢ[ℂ] Submodule.span ℂ (Set.range b) :=
  (LinearIsometryEquiv.ofEq _ _ (range_synthLM_eq_span a).symm).trans
    ((rangeIsometry h).trans
      (LinearIsometryEquiv.ofEq _ _ (range_synthLM_eq_span b)))

/-- Generators have equal norms. -/
theorem spanIsometry_norm_single {a b : ι → V} (h : EqualGram a b) (x : ι) :
    ‖a x‖ = ‖b x‖ := by
  have hn := synth_norm_eq h (Finsupp.single x (1 : ℂ))
  rwa [synth_single, synth_single] at hn

/-- `synthLM a (single x 1) = a x` (linearity form of `synth_single`). -/
theorem synthLM_single (a : ι → V) (x : ι) :
    synthLM a (Finsupp.single x (1 : ℂ)) = a x :=
  synth_single a x

/-- Membership of a generator in its range. -/
theorem mem_range_single' (a : ι → V) (x : ι) :
    ∃ α : ι →₀ ℂ, synthLM a α = a x :=
  ⟨Finsupp.single x (1 : ℂ), synthLM_single a x⟩

/-- The span isometry maps the generator `a x` to `b x`. -/
theorem spanIsometry_apply {a b : ι → V} (h : EqualGram a b) (x : ι) :
    (spanIsometry h
        ⟨a x, Submodule.subset_span (Set.mem_range_self x)⟩ : V) = b x := by
  have hcoe := rangeEquiv_coe h (Finsupp.single x (1 : ℂ))
  have ha : a x = synthLM a (Finsupp.single x (1 : ℂ)) :=
    (synthLM_single a x).symm
  have hmem : synthLM a (Finsupp.single x (1 : ℂ))
      ∈ LinearMap.range (synthLM a) := mem_range_synth a _
  -- the span element equals the ofEq-preimage of the range element
  have hpack :
      (⟨a x, Submodule.subset_span (Set.mem_range_self x)⟩
        : Submodule.span ℂ (Set.range a))
      = (LinearIsometryEquiv.ofEq _ _
          (range_synthLM_eq_span a).symm).symm
        ⟨synthLM a (Finsupp.single x (1 : ℂ)), hmem⟩ := by
    apply Subtype.ext
    show a x = synthLM a (Finsupp.single x (1 : ℂ))
    exact ha
  -- spanIsometry applies as ofEq ∘ rangeIsometry ∘ ofEq
  have key :
      (spanIsometry h
          ⟨a x, Submodule.subset_span (Set.mem_range_self x)⟩ : V)
      = (rangeIsometry h ⟨synthLM a (Finsupp.single x (1 : ℂ)), hmem⟩ : V) := by
    unfold spanIsometry
    rw [hpack]
    simp only [LinearIsometryEquiv.trans_apply,
      LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.coe_ofEq_apply]
  rw [key]
  have h2 :
      (rangeIsometry h ⟨synthLM a (Finsupp.single x (1 : ℂ)), hmem⟩ : V)
      = synthLM b (Finsupp.single x (1 : ℂ)) := by
    have hxeq :
        (⟨synthLM a (Finsupp.single x (1 : ℂ)), hmem⟩
          : LinearMap.range (synthLM a))
        = ⟨synthLM a (Finsupp.single x (1 : ℂ)), mem_range_synth a _⟩ := rfl
    rw [hxeq]
    show (rangeEquiv h _ : V) = _
    exact hcoe
  rw [h2]
  exact synthLM_single b x

section ClosedSpans

variable [CompleteSpace V]

/-- Closed span of the family `a`. -/
def cspan (a : ι → V) : Submodule ℂ V :=
  (Submodule.span ℂ (Set.range a)).topologicalClosure

/-- Closed spans are complete. -/
instance cspan_complete (a : ι → V) : CompleteSpace (cspan a) :=
  Submodule.topologicalClosure.completeSpace (Submodule.span ℂ (Set.range a))

/-- Inclusion of the algebraic span into its topological closure. -/
noncomputable def spanIncl (a : ι → V) :
    Submodule.span ℂ (Set.range a) →L[ℂ] cspan a :=
  (Submodule.span ℂ (Set.range a)).subtypeL.codRestrict (cspan a)
    (fun x => Submodule.le_topologicalClosure (Submodule.span ℂ (Set.range a)) x.2)

/-- `Set.range` of the span inclusion is the algebraic span, as a set. -/
theorem range_spanIncl (a : ι → V) :
    Set.range (spanIncl a)
      = (Submodule.span ℂ (Set.range a)).comap (cspan a).subtype := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, rfl⟩ := Set.mem_range.mp hy
    simp [spanIncl, ContinuousLinearMap.codRestrict]
  · intro hy
    refine ⟨(⟨y, hy⟩ : Submodule.span ℂ (Set.range a)), ?_⟩
    apply Subtype.ext
    rfl

-- DenseRange (spanIncl a) is the next density fact; proved via
-- `Submodule.dense_iff_topologicalClosure_eq_top` once the comap
-- identification is complete.  Continue with ContinuousLinearMap.extend.

-- Next: ContinuousLinearMap.extend of spanIsometry to the closed spans,
-- inverse composition on a dense subspace, then the stabilized unitary.


/-! ## Dense inclusion and continuous extension -/

lemma spanIncl_dense (a : ι → V) : DenseRange (spanIncl a) := by
  change DenseRange (Set.inclusion
    (show (Submodule.span ℂ (Set.range a) : Set V) ⊆ (cspan a : Set V) from
      Submodule.le_topologicalClosure _))
  apply (denseRange_inclusion_iff _).2
  exact Set.Subset.rfl

lemma spanIncl_isometry (a : ι → V) : Isometry (spanIncl a) := by
  intro x y
  rfl

def cspanMap {a b : ι → V} (h : EqualGram a b) : cspan a →L[ℂ] cspan b :=
  ContinuousLinearMap.extend
    ((spanIncl b).comp (spanIsometry h).toLinearIsometry.toContinuousLinearMap)
    (spanIncl a) (spanIncl_dense a) (spanIncl_isometry a).isUniformInducing

lemma cspanMap_apply_span {a b : ι → V} (h : EqualGram a b)
    (x : Submodule.span ℂ (Set.range a)) :
    cspanMap h (spanIncl a x) = spanIncl b (spanIsometry h x) := by
  exact ContinuousLinearMap.extend_eq _ _ _ _ x

/-- Norm equality is a closed property; `cspanMap` preserves norms on the
    dense image of the algebraic span, hence everywhere. -/
theorem cspanMap_norm {a b : ι → V} (h : EqualGram a b) (x : cspan a) :
    ‖cspanMap h x‖ = ‖x‖ := by
  -- the set of points where norms agree is closed
  have hclosed : IsClosed {x : cspan a | ‖cspanMap h x‖ = ‖x‖} := by
    refine isClosed_eq ?_ ?_
    · exact (cspanMap h).continuous.norm
    · exact continuous_norm
  -- it contains the dense image of the algebraic span
  have hsubset : Set.range (spanIncl a)
      ⊆ {x : cspan a | ‖cspanMap h x‖ = ‖x‖} := by
    intro y hy
    obtain ⟨z, rfl⟩ := Set.mem_range.mp hy
    have hap := cspanMap_apply_span h z
    simp only [Set.mem_setOf_eq]
    rw [hap]
    have hn : ‖(spanIncl b (spanIsometry h z) : cspan b)‖
        = ‖(spanIsometry h z : Submodule.span ℂ (Set.range b))‖ := rfl
    -- spanIncl is isometric and spanIsometry is isometric
    have h1 : ‖(spanIncl a z : cspan a)‖ = ‖z‖ := rfl
    have h2 : ‖(spanIncl b (spanIsometry h z) : cspan b)‖
        = ‖spanIsometry h z‖ := rfl
    have h3 : ‖spanIsometry h z‖ = ‖z‖ := LinearIsometryEquiv.norm_map _ _
    rw [h1, h2, h3]
  -- dense + closed ⇒ all
  have hclo : ∀ y : cspan a, y ∈ closure (Set.range (spanIncl a)) := by
    intro y
    have hd : Dense (Set.range (spanIncl a)) := spanIncl_dense a
    have hcl : closure (Set.range (spanIncl a)) = (⊤ : Set (cspan a)) :=
      dense_iff_closure_eq.mp hd
    have : y ∈ (⊤ : Set (cspan a)) := Set.mem_univ y
    rwa [← hcl] at this
  have hsub : closure (Set.range (spanIncl a))
      ⊆ {y : cspan a | ‖cspanMap h y‖ = ‖y‖} :=
    closure_minimal hsubset hclosed
  exact hsub (hclo x)

/-- Continuous linear extension packaged as a linear isometry. -/
noncomputable def cspanIsometry {a b : ι → V} (h : EqualGram a b) :
    cspan a →ₗᵢ[ℂ] cspan b where
  toLinearMap := (cspanMap h).toLinearMap
  norm_map' := cspanMap_norm h

/-- The isometry `cspanIsometry` agrees with `cspanMap` on the algebraic span. -/
theorem cspanIsometry_apply_span {a b : ι → V} (h : EqualGram a b)
    (x : Submodule.span ℂ (Set.range a)) :
    cspanIsometry h (spanIncl a x) = spanIncl b (spanIsometry h x) :=
  cspanMap_apply_span h x

/-- `cspanIsometry` maps the closed-span generator to the other generator. -/
theorem cspanIsometry_apply {a b : ι → V} (h : EqualGram a b) (x : ι) :
    (cspanIsometry h
        ⟨a x, Submodule.le_topologicalClosure _
          (Submodule.subset_span (Set.mem_range_self x))⟩ : V) = b x := by
  have hx : (⟨a x, Submodule.subset_span (Set.mem_range_self x)⟩
      : Submodule.span ℂ (Set.range a)) = ⟨a x, _⟩ := rfl
  have ha : (⟨a x, Submodule.le_topologicalClosure _
        (Submodule.subset_span (Set.mem_range_self x))⟩ : cspan a)
      = spanIncl a ⟨a x, Submodule.subset_span (Set.mem_range_self x)⟩ := by
    apply Subtype.ext
    rfl
  rw [ha, cspanIsometry_apply_span]
  -- spanIncl b z coerces to z
  change (spanIsometry h
      (⟨a x, Submodule.subset_span (Set.mem_range_self x)⟩
        : Submodule.span ℂ (Set.range a)) : V) = b x
  exact spanIsometry_apply h x

/-- The range of `cspanIsometry` contains the algebraic span of `b`. -/
theorem range_cspanIsometry_of_mem_spanIncl {a b : ι → V} (h : EqualGram a b)
    (v : cspan b) (hv : v ∈ Set.range (spanIncl b)) :
    v ∈ Set.range (⇑(cspanIsometry h)) := by
  obtain ⟨z, rfl⟩ := Set.mem_range.mp hv
  obtain ⟨w, hw⟩ := (spanIsometry h).surjective z
  refine ⟨spanIncl a w, ?_⟩
  rw [cspanIsometry_apply_span, hw]

/-- The range of `cspanIsometry` is dense in `cspan b`. -/
theorem dense_range_cspanIsometry {a b : ι → V} (h : EqualGram a b) :
    Dense (Set.range (⇑(cspanIsometry h))) := by
  have hsub : Set.range (spanIncl b)
      ⊆ Set.range (⇑(cspanIsometry h)) := by
    intro v hv
    exact range_cspanIsometry_of_mem_spanIncl h v hv
  exact (spanIncl_dense b).mono hsub

/-- Closed-span linear isometric equivalence via `ofSurjective`. -/
noncomputable def cspanEquiv {a b : ι → V} (h : EqualGram a b) :
    cspan a ≃ₗᵢ[ℂ] cspan b :=
  LinearIsometryEquiv.ofSurjective (cspanIsometry h) (by
    have hiso : Isometry (⇑(cspanIsometry h)) := (cspanIsometry h).isometry
    have hclo : IsClosed (Set.range (⇑(cspanIsometry h))) :=
      hiso.isClosedEmbedding.isClosed_range
    have hd := dense_range_cspanIsometry h
    intro y
    have hy : y ∈ closure (Set.range (⇑(cspanIsometry h))) := hd y
    rw [hclo.closure_eq] at hy
    exact hy)

/-- `cspanEquiv` maps closed-span generators to generators. -/
theorem cspanEquiv_apply {a b : ι → V} (h : EqualGram a b) (x : ι) :
    (cspanEquiv h
        ⟨a x, Submodule.le_topologicalClosure _
          (Submodule.subset_span (Set.mem_range_self x))⟩ : V) = b x := by
  have h1 : (cspanEquiv h
      (⟨a x, Submodule.le_topologicalClosure _
        (Submodule.subset_span (Set.mem_range_self x))⟩ : cspan a) : V)
      = (cspanIsometry h
        (⟨a x, Submodule.le_topologicalClosure _
          (Submodule.subset_span (Set.mem_range_self x))⟩ : cspan a) : V) := by
    simp [cspanEquiv, LinearIsometryEquiv.ofSurjective]
  rw [h1]
  exact cspanIsometry_apply h x

-- Next: ℓ²κ stabilization of the orthogonal complements, single unitary.
