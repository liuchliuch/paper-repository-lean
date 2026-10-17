import Paper27.Geometry.NormalAtlasAction
import Paper27.Geometry.RamificationDichotomy
import Paper27.Geometry.RetractionFactorization

/-!
# Isolating actual components and retaining punctured transversality

All isolation and transversality statements below are proved from actual
finite disjoint curve families, actual ramification-set coverage, and actual
factorizations through unramified restrictions. No punctured transversality,
meromorphic extension, pole bound, or averaging theorem is a classical input.
The action construction uses only the general division, regularity, and germ
gluing interfaces already separated in `NormalAtlasAction`.
-/

noncomputable section
open scoped Manifold Topology
open Filter

namespace Paper27.Geometry

variable {X : CompactComplexSurface}

namespace DisjointCurveFamily

/-- Remove the other finitely many compact components. -/
def isolatingNeighbourhood (F : DisjointCurveFamily X) (j : F.Index) :
    (F.member j).Neighbourhood where
  domain := (⋃ i : {i : F.Index // i ≠ j}, (F.member i.val).support)ᶜ
  open_domain := (isClosed_iUnion_of_finite fun i : {i : F.Index // i ≠ j} =>
    (F.member i.val).support_isClosed).isOpen_compl
  contains := by
    intro p hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    exact Set.disjoint_left.mp (F.disjoint i.property) hi ⟨p, rfl⟩

theorem isolating_support_eq (F : DisjointCurveFamily X) (j : F.Index) :
    F.support ∩ (F.isolatingNeighbourhood j).domain =
      (F.member j).support ∩ (F.isolatingNeighbourhood j).domain := by
  ext x
  constructor
  · rintro ⟨hF, hx⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hF
    have hij : i = j := by
      by_contra hne
      exact hx (Set.mem_iUnion.mpr ⟨⟨i, hne⟩, hi⟩)
    exact ⟨hij ▸ hi, hx⟩
  · rintro ⟨hj, hx⟩
    exact ⟨Set.mem_iUnion.mpr ⟨j, hj⟩, hx⟩

/-- The same open set as an actual neighbourhood of any embedded curve
with the same support as the selected member. -/
def isolatingNeighbourhoodFor (F : DisjointCurveFamily X) (D : EmbeddedCurve X)
    (j : F.Index) (hD : D.support = (F.member j).support) : D.Neighbourhood where
  domain := (F.isolatingNeighbourhood j).domain
  open_domain := (F.isolatingNeighbourhood j).open_domain
  contains := by
    intro p
    have hp : D.inclusion p ∈ (F.member j).support := hD ▸ (show D.inclusion p ∈ D.support from ⟨p, rfl⟩)
    obtain ⟨q, hq⟩ := hp
    rw [← hq]
    exact (F.isolatingNeighbourhood j).contains q

theorem not_mem_support_of_punctured_isolation (F : DisjointCurveFamily X)
    (D : EmbeddedCurve X) (j : F.Index) (hD : D.support = (F.member j).support)
    {x : X} (hx : x ∈ (F.isolatingNeighbourhoodFor D j hD).domain)
    (hpuncture : x ∉ D.support) : x ∉ F.support := by
  intro hF
  have hmember := ((Set.ext_iff.mp (F.isolating_support_eq j)) x).mp ⟨hF, hx⟩
  exact hpuncture (hD.symm ▸ hmember.1)

end DisjointCurveFamily

namespace PuncturedNeighbourhoods

variable {D : EmbeddedCurve X} {U : D.Neighbourhood}

/-- The joint differential of the actual retraction functions. Global
regularity of the arbitrary extensions outside their domains is not used. -/
def jointDifferential {V : D.Neighbourhood} (r : D.Retraction U) (s : D.Retraction V)
    (x : X) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun x).prod
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) s.toFun x)

/-- Actual nonsingularity at every point of the punctured neighbourhood. -/
def JointTransverse (r s : D.Retraction U) : Prop :=
  ∀ x ∈ U.domain, x ∉ D.support → Function.Bijective (jointDifferential r s x)

theorem not_ramified_of_isolation {f g : Fibration X}
    (F : RamificationCurveFamily f g) (j : F.Index)
    (hD : D.support = (F.member j).support) {x : X}
    (hx : x ∈ (F.toDisjointCurveFamily.isolatingNeighbourhoodFor D j hD).domain)
    (hpuncture : x ∉ D.support) : x ∉ RamificationSupport.ramificationSet f g := by
  rw [← F.support_eq]
  exact F.toDisjointCurveFamily.not_mem_support_of_punctured_isolation D j hD hx hpuncture

/-- Isolation gives nonsingularity of the actual paired holomorphic map,
before passing to any covering retractions. -/
theorem pair_joint_bijective_of_isolation {f g : Fibration X}
    (F : RamificationCurveFamily f g) (j : F.Index)
    (hD : D.support = (F.member j).support) {x : X}
    (hx : x ∈ (F.toDisjointCurveFamily.isolatingNeighbourhoodFor D j hD).domain)
    (hpuncture : x ∉ D.support) :
    Function.Bijective (RetractionFactorization.jointDifferential
      (CoordinateCalculus.fibrationMap f) (CoordinateCalculus.fibrationMap g) x) :=
  RetractionFactorization.joint_bijective_of_not_ramified f g x
    (not_ramified_of_isolation F j hD hx hpuncture)

/-- Two different actual ramification families can be isolated at one
common actual component. Intersecting with U keeps the existing retractions
holomorphic on the resulting actual open neighbourhood. -/
theorem common_isolating_neighbourhood (f g h : Fibration X)
    (F : RamificationCurveFamily f g) (E : RamificationCurveFamily f h)
    (j : F.Index) (k : E.Index)
    (hD : D.support = (F.member j).support)
    (hE : D.support = (E.member k).support) (U : D.Neighbourhood) :
    ∃ V : D.Neighbourhood, V.domain ⊆ U.domain ∧
      (∀ x ∈ V.domain, x ∉ D.support → x ∉ RamificationSupport.ramificationSet f g) ∧
      (∀ x ∈ V.domain, x ∉ D.support → x ∉ RamificationSupport.ramificationSet f h) := by
  let VF := F.toDisjointCurveFamily.isolatingNeighbourhoodFor D j hD
  let VE := E.toDisjointCurveFamily.isolatingNeighbourhoodFor D k hE
  let V : D.Neighbourhood :=
    { domain := U.domain ∩ VF.domain ∩ VE.domain
      open_domain := (U.open_domain.inter VF.open_domain).inter VE.open_domain
      contains := fun p => ⟨⟨U.contains p, VF.contains p⟩, VE.contains p⟩ }
  refine ⟨V, (fun _ hx => hx.1.1), ?_, ?_⟩
  · intro x hx hp
    exact not_ramified_of_isolation F j hD hx.1.2 hp
  · intro x hx hp
    exact not_ramified_of_isolation E k hE hx.2 hp

/-- The same finite-intersection argument simultaneously isolates the three
actual pair ramification families at a common embedded curve. -/
theorem three_isolating_neighbourhood (f g h : Fibration X)
    (F : RamificationCurveFamily f g) (E : RamificationCurveFamily f h)
    (H : RamificationCurveFamily g h) (j : F.Index) (k : E.Index) (l : H.Index)
    (hD : D.support = (F.member j).support)
    (hE : D.support = (E.member k).support)
    (hH : D.support = (H.member l).support) (U : D.Neighbourhood) :
    ∃ V : D.Neighbourhood, V.domain ⊆ U.domain ∧
      (∀ x ∈ V.domain, x ∉ D.support → x ∉ RamificationSupport.ramificationSet f g) ∧
      (∀ x ∈ V.domain, x ∉ D.support → x ∉ RamificationSupport.ramificationSet f h) ∧
      (∀ x ∈ V.domain, x ∉ D.support → x ∉ RamificationSupport.ramificationSet g h) := by
  obtain ⟨V, hVU, hfg, hfh⟩ := common_isolating_neighbourhood f g h F E j k hD hE U
  let VH := H.toDisjointCurveFamily.isolatingNeighbourhoodFor D l hH
  let W : D.Neighbourhood :=
    { domain := V.domain ∩ VH.domain
      open_domain := V.open_domain.inter VH.open_domain
      contains := fun p => ⟨V.contains p, VH.contains p⟩ }
  exact ⟨W, (fun _ hx => hVU hx.1),
    (fun _ hx hp => hfg _ hx.1 hp), (fun _ hx hp => hfh _ hx.1 hp),
    (fun _ hx hp => not_ramified_of_isolation H l hH hx.2 hp)⟩

/-- Independent invertible postcomposition in both scalar coordinates
preserves bijectivity of the joint map. -/
theorem joint_bijective_iff_scalar_bijections (a b : ℂ → ℂ)
    (ha : Function.Bijective a) (hb : Function.Bijective b)
    (l k : (ℂ × ℂ) → ℂ) :
    Function.Bijective (fun v => (l v, k v)) ↔
      Function.Bijective (fun v => (a (l v), b (k v))) := by
  let e : (ℂ × ℂ) ≃ (ℂ × ℂ) :=
    (Equiv.ofBijective a ha).prodCongr (Equiv.ofBijective b hb)
  change Function.Bijective (fun v => (l v, k v)) ↔
    Function.Bijective (e ∘ fun v => (l v, k v))
  constructor
  · exact fun h => e.bijective.comp h
  · intro h
    have hinv := e.symm.bijective.comp h
    convert hinv using 1
    funext v
    exact (e.symm_apply_apply (l v, k v)).symm

/-- Differentiate the two actual factorizations on their respective open
domains. The unramified actual restriction maps remove precisely the two
invertible scalar postcompositions. -/
theorem joint_retractions_bijective_iff {V : D.Neighbourhood}
    (r : D.Retraction U) (s : D.Retraction V) (f g : Fibration X)
    (hf : D.Unramified f) (hg : D.Unramified g)
    (hr : RetractionFactorization.Factorization r f)
    (hs : RetractionFactorization.Factorization s g)
    (x : X) (hxU : x ∈ U.domain) (hxV : x ∈ V.domain) :
    Function.Bijective (jointDifferential r s x) ↔
      Function.Bijective (RetractionFactorization.jointDifferential
        (CoordinateCalculus.fibrationMap f) (CoordinateCalculus.fibrationMap g) x) := by
  let a : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) (r.toFun x)
  let b : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap g) (s.toFun x)
  let l : (ℂ × ℂ) →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun x
  let k : (ℂ × ℂ) →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) s.toFun x
  have hderivf : a.comp l = mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f x :=
    RetractionFactorization.factorization_derivative r f hr ⟨x, hxU⟩
  have hderivg : b.comp k = mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) g x :=
    RetractionFactorization.factorization_derivative s g hs ⟨x, hxV⟩
  have hiff := joint_bijective_iff_scalar_bijections a b (hf _) (hg _) l k
  have heq : (fun v => (a (l v), b (k v))) =
      RetractionFactorization.jointDifferential
        (CoordinateCalculus.fibrationMap f) (CoordinateCalculus.fibrationMap g) x := by
    funext v
    exact Prod.ext (congrArg (fun L : (ℂ × ℂ) →L[ℂ] ℂ => L v) hderivf)
      (congrArg (fun L : (ℂ × ℂ) →L[ℂ] ℂ => L v) hderivg)
  rw [heq] at hiff
  exact hiff

/-- The actual ramification families imply punctured joint transversality
for all three retractions after one common neighbourhood restriction. -/
theorem exists_punctured_transverse_neighbourhood
    (f g h : Fibration X) (F : RamificationCurveFamily f g)
    (E : RamificationCurveFamily f h) (j : F.Index) (k : E.Index)
    (hD : D.support = (F.member j).support)
    (hE : D.support = (E.member k).support)
    (r₁ r₂ r₃ : D.Retraction U)
    (hf : D.Unramified f) (hg : D.Unramified g) (hh : D.Unramified h)
    (hr₁ : RetractionFactorization.Factorization r₁ f)
    (hr₂ : RetractionFactorization.Factorization r₂ g)
    (hr₃ : RetractionFactorization.Factorization r₃ h) :
    ∃ (V : D.Neighbourhood) (hVU : V.domain ⊆ U.domain),
      JointTransverse (RetractionFactorization.restrictRetraction r₁ V hVU)
        (RetractionFactorization.restrictRetraction r₂ V hVU) ∧
      JointTransverse (RetractionFactorization.restrictRetraction r₁ V hVU)
        (RetractionFactorization.restrictRetraction r₃ V hVU) := by
  obtain ⟨V, hVU, hfg, hfh⟩ := common_isolating_neighbourhood f g h F E j k hD hE U
  refine ⟨V, hVU, ?_, ?_⟩
  · intro x hx hp
    apply (joint_retractions_bijective_iff r₁ r₂ f g hf hg hr₁ hr₂ x (hVU hx) (hVU hx)).mpr
    exact RetractionFactorization.joint_bijective_of_not_ramified f g x (hfg x hx hp)
  · intro x hx hp
    apply (joint_retractions_bijective_iff r₁ r₃ f h hf hh hr₁ hr₃ x (hVU hx) (hVU hx)).mpr
    exact RetractionFactorization.joint_bijective_of_not_ramified f h x (hfh x hx hp)

theorem jointTransverse_on_smaller {V W : D.Neighbourhood}
    (r s : D.Retraction V) (r' s' : D.Retraction W)
    (hWV : W.domain ⊆ V.domain) (hr : r'.toFun = r.toFun) (hs : s'.toFun = s.toFun)
    (ht : JointTransverse r s) : JointTransverse r' s' := by
  intro x hx hp
  have h := ht x (hWV hx) hp
  change Function.Bijective ((mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r'.toFun x :
    (ℂ × ℂ) →L[ℂ] ℂ).prod (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) s'.toFun x))
  rw [hr, hs]
  exact h

/-- Any actual action fixing D pointwise preserves both D and its punctured
complement. The reverse implication uses the actual inverse group element. -/
theorem action_preserves_support_iff {G : Type} [Group G] {r : D.Retraction U}
    (action : NeighbourhoodSplittings.NeighbourhoodAction G r)
    (hfix : ∀ g p, action.map g (D.inclusion p) = D.inclusion p)
    (g : G) (x : X) (hx : x ∈ U.domain) :
    action.map g x ∈ D.support ↔ x ∈ D.support := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    calc
      D.inclusion p = action.map (g⁻¹) (D.inclusion p) := (hfix (g⁻¹) p).symm
      _ = action.map (g⁻¹) (action.map g x) := congrArg (action.map (g⁻¹)) hp
      _ = action.map (g⁻¹ * g) x := (action.map_mul_point (g⁻¹) g ⟨x, hx⟩).symm
      _ = action.map 1 x := by rw [inv_mul_cancel]
      _ = x := action.map_one_point ⟨x, hx⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, by rw [← hp, hfix]⟩

/-- Build the actual finite normal-chart action inside a prescribed smaller
neighbourhood, retaining the two actual punctured transversality conditions
and all actual rotation germs. -/
theorem action_with_punctured_transverse
    (division : NormalAtlasAction.HolomorphicNormalDivision)
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (gluing : NormalAtlasAction.HolomorphicOpenGermGluing)
    {r₁ r₂ : D.Retraction U} {n : ℕ}
    (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n) (hn : 0 < n)
    (r₃ : D.Retraction U) (V : D.Neighbourhood) (hVU : V.domain ⊆ U.domain)
    (h₁₂ : JointTransverse (RetractionFactorization.restrictRetraction r₁ V hVU)
      (RetractionFactorization.restrictRetraction r₂ V hVU))
    (h₁₃ : JointTransverse (RetractionFactorization.restrictRetraction r₁ V hVU)
      (RetractionFactorization.restrictRetraction r₃ V hVU))
    {G : Type} [Group G] [Fintype G] (scalar : G →* ℂˣ)
    (hroot : ∀ g, (scalar g : ℂ) ^ n = 1) :
    ∃ (W : D.Neighbourhood) (r s t : D.Retraction W)
      (action : NeighbourhoodSplittings.NeighbourhoodAction G r),
      W.domain ⊆ V.domain ∧ W.domain ⊆ U.domain ∧
      r.toFun = r₁.toFun ∧ s.toFun = r₂.toFun ∧ t.toFun = r₃.toFun ∧
      JointTransverse r s ∧ JointTransverse r t ∧
      (∀ g p, action.map g =ᶠ[𝓝 (D.inclusion p)]
        NormalAtlasAction.localRotation (A.chart p p).coordinates (scalar g : ℂ)) ∧
      (∀ g p, action.map g (D.inclusion p) = D.inclusion p) ∧
      (∀ g x, x ∈ W.domain →
        (action.map g x ∈ D.support ↔ x ∈ D.support)) ∧
      (∀ g x, x ∈ W.domain → s.toFun (action.map g x) = s.toFun x) := by
  obtain ⟨W, r, action, hWV, hWU, hr, hgerm, hs⟩ :=
    NormalAtlasAction.action_from_normalAtlas division regularity gluing A hn scalar hroot V
  let s := RetractionFactorization.restrictRetraction r₂ W hWU
  let t := RetractionFactorization.restrictRetraction r₃ W hWU
  have hfix : ∀ g p, action.map g (D.inclusion p) = D.inclusion p := by
    intro g p
    exact (hgerm g p).self_of_nhds.trans (NormalAtlasAction.localRotation_fixed
      (A.chart p p).coordinates (scalar g : ℂ)
      (A.source_mem p p (mem_chart_source ℂ p))
      (by rw [A.centre p p (mem_chart_source ℂ p)]))
  refine ⟨W, r, s, t, action, hWV, hWU, hr, rfl, rfl, ?_, ?_, hgerm, hfix, ?_, hs⟩
  · exact jointTransverse_on_smaller _ _ r s hWV hr rfl h₁₂
  · exact jointTransverse_on_smaller _ _ r t hWV hr rfl h₁₃
  · intro g x hx
    exact action_preserves_support_iff action hfix g x hx

/-- The complete family-to-action assembly. The punctured joint conditions
are consequences of the two actual curve families, not extra hypotheses. -/
theorem family_action_with_punctured_transverse
    (division : NormalAtlasAction.HolomorphicNormalDivision)
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (gluing : NormalAtlasAction.HolomorphicOpenGermGluing)
    (f g h : Fibration X) (F : RamificationCurveFamily f g)
    (E : RamificationCurveFamily f h) (j : F.Index) (k : E.Index)
    (hD : D.support = (F.member j).support)
    (hE : D.support = (E.member k).support)
    {r₁ r₂ : D.Retraction U} {n : ℕ}
    (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n) (hn : 0 < n)
    (r₃ : D.Retraction U)
    (hf : D.Unramified f) (hg : D.Unramified g) (hh : D.Unramified h)
    (hr₁ : RetractionFactorization.Factorization r₁ f)
    (hr₂ : RetractionFactorization.Factorization r₂ g)
    (hr₃ : RetractionFactorization.Factorization r₃ h)
    {G : Type} [Group G] [Fintype G] (scalar : G →* ℂˣ)
    (hroot : ∀ g, (scalar g : ℂ) ^ n = 1) :
    ∃ (W : D.Neighbourhood) (r s t : D.Retraction W)
      (action : NeighbourhoodSplittings.NeighbourhoodAction G r),
      W.domain ⊆ U.domain ∧
      r.toFun = r₁.toFun ∧ s.toFun = r₂.toFun ∧ t.toFun = r₃.toFun ∧
      JointTransverse r s ∧ JointTransverse r t ∧
      (∀ g p, action.map g =ᶠ[𝓝 (D.inclusion p)]
        NormalAtlasAction.localRotation (A.chart p p).coordinates (scalar g : ℂ)) ∧
      (∀ g p, action.map g (D.inclusion p) = D.inclusion p) ∧
      (∀ g x, x ∈ W.domain →
        (action.map g x ∈ D.support ↔ x ∈ D.support)) ∧
      (∀ g x, x ∈ W.domain → s.toFun (action.map g x) = s.toFun x) := by
  obtain ⟨V, hVU, h₁₂, h₁₃⟩ := exists_punctured_transverse_neighbourhood
    f g h F E j k hD hE r₁ r₂ r₃ hf hg hh hr₁ hr₂ hr₃
  obtain ⟨W, r, s, t, action, _hWV, hWU, hr, hs, ht, h₁₂, h₁₃, hgerm, hfix, hpuncture, hpres⟩ :=
    action_with_punctured_transverse division regularity gluing A hn r₃ V hVU h₁₂ h₁₃ scalar hroot
  exact ⟨W, r, s, t, action, hWU, hr, hs, ht, h₁₂, h₁₃, hgerm, hfix, hpuncture, hpres⟩

/-- Specialize to the actual finite group of all n-th roots of unity.
There is no separately supplied group action or scalar representation. -/
theorem cyclic_family_action_with_punctured_transverse
    (division : NormalAtlasAction.HolomorphicNormalDivision)
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (gluing : NormalAtlasAction.HolomorphicOpenGermGluing)
    (f g h : Fibration X) (F : RamificationCurveFamily f g)
    (E : RamificationCurveFamily f h) (j : F.Index) (k : E.Index)
    (hD : D.support = (F.member j).support)
    (hE : D.support = (E.member k).support)
    {r₁ r₂ : D.Retraction U} {n : ℕ}
    (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n) (hn : 2 ≤ n)
    (r₃ : D.Retraction U)
    (hf : D.Unramified f) (hg : D.Unramified g) (hh : D.Unramified h)
    (hr₁ : RetractionFactorization.Factorization r₁ f)
    (hr₂ : RetractionFactorization.Factorization r₂ g)
    (hr₃ : RetractionFactorization.Factorization r₃ h) :
    ∃ (W : D.Neighbourhood) (r s t : D.Retraction W)
      (action : NeighbourhoodSplittings.NeighbourhoodAction (rootsOfUnity n ℂ) r),
      W.domain ⊆ U.domain ∧
      r.toFun = r₁.toFun ∧ s.toFun = r₂.toFun ∧ t.toFun = r₃.toFun ∧
      JointTransverse r s ∧ JointTransverse r t ∧
      (∀ g p, action.map g =ᶠ[𝓝 (D.inclusion p)]
        NormalAtlasAction.localRotation (A.chart p p).coordinates ((g : ℂˣ) : ℂ)) ∧
      (∀ g p, action.map g (D.inclusion p) = D.inclusion p) ∧
      (∀ g x, x ∈ W.domain →
        (action.map g x ∈ D.support ↔ x ∈ D.support)) ∧
      (∀ g x, x ∈ W.domain → s.toFun (action.map g x) = s.toFun x) := by
  letI : NeZero n := ⟨by omega⟩
  let scalar : rootsOfUnity n ℂ →* ℂˣ := (rootsOfUnity n ℂ).subtype
  have hroot : ∀ g, (scalar g : ℂ) ^ n = 1 :=
    fun g => (mem_rootsOfUnity' n g.val).mp g.property
  exact family_action_with_punctured_transverse division regularity gluing f g h F E j k
    hD hE A (by omega) r₃ hf hg hh hr₁ hr₂ hr₃ scalar hroot

end PuncturedNeighbourhoods
end Paper27.Geometry
