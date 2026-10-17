import Paper27.Geometry.RetractionCoordinateGerms
import Paper27.Geometry.NeighbourhoodSplittings
import Paper27.Geometry.ActionGluing
import Mathlib.Topology.Separation.Hausdorff

/-!
# Actual normal rotations and their neighbourhood representatives

The local maps in this file are the actual conjugates c⁻¹(x,αy).
General holomorphic division and germ-sheaf gluing are kept separate from
the own compatibility, finite-group, and actual differential calculations.
-/

noncomputable section
open scoped Manifold Topology BigOperators
open Filter

namespace Paper27.Geometry.NormalAtlasAction

def rotate (α : ℂ) (z : ℂ × ℂ) : ℂ × ℂ := (z.1, α * z.2)

@[simp] theorem rotate_one (z : ℂ × ℂ) : rotate 1 z = z := by
  simp only [rotate, one_mul, Prod.eta]

@[simp] theorem rotate_mul (α β : ℂ) (z : ℂ × ℂ) :
    rotate α (rotate β z) = rotate (α * β) z := by
  simp only [rotate, mul_assoc]

theorem rotate_continuous (α : ℂ) : Continuous (rotate α) :=
  continuous_fst.prodMk (continuous_const.mul continuous_snd)

def rotateLinear (α : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).prod (α • ContinuousLinearMap.snd ℂ ℂ ℂ)

@[simp] theorem rotateLinear_apply (α : ℂ) (v : ℂ × ℂ) :
    rotateLinear α v = rotate α v := rfl

variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ : D.Retraction U} {n : ℕ}

/-- The actual local surface map, with arbitrary values outside the domain
where both chart directions are valid. -/
def localRotation (c : OpenPartialHomeomorph X (ℂ × ℂ)) (α : ℂ) : X → X :=
  fun q => c.symm (rotate α (c q))

theorem localRotation_coordinate (c : OpenPartialHomeomorph X (ℂ × ℂ)) (α : ℂ)
    {q : X} (hq : rotate α (c q) ∈ c.target) :
    c (localRotation c α q) = rotate α (c q) := c.right_inv hq

theorem localRotation_mem (c : OpenPartialHomeomorph X (ℂ × ℂ)) (α : ℂ)
    {q : X} (hq : rotate α (c q) ∈ c.target) :
    localRotation c α q ∈ c.source := c.map_target hq

theorem normal_coordinate_zero_on_curve
    (i : D.curve) (c : RetractionAtlas.NormalFormChart D.curve r₁.toFun r₂.toFun n i)
    (hn : 0 < n) (p : D.curve)
    (hp : D.inclusion p ∈ c.coordinates.source) :
    (c.coordinates (D.inclusion p)).2 = 0 := by
  have hr := c.r_normal _ hp
  have hs := c.s_normal _ hp
  rw [r₁.retract] at hr
  rw [r₂.retract] at hs
  have hz : (c.coordinates (D.inclusion p)).2 ^ n = 0 := by
    linear_combination hr - hs
  exact (pow_eq_zero_iff (Nat.ne_of_gt hn)).mp hz

theorem localRotation_fixed (c : OpenPartialHomeomorph X (ℂ × ℂ)) (α : ℂ)
    {q : X} (hq : q ∈ c.source) (hz : (c q).2 = 0) : localRotation c α q = q := by
  have hr : rotate α (c q) = c q := by
    apply Prod.ext
    · rfl
    · simp only [rotate, hz, mul_zero]
  exact (congrArg c.symm hr).trans (c.left_inv hq)

theorem localRotation_continuousAt (c : OpenPartialHomeomorph X (ℂ × ℂ))
    (α : ℂ) {q : X} (hq : q ∈ c.source) (hz : (c q).2 = 0) :
    ContinuousAt (localRotation c α) q := by
  have hr : rotate α (c q) = c q := Prod.ext rfl (by simp [rotate, hz])
  apply (c.continuousAt_symm ?_).comp
    ((rotate_continuous α).continuousAt.comp (c.continuousAt hq))
  change rotate α (c q) ∈ c.target
  rw [hr]
  exact c.map_source hq

theorem localRotation_eventually_target (c : OpenPartialHomeomorph X (ℂ × ℂ))
    (α : ℂ) {q : X} (hq : q ∈ c.source) (hz : (c q).2 = 0) :
    ∀ᶠ x in 𝓝 q, x ∈ c.source ∧ rotate α (c x) ∈ c.target := by
  have hr : rotate α (c q) = c q := Prod.ext rfl (by simp [rotate, hz])
  have hcont := (rotate_continuous α).continuousAt.comp (c.continuousAt hq)
  have ht := hcont.tendsto (c.open_target.mem_nhds (by
    change rotate α (c q) ∈ c.target
    rw [hr]
    exact c.map_source hq))
  filter_upwards [c.open_source.mem_nhds hq, ht] with x hx htx
  exact ⟨hx, htx⟩

theorem localRotation_preserves (i : D.curve)
    (c : RetractionAtlas.NormalFormChart D.curve r₁.toFun r₂.toFun n i)
    (α : ℂ) (hα : α ^ n = 1) {q : X} (hq : q ∈ c.coordinates.source)
    (ht : rotate α (c.coordinates q) ∈ c.coordinates.target) :
    r₁.toFun (localRotation c.coordinates α q) = r₁.toFun q ∧
      r₂.toFun (localRotation c.coordinates α q) = r₂.toFun q :=
  RetractionAtlas.normal_rotation_preserves_maps D.curve r₁.toFun r₂.toFun n i c
    q _ hq (localRotation_mem c.coordinates α ht) α hα
    (localRotation_coordinate c.coordinates α ht)

theorem localRotation_mul_germ (c : OpenPartialHomeomorph X (ℂ × ℂ))
    (α β : ℂ) {q : X} (hq : q ∈ c.source) (hz : (c q).2 = 0) :
    localRotation c α ∘ localRotation c β =ᶠ[𝓝 q] localRotation c (α * β) := by
  filter_upwards [localRotation_eventually_target c β hq hz] with x hx
  change c.symm (rotate α (c (c.symm (rotate β (c x))))) =
    c.symm (rotate (α * β) (c x))
  rw [c.right_inv hx.2, rotate_mul]

theorem localRotation_one_germ (c : OpenPartialHomeomorph X (ℂ × ℂ))
    {q : X} (hq : q ∈ c.source) : localRotation c 1 =ᶠ[𝓝 q] id :=
  Filter.eventually_of_mem (c.open_source.mem_nhds hq) fun x hx => by
    exact (congrArg c.symm (rotate_one (c x))).trans (c.left_inv hx)

/-- A finite-valued continuous germ is constant. This is the local version
of the finite-root argument in `CyclicTransitions.root_valued_constant`. -/
theorem finite_valued_germ_constant {E : Type*} [TopologicalSpace E]
    {p : E} {f : E → ℂ} (hf : ContinuousAt f p) (s : Set ℂ) (hs : s.Finite)
    (hmem : ∀ᶠ x in 𝓝 p, f x ∈ s) : ∀ᶠ x in 𝓝 p, f x = f p := by
  have hclosed : IsClosed (s \ {f p}) := hs.diff.isClosed
  have havoid : ∀ᶠ x in 𝓝 p, f x ∉ s \ {f p} :=
    hf.tendsto (hclosed.isOpen_compl.mem_nhds (by simp))
  filter_upwards [hmem, havoid] with x hx hav
  by_contra hne
  exact hav ⟨hx, hne⟩

/-- Root-valued quotient uniqueness, on an actual continuous unit germ. -/
theorem unit_rotation_invariant_germ {h : (ℂ × ℂ) → ℂ} {p : ℂ × ℂ}
    {α : ℂ} (hp : p.2 = 0) (hh : ContinuousAt h p) (hzero : h p ≠ 0)
    (hn : 0 < n) (hpow : ∀ᶠ z in 𝓝 p, h (rotate α z) ^ n = h z ^ n) :
    (fun z => h (rotate α z)) =ᶠ[𝓝 p] h := by
  have hfixed : rotate α p = p := Prod.ext rfl (by simp [rotate, hp])
  have hhrot : ContinuousAt h (rotate α p) := by rwa [hfixed]
  have hcont : ContinuousAt (fun z => h (rotate α z) / h z) p :=
    (hhrot.comp (rotate_continuous α).continuousAt).div hh hzero
  have hroot : ∀ᶠ z in 𝓝 p,
      h (rotate α z) / h z ∈ (Polynomial.nthRootsFinset n (1 : ℂ) : Set ℂ) := by
    filter_upwards [hpow, hh.eventually_ne hzero] with z hz hne
    apply (Polynomial.mem_nthRootsFinset hn 1).mpr
    rw [div_pow, hz, div_self (pow_ne_zero _ hne)]
  have hconstant := finite_valued_germ_constant hcont _
    (Polynomial.nthRootsFinset n (1 : ℂ)).finite_toSet hroot
  have hone : h (rotate α p) / h p = 1 := by rw [hfixed, div_self hzero]
  filter_upwards [hconstant, hh.eventually_ne hzero] with z hz hne
  exact (div_eq_one_iff_eq hne).mp (hz.trans hone)

/-- Cancellation by a power of the normal coordinate in continuous germs.
The missing hyperplane is dense, so cancellation extends to its points. -/
theorem cancel_normal_power_germ {f g : (ℂ × ℂ) → ℂ} {p : ℂ × ℂ}
    (hf : ∀ᶠ z in 𝓝 p, ContinuousAt f z) (hg : ∀ᶠ z in 𝓝 p, ContinuousAt g z)
    (hpow : ∀ᶠ z in 𝓝 p, z.2 ^ n * f z = z.2 ^ n * g z) : f =ᶠ[𝓝 p] g := by
  obtain ⟨W, hW, hWo, hpW⟩ := mem_nhds_iff.mp (hf.and (hg.and hpow))
  let S : Set (ℂ × ℂ) := {z | z.2 ≠ 0}
  have hS : Dense S := (dense_compl_singleton (0 : ℂ)).preimage isOpenMap_snd
  have hclosure : W ⊆ closure (W ∩ S) := by
    intro x hx
    apply mem_closure_iff.mpr
    intro O hO hxO
    obtain ⟨y, hyOW, hyS⟩ := hS.inter_open_nonempty (O ∩ W) (hO.inter hWo)
      ⟨x, hxO, hx⟩
    exact ⟨y, hyOW.1, hyOW.2, hyS⟩
  have heq : Set.EqOn f g (W ∩ S) := by
    intro z hz
    exact mul_left_cancel₀ (pow_ne_zero n hz.2) (hW hz.1).2.2
  have hfull := heq.of_subset_closure
    (fun z hz => (hW hz).1.continuousWithinAt)
    (fun z hz => (hW hz).2.1.continuousWithinAt) Set.inter_subset_left hclosure
  exact Filter.eventually_of_mem (hWo.mem_nhds hpW) hfull

/-- Ordinary holomorphic divisibility by the coordinate defining a smooth
hypersurface. There is no index, root, rotation, or action in this interface. -/
def HolomorphicNormalDivision : Prop :=
  ∀ (F : (ℂ × ℂ) → ℂ) (p : ℂ × ℂ), p.2 = 0 → AnalyticAt ℂ F p →
    (∀ᶠ x in 𝓝 p.1, F (x, 0) = 0) →
      ∃ h : (ℂ × ℂ) → ℂ, AnalyticAt ℂ h p ∧
        F =ᶠ[𝓝 p] (fun z => z.2 * h z)

theorem division_value_eq_normal_derivative {F h : (ℂ × ℂ) → ℂ} {p : ℂ × ℂ}
    (hp : p.2 = 0) (hh : AnalyticAt ℂ h p)
    (hfactor : F =ᶠ[𝓝 p] fun z => z.2 * h z) :
    h p = fderiv ℂ F p (0, 1) := by
  have hprod := (hasFDerivAt_snd (𝕜 := ℂ) (p := p)).mul
    hh.differentiableAt.hasFDerivAt
  rw [hfactor.fderiv_eq (𝕜 := ℂ)]
  change h p = fderiv ℂ (Prod.snd * h) p (0, 1)
  rw [hprod.fderiv]
  simp [hp]

/-- From equality of the actual nth powers, division and continuous
cancellation prove rotation compatibility of the actual normal germ. -/
theorem normal_rotation_commutes_germ (division : HolomorphicNormalDivision)
    {F : (ℂ × ℂ) → ℂ} {p : ℂ × ℂ} {α : ℂ}
    (hn : 0 < n) (hp : p.2 = 0) (hα : α ^ n = 1)
    (hF : AnalyticAt ℂ F p) (hvanish : ∀ᶠ x in 𝓝 p.1, F (x, 0) = 0)
    (hderiv : fderiv ℂ F p (0, 1) ≠ 0)
    (hpower : ∀ᶠ z in 𝓝 p, F (rotate α z) ^ n = F z ^ n) :
    F ∘ rotate α =ᶠ[𝓝 p] fun z => α * F z := by
  obtain ⟨h, hh, hfactor⟩ := division F p hp hF hvanish
  have hunit : h p ≠ 0 := by rw [division_value_eq_normal_derivative hp hh hfactor]; exact hderiv
  have hfixed : rotate α p = p := Prod.ext rfl (by simp [rotate, hp])
  have htendsto : Tendsto (rotate α) (𝓝 p) (𝓝 p) := by
    simpa only [hfixed] using (rotate_continuous α).continuousAt.tendsto (x := p)
  have hfactor_rot : ∀ᶠ z in 𝓝 p,
      F (rotate α z) = (rotate α z).2 * h (rotate α z) := hfactor.comp_tendsto htendsto
  have hcontinuous : ∀ᶠ z in 𝓝 p, ContinuousAt (fun w => h (rotate α w) ^ n) z := by
    filter_upwards [htendsto.eventually hh.eventually_analyticAt] with z hz
    exact (hz.continuousAt.comp (rotate_continuous α).continuousAt).pow n
  have hcontinuous' : ∀ᶠ z in 𝓝 p, ContinuousAt (fun w => h w ^ n) z :=
    hh.eventually_analyticAt.mono (fun _ hz => hz.continuousAt.pow n)
  have hunitpow : ∀ᶠ z in 𝓝 p, h (rotate α z) ^ n = h z ^ n := by
    apply cancel_normal_power_germ (n := n) hcontinuous hcontinuous'
    filter_upwards [hfactor, hfactor_rot, hpower] with z hz hr hpz
    rw [hz, hr, mul_pow, mul_pow] at hpz
    simpa only [rotate, mul_pow, hα, one_mul] using hpz
  have hinvariant := unit_rotation_invariant_germ hp hh.continuousAt hunit hn hunitpow
  filter_upwards [hfactor, hfactor_rot, hinvariant] with z hz hr hinv
  change F (rotate α z) = α * F z
  rw [hr, hz, hinv]
  simp only [rotate, mul_assoc]

/-- Actual inverse chart identities give both inverse differential identities.
No nonsingularity label is supplied as an extra geometric assumption. -/
theorem chart_differentials_inverse (c : OpenPartialHomeomorph X (ℂ × ℂ))
    (hc : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c c.source)
    (hi : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c.symm c.target)
    (q : X) (hq : q ∈ c.source) :
    let L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c q
    let K : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c.symm (c q)
    Function.LeftInverse K L ∧ Function.RightInverse K L := by
  let L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c q
  let K : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) := mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c.symm (c q)
  have hcd := hc.mdifferentiableAt (c.open_source.mem_nhds hq)
  have hid := hi.mdifferentiableAt (c.open_target.mem_nhds (c.map_source hq))
  have hl : c.symm ∘ c =ᶠ[𝓝 q] id :=
    Filter.eventually_of_mem (c.open_source.mem_nhds hq) (fun x hx => c.left_inv hx)
  have hr : c ∘ c.symm =ᶠ[𝓝 (c q)] id :=
    Filter.eventually_of_mem (c.open_target.mem_nhds (c.map_source hq))
      (fun z hz => c.right_inv hz)
  have hKL : K.comp L = ContinuousLinearMap.id ℂ (ℂ × ℂ) := by
    have hchain := mfderiv_comp q hid hcd
    rw [hl.mfderiv_eq, mfderiv_id] at hchain
    exact hchain.symm
  have hLK : L.comp K = ContinuousLinearMap.id ℂ (ℂ × ℂ) := by
    have hcd' : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c (c.symm (c q)) := by
      simpa only [c.left_inv hq] using hcd
    have hchain := mfderiv_comp (c q) hcd' hid
    rw [hr.mfderiv_eq, mfderiv_id] at hchain
    have hpoint : (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c (c.symm (c q)) :
        (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) = L := mfderiv_congr_point (c.left_inv hq)
    change ContinuousLinearMap.id ℂ (ℂ × ℂ) =
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c (c.symm (c q))).comp K at hchain
    rw [hpoint] at hchain
    exact hchain.symm
  exact ⟨fun v => congrArg (fun H : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) => H v) hKL,
    fun v => congrArg (fun H : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) => H v) hLK⟩

structure HolomorphicNormalChart (i : D.curve)
    extends RetractionAtlas.NormalFormChart D.curve r₁.toFun r₂.toFun n i where
  holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) coordinates coordinates.source
  inverse_holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
    coordinates.symm coordinates.target

def normalChart (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)
    (i p : D.curve) : HolomorphicNormalChart (r₁ := r₁) (r₂ := r₂) (n := n) i :=
  ⟨A.chart i p, A.holomorphic i p, A.inverse_holomorphic i p⟩

namespace HolomorphicNormalChart

variable {i j : D.curve}
  (c : HolomorphicNormalChart (r₁ := r₁) (r₂ := r₂) (n := n) i)
  (d : HolomorphicNormalChart (r₁ := r₁) (r₂ := r₂) (n := n) j)

def transition (z : ℂ × ℂ) : ℂ × ℂ := d.coordinates (c.coordinates.symm z)

theorem transition_eventually (q : X) (hc : q ∈ c.coordinates.source)
    (hd : q ∈ d.coordinates.source) :
    ∀ᶠ z in 𝓝 (c.coordinates q), z ∈ c.coordinates.target ∧
      c.coordinates.symm z ∈ d.coordinates.source := by
  have hcont := (c.coordinates.continuousAt_symm (c.coordinates.map_source hc)).tendsto
  have hd' : c.coordinates.symm (c.coordinates q) ∈ d.coordinates.source := by
    rw [c.coordinates.left_inv hc]
    exact hd
  filter_upwards [c.coordinates.open_target.mem_nhds (c.coordinates.map_source hc),
    hcont (d.coordinates.open_source.mem_nhds hd')] with z hz hdz
  exact ⟨hz, hdz⟩

theorem transition_formula (q : X) (hc : q ∈ c.coordinates.source)
    (hd : q ∈ d.coordinates.source) :
    ∀ᶠ z in 𝓝 (c.coordinates q),
      (c.transition d z).1 = D.curve.chartChange i j z.1 ∧
      (c.transition d z).2 ^ n = D.curve.chartChange i j (z.1 + z.2 ^ n) -
        D.curve.chartChange i j z.1 := by
  filter_upwards [c.transition_eventually d q hc hd] with z hz
  have h := RetractionAtlas.overlap_formula_three D.curve r₁.toFun r₂.toFun n i j
    c.toNormalFormChart d.toNormalFormChart (c.coordinates.symm z)
    (c.coordinates.map_target hz.1) hz.2
  simpa only [transition, c.coordinates.right_inv hz.1] using h

theorem transition_differentiable (q : X) (hc : q ∈ c.coordinates.source)
    (hd : q ∈ d.coordinates.source) :
    ∀ᶠ z in 𝓝 (c.coordinates q), DifferentiableAt ℂ (c.transition d) z := by
  filter_upwards [c.transition_eventually d q hc hd] with z hz
  exact mdifferentiableAt_iff_differentiableAt.mp
    ((d.holomorphic.mdifferentiableAt (d.coordinates.open_source.mem_nhds hz.2)).comp z
      (c.inverse_holomorphic.mdifferentiableAt (c.coordinates.open_target.mem_nhds hz.1)))

theorem transition_derivative_bijective (q : X) (hc : q ∈ c.coordinates.source)
    (hd : q ∈ d.coordinates.source) :
    Function.Bijective (fderiv ℂ (c.transition d) (c.coordinates q)) := by
  obtain ⟨hci, hci'⟩ := chart_differentials_inverse c.coordinates c.holomorphic
    c.inverse_holomorphic q hc
  obtain ⟨hdi, hdi'⟩ := chart_differentials_inverse d.coordinates d.holomorphic
    d.inverse_holomorphic q hd
  have hchain := mfderiv_comp (c.coordinates q)
    (d.holomorphic.mdifferentiableAt (d.coordinates.open_source.mem_nhds (by
      rw [c.coordinates.left_inv hc]; exact hd)))
    (c.inverse_holomorphic.mdifferentiableAt
      (c.coordinates.open_target.mem_nhds (c.coordinates.map_source hc)))
  rw [c.coordinates.left_inv hc] at hchain
  rw [← mfderiv_eq_fderiv]
  have hb := (show Function.Bijective
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) d.coordinates q) from
    ⟨hdi.injective, hdi'.surjective⟩).comp ⟨hci'.injective, hci.surjective⟩
  have hb' : Function.Bijective
      ((mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) d.coordinates q).comp
        (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c.coordinates.symm (c.coordinates q))) := hb
  rw [← hchain] at hb'
  simpa only [transition, Function.comp_def] using hb'

end HolomorphicNormalChart

theorem first_normal_derivative_zero {H : (ℂ × ℂ) → (ℂ × ℂ)} {p : ℂ × ℂ}
    {φ : ℂ → ℂ} (hp : p.2 = 0) (hH : DifferentiableAt ℂ H p)
    (hfirst : ∀ᶠ z in 𝓝 p, (H z).1 = φ z.1) :
    (fderiv ℂ H p (0, 1)).1 = 0 := by
  have hp' : (p.1, (0 : ℂ)) = p := Prod.ext rfl hp.symm
  have hline : HasDerivAt (fun t : ℂ => (p.1, t)) (0, 1) 0 :=
    (hasDerivAt_const (0 : ℂ) p.1).prodMk (hasDerivAt_id (0 : ℂ))
  have hHp : HasFDerivAt H (fderiv ℂ H p) (p.1, 0) := by
    rw [hp']
    exact hH.hasFDerivAt
  have hderiv : HasDerivAt (fun t : ℂ => (H (p.1, t)).1)
      (fderiv ℂ H p (0, 1)).1 (0 : ℂ) := (hHp.comp_hasDerivAt 0 hline).fst
  have ht : Tendsto (fun t : ℂ => (p.1, t)) (𝓝 0) (𝓝 p) := by
    simpa only [hp'] using hline.continuousAt.tendsto
  have heq : (fun t : ℂ => (H (p.1, t)).1) =ᶠ[𝓝 0] fun _ => φ p.1 :=
    ht.eventually hfirst
  exact hderiv.deriv.symm.trans (by rw [heq.deriv_eq, deriv_const])

theorem normal_derivative_ne_zero_of_bijective {H : (ℂ × ℂ) → (ℂ × ℂ)}
    {p : ℂ × ℂ} (hH : DifferentiableAt ℂ H p)
    (hbij : Function.Bijective (fderiv ℂ H p))
    (hfirst : (fderiv ℂ H p (0, 1)).1 = 0) :
    fderiv ℂ (fun z => (H z).2) p (0, 1) ≠ 0 := by
  intro hzero
  have hs := congrArg (fun L : (ℂ × ℂ) →L[ℂ] ℂ => L (0, 1))
    hH.hasFDerivAt.snd.fderiv
  have hsecond : (fderiv ℂ H p (0, 1)).2 = 0 := hs.symm.trans hzero
  have heq : fderiv ℂ H p (0, 1) = fderiv ℂ H p 0 := by
    rw [map_zero]
    exact Prod.ext hfirst hsecond
  have h10 := congrArg Prod.snd (hbij.1 heq)
  exact one_ne_zero h10

namespace HolomorphicNormalChart

variable {i j : D.curve}
  (c : HolomorphicNormalChart (r₁ := r₁) (r₂ := r₂) (n := n) i)
  (d : HolomorphicNormalChart (r₁ := r₁) (r₂ := r₂) (n := n) j)

theorem transition_rotation_commutes (division : HolomorphicNormalDivision)
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (hn : 0 < n) (α : ℂ) (hα : α ^ n = 1) (t : D.curve)
    (hc : D.inclusion t ∈ c.coordinates.source) (hd : D.inclusion t ∈ d.coordinates.source) :
    (c.transition d) ∘ rotate α =ᶠ[𝓝 (c.coordinates (D.inclusion t))]
      rotate α ∘ c.transition d := by
  let p := c.coordinates (D.inclusion t)
  have hp : p.2 = 0 := normal_coordinate_zero_on_curve i c.toNormalFormChart hn t hc
  have hf := c.transition_formula d (D.inclusion t) hc hd
  have hdiff := c.transition_differentiable d (D.inclusion t) hc hd
  have hd0 := hdiff.self_of_nhds
  have hfirst : (fderiv ℂ (c.transition d) p (0, 1)).1 = 0 :=
    first_normal_derivative_zero hp hd0 (hf.mono (fun _ hz => hz.1))
  have hnonzero := normal_derivative_ne_zero_of_bijective hd0
    (c.transition_derivative_bijective d (D.inclusion t) hc hd) hfirst
  have hanalytic : AnalyticAt ℂ (fun z => (c.transition d z).2) p :=
    regularity _ p (hdiff.mono (fun _ hz => hz.snd))
  have hp' : (p.1, (0 : ℂ)) = p := Prod.ext rfl hp.symm
  have hline : Tendsto (fun x : ℂ => (x, (0 : ℂ))) (𝓝 p.1) (𝓝 p) := by
    simpa only [id_eq, hp'] using
      ((continuousAt_id : ContinuousAt (fun x : ℂ => x) p.1).prodMk
        (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℂ)) p.1)).tendsto
  have hvanish : ∀ᶠ x in 𝓝 p.1, (c.transition d (x, 0)).2 = 0 := by
    filter_upwards [hline.eventually hf] with x hx
    apply (pow_eq_zero_iff (Nat.ne_of_gt hn)).mp
    simpa only [zero_pow (Nat.ne_of_gt hn), add_zero, sub_self] using hx.2
  have hfixed : rotate α p = p := Prod.ext rfl (by simp [rotate, hp])
  have ht : Tendsto (rotate α) (𝓝 p) (𝓝 p) := by
    simpa only [hfixed] using (rotate_continuous α).continuousAt.tendsto (x := p)
  have hpower : ∀ᶠ z in 𝓝 p,
      (c.transition d (rotate α z)).2 ^ n = (c.transition d z).2 ^ n := by
    filter_upwards [hf, ht.eventually hf] with z hz hr
    rw [hr.2, hz.2]
    simp only [rotate, mul_pow, hα, one_mul]
  have hnormal := normal_rotation_commutes_germ division hn hp hα hanalytic hvanish hnonzero hpower
  filter_upwards [hf, ht.eventually hf, hnormal] with z hz hr hnz
  apply Prod.ext
  · exact hr.1.trans hz.1.symm
  · exact hnz

theorem localRotation_compatible_germ (division : HolomorphicNormalDivision)
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (hn : 0 < n) (α : ℂ) (hα : α ^ n = 1) (t : D.curve)
    (hc : D.inclusion t ∈ c.coordinates.source) (hd : D.inclusion t ∈ d.coordinates.source) :
    localRotation c.coordinates α =ᶠ[𝓝 (D.inclusion t)] localRotation d.coordinates α := by
  have hcz := normal_coordinate_zero_on_curve i c.toNormalFormChart hn t hc
  have hdz := normal_coordinate_zero_on_curve j d.toNormalFormChart hn t hd
  have hcomm := c.transition_rotation_commutes d division regularity hn α hα t hc hd
  have hcomm' := hcomm.comp_tendsto (c.coordinates.continuousAt hc).tendsto
  have hcont := localRotation_continuousAt c.coordinates α hc hcz
  have hinD : ∀ᶠ x in 𝓝 (D.inclusion t), localRotation c.coordinates α x ∈ d.coordinates.source := by
    have ht : Tendsto (localRotation c.coordinates α) (𝓝 (D.inclusion t))
        (𝓝 (D.inclusion t)) := by
      simpa only [localRotation_fixed c.coordinates α hc hcz] using hcont.tendsto
    exact ht (d.coordinates.open_source.mem_nhds hd)
  filter_upwards [hcomm', localRotation_eventually_target c.coordinates α hc hcz,
    localRotation_eventually_target d.coordinates α hd hdz, hinD] with x hx hcx hdx hinDx
  apply d.coordinates.injOn hinDx (localRotation_mem d.coordinates α hdx.2)
  change d.coordinates (c.coordinates.symm (rotate α (c.coordinates x))) =
    d.coordinates (d.coordinates.symm (rotate α (d.coordinates x)))
  rw [d.coordinates.right_inv hdx.2]
  change d.coordinates (c.coordinates.symm (rotate α (c.coordinates x))) =
    rotate α (d.coordinates (c.coordinates.symm (c.coordinates x))) at hx
  simpa only [c.coordinates.left_inv hcx.1] using hx

end HolomorphicNormalChart

def rotationDomain (c : OpenPartialHomeomorph X (ℂ × ℂ)) (α : ℂ) : Set X :=
  c.source ∩ c ⁻¹' (rotate α ⁻¹' c.target)

theorem rotationDomain_open (c : OpenPartialHomeomorph X (ℂ × ℂ)) (α : ℂ) :
    IsOpen (rotationDomain c α) :=
  c.isOpen_inter_preimage (c.open_target.preimage (rotate_continuous α))

def rotationHomeomorph (α : ℂ) (hα : α ≠ 0) : (ℂ × ℂ) ≃ₜ (ℂ × ℂ) :=
  (Homeomorph.refl ℂ).prodCongr (Homeomorph.mulLeft₀ α hα)

theorem localRotation_openOn (c : OpenPartialHomeomorph X (ℂ × ℂ)) (α : ℂ)
    (hα : α ≠ 0) (W : Set X) (hW : IsOpen W) (hsub : W ⊆ rotationDomain c α) :
    IsOpen (localRotation c α '' W) := by
  have hWc : IsOpen (c '' W) := c.isOpen_image_of_subset_source hW (fun x hx => (hsub hx).1)
  have hWr : IsOpen (rotate α '' (c '' W)) := (rotationHomeomorph α hα).isOpenMap _ hWc
  have htarget : rotate α '' (c '' W) ⊆ c.target := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact (hsub hx).2
  have hfinal := c.symm.isOpen_image_of_subset_source hWr htarget
  simpa only [Set.image_image, localRotation, Function.comp_def] using hfinal

theorem localRotation_holomorphic (i : D.curve)
    (c : HolomorphicNormalChart (r₁ := r₁) (r₂ := r₂) (n := n) i) (α : ℂ) :
    MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (localRotation c.coordinates α)
      (rotationDomain c.coordinates α) := by
  intro q hq
  apply MDifferentiableAt.mdifferentiableWithinAt
  apply (c.inverse_holomorphic.mdifferentiableAt
    (c.coordinates.open_target.mem_nhds hq.2)).comp q
  exact (mdifferentiableAt_iff_differentiableAt.mpr
    (rotateLinear α).differentiableAt).comp q
    (c.holomorphic.mdifferentiableAt (c.coordinates.open_source.mem_nhds hq.1))

/-- The only neighbourhood gluing parameter: compatible actual local
holomorphic open-map germs admit a representative along the compact curve.
The representative retains the local open-map property. There is no group,
retraction, rotation, or index in this general sheaf statement. -/
def HolomorphicOpenGermGluing : Prop :=
  ∀ (X : CompactComplexSurface) (D : EmbeddedCurve X) (I : Type)
    (localMap : I → X → X) (domain : I → Set X),
    (∀ i, IsOpen (domain i)) →
    (∀ i, MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (localMap i) (domain i)) →
    (∀ i W, IsOpen W → W ⊆ domain i → IsOpen (localMap i '' W)) →
    (∀ p : D.curve, ∃ i, D.inclusion p ∈ domain i) →
    (∀ i j (p : D.curve), D.inclusion p ∈ domain i → D.inclusion p ∈ domain j →
      localMap i =ᶠ[𝓝 (D.inclusion p)] localMap j) →
    ∃ (V : D.Neighbourhood) (τ : X → X),
      MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) τ V.domain ∧
      (∀ W, IsOpen W → W ⊆ V.domain → IsOpen (τ '' W)) ∧
      ∀ i (p : D.curve), D.inclusion p ∈ domain i → τ =ᶠ[𝓝 (D.inclusion p)] localMap i

structure RotationRepresentative
    (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n) (α : ℂ) where
  neighbourhood : D.Neighbourhood
  map : X → X
  holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) map neighbourhood.domain
  openOn : ∀ W, IsOpen W → W ⊆ neighbourhood.domain → IsOpen (map '' W)
  germ : ∀ p : D.curve, map =ᶠ[𝓝 (D.inclusion p)]
    localRotation (A.chart p p).coordinates α

theorem nonempty_rotationRepresentative (division : HolomorphicNormalDivision)
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (gluing : HolomorphicOpenGermGluing)
    (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)
    (hn : 0 < n) (α : ℂ) (hα : α ^ n = 1) : Nonempty (RotationRepresentative A α) := by
  have hα0 : α ≠ 0 := by
    intro hz
    rw [hz, zero_pow (Nat.ne_of_gt hn)] at hα
    exact zero_ne_one hα
  obtain ⟨V, τ, hhol, hopen, hgerm⟩ := gluing X D D.curve
    (fun p => localRotation (A.chart p p).coordinates α)
    (fun p => rotationDomain (A.chart p p).coordinates α)
    (fun p => rotationDomain_open _ α)
    (fun p => localRotation_holomorphic p (normalChart A p p) α)
    (fun p => localRotation_openOn _ α hα0)
    (fun p => ⟨p, (localRotation_eventually_target (A.chart p p).coordinates α
      (A.source_mem p p (mem_chart_source ℂ p))
      (by rw [A.centre p p (mem_chart_source ℂ p)])).self_of_nhds⟩)
    (fun i j p hi hj => (normalChart A i i).localRotation_compatible_germ
      (normalChart A j j) division regularity hn α hα p hi.1 hj.1)
  exact ⟨⟨V, τ, hhol, hopen, fun p => hgerm p p
    ((localRotation_eventually_target (A.chart p p).coordinates α
      (A.source_mem p p (mem_chart_source ℂ p))
      (by rw [A.centre p p (mem_chart_source ℂ p)])).self_of_nhds)⟩⟩

/-- A property valid as a germ along the actual compact curve has an actual
open neighbourhood on which it holds. This elementary union construction is
separate from the sheaf input. -/
theorem neighbourhood_of_germs (P : X → Prop)
    (hP : ∀ p : D.curve, ∀ᶠ x in 𝓝 (D.inclusion p), P x) :
    ∃ V : D.Neighbourhood, ∀ x ∈ V.domain, P x := by
  choose W hW hWo hpW using fun p => mem_nhds_iff.mp (hP p)
  refine ⟨⟨⋃ p, W p, isOpen_iUnion hWo, fun p => Set.mem_iUnion.mpr ⟨p, hpW p⟩⟩, ?_⟩
  intro x hx
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx
  exact hW p hp

/-- Construct an invariant actual action domain from finite group germs.
This theorem proves the finite intersection/union step itself; its inputs
are actual representative maps with local laws, not an existing action. -/
theorem action_of_finite_germs {G : Type} [Group G] [Fintype G]
    (τ : G → X → X) (V : D.Neighbourhood) (hVU : V.domain ⊆ U.domain)
    (hhol : ∀ g, MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (τ g) V.domain)
    (hopen : ∀ g W, IsOpen W → W ⊆ V.domain → IsOpen (τ g '' W))
    (hfix : ∀ g p, τ g (D.inclusion p) = D.inclusion p)
    (hcomp : ∀ g h p, ∀ᶠ x in 𝓝 (D.inclusion p), τ g (τ h x) = τ (g * h) x)
    (hone : ∀ p, τ 1 =ᶠ[𝓝 (D.inclusion p)] id)
    (hr : ∀ g p, ∀ᶠ x in 𝓝 (D.inclusion p),
      r₁.toFun (τ g x) = r₁.toFun x ∧ r₂.toFun (τ g x) = r₂.toFun x) :
    ∃ (W : D.Neighbourhood) (r : D.Retraction W)
      (action : NeighbourhoodSplittings.NeighbourhoodAction G r),
      W.domain ⊆ V.domain ∧ r.toFun = r₁.toFun ∧ action.map = τ ∧
      ∀ g x, x ∈ W.domain → r₂.toFun (action.map g x) = r₂.toFun x := by
  have hmaps (g : G) (p : D.curve) : ∀ᶠ x in 𝓝 (D.inclusion p), τ g x ∈ V.domain := by
    have hc := (hhol g).mdifferentiableAt (V.open_domain.mem_nhds (V.contains p))
    have ht : Tendsto (τ g) (𝓝 (D.inclusion p)) (𝓝 (D.inclusion p)) := by
      simpa only [hfix g p] using hc.continuousAt.tendsto
    exact ht (V.open_domain.mem_nhds (V.contains p))
  obtain ⟨W, hW⟩ := neighbourhood_of_germs (D := D)
    (fun x => x ∈ V.domain ∧ (∀ g, τ g x ∈ V.domain) ∧
      (∀ g h, τ g (τ h x) = τ (g * h) x) ∧ τ 1 x = x ∧
      ∀ g, r₁.toFun (τ g x) = r₁.toFun x ∧ r₂.toFun (τ g x) = r₂.toFun x) (fun p => by
        filter_upwards [V.open_domain.mem_nhds (V.contains p),
          Filter.eventually_all.mpr (fun g => hmaps g p),
          Filter.eventually_all.mpr (fun g => Filter.eventually_all.mpr (fun h => hcomp g h p)),
          hone p, Filter.eventually_all.mpr (fun g => hr g p)] with x hx hm hc hi hrx
        exact ⟨hx, hm, hc, hi, hrx⟩)
  have hcompW : ∀ g h x, x ∈ W.domain → τ g (τ h x) = τ (g * h) x :=
    fun g h x hx => (hW x hx).2.2.1 g h
  let O := ActionGluing.invariantNeighbourhood τ W.domain
  have hOV : O ⊆ V.domain := by
    intro x hx
    obtain ⟨g, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    exact (hW y hy).2.1 g
  have hOo : IsOpen O := ActionGluing.invariantNeighbourhood_open τ W.domain
    (fun g => hopen g W.domain W.open_domain (fun x hx => (hW x hx).1))
  let N : D.Neighbourhood :=
    ⟨O, hOo, fun p => ActionGluing.curve_subset_union τ W.domain D.support
      (by rintro _ ⟨q, rfl⟩; exact W.contains q)
      (by rintro g _ ⟨q, rfl⟩; exact hfix g q) ⟨p, rfl⟩⟩
  let r : D.Retraction N :=
    ⟨r₁.toFun, r₁.holomorphic.mono (fun x hx => hVU (hOV hx)), r₁.retract⟩
  let action : NeighbourhoodSplittings.NeighbourhoodAction G r :=
    { map := τ
      permutation := ActionGluing.action τ W.domain hcompW
      map_eq := fun _ _ => rfl
      holomorphic := fun g => (hhol g).mono hOV
      preserves_retraction := fun g x => ActionGluing.preserves_on_union τ W.domain hcompW
        r₁.toFun (fun k y hy => ((hW y hy).2.2.2.2 k).1) g x x.property }
  exact ⟨N, r, action, hOV, rfl, rfl, fun g x hx =>
    ActionGluing.preserves_on_union τ W.domain hcompW r₂.toFun
      (fun k y hy => ((hW y hy).2.2.2.2 k).2) g x hx⟩

namespace RotationRepresentative

variable {A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n} {α : ℂ}

theorem fixes_curve (R : RotationRepresentative A α) (p : D.curve) :
    R.map (D.inclusion p) = D.inclusion p :=
  (R.germ p).self_of_nhds.trans
    (localRotation_fixed (A.chart p p).coordinates α
      (A.source_mem p p (mem_chart_source ℂ p))
      (by rw [A.centre p p (mem_chart_source ℂ p)]))

theorem preserves_germ (R : RotationRepresentative A α) (hα : α ^ n = 1) (p : D.curve) :
    ∀ᶠ x in 𝓝 (D.inclusion p),
      r₁.toFun (R.map x) = r₁.toFun x ∧ r₂.toFun (R.map x) = r₂.toFun x := by
  filter_upwards [R.germ p,
    localRotation_eventually_target (A.chart p p).coordinates α
      (A.source_mem p p (mem_chart_source ℂ p))
      (by rw [A.centre p p (mem_chart_source ℂ p)])] with x hx hdom
  rw [hx]
  exact localRotation_preserves p (A.chart p p) α hα hdom.1 hdom.2

end RotationRepresentative

/-- A genuine finite action, inside any prescribed smaller neighbourhood,
constructed from the actual normal atlas and the generic germ-sheaf theorem.
The output retains the actual local rotation germ for every group element. -/
theorem action_from_normalAtlas (division : HolomorphicNormalDivision)
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (gluing : HolomorphicOpenGermGluing)
    (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n) (hn : 0 < n)
    {G : Type} [Group G] [Fintype G] (scalar : G →* ℂˣ)
    (hroot : ∀ g, (scalar g : ℂ) ^ n = 1) (V : D.Neighbourhood) :
    ∃ (W : D.Neighbourhood) (r : D.Retraction W)
      (action : NeighbourhoodSplittings.NeighbourhoodAction G r),
      W.domain ⊆ V.domain ∧ W.domain ⊆ U.domain ∧ r.toFun = r₁.toFun ∧
      (∀ g p, action.map g =ᶠ[𝓝 (D.inclusion p)]
        localRotation (A.chart p p).coordinates (scalar g : ℂ)) ∧
      ∀ g x, x ∈ W.domain → r₂.toFun (action.map g x) = r₂.toFun x := by
  let R : ∀ g : G, RotationRepresentative A (scalar g : ℂ) := fun g =>
    Classical.choice (nonempty_rotationRepresentative division regularity gluing A hn _ (hroot g))
  let τ : G → X → X := fun g => (R g).map
  let V₀ : D.Neighbourhood :=
    { domain := V.domain ∩ U.domain ∩ ⋂ g, (R g).neighbourhood.domain
      open_domain := (V.open_domain.inter U.open_domain).inter
        (isOpen_iInter_of_finite (fun g => (R g).neighbourhood.open_domain))
      contains := fun p => ⟨⟨V.contains p, U.contains p⟩,
        Set.mem_iInter.mpr (fun g => (R g).neighbourhood.contains p)⟩ }
  have hhol : ∀ g, MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (τ g) V₀.domain :=
    fun g => (R g).holomorphic.mono (fun _ hx => Set.mem_iInter.mp hx.2 g)
  have hopen : ∀ g O, IsOpen O → O ⊆ V₀.domain → IsOpen (τ g '' O) :=
    fun g O hO hsub => (R g).openOn O hO (fun _ hx => Set.mem_iInter.mp (hsub hx).2 g)
  have hfix : ∀ g p, τ g (D.inclusion p) = D.inclusion p := fun g => (R g).fixes_curve
  have hcomp : ∀ g h p, ∀ᶠ x in 𝓝 (D.inclusion p), τ g (τ h x) = τ (g * h) x := by
    intro g h p
    have ht : Tendsto (τ h) (𝓝 (D.inclusion p)) (𝓝 (D.inclusion p)) := by
      simpa only [(R h).fixes_curve p] using
        ((R h).holomorphic.mdifferentiableAt
          ((R h).neighbourhood.open_domain.mem_nhds ((R h).neighbourhood.contains p))).continuousAt.tendsto
    have hleft := ((R g).germ p).comp_tendsto ht
    have hlocal := localRotation_mul_germ (A.chart p p).coordinates
      (scalar g : ℂ) (scalar h : ℂ) (A.source_mem p p (mem_chart_source ℂ p))
      (by rw [A.centre p p (mem_chart_source ℂ p)])
    filter_upwards [hleft, (R h).germ p, hlocal, (R (g * h)).germ p] with x hx hh hl hr
    change τ g (τ h x) = localRotation (A.chart p p).coordinates (scalar g : ℂ) (τ h x) at hx
    change τ h x = localRotation (A.chart p p).coordinates (scalar h : ℂ) x at hh
    change localRotation (A.chart p p).coordinates (scalar g : ℂ)
      (localRotation (A.chart p p).coordinates (scalar h : ℂ) x) = _ at hl
    change τ (g * h) x = localRotation (A.chart p p).coordinates (scalar (g * h) : ℂ) x at hr
    rw [hx, hh, hl, hr]
    simp only [map_mul, Units.val_mul]
  have hone : ∀ p, τ 1 =ᶠ[𝓝 (D.inclusion p)] id := by
    intro p
    have h := (R 1).germ p
    simp only [map_one, Units.val_one] at h
    exact h.trans (localRotation_one_germ (A.chart p p).coordinates
      (A.source_mem p p (mem_chart_source ℂ p)))
  obtain ⟨W, r, action, hW, hr, hmap, hs⟩ := action_of_finite_germs τ V₀
    (fun _ hx => hx.1.2) hhol hopen hfix hcomp hone (fun g => (R g).preserves_germ (hroot g))
  refine ⟨W, r, action, (fun x hx => (hW hx).1.1), (fun x hx => (hW hx).1.2), hr, ?_, hs⟩
  intro g p
  rw [hmap]
  exact (R g).germ p

/-- Differentiate the actual coordinate identity of the local rotation germ. -/
theorem rotation_derivative_conjugacy (c : OpenPartialHomeomorph X (ℂ × ℂ))
    (hc : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c c.source)
    (α : ℂ) (q : X) (hq : q ∈ c.source) (hz : (c q).2 = 0)
    (τ : X → X) (hτ : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) τ q)
    (hgerm : τ =ᶠ[𝓝 q] localRotation c α) (v : ℂ × ℂ) :
    mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c q
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) τ q v) =
        rotate α (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c q v) := by
  have hfix : τ q = q := hgerm.self_of_nhds.trans (localRotation_fixed c α hq hz)
  have heq : c ∘ τ =ᶠ[𝓝 q] (rotateLinear α) ∘ c := by
    filter_upwards [hgerm, localRotation_eventually_target c α hq hz] with x hx ht
    change c (τ x) = rotate α (c x)
    rw [hx]
    exact localRotation_coordinate c α ht.2
  have hcd := hc.mdifferentiableAt (c.open_source.mem_nhds hq)
  have hcd' : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c (τ q) := by
    rw [hfix]
    exact hcd
  have he := heq.mfderiv_eq (I := 𝓘(ℂ, ℂ × ℂ)) (I' := 𝓘(ℂ, ℂ × ℂ))
  rw [mfderiv_comp q hcd' hτ,
    mfderiv_comp q (rotateLinear α).mdifferentiableAt hcd,
    ContinuousLinearMap.mfderiv_eq] at he
  have hpoint : (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c (τ q) :
    (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) = mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c q :=
    mfderiv_congr_point hfix
  rw [hpoint] at he
  exact congrArg (fun L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) => L v) he

theorem chart_normal_annihilates_inclusion (i : D.curve)
    (c : HolomorphicNormalChart (r₁ := r₁) (r₂ := r₂) (n := n) i)
    (hn : 0 < n) (p : D.curve) (hp : D.inclusion p ∈ c.coordinates.source) (v : ℂ) :
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c.coordinates (D.inclusion p)
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p v)).2 = 0 := by
  let snd : (ℂ × ℂ) →L[ℂ] ℂ := ContinuousLinearMap.snd ℂ ℂ ℂ
  have hcd := c.holomorphic.mdifferentiableAt (c.coordinates.open_source.mem_nhds hp)
  have hcomp := hcd.comp p (D.inclusion.holomorphic p)
  have heq : snd ∘ c.coordinates ∘ D.inclusion =ᶠ[𝓝 p] fun _ => (0 : ℂ) := by
    filter_upwards [D.inclusion.holomorphic.continuous.continuousAt.tendsto
      (c.coordinates.open_source.mem_nhds hp)] with q hq
    exact normal_coordinate_zero_on_curve i c.toNormalFormChart hn q hq
  have hd := heq.mfderiv_eq (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ))
  rw [mfderiv_comp p snd.mdifferentiableAt hcomp,
    mfderiv_comp p hcd (D.inclusion.holomorphic p),
    ContinuousLinearMap.mfderiv_eq, mfderiv_const] at hd
  exact congrArg (fun L : ℂ →L[ℂ] ℂ => L v) hd

theorem covector_factor_through_second (l : (ℂ × ℂ) →L[ℂ] ℂ)
    (hl : ∀ z : ℂ, l (z, 0) = 0) (v : ℂ × ℂ) : l v = l (0, 1) * v.2 := by
  have hv : v = (v.1, 0) + v.2 • (0, 1) := by ext <;> simp
  calc
    l v = l (v.1, 0) + v.2 • l (0, 1) := by
      conv_lhs => rw [hv, map_add, map_smul]
    _ = l (0, 1) * v.2 := by rw [hl]; simp only [zero_add, smul_eq_mul, mul_comm]

/-- The scalar induced on a one-dimensional quotient does not depend on
which adapted ambient frame represents that quotient. -/
theorem normal_scalar_transport (L T : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ))
    (frame : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ)) (α : ℂ) (hL : Function.Bijective L)
    (htangent : ∀ z : ℂ, (L (frame (z, 0))).2 = 0)
    (hconjugate : ∀ v, (L (T v)).2 = α * (L v).2) (v : ℂ × ℂ) :
    (frame.symm (T (frame v))).2 = α * v.2 := by
  let l : (ℂ × ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.snd ℂ ℂ ℂ).comp (L.comp frame.toContinuousLinearMap)
  have hfactor := covector_factor_through_second l htangent
  have hlzero : l (0, 1) ≠ 0 := by
    intro hzero
    obtain ⟨w, hw⟩ := hL.2 (0, 1)
    have heq := hfactor (frame.symm w)
    change (L (frame (frame.symm w))).2 = l (0, 1) * (frame.symm w).2 at heq
    rw [frame.apply_symm_apply, hw, hzero, zero_mul] at heq
    exact one_ne_zero heq
  have heq := hconjugate (frame v)
  have hleft := hfactor (frame.symm (T (frame v)))
  have hright := hfactor v
  change (L (frame (frame.symm (T (frame v))))).2 = _ at hleft
  rw [frame.apply_symm_apply] at hleft
  change (L (frame v)).2 = _ at hright
  rw [hleft, hright] at heq
  apply mul_left_cancel₀ hlzero
  calc
    l (0, 1) * (frame.symm (T (frame v))).2 = α * (l (0, 1) * v.2) := heq
    _ = l (0, 1) * (α * v.2) := by ring

/-- An action carrying the actual local normal rotation germs has the actual
normal eigenvalue α in every honest adapted frame. No eigenvalue assumption
or identification with a point-dependent normal-chart derivative is needed. -/
theorem normalRotation_of_germs
    (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n) (hn : 0 < n)
    {W : D.Neighbourhood} {r : D.Retraction W} {G : Type} [Group G]
    (action : NeighbourhoodSplittings.NeighbourhoodAction G r)
    {N T : HolomorphicLineCocycle D.curve}
    (frames : EmbeddedFrames.RawEmbeddedFrames D N T) (g : G) (α : ℂ)
    (hgerm : ∀ p, action.map g =ᶠ[𝓝 (D.inclusion p)]
      localRotation (A.chart p p).coordinates α) : action.NormalRotation frames g α := by
  constructor
  · intro p
    apply Subtype.ext
    change (action.permutation g (NeighbourhoodSplittings.curvePoint W p)).val = D.inclusion p
    rw [← action.map_eq]
    exact (hgerm p).self_of_nhds.trans (localRotation_fixed (A.chart p p).coordinates α
      (A.source_mem p p (mem_chart_source ℂ p))
      (by rw [A.centre p p (mem_chart_source ℂ p)]))
  · intro p v
    let c := A.chart p p
    let L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
      mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c.coordinates (D.inclusion p)
    have hc := A.source_mem p p (mem_chart_source ℂ p)
    have hz : (c.coordinates (D.inclusion p)).2 = 0 := by
      rw [A.centre p p (mem_chart_source ℂ p)]
    obtain ⟨hleft, hright⟩ := chart_differentials_inverse c.coordinates
      (A.holomorphic p p) (A.inverse_holomorphic p p) (D.inclusion p) hc
    apply normal_scalar_transport L (action.derivative g (NeighbourhoodSplittings.curvePoint W p))
      (frames.frame p p) α ⟨hleft.injective, hright.surjective⟩
    · intro z
      rw [frames.tangent_adapted p p (mem_chart_source ℂ p)]
      exact chart_normal_annihilates_inclusion p (normalChart A p p) hn p hc _
    · intro w
      exact congrArg Prod.snd (rotation_derivative_conjugacy c.coordinates
        (A.holomorphic p p) α (D.inclusion p) hc hz (action.map g)
        (action.differentiableAt g (NeighbourhoodSplittings.curvePoint W p)) (hgerm p) w)

/-- The actual finite normal-rotation action of the roots of unity, inside
any prescribed neighbourhood. Its normal eigenvalue ζ in arbitrary honest
normal frames is a conclusion of the actual differential calculation. -/
theorem finite_normal_action (division : HolomorphicNormalDivision)
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (gluing : HolomorphicOpenGermGluing)
    (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n) (hn : 2 ≤ n)
    (V : D.Neighbourhood) {N T : HolomorphicLineCocycle D.curve}
    (frames : EmbeddedFrames.RawEmbeddedFrames D N T) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ n) :
    ∃ (W : D.Neighbourhood) (r : D.Retraction W)
      (action : NeighbourhoodSplittings.NeighbourhoodAction (rootsOfUnity n ℂ) r)
      (g : rootsOfUnity n ℂ),
      W.domain ⊆ V.domain ∧ W.domain ⊆ U.domain ∧ r.toFun = r₁.toFun ∧
      action.NormalRotation frames g ζ ∧ ζ ≠ 1 ∧
      ∀ h x, x ∈ W.domain → r₂.toFun (action.map h x) = r₂.toFun x := by
  letI : NeZero n := ⟨by omega⟩
  let scalar : rootsOfUnity n ℂ →* ℂˣ := (rootsOfUnity n ℂ).subtype
  have hroot : ∀ g, (scalar g : ℂ) ^ n = 1 :=
    fun g => (mem_rootsOfUnity' n g.val).mp g.property
  obtain ⟨W, r, action, hWV, hWU, hr, hgerm, hs⟩ := action_from_normalAtlas
    division regularity gluing A (by omega) scalar hroot V
  let g : rootsOfUnity n ℂ := rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one
  have hscalar : (scalar g : ℂ) = ζ := rfl
  have hnormal := normalRotation_of_germs A (by omega) action frames g (scalar g : ℂ) (hgerm g)
  rw [hscalar] at hnormal
  exact ⟨W, r, action, g, hWV, hWU, hr, hnormal, hζ.ne_one (by omega), hs⟩

/-- The arbitrary-neighbourhood construction retains a previously established
actual joint transversality condition after shrinking the retraction domain. -/
theorem jointTransverse_on_smaller {V W : D.Neighbourhood}
    (rV : D.Retraction V) (rW : D.Retraction W) (hsub : W.domain ⊆ V.domain)
    (hr : rW.toFun = rV.toFun) {B : Curve} (h : HolomorphicMap X B)
    (htransverse : NeighbourhoodSplittings.JointTransverse rV h) :
    NeighbourhoodSplittings.JointTransverse rW h := by
  intro p
  have ht := htransverse ⟨p.val, hsub p.property⟩
  change Function.Bijective
    ((mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) rW.toFun p.val).prod
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) h p.val))
  rw [hr]
  exact ht

/-- The actual local normal rotation germs detect every element of a faithful
scalar group, so the constructed permutation action is faithful as well. -/
theorem action_faithful_of_germs
    (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)
    {W : D.Neighbourhood} {r : D.Retraction W} {G : Type} [Group G]
    (action : NeighbourhoodSplittings.NeighbourhoodAction G r)
    (scalar : G →* ℂˣ) (hscalar : Function.Injective scalar)
    (hgerm : ∀ g p, action.map g =ᶠ[𝓝 (D.inclusion p)]
      localRotation (A.chart p p).coordinates (scalar g : ℂ)) :
    Function.Injective action.permutation := by
  apply (injective_iff_map_eq_one action.permutation).mpr
  intro g hidentity
  let p := D.curve.basepoint
  let c := (A.chart p p).coordinates
  have hc : D.inclusion p ∈ c.source := A.source_mem p p (mem_chart_source ℂ p)
  have hz : (c (D.inclusion p)).2 = 0 := by rw [A.centre p p (mem_chart_source ℂ p)]
  have heq : action.map g =ᶠ[𝓝 (D.inclusion p)] id :=
    Filter.eventually_of_mem (W.open_domain.mem_nhds (W.contains p)) (fun x hx => by
      calc
        action.map g x = (action.permutation g ⟨x, hx⟩).val := action.map_eq g ⟨x, hx⟩
        _ = x := by rw [hidentity]; rfl)
  have hdτ : (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (action.map g) (D.inclusion p) :
      (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) = ContinuousLinearMap.id ℂ (ℂ × ℂ) := by
    simpa only [mfderiv_id] using
      (heq.mfderiv_eq (I := 𝓘(ℂ, ℂ × ℂ)) (I' := 𝓘(ℂ, ℂ × ℂ)))
  obtain ⟨_, hright⟩ := chart_differentials_inverse c (A.holomorphic p p)
    (A.inverse_holomorphic p p) (D.inclusion p) hc
  obtain ⟨v, hv⟩ := hright.surjective (0, 1)
  have hconjugate := rotation_derivative_conjugacy c (A.holomorphic p p)
    (scalar g : ℂ) (D.inclusion p) hc hz (action.map g)
    (action.differentiableAt g (NeighbourhoodSplittings.curvePoint W p)) (hgerm g p) v
  rw [hdτ] at hconjugate
  change (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c (D.inclusion p)) v =
    rotate (scalar g : ℂ) ((mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c (D.inclusion p)) v) at hconjugate
  change (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c (D.inclusion p)) v = (0, 1) at hv
  rw [hv] at hconjugate
  have hvalue : (scalar g : ℂ) = 1 := by
    have hsecond := congrArg Prod.snd hconjugate
    simpa only [rotate, mul_one] using hsecond.symm
  apply hscalar
  apply Units.ext
  simpa only [map_one, Units.val_one] using hvalue

/-- Proposition 2.4's finite normal action also has the exact primitive
generator order. Both faithfulness and the order are conclusions, obtained
from the actual rotation germs and mathlib's primitive-root order theorem. -/
theorem finite_normal_action_with_order (division : HolomorphicNormalDivision)
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (gluing : HolomorphicOpenGermGluing)
    (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n) (hn : 2 ≤ n)
    (V : D.Neighbourhood) {N T : HolomorphicLineCocycle D.curve}
    (frames : EmbeddedFrames.RawEmbeddedFrames D N T) (ζ : ℂ) (hζ : IsPrimitiveRoot ζ n) :
    ∃ (W : D.Neighbourhood) (r : D.Retraction W)
      (action : NeighbourhoodSplittings.NeighbourhoodAction (rootsOfUnity n ℂ) r)
      (g : rootsOfUnity n ℂ),
      W.domain ⊆ V.domain ∧ W.domain ⊆ U.domain ∧ r.toFun = r₁.toFun ∧
      action.NormalRotation frames g ζ ∧ ζ ≠ 1 ∧
      Function.Injective action.permutation ∧ orderOf (action.permutation g) = n ∧
      ∀ h x, x ∈ W.domain → r₂.toFun (action.map h x) = r₂.toFun x := by
  letI : NeZero n := ⟨by omega⟩
  let scalar : rootsOfUnity n ℂ →* ℂˣ := (rootsOfUnity n ℂ).subtype
  have hscalar : Function.Injective scalar := Subtype.val_injective
  have hroot : ∀ g, (scalar g : ℂ) ^ n = 1 :=
    fun g => (mem_rootsOfUnity' n g.val).mp g.property
  obtain ⟨W, r, action, hWV, hWU, hr, hgerm, hs⟩ := action_from_normalAtlas
    division regularity gluing A (by omega) scalar hroot V
  let g : rootsOfUnity n ℂ := rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one
  have hvalue : (scalar g : ℂ) = ζ := rfl
  have hnormal := normalRotation_of_germs A (by omega) action frames g (scalar g : ℂ) (hgerm g)
  rw [hvalue] at hnormal
  have hfaithful := action_faithful_of_germs A action scalar hscalar hgerm
  let complexScalar : rootsOfUnity n ℂ →* ℂ := (Units.coeHom ℂ).comp scalar
  have hcomplex : Function.Injective complexScalar := Units.val_injective.comp hscalar
  have horder : orderOf (action.permutation g) = n := by
    calc
      orderOf (action.permutation g) = orderOf g := orderOf_injective action.permutation hfaithful g
      _ = orderOf (complexScalar g) := (orderOf_injective complexScalar hcomplex g).symm
      _ = orderOf ζ := congrArg orderOf hvalue
      _ = n := hζ.eq_orderOf.symm
  exact ⟨W, r, action, g, hWV, hWU, hr, hnormal, hζ.ne_one (by omega), hfaithful, horder, hs⟩

end Paper27.Geometry.NormalAtlasAction
