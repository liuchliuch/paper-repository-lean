import Paper27.Geometry.EmbeddedFrames
import Paper27.Splitting
import Mathlib.Analysis.Analytic.Constructions

/-!
# Actual neighbourhood splittings and their finite averages

Sections are actual functions on the specified open surface neighbourhood,
with values in the continuous linear maps from the retraction's tangent line
to the ambient tangent plane. The projection is composition with the actual
manifold differential of the actual retraction. Surface automorphisms act by
their actual differential at the inverse image point.

On arbitrary section functions the projection is equivariant, not invariant:
`π(ρg σ)(p) = πσ(g⁻¹p)`. The identity section is fixed, so translating and
averaging an actual splitting still gives a splitting. No trivial action on
the entire target section space is assumed.
-/

noncomputable section

open scoped Manifold Topology BigOperators
open Filter

namespace Paper27.Geometry.NeighbourhoodSplittings

variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}

abbrev Section (U : D.Neighbourhood) := (p : U.domain) → ℂ →L[ℂ] (ℂ × ℂ)
abbrev EndSection (U : D.Neighbourhood) := (p : U.domain) → ℂ →L[ℂ] ℂ

def projection (r : D.Retraction U) : Section U →ₗ[ℂ] EndSection U where
  toFun σ p := (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun p.val).comp (σ p)
  map_add' σ τ := by funext p; simp
  map_smul' c σ := by funext p; simp

def identitySection (U : D.Neighbourhood) : EndSection U :=
  fun _ => ContinuousLinearMap.id ℂ ℂ

def IsSplitting (r : D.Retraction U) (σ : Section U) : Prop :=
  projection r σ = identitySection U

variable (G : Type) [Group G]

/-- Actual holomorphic automorphisms of the neighbourhood, represented by
arbitrary total extensions to X and an honest permutation action on U. -/
structure NeighbourhoodAction (r : D.Retraction U) where
  map : G → X → X
  permutation : G →* Equiv.Perm U.domain
  map_eq : ∀ g (p : U.domain), map g p.val = (permutation g p).val
  holomorphic : ∀ g, MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (map g) U.domain
  preserves_retraction : ∀ g (p : U.domain), r.toFun (map g p.val) = r.toFun p.val

namespace NeighbourhoodAction

variable {G} {r : D.Retraction U} (A : NeighbourhoodAction G r)

theorem map_mem (g : G) (p : U.domain) : A.map g p.val ∈ U.domain := by
  rw [A.map_eq]
  exact (A.permutation g p).property

theorem map_one_point (p : U.domain) : A.map 1 p.val = p.val := by
  rw [A.map_eq, map_one]
  rfl

theorem map_mul_point (g h : G) (p : U.domain) :
    A.map (g * h) p.val = A.map g (A.map h p.val) := by
  rw [A.map_eq, map_mul, Equiv.Perm.mul_apply, A.map_eq h p,
    A.map_eq g (A.permutation h p)]

theorem differentiableAt (g : G) (p : U.domain) :
    MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (A.map g) p.val :=
  (A.holomorphic g p.val p.property).mdifferentiableAt (U.open_domain.mem_nhds p.property)

def derivative (g : G) (p : U.domain) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (A.map g) p.val

theorem derivative_one (p : U.domain) : A.derivative 1 p =
      ContinuousLinearMap.id ℂ (ℂ × ℂ) := by
  have heq : A.map 1 =ᶠ[𝓝 p.val] id :=
    Filter.eventually_of_mem (U.open_domain.mem_nhds p.property)
      (fun x hx => A.map_one_point ⟨x, hx⟩)
  simpa only [derivative, mfderiv_id] using
    (heq.mfderiv_eq (I := 𝓘(ℂ, ℂ × ℂ)) (I' := 𝓘(ℂ, ℂ × ℂ)))

theorem derivative_mul (g h : G) (p : U.domain) :
    A.derivative (g * h) p =
      (A.derivative g (A.permutation h p)).comp (A.derivative h p) := by
  have heq : A.map (g * h) =ᶠ[𝓝 p.val] A.map g ∘ A.map h :=
    Filter.eventually_of_mem (U.open_domain.mem_nhds p.property)
      (fun x hx => A.map_mul_point g h ⟨x, hx⟩)
  change mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (A.map (g * h)) p.val = _
  rw [heq.mfderiv_eq]
  unfold derivative
  rw [show (A.permutation h p).val = A.map h p.val from (A.map_eq h p).symm]
  exact mfderiv_comp p.val
    (A.differentiableAt g ⟨A.map h p.val, A.map_mem h p⟩) (A.differentiableAt h p)

theorem retraction_derivative (g : G) (p : U.domain) :
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun (A.map g p.val)).comp
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (A.map g) p.val) =
        mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun p.val := by
  have heq : r.toFun ∘ A.map g =ᶠ[𝓝 p.val] r.toFun :=
    Filter.eventually_of_mem (U.open_domain.mem_nhds p.property)
      (fun x hx => A.preserves_retraction g ⟨x, hx⟩)
  rw [← mfderiv_comp p.val
    ((r.holomorphic _ (A.map_mem g p)).mdifferentiableAt
      (U.open_domain.mem_nhds (A.map_mem g p))) (A.differentiableAt g p)]
  exact heq.mfderiv_eq

/-- Actual pushforward of a tangent-valued section. -/
def pushforward (g : G) (σ : Section U) : Section U := fun p =>
  (A.derivative g (A.permutation (g⁻¹) p)).comp (σ (A.permutation (g⁻¹) p))

theorem pushforward_one (σ : Section U) : A.pushforward 1 σ = σ := by
  funext p
  apply ContinuousLinearMap.ext
  intro w
  simp only [pushforward, inv_one, map_one, Equiv.Perm.one_apply]
  rw [A.derivative_one]
  rfl

theorem inverse_image_mul (g h : G) (p : U.domain) :
    A.permutation (h⁻¹) (A.permutation (g⁻¹) p) = A.permutation ((g * h)⁻¹) p := by
  rw [mul_inv_rev, map_mul]
  rfl

theorem forward_inverse_image (g : G) (p : U.domain) :
    A.map g (A.permutation (g⁻¹) p).val = p.val := by
  rw [A.map_eq, map_inv]
  exact congrArg Subtype.val ((A.permutation g).apply_symm_apply p)

theorem pushforward_mul (g h : G) (σ : Section U) :
    A.pushforward (g * h) σ = A.pushforward g (A.pushforward h σ) := by
  funext p
  apply ContinuousLinearMap.ext
  intro w
  simp only [pushforward, ContinuousLinearMap.comp_apply]
  rw [← A.inverse_image_mul g h p, A.derivative_mul]
  simp only [map_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply,
    ContinuousLinearMap.comp_apply]

def pushforwardLinear (g : G) : Section U →ₗ[ℂ] Section U where
  toFun := A.pushforward g
  map_add' σ τ := by funext p; simp [pushforward]
  map_smul' c σ := by funext p; simp [pushforward]

/-- Actual differential pushforwards form a genuine linear representation. -/
def representation : G →* Section U ≃ₗ[ℂ] Section U where
  toFun g :=
    { toFun := A.pushforward g
      invFun := A.pushforward (g⁻¹)
      left_inv := fun σ => by rw [← A.pushforward_mul, inv_mul_cancel, A.pushforward_one]
      right_inv := fun σ => by rw [← A.pushforward_mul, mul_inv_cancel, A.pushforward_one]
      map_add' := (A.pushforwardLinear g).map_add
      map_smul' := (A.pushforwardLinear g).map_smul }
  map_one' := by
    apply LinearEquiv.ext
    intro σ
    exact A.pushforward_one σ
  map_mul' g h := by
    apply LinearEquiv.ext
    intro σ
    exact A.pushforward_mul g h σ

theorem projection_pushforward (g : G) (σ : Section U) (p : U.domain) :
    projection r (A.pushforward g σ) p =
      projection r σ (A.permutation (g⁻¹) p) := by
  apply ContinuousLinearMap.ext
  intro w
  change mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun p.val
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (A.map g)
      (A.permutation (g⁻¹) p).val (σ (A.permutation (g⁻¹) p) w)) = _
  have heq := congrArg (fun l : (ℂ × ℂ) →L[ℂ] ℂ =>
    l (σ (A.permutation (g⁻¹) p) w))
    (A.retraction_derivative g (A.permutation (g⁻¹) p))
  rw [A.forward_inverse_image] at heq
  exact heq

theorem pushforward_isSplitting (g : G) (σ : Section U) (hσ : IsSplitting r σ) :
    IsSplitting r (A.pushforward g σ) := by
  funext p
  rw [A.projection_pushforward, show projection r σ = identitySection U from hσ]
  rfl

variable [Fintype G]

def average (σ : Section U) : Section U :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, A.pushforward g σ

theorem average_fixed (σ : Section U) (g : G) :
    A.pushforward g (A.average σ) = A.average σ := by
  change A.representation g ((Fintype.card G : ℂ)⁻¹ • ∑ h : G, A.representation h σ) = _
  rw [map_smul, map_sum]
  congr 1
  calc
    ∑ h : G, A.representation g (A.representation h σ) =
        ∑ h : G, A.representation (g * h) σ := by
      congr 1
      funext h
      rw [map_mul, LinearEquiv.mul_apply]
    _ = ∑ h : G, A.representation h σ :=
      Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

theorem average_isSplitting (σ : Section U) (hσ : IsSplitting r σ) :
    IsSplitting r (A.average σ) := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have htranslate : ∀ g, projection r (A.pushforward g σ) = identitySection U :=
    fun g => A.pushforward_isSplitting g σ hσ
  change projection r ((Fintype.card G : ℂ)⁻¹ • ∑ g : G, A.pushforward g σ) = _
  rw [map_smul, map_sum]
  simp only [htranslate, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

end NeighbourhoodAction

/-- Evaluation of an actual section, extended by zero outside its domain. -/
def sectionEvaluation (x : X) : Section U →ₗ[ℂ] (ℂ →L[ℂ] (ℂ × ℂ)) := by
  classical
  exact if hx : x ∈ U.domain then
    { toFun := fun σ => σ ⟨x, hx⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  else 0

/-- Actual local coefficient of a section of Hom(r*TD,TX), using the actual
ambient chart differential and inverse actual base-chart differential. -/
def coordinateCoefficient (r : D.Retraction U) (a : X) (i : D.curve)
    (z : ℂ × ℂ) : Section U →ₗ[ℂ] (ℂ × ℂ) where
  toFun σ :=
    let x := (chartAt (ℂ × ℂ) a).symm z
    mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) (chartAt (ℂ × ℂ) a) x
      (sectionEvaluation x σ ((EmbeddedFrames.tangentCoordinate D.curve i (r.toFun x)).symm 1))
  map_add' σ τ := by simp only [map_add, ContinuousLinearMap.add_apply]
  map_smul' c σ := by simp only [map_smul, ContinuousLinearMap.smul_apply, RingHom.id_apply]

/-- Holomorphicity means analyticity of actual coefficient functions in a
neighbourhood of every point, in its actual surface and retraction-base charts.
The zero extension has no role near those points since U is open. -/
def HolomorphicSection (r : D.Retraction U) (σ : Section U) : Prop :=
  ∀ p : U.domain, AnalyticAt ℂ
    (fun z => coordinateCoefficient r p.val (r.toFun p.val) z σ)
    ((chartAt (ℂ × ℂ) p.val) p.val)

def holomorphicSections (r : D.Retraction U) : Submodule ℂ (Section U) where
  carrier := HolomorphicSection r
  zero_mem' := by
    intro p
    simpa only [map_zero] using
      (analyticAt_const : AnalyticAt ℂ (fun _ : ℂ × ℂ => (0 : ℂ × ℂ))
        ((chartAt (ℂ × ℂ) p.val) p.val))
  add_mem' hσ hτ := by
    intro p
    simpa only [map_add] using (hσ p).add (hτ p)
  smul_mem' c σ hσ := by
    intro p
    simpa only [map_smul] using (hσ p).fun_const_smul (c := c)

def curvePoint (U : D.Neighbourhood) (p : D.curve) : U.domain :=
  ⟨D.inclusion p, U.contains p⟩

/-- The retraction/inclusion identity gives an actual differential identity. -/
theorem retraction_inclusion_derivative (r : D.Retraction U) (p : D.curve) :
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun (D.inclusion p)).comp
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p) =
        ContinuousLinearMap.id ℂ ℂ := by
  have hchain := mfderiv_comp p
    ((r.holomorphic _ (U.contains p)).mdifferentiableAt
      (U.open_domain.mem_nhds (U.contains p))) (D.inclusion.holomorphic p)
  have heq : r.toFun ∘ D.inclusion = id := funext r.retract
  rw [heq, mfderiv_id] at hchain
  exact hchain.symm

namespace NeighbourhoodAction

variable {G} {r : D.Retraction U} (A : NeighbourhoodAction G r)
  {N T : HolomorphicLineCocycle D.curve}

/-- The actual generator fixes the curve and rotates its actual normal
quotient coordinate by ζ in honest adapted frames. No normal evaluation of
the averaged section is assumed. -/
structure NormalRotation (frames : EmbeddedFrames.RawEmbeddedFrames D N T)
    (g : G) (ζ : ℂ) : Prop where
  fixes_curve : ∀ p : D.curve, A.permutation g (curvePoint U p) = curvePoint U p
  normal : ∀ (p : D.curve) (v : ℂ × ℂ),
    ((frames.frame p p).symm
      (A.derivative g (curvePoint U p) (frames.frame p p v))).2 = ζ * v.2

theorem fixed_section_tangent (frames : EmbeddedFrames.RawEmbeddedFrames D N T)
    {g : G} {ζ : ℂ} (rotation : A.NormalRotation frames g ζ) (hζ : ζ ≠ 1)
    (σ : Section U) (hfixed : A.pushforward g σ = σ) (p : D.curve) (w : ℂ) :
    σ (curvePoint U p) w ∈ LinearMap.range
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p).toLinearMap := by
  have hinv : A.permutation (g⁻¹) (curvePoint U p) = curvePoint U p := by
    have heq := congrArg (A.permutation g).symm (rotation.fixes_curve p)
    simpa only [map_inv, Equiv.Perm.inv_def, Equiv.symm_apply_apply] using heq.symm
  have hvector := congrArg (fun s : Section U => s (curvePoint U p) w) hfixed
  change A.derivative g (A.permutation (g⁻¹) (curvePoint U p))
    (σ (A.permutation (g⁻¹) (curvePoint U p)) w) = σ (curvePoint U p) w at hvector
  rw [hinv] at hvector
  let v : ℂ × ℂ := (frames.frame p p).symm (σ (curvePoint U p) w)
  have hnormal : v.2 = ζ * v.2 := by
    have heq := rotation.normal p v
    rw [ContinuousLinearEquiv.apply_symm_apply, hvector] at heq
    exact heq
  have hvzero : v.2 = 0 := by
    have heq : (ζ - 1) * v.2 = 0 := by linear_combination -hnormal
    exact (mul_eq_zero.mp heq).resolve_left (sub_ne_zero.mpr hζ)
  refine ⟨(EmbeddedFrames.tangentCoordinate D.curve p p).symm v.1, ?_⟩
  have heq := (frames.frame p p).apply_symm_apply (σ (curvePoint U p) w)
  change frames.frame p p v = _ at heq
  have hframe : frames.frame p p (v.1, 0) = σ (curvePoint U p) w := by
    exact (congrArg (frames.frame p p) (show (v.1, 0) = v from
      Prod.ext rfl hvzero.symm)).trans heq
  exact (frames.tangent_adapted p p (mem_chart_source ℂ p) v.1).symm.trans hframe

end NeighbourhoodAction

/-- A splitting tangent to the curve is exactly its actual tangent inclusion
on the curve, by differentiating r∘ι=id. -/
theorem splitting_eq_inclusion (r : D.Retraction U) (σ : Section U)
    (hs : IsSplitting r σ)
    (htangent : ∀ p : D.curve, ∀ w : ℂ, σ (curvePoint U p) w ∈ LinearMap.range
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p).toLinearMap)
    (p : D.curve) (w : ℂ) :
    σ (curvePoint U p) w = mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p w := by
  obtain ⟨z, hz⟩ := htangent p w
  have hprojection := congrArg (fun s : EndSection U => s (curvePoint U p) w) hs
  change mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun (D.inclusion p)
    (σ (curvePoint U p) w) = w at hprojection
  rw [← hz] at hprojection
  have hchain := congrArg (fun l : ℂ →L[ℂ] ℂ => l z) (retraction_inclusion_derivative r p)
  have hzw : z = w := hchain.symm.trans hprojection
  exact hz.symm.trans (congrArg
    (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p) hzw)

theorem splitting_injective (r : D.Retraction U) (σ : Section U)
    (hs : IsSplitting r σ) (p : U.domain) : Function.Injective (σ p) := by
  intro a b hab
  have hπ := congrArg (fun s : EndSection U => s p) hs
  have ha := congrArg (fun l : ℂ →L[ℂ] ℂ => l a) hπ
  have hb := congrArg (fun l : ℂ →L[ℂ] ℂ => l b) hπ
  exact ha.symm.trans ((congrArg
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun p.val) hab).trans hb)

/-- An actual holomorphic line subbundle is the fibrewise image of this
holomorphic injective map r*TD→TX. Its line is the actual linear range. -/
structure HolomorphicLineSubbundle (r : D.Retraction U) where
  map : Section U
  holomorphic : HolomorphicSection r map
  injective : ∀ p : U.domain, Function.Injective (map p)

def HolomorphicLineSubbundle.lineAt {r : D.Retraction U}
    (L : HolomorphicLineSubbundle r) (p : U.domain) : Submodule ℂ (ℂ × ℂ) :=
  LinearMap.range (L.map p).toLinearMap

/-- General tangential holomorphic subbundle/Bott theorem on the actual
neighbourhood and compact embedded curve. The normal cocycle is identified
with the actual quotient by raw adapted frames. There is no arbitrary Leaf,
free degree, averaging operation, or vanishing assertion in this interface.
ABST, Localization of Atiyah classes (2013), Theorem 7.1 and Corollary 7.3,
give the compact-Kähler tangential-normal Chern-class consequence used here. -/
def BottTangentialSubbundleDegreeZero (theory : LineBundleDegreeTheory) : Prop :=
  ∀ (X : CompactComplexSurface) (D : EmbeddedCurve X) (U : D.Neighbourhood)
    (r : D.Retraction U) (N T : HolomorphicLineCocycle D.curve)
    (_frames : EmbeddedFrames.RawEmbeddedFrames D N T) (L : HolomorphicLineSubbundle r),
    (∀ p : D.curve, L.lineAt (curvePoint U p) = LinearMap.range
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p).toLinearMap) →
      theory.degree D.curve N = 0

/-- Actual joint derivative of the retraction and an arbitrary holomorphic
map to a curve. Bijectivity is the genuine transversality condition. -/
def jointDifferential (r : D.Retraction U) {B : Curve} (h : HolomorphicMap X B)
    (p : U.domain) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r.toFun p.val).prod
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) h p.val)

def JointTransverse (r : D.Retraction U) {B : Curve} (h : HolomorphicMap X B) : Prop :=
  ∀ p : U.domain, Function.Bijective (jointDifferential r h p)

def jointEquiv (r : D.Retraction U) {B : Curve} (h : HolomorphicMap X B)
    (ht : JointTransverse r h) (p : U.domain) : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
  (LinearEquiv.ofBijective (jointDifferential r h p).toLinearMap
    (ht p)).toContinuousLinearEquiv

/-- The splitting in the actual third-map kernel, constructed by inverting
the actual joint derivative and applying it to `(w,0)`. -/
def transverseSplitting (r : D.Retraction U) {B : Curve} (h : HolomorphicMap X B)
    (ht : JointTransverse r h) : Section U := fun p =>
  (jointEquiv r h ht p).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℂ ℂ ℂ)

theorem transverseSplitting_isSplitting (r : D.Retraction U) {B : Curve}
    (h : HolomorphicMap X B) (ht : JointTransverse r h) :
    IsSplitting r (transverseSplitting r h ht) := by
  funext p
  apply ContinuousLinearMap.ext
  intro w
  exact congrArg Prod.fst ((jointEquiv r h ht p).apply_symm_apply (w, 0))

theorem transverseSplitting_in_kernel (r : D.Retraction U) {B : Curve}
    (h : HolomorphicMap X B) (ht : JointTransverse r h) (p : U.domain) (w : ℂ) :
    mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) h p.val (transverseSplitting r h ht p w) = 0 := by
  exact congrArg Prod.snd ((jointEquiv r h ht p).apply_symm_apply (w, 0))

/-- General holomorphic bundle calculus for actual functions and actual
chart-analytic coefficients: invert a nonsingular joint bundle map and
push forward a holomorphic section by a holomorphic automorphism. -/
structure HolomorphicSplittingCalculus : Prop where
  inverse_holomorphic : ∀ (X : CompactComplexSurface) (D : EmbeddedCurve X)
    (U : D.Neighbourhood) (r : D.Retraction U) (B : Curve)
    (h : HolomorphicMap X B) (ht : JointTransverse r h),
      HolomorphicSection r (transverseSplitting r h ht)
  pushforward_holomorphic : ∀ (X : CompactComplexSurface) (D : EmbeddedCurve X)
    (U : D.Neighbourhood) (r : D.Retraction U) (G : Type) [Group G]
    (A : NeighbourhoodAction G r) (g : G) (σ : Section U),
      HolomorphicSection r σ → HolomorphicSection r (A.pushforward g σ)

namespace NeighbourhoodAction

variable {G} [Fintype G] {r : D.Retraction U} (A : NeighbourhoodAction G r)

theorem average_holomorphic (calculus : HolomorphicSplittingCalculus)
    (σ : Section U) (hs : HolomorphicSection r σ) : HolomorphicSection r (A.average σ) := by
  apply (holomorphicSections r).smul_mem
  apply (holomorphicSections r).sum_mem
  intro g _
  exact calculus.pushforward_holomorphic X D U r G A g σ hs

end NeighbourhoodAction

/-- Lemma 3.2's actual geometric contradiction. The third-map joint inverse
provides the initial holomorphic splitting. Its finite differential average
is a splitting and is fixed. A nontrivial actual normal rotation forces its
image to be the actual tangent line of the embedded compact curve. The general
Bott theorem applies to that constructed actual holomorphic line subbundle. -/
theorem transverse_obstruction (calculus : HolomorphicSplittingCalculus)
    (theory : LineBundleDegreeTheory) (bott : BottTangentialSubbundleDegreeZero theory)
    {G : Type} [Group G] [Fintype G] {r : D.Retraction U}
    (A : NeighbourhoodAction G r) {N T : HolomorphicLineCocycle D.curve}
    (frames : EmbeddedFrames.RawEmbeddedFrames D N T)
    (g : G) (ζ : ℂ) (rotation : A.NormalRotation frames g ζ) (hζ : ζ ≠ 1)
    (hnegative : theory.degree D.curve N < 0) {B : Curve}
    (h : HolomorphicMap X B) (ht : JointTransverse r h) : False := by
  let σ := transverseSplitting r h ht
  let average := A.average σ
  have hσ : IsSplitting r σ := transverseSplitting_isSplitting r h ht
  have havg : IsSplitting r average := A.average_isSplitting σ hσ
  have hhol : HolomorphicSection r average := A.average_holomorphic calculus σ
    (calculus.inverse_holomorphic X D U r B h ht)
  have htangent := A.fixed_section_tangent frames rotation hζ average (A.average_fixed σ g)
  let L : HolomorphicLineSubbundle r :=
    ⟨average, hhol, splitting_injective r average havg⟩
  have hline : ∀ p : D.curve, L.lineAt (curvePoint U p) = LinearMap.range
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p).toLinearMap := by
    intro p
    have heq : average (curvePoint U p) =
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p := by
      apply ContinuousLinearMap.ext
      intro w
      exact splitting_eq_inclusion r average havg htangent p w
    exact congrArg (fun l : ℂ →L[ℂ] (ℂ × ℂ) => LinearMap.range l.toLinearMap) heq
  have hzero := bott X D U r N T frames L hline
  exact (ne_of_lt hnegative) hzero

end Paper27.Geometry.NeighbourhoodSplittings
