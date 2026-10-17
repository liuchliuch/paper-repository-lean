import Paper27.Geometry.Factorization
import Mathlib.Topology.Covering

/-!
# Products of curves and the unramified case

Products and their two smooth projections are constructed with mathlib's actual
product charts. The classical product-rigidity input is the one-component form
of the argument in F. Catanese, *Fibred surfaces, varieties isogenous to a
product and related moduli spaces*, AJM 122 (2000), p. 19, Rigidity Lemma 3.8
and its proof: https://www.mathe8.uni-bayreuth.de/de/team/prof-fabrizio-catanese-old/pdf/066.pdf
The exact published lemma concerns surjective maps between two products; its
proof gives the component rigidity used here. No fibration-equivalence assertion
is included in that input.
-/

noncomputable section

open scoped Manifold Topology

namespace Paper27.Geometry

namespace Curve

instance productChartedSpace (C D : Curve) : ChartedSpace (ℂ × ℂ) (C × D) :=
  prodChartedSpace ℂ C ℂ D

instance productIsManifold (C D : Curve) : IsManifold 𝓘(ℂ, ℂ × ℂ) 1 (C × D) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ)) (n := 1) C D

/-- The actual product of compact complex curves, with the product atlas. -/
def productSurface (C D : Curve) : CompactComplexSurface where
  Carrier := C × D
  topology := inferInstance
  hausdorff := inferInstance
  secondCountable := inferInstance
  connected := inferInstance
  compact := inferInstance
  charted := prodChartedSpace ℂ C ℂ D
  manifold := productIsManifold C D

def firstProjection (C D : Curve) : Fibration (C.productSurface D) where
  base := C
  map := Prod.fst
  holomorphic := by
    rw [modelWithCornersSelf_prod]
    exact mdifferentiable_fst (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ)) (M := C) (M' := D)
  surjective := fun c => ⟨(c, D.basepoint), rfl⟩
  connected_fibres := by
    intro c
    have heq : (Prod.fst ⁻¹' {c} : Set (C × D)) = {c} ×ˢ Set.univ := by
      ext p
      simp
    rw [heq]
    exact isConnected_singleton.prod isConnected_univ

def secondProjection (C D : Curve) : Fibration (C.productSurface D) where
  base := D
  map := Prod.snd
  holomorphic := by
    rw [modelWithCornersSelf_prod]
    exact mdifferentiable_snd (I := 𝓘(ℂ, ℂ)) (I' := 𝓘(ℂ, ℂ)) (M := C) (M' := D)
  surjective := fun d => ⟨(C.basepoint, d), rfl⟩
  connected_fibres := by
    intro d
    have heq : (Prod.snd ⁻¹' {d} : Set (C × D)) = Set.univ ×ˢ {d} := by
      ext p
      simp
    rw [heq]
    exact isConnected_univ.prod isConnected_singleton

theorem firstProjection_smooth (C D : Curve) : (C.firstProjection D).Smooth := by
  intro p
  change Function.Surjective (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) Prod.fst p)
  rw [modelWithCornersSelf_prod, mfderiv_fst]
  exact fun v => ⟨(v, 0), rfl⟩

theorem secondProjection_smooth (C D : Curve) : (C.secondProjection D).Smooth := by
  intro p
  change Function.Surjective (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) Prod.snd p)
  rw [modelWithCornersSelf_prod, mfderiv_snd]
  exact fun v => ⟨(0, v), rfl⟩

theorem firstProjection_mfderiv (C D : Curve) (p : C.productSurface D) :
    mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) (C.firstProjection D).map p =
      ContinuousLinearMap.fst ℂ ℂ ℂ := by
  change mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) Prod.fst p = _
  rw [modelWithCornersSelf_prod, mfderiv_fst]
  rfl

theorem secondProjection_mfderiv (C D : Curve) (p : C.productSurface D) :
    mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) (C.secondProjection D).map p =
      ContinuousLinearMap.snd ℂ ℂ ℂ := by
  change mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) Prod.snd p = _
  rw [modelWithCornersSelf_prod, mfderiv_snd]
  rfl

/-- The two projections are inequivalent, because one can vary the second
coordinate while the first remains fixed. -/
theorem projections_inequivalent (C D : Curve) :
    ¬ Fibration.Equivalent (C.firstProjection D) (C.secondProjection D) := by
  rintro ⟨e, he⟩
  obtain ⟨d, d', hdd'⟩ := D.exists_distinct
  have hd := he (C.basepoint, d)
  have hd' := he (C.basepoint, d')
  exact hdd' (hd.symm.trans hd')

/-- The product examples give two inequivalent smooth hyperbolic fibrations. -/
theorem product_has_two (C D : Curve) (hC : C.Hyperbolic) (hD : D.Hyperbolic) :
    ∃ f g : HyperbolicSmoothFibration (C.productSurface D),
      ¬ Fibration.Equivalent f.val g.val :=
  ⟨⟨C.firstProjection D, C.firstProjection_smooth D, hC⟩,
    ⟨C.secondProjection D, C.secondProjection_smooth D, hD⟩,
    C.projections_inequivalent D⟩

end Curve

/-- Classical product rigidity for a single holomorphic map to a hyperbolic
curve. This input concerns only maps on an actual product, without fibrations. -/
def ProductCurveRigidity : Prop :=
  ∀ (A B C : Curve), C.Hyperbolic →
    ∀ F : HolomorphicMap (A.productSurface B) C,
      (∃ a : HolomorphicMap A C, ∀ p : A × B, F p = a p.1) ∨
        (∃ b : HolomorphicMap B C, ∀ p : A × B, F p = b p.2)

/-- A finite unramified holomorphic covering, expressed by actual covering-map
and differential conditions. The differential is bijective, as for a local
biholomorphism; no predicate is a free geometric label. -/
structure FiniteUnramifiedCover {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (M : CompactComplexManifold E) (N : CompactComplexManifold F) where
  map : HolomorphicMap M N
  surjective : Function.Surjective map
  finite_fibres : ∀ n : N, (map ⁻¹' {n}).Finite
  covering : IsCoveringMap map
  differential_bijective : ∀ p : M, Function.Bijective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, F) map p)

/-- The product cover furnished by finite-index subgroup covering theory.  Its
diagram is stated pointwise on the actual manifolds. -/
structure ProductCoverModel {X : CompactComplexSurface} {C D : Curve}
    (q : FiniteUnramifiedCover X (C.productSurface D)) where
  leftCurve : Curve
  rightCurve : Curve
  cover : FiniteUnramifiedCover (leftCurve.productSurface rightCurve) X
  left : FiniteUnramifiedCover leftCurve C
  right : FiniteUnramifiedCover rightCurve D
  commutes : ∀ z : leftCurve × rightCurve,
    q.map (cover.map z) = (left.map z.1, right.map z.2)

/-- The standard covering-space existence theorem for a finite cover of a
product. Its conclusion contains no third map or fibration-equivalence claim. -/
def ProductCoverExistence : Prop :=
  ∀ (X : CompactComplexSurface) (C D : Curve)
    (q : FiniteUnramifiedCover X (C.productSurface D)), Nonempty (ProductCoverModel q)

/-- The classical zero-differential theorem on connected smooth fibres,
formulated for actual holomorphic maps and their actual manifold derivatives. -/
def ConnectedFibreDerivativeConstancy : Prop :=
  ∀ (X : CompactComplexSurface) (B C : Curve)
    (f : HolomorphicMap X B) (h : HolomorphicMap X C),
    (∀ b : B, IsConnected (f ⁻¹' {b})) →
    (∀ p : X, Function.Surjective (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f p)) →
    (∀ (p : X) (v : ℂ × ℂ),
      mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f p v = 0 →
        mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) h p v = 0) →
    ∀ (b : B) (p r : X), f p = b → f r = b → h p = h r

/-- Holomorphic submersions have local holomorphic sections. -/
def HolomorphicSubmersionSections : Prop :=
  ∀ (X : CompactComplexSurface) (f : Fibration X), f.Smooth → f.LocalHolomorphicSections

/-- Equality of the actual factorizations gives the exact chain-rule identity. -/
theorem derivative_factorization_apply {P X : CompactComplexSurface} {A B : Curve}
    (f : HolomorphicMap X B) (p : HolomorphicMap P X)
    (a : HolomorphicMap A B) (r : HolomorphicMap P A)
    (heq : ∀ z, f (p z) = a (r z)) (z : P) (v : ℂ × ℂ) :
    mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f (p z)
        (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) p z v) =
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) a (r z)
        (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r z v) := by
  have hfun : (f ∘ p) = (a ∘ r) := funext heq
  calc
    _ = mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) (f ∘ p) z v :=
      (mfderiv_comp_apply z (f.holomorphic (p z)) (p.holomorphic z) v).symm
    _ = mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) (a ∘ r) z v :=
      congrArg (fun k : P → B => mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) k z v) hfun
    _ = _ := mfderiv_comp_apply z (a.holomorphic (r z)) (r.holomorphic z) v

/-- The chain rule transfers the common factorization upstairs into vanishing
on the vertical kernel downstairs. Surjectivity of `dp` and injectivity of `da`
are used explicitly. This is the local-biholomorphism step of Lemma 3.4. -/
theorem vertical_derivative_of_cover_factorization
    {P X : CompactComplexSurface} {A B C : Curve}
    (f : HolomorphicMap X B) (h : HolomorphicMap X C)
    (p : HolomorphicMap P X) (r : HolomorphicMap P A)
    (a : HolomorphicMap A B) (β : HolomorphicMap A C)
    (hpsurj : Function.Surjective p)
    (hdp : ∀ z : P, Function.Surjective (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) p z))
    (hda : ∀ t : A, Function.Injective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) a t))
    (hf : ∀ z, f (p z) = a (r z)) (hh : ∀ z, h (p z) = β (r z)) :
    ∀ (x : X) (v : ℂ × ℂ),
      mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f x v = 0 →
        mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) h x v = 0 := by
  intro x v hv
  obtain ⟨z, rfl⟩ := hpsurj x
  obtain ⟨w, hw⟩ := hdp z v
  have hchain := derivative_factorization_apply f p a r hf z w
  have hazero : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) a (r z)
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r z w) = 0 := by
    rw [← hchain, hw]
    exact hv
  have hrzero : mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) r z w = 0 :=
    hda (r z) (by simpa only [map_zero] using hazero)
  calc
    _ = mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) h (p z)
        (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) p z w) :=
      congrArg (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) h (p z)) hw.symm
    _ = _ := derivative_factorization_apply h p β r hh z w
    _ = 0 := by rw [hrzero, map_zero]

namespace FiniteUnramifiedCover

variable {X : CompactComplexSurface} {C D : Curve}

/-- The first induced factor map, with its actual connected-fibre hypothesis. -/
def firstFibration (q : FiniteUnramifiedCover X (C.productSurface D))
    (hconnected : ∀ c : C, IsConnected ((fun x : X => (q.map x).1) ⁻¹' {c})) :
    Fibration X where
  base := C
  map := fun x => (q.map x).1
  holomorphic := (C.firstProjection D).holomorphic.comp q.map.holomorphic
  surjective := by
    intro c
    obtain ⟨x, hx⟩ := q.surjective (c, D.basepoint)
    exact ⟨x, congrArg Prod.fst hx⟩
  connected_fibres := hconnected

def secondFibration (q : FiniteUnramifiedCover X (C.productSurface D))
    (hconnected : ∀ d : D, IsConnected ((fun x : X => (q.map x).2) ⁻¹' {d})) :
    Fibration X where
  base := D
  map := fun x => (q.map x).2
  holomorphic := (C.secondProjection D).holomorphic.comp q.map.holomorphic
  surjective := by
    intro d
    obtain ⟨x, hx⟩ := q.surjective (C.basepoint, d)
    exact ⟨x, congrArg Prod.snd hx⟩
  connected_fibres := hconnected

theorem firstFibration_smooth (q : FiniteUnramifiedCover X (C.productSurface D))
    (hconnected : ∀ c : C, IsConnected ((fun x : X => (q.map x).1) ⁻¹' {c})) :
    (q.firstFibration hconnected).Smooth := by
  intro x v
  obtain ⟨w, hw⟩ := (q.differential_bijective x).2 (v, 0)
  refine ⟨w, ?_⟩
  change mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) ((C.firstProjection D).map ∘ q.map) x w = v
  rw [mfderiv_comp_apply x ((C.firstProjection D).holomorphic (q.map x)) (q.map.holomorphic x)]
  rw [Curve.firstProjection_mfderiv]
  exact congrArg Prod.fst hw

theorem secondFibration_smooth (q : FiniteUnramifiedCover X (C.productSurface D))
    (hconnected : ∀ d : D, IsConnected ((fun x : X => (q.map x).2) ⁻¹' {d})) :
    (q.secondFibration hconnected).Smooth := by
  intro x v
  obtain ⟨w, hw⟩ := (q.differential_bijective x).2 (0, v)
  refine ⟨w, ?_⟩
  change mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) ((C.secondProjection D).map ∘ q.map) x w = v
  rw [mfderiv_comp_apply x ((C.secondProjection D).holomorphic (q.map x)) (q.map.holomorphic x)]
  rw [Curve.secondProjection_mfderiv]
  exact congrArg Prod.snd hw

end FiniteUnramifiedCover

namespace Fibration

variable {X : CompactComplexSurface}

/-- For onto fibrations, the nonconstancy and finiteness hypotheses of the
connected-fibre factorization theorem follow from the classical curve theorem. -/
theorem equivalent_of_curve_factorization (curveMaps : NonconstantCompactCurveMapTheorem)
    (inverseTheorem : BijectiveHolomorphicInverse) (f h : Fibration X)
    (a : HolomorphicMap f.base h.base) (hfactor : ∀ x, a (f x) = h x) :
    Equivalent f h := by
  have hn := surjective_curve_map_nonconstant a (factor_surjective f h a hfactor)
  exact equivalent_of_factorization inverseTheorem f h a hfactor
    (curveMaps f.base h.base a hn).1

/-- Zero vertical differential gives actual holomorphic descent, and then the
proved connected-fibre argument gives equivalence. No smoothness of `h` occurs. -/
theorem equivalent_of_vertical_derivative
    (curveMaps : NonconstantCompactCurveMapTheorem)
    (inverseTheorem : BijectiveHolomorphicInverse)
    (constancy : ConnectedFibreDerivativeConstancy)
    (sections : HolomorphicSubmersionSections) (f h : Fibration X) (hf : f.Smooth)
    (hvertical : ∀ (p : X) (v : ℂ × ℂ),
      mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f.map p v = 0 →
        mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) h.map p v = 0) : Equivalent f h := by
  have hall : ∀ b, ConstantOnFibre f h b :=
    constancy X f.base h.base ⟨f.map, f.holomorphic⟩ ⟨h.map, h.holomorphic⟩
      f.connected_fibres hf hvertical
  exact equivalent_of_curve_factorization curveMaps inverseTheorem f h
    (descendedHolomorphicMap f h hall (sections X f hf))
    (descendedFunction_factor f h hall)

end Fibration

/-- Lemma 3.4 for the actual induced factor maps of a finite unramified cover.
The third fibration `h` is not assumed smooth. The factor maps' smoothness,
derivative-kernel comparison, descent, and final equivalence are proved here. -/
theorem unramified_pair_fibration_equivalent
    (rigidity : ProductCurveRigidity) (productCovers : ProductCoverExistence)
    (constancy : ConnectedFibreDerivativeConstancy) (sections : HolomorphicSubmersionSections)
    (curveMaps : NonconstantCompactCurveMapTheorem) (inverseTheorem : BijectiveHolomorphicInverse)
    {X : CompactComplexSurface} {C D : Curve} (_hC : C.Hyperbolic) (_hD : D.Hyperbolic)
    (q : FiniteUnramifiedCover X (C.productSurface D))
    (hc : ∀ c : C, IsConnected ((fun x : X => (q.map x).1) ⁻¹' {c}))
    (hd : ∀ d : D, IsConnected ((fun x : X => (q.map x).2) ⁻¹' {d}))
    (h : Fibration X) (hh : h.Hyperbolic) :
    Fibration.Equivalent h (q.firstFibration hc) ∨
      Fibration.Equivalent h (q.secondFibration hd) := by
  obtain ⟨P⟩ := productCovers X C D q
  let F : HolomorphicMap (P.leftCurve.productSurface P.rightCurve) h.base :=
    ⟨fun z => h (P.cover.map z), h.holomorphic.comp P.cover.map.holomorphic⟩
  rcases rigidity P.leftCurve P.rightCurve h.base hh F with hfirst | hsecond
  · obtain ⟨a, ha⟩ := hfirst
    let r : HolomorphicMap (P.leftCurve.productSurface P.rightCurve) P.leftCurve :=
      ⟨(P.leftCurve.firstProjection P.rightCurve).map,
        (P.leftCurve.firstProjection P.rightCurve).holomorphic⟩
    have hv := vertical_derivative_of_cover_factorization
      (⟨(q.firstFibration hc).map, (q.firstFibration hc).holomorphic⟩ : HolomorphicMap X C)
      (⟨h.map, h.holomorphic⟩ : HolomorphicMap X h.base) P.cover.map r P.left.map a
      P.cover.surjective (fun z => (P.cover.differential_bijective z).2)
      (fun t => (P.left.differential_bijective t).1)
      (fun z => congrArg Prod.fst (P.commutes z)) ha
    exact Or.inl (Fibration.equivalent_symm
      (Fibration.equivalent_of_vertical_derivative curveMaps inverseTheorem constancy sections
        (q.firstFibration hc) h (q.firstFibration_smooth hc) hv))
  · obtain ⟨a, ha⟩ := hsecond
    let r : HolomorphicMap (P.leftCurve.productSurface P.rightCurve) P.rightCurve :=
      ⟨(P.leftCurve.secondProjection P.rightCurve).map,
        (P.leftCurve.secondProjection P.rightCurve).holomorphic⟩
    have hv := vertical_derivative_of_cover_factorization
      (⟨(q.secondFibration hd).map, (q.secondFibration hd).holomorphic⟩ : HolomorphicMap X D)
      (⟨h.map, h.holomorphic⟩ : HolomorphicMap X h.base) P.cover.map r P.right.map a
      P.cover.surjective (fun z => (P.cover.differential_bijective z).2)
      (fun t => (P.right.differential_bijective t).1)
      (fun z => congrArg Prod.snd (P.commutes z)) ha
    exact Or.inr (Fibration.equivalent_symm
      (Fibration.equivalent_of_vertical_derivative curveMaps inverseTheorem constancy sections
        (q.secondFibration hd) h (q.secondFibration_smooth hd) hv))

/-- On an actual product, rigidity and connected fibres already classify every
hyperbolic fibration, including those not initially assumed smooth. -/
theorem product_fibration_equivalent (rigidity : ProductCurveRigidity)
    (curveMaps : NonconstantCompactCurveMapTheorem) (inverseTheorem : BijectiveHolomorphicInverse)
    (C D : Curve) (h : Fibration (C.productSurface D)) (hh : h.Hyperbolic) :
    Fibration.Equivalent h (C.firstProjection D) ∨
      Fibration.Equivalent h (C.secondProjection D) := by
  rcases rigidity C D h.base hh ⟨h.map, h.holomorphic⟩ with hfirst | hsecond
  · obtain ⟨a, ha⟩ := hfirst
    exact Or.inl (Fibration.equivalent_symm
      (Fibration.equivalent_of_curve_factorization curveMaps inverseTheorem
        (C.firstProjection D) h a (fun z => (ha z).symm)))
  · obtain ⟨a, ha⟩ := hsecond
    exact Or.inr (Fibration.equivalent_symm
      (Fibration.equivalent_of_curve_factorization curveMaps inverseTheorem
        (C.secondProjection D) h a (fun z => (ha z).symm)))

/-- The bound of two on products, with no existence hypothesis on extra maps. -/
theorem product_atMostTwo (rigidity : ProductCurveRigidity)
    (curveMaps : NonconstantCompactCurveMapTheorem) (inverseTheorem : BijectiveHolomorphicInverse)
    (C D : Curve) : AtMostTwoSmoothHyperbolicFibrations (C.productSurface D) := by
  intro f g h
  have classify (k : HyperbolicSmoothFibration (C.productSurface D)) :=
    product_fibration_equivalent rigidity curveMaps inverseTheorem C D k.val k.property.2
  rcases classify f with hf | hf
  · rcases classify g with hg | hg
    · exact Or.inl (Fibration.equivalent_trans hf (Fibration.equivalent_symm hg))
    · rcases classify h with hh | hh
      · exact Or.inr (Or.inl (Fibration.equivalent_trans hf (Fibration.equivalent_symm hh)))
      · exact Or.inr (Or.inr (Fibration.equivalent_trans hg (Fibration.equivalent_symm hh)))
  · rcases classify g with hg | hg
    · rcases classify h with hh | hh
      · exact Or.inr (Or.inr (Fibration.equivalent_trans hg (Fibration.equivalent_symm hh)))
      · exact Or.inr (Or.inl (Fibration.equivalent_trans hf (Fibration.equivalent_symm hh)))
    · exact Or.inl (Fibration.equivalent_trans hf (Fibration.equivalent_symm hg))

end Paper27.Geometry
