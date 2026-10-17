import Paper27.Geometry.RetractionFactorization

/-!
# Choosing one actual retraction for each map on a common neighbourhood

Each actual unramified restricted map supplies its own covering lift. Finite
intersection gives one actual neighbourhood on which all lifts are defined.
All pairs then use these same actual retractions; no identification of
independently chosen pair-specific lifts is needed.
-/
noncomputable section
namespace Paper27.Geometry.CommonRetractions
open RetractionFactorization
variable {X : CompactComplexSurface} {D : EmbeddedCurve X}

structure Pair (D : EmbeddedCurve X) (f g : Fibration X) where
  neighbourhood : D.Neighbourhood
  first : D.Retraction neighbourhood
  second : D.Retraction neighbourhood
  first_factor : Factorization first f
  second_factor : Factorization second g

def pairOfFactored (f g : Fibration X) (R : FactoredRetraction D f)
    (S : FactoredRetraction D g) : Pair D f g := by
  let U : D.Neighbourhood :=
    { domain := R.neighbourhood.domain ∩ S.neighbourhood.domain
      open_domain := R.neighbourhood.open_domain.inter S.neighbourhood.open_domain
      contains := fun p => ⟨R.neighbourhood.contains p, S.neighbourhood.contains p⟩ }
  exact
    { neighbourhood := U
      first := restrictRetraction R.retraction U (fun _ hx => hx.1)
      second := restrictRetraction S.retraction U (fun _ hx => hx.2)
      first_factor := fun x hx => R.factor x hx.1
      second_factor := fun x hx => S.factor x hx.2 }

def pair (covering : CompactUnramifiedCurveCovering)
    (lifting : TopologicalCoverNeighbourhoodLifting) (regularity : HolomorphicEtaleLiftRegularity)
    (D : EmbeddedCurve X) (f g : Fibration X) (hf : D.Unramified f) (hg : D.Unramified g) :
    Pair D f g :=
  pairOfFactored f g (factoredRetraction covering lifting regularity D f hf)
    (factoredRetraction covering lifting regularity D g hg)

structure Triple (D : EmbeddedCurve X) (f g h : Fibration X) where
  neighbourhood : D.Neighbourhood
  first : D.Retraction neighbourhood
  second : D.Retraction neighbourhood
  third : D.Retraction neighbourhood
  first_factor : Factorization first f
  second_factor : Factorization second g
  third_factor : Factorization third h

def tripleOfFactored (f g h : Fibration X) (R : FactoredRetraction D f)
    (S : FactoredRetraction D g) (T : FactoredRetraction D h) : Triple D f g h := by
  let U : D.Neighbourhood :=
    { domain := R.neighbourhood.domain ∩ S.neighbourhood.domain ∩ T.neighbourhood.domain
      open_domain := (R.neighbourhood.open_domain.inter S.neighbourhood.open_domain).inter
        T.neighbourhood.open_domain
      contains := fun p => ⟨⟨R.neighbourhood.contains p, S.neighbourhood.contains p⟩,
        T.neighbourhood.contains p⟩ }
  exact
    { neighbourhood := U
      first := restrictRetraction R.retraction U (fun _ hx => hx.1.1)
      second := restrictRetraction S.retraction U (fun _ hx => hx.1.2)
      third := restrictRetraction T.retraction U (fun _ hx => hx.2)
      first_factor := fun x hx => R.factor x hx.1.1
      second_factor := fun x hx => S.factor x hx.1.2
      third_factor := fun x hx => T.factor x hx.2 }

def triple (covering : CompactUnramifiedCurveCovering)
    (lifting : TopologicalCoverNeighbourhoodLifting) (regularity : HolomorphicEtaleLiftRegularity)
    (D : EmbeddedCurve X) (f g h : Fibration X)
    (hf : D.Unramified f) (hg : D.Unramified g) (hh : D.Unramified h) : Triple D f g h :=
  tripleOfFactored f g h (factoredRetraction covering lifting regularity D f hf)
    (factoredRetraction covering lifting regularity D g hg)
    (factoredRetraction covering lifting regularity D h hh)

end Paper27.Geometry.CommonRetractions
