import Paper27.Geometry.FibrationBound

/-!
# Kodaira fibrations and the sharpness consequences

Non-isotriviality means that two actual compact fibre curves are not
biholomorphic. Hyperbolicity of the base is not part of this definition. Its
classical deduction is an explicit universal external parameter, after which
Corollary 1.2 follows from the proved actual-surface theorem.

The product examples are constructed in `ProductCover`; the double Kodaira
example is a separately named published existence input. The deductions that
these examples attain the proved bound are internal.
-/
noncomputable section
namespace Paper27.Geometry

namespace Fibration
variable {X : CompactComplexSurface}

/-- Two genuine compact complex fibres have different complex structures. -/
def NonIsotrivial (f : Fibration X) : Prop :=
  ∃ (b c : f.base) (F : FibreCurveModel f b) (G : FibreCurveModel f c),
    ¬ Nonempty (Biholomorphism F.curve G.curve)

end Fibration

/-- A Kodaira fibration retains actual smoothness and actual variation of
the fibre complex structures; its base genus is a theorem, not a field. -/
abbrev KodairaFibration (X : CompactComplexSurface) :=
  {f : Fibration X // f.Smooth ∧ f.NonIsotrivial}

/-- The standard hyperbolicity theorem for a smooth non-isotrivial family of
compact curves. See Catanese--Rollenske, *Double Kodaira fibrations*, Remark
2.3, arXiv:math/0611428, p. 4; also Llosa Isenrich--Py, *Mapping class groups,
multiple Kodaira fibrations, and CAT(0) spaces*, Introduction, p. 2.
This universal classical theorem has not been constructed in Lean here. -/
def KodairaBaseHyperbolicity : Prop :=
  ∀ (X : CompactComplexSurface) (f : Fibration X),
    f.Smooth → f.NonIsotrivial → f.Hyperbolic

def AtMostTwoKodairaFibrations (X : CompactComplexSurface) : Prop :=
  ∀ f g h : KodairaFibration X,
    Fibration.Equivalent f.val g.val ∨ Fibration.Equivalent f.val h.val ∨
      Fibration.Equivalent g.val h.val

/-- Corollary 1.2, with the precise external base-genus theorem displayed. -/
theorem at_most_two_kodaira (K : ClassicalInputs) (bases : KodairaBaseHyperbolicity)
    (X : CompactComplexSurface) : AtMostTwoKodairaFibrations X := by
  intro f g h
  exact K.at_most_two X
    ⟨f.val, f.property.1, bases X f.val f.property.1 f.property.2⟩
    ⟨g.val, g.property.1, bases X g.val g.property.1 g.property.2⟩
    ⟨h.val, h.property.1, bases X h.val h.property.1 h.property.2⟩

/-- There are two distinct actual classes and every counted map belongs to
one of them. This expresses sharpness without a cardinality convention. -/
def ExactlyTwoSmoothHyperbolicFibrationClasses (X : CompactComplexSurface) : Prop :=
  ∃ f g : HyperbolicSmoothFibration X,
    ¬ Fibration.Equivalent f.val g.val ∧
      ∀ h : HyperbolicSmoothFibration X,
        Fibration.Equivalent h.val f.val ∨ Fibration.Equivalent h.val g.val

theorem exactly_two_of_two (K : ClassicalInputs) {X : CompactComplexSurface}
    (f g : HyperbolicSmoothFibration X) (hne : ¬ Fibration.Equivalent f.val g.val) :
    ExactlyTwoSmoothHyperbolicFibrationClasses X := by
  refine ⟨f, g, hne, ?_⟩
  intro h
  rcases K.at_most_two X f g h with hfg | hfh | hgh
  · exact False.elim (hne hfg)
  · exact Or.inl (Fibration.equivalent_symm hfh)
  · exact Or.inr (Fibration.equivalent_symm hgh)

/-- The actual projections of every product of two actual hyperbolic curves
attain the bound of Theorem 1.1. -/
theorem product_exactly_two (K : ClassicalInputs) (C D : Curve)
    (hC : C.Hyperbolic) (hD : D.Hyperbolic) :
    ExactlyTwoSmoothHyperbolicFibrationClasses (C.productSurface D) := by
  obtain ⟨f, g, hne⟩ := Curve.product_has_two C D hC hD
  exact exactly_two_of_two K f g hne

def ExactlyTwoKodairaFibrationClasses (X : CompactComplexSurface) : Prop :=
  ∃ f g : KodairaFibration X,
    ¬ Fibration.Equivalent f.val g.val ∧ ∀ h : KodairaFibration X,
      Fibration.Equivalent h.val f.val ∨ Fibration.Equivalent h.val g.val

/-- The published construction of double Kodaira fibrations, recorded solely
as an explicit external existence parameter. Catanese--Rollenske,
*Double Kodaira fibrations*, arXiv:math/0611428, Example 5.8 (p. 16) and
Corollary 6.6 (p. 20). The constructed surfaces are not reconstructed here. -/
def DoubleKodairaExistence : Prop :=
  ∃ (X : CompactComplexSurface) (f g : KodairaFibration X),
    ¬ Fibration.Equivalent f.val g.val

/-- The external examples and the proved upper bound give exactly two
classes for a double Kodaira surface. -/
theorem double_kodaira_exactly_two (K : ClassicalInputs) (bases : KodairaBaseHyperbolicity)
    (examples : DoubleKodairaExistence) :
    ∃ X : CompactComplexSurface, ExactlyTwoKodairaFibrationClasses X := by
  obtain ⟨X, f, g, hne⟩ := examples
  refine ⟨X, f, g, hne, ?_⟩
  intro h
  rcases at_most_two_kodaira K bases X f g h with hfg | hfh | hgh
  · exact False.elim (hne hfg)
  · exact Or.inl (Fibration.equivalent_symm hfh)
  · exact Or.inr (Fibration.equivalent_symm hgh)

/-- A published double Kodaira surface attains the full smooth-hyperbolic
bound as well as the Kodaira bound, on the very same actual surface. -/
theorem double_kodaira_attains_bound (K : ClassicalInputs) (bases : KodairaBaseHyperbolicity)
    (examples : DoubleKodairaExistence) :
    ∃ X : CompactComplexSurface, ExactlyTwoSmoothHyperbolicFibrationClasses X ∧
      ExactlyTwoKodairaFibrationClasses X := by
  obtain ⟨X, f, g, hne⟩ := examples
  have htwo := exactly_two_of_two K
    ⟨f.val, f.property.1, bases X f.val f.property.1 f.property.2⟩
    ⟨g.val, g.property.1, bases X g.val g.property.1 g.property.2⟩ hne
  refine ⟨X, htwo, f, g, hne, ?_⟩
  intro h
  rcases at_most_two_kodaira K bases X f g h with hfg | hfh | hgh
  · exact False.elim (hne hfg)
  · exact Or.inl (Fibration.equivalent_symm hfh)
  · exact Or.inr (Fibration.equivalent_symm hgh)

end Paper27.Geometry
