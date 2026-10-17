import Paper28.CurrentChainComplex
import Paper28.ConcreteHomologyClasses

/-! The algebraic composition of the standard comparison maps. The
current-integration map on simplicial homology is injective because the
two canonical Lipschitz comparison maps and simplicial--singular comparison
are isomorphisms. No prescribed filling is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory
universe v

theorem integration_homology_mono
    {P L C S : ChainComplex AddCommGrpCat.{v} ℕ}
    (toLip : P ⟶ L) (lipToCurrent : L ⟶ C) (lipToSingular : L ⟶ S)
    (toSingular : P ⟶ S) (integration : P ⟶ C)
    (hSingular : toLip ≫ lipToSingular = toSingular)
    (hCurrent : toLip ≫ lipToCurrent = integration)
    (k : ℕ)
    [IsIso (HomologicalComplex.homologyMap lipToCurrent k)]
    [IsIso (HomologicalComplex.homologyMap toSingular k)] :
    Mono (HomologicalComplex.homologyMap integration k) := by
  have hSing : HomologicalComplex.homologyMap toLip k ≫
      HomologicalComplex.homologyMap lipToSingular k = HomologicalComplex.homologyMap toSingular k := by
    rw [← HomologicalComplex.homologyMap_comp,hSingular]
  haveI : Mono (HomologicalComplex.homologyMap toLip k ≫ HomologicalComplex.homologyMap lipToSingular k) := by
    rw [hSing]
    infer_instance
  haveI : Mono (HomologicalComplex.homologyMap toLip k) := mono_of_mono _ (HomologicalComplex.homologyMap lipToSingular k)
  rw [← hCurrent,HomologicalComplex.homologyMap_comp]
  infer_instance

theorem short_integration_homology_mono
    {P L C S : ShortComplex AddCommGrpCat.{v}}
    (toLip : P ⟶ L) (lipToCurrent : L ⟶ C) (lipToSingular : L ⟶ S)
    (toSingular : P ⟶ S) (integration : P ⟶ C)
    (hSingular : toLip ≫ lipToSingular = toSingular)
    (hCurrent : toLip ≫ lipToCurrent = integration)
    [IsIso (ShortComplex.homologyMap lipToCurrent)]
    [IsIso (ShortComplex.homologyMap toSingular)] :
    Mono (ShortComplex.homologyMap integration) := by
  have hSing : ShortComplex.homologyMap toLip ≫ ShortComplex.homologyMap lipToSingular =
      ShortComplex.homologyMap toSingular := by rw [← ShortComplex.homologyMap_comp,hSingular]
  haveI : Mono (ShortComplex.homologyMap toLip ≫ ShortComplex.homologyMap lipToSingular) := by
    rw [hSing]
    infer_instance
  haveI : Mono (ShortComplex.homologyMap toLip) := mono_of_mono _ (ShortComplex.homologyMap lipToSingular)
  rw [← hCurrent,ShortComplex.homologyMap_comp]
  infer_instance

/-- The paper-owned prescribed filling step: comparison theorems are used
only for their canonical homology isomorphisms. An exact current boundary
is then pulled back to an exact integer simplicial chain boundary. -/
theorem prescribed_filling_from_comparison_maps
    {P L C S : ShortComplex AddCommGrpCat.{v}}
    (toLip : P ⟶ L) (lipToCurrent : L ⟶ C) (lipToSingular : L ⟶ S)
    (toSingular : P ⟶ S) (integration : P ⟶ C)
    (hSingular : toLip ≫ lipToSingular = toSingular)
    (hCurrent : toLip ≫ lipToCurrent = integration)
    [IsIso (ShortComplex.homologyMap lipToCurrent)]
    [IsIso (ShortComplex.homologyMap toSingular)]
    (z : P.X₂) (hz : P.g z = 0) (hBounds : ∃ D : C.X₁, C.f D = integration.τ₂ z) :
    ∃ Q : P.X₁, P.f Q = z := by
  haveI := short_integration_homology_mono toLip lipToCurrent lipToSingular toSingular integration hSingular hCurrent
  exact prescribed_filling_of_homology_injective integration
    ((AddCommGrpCat.mono_iff_injective _).mp inferInstance) z hz hBounds

end Paper28
