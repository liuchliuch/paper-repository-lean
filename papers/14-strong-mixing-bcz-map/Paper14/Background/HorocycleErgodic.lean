import Paper14.Background.MautnerSL2
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Measure.Haar.Quotient

open MeasureTheory Filter Set Topology
open scoped ENNReal Matrix
open Matrix
namespace Paper14.Background
noncomputable section

instance : MeasurableSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin 2 → Fin 2 → ℝ))
instance : BorelSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
  inferInstanceAs (BorelSpace (Fin 2 → Fin 2 → ℝ))

instance : MeasurableSpace SL2R := Subtype.instMeasurableSpace
instance : BorelSpace SL2R :=
  inferInstanceAs (BorelSpace {g : Matrix (Fin 2) (Fin 2) ℝ // g.det=1})

def slKoopmanHom : SL2R →* SL2Rᵈᵐᵃ where
  toFun g := DomMulAct.mk g⁻¹
  map_one' := by simp
  map_mul' g h := by simp

lemma continuous_slKoopmanHom : Continuous slKoopmanHom :=
  DomMulAct.continuous_mk.comp continuous_inv

section
variable {X : Type*} [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
  [MulAction SL2R X] [ContinuousSMul SL2R X] [MeasurableSMul SL2R X] {μ : Measure X}
  [IsFiniteMeasure μ] [μ.InnerRegularCompactLTTop] [SMulInvariantMeasure SL2R X μ]

/-- On a finite invariant measure space, invariance under the upper horocycle
subgroup entails invariance under every element of SL₂(ℝ). -/
theorem slUpper_ae_invariant_all {s : Set X} (hs : MeasurableSet s)
    (hU : ∀ t : ℝ, (fun x : X => slUpper t • x) ⁻¹' s =ᵐ[μ] s) :
    ∀ g : SL2R, (fun x : X => g • x) ⁻¹' s =ᵐ[μ] s := by
  letI : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let v : Lp ℝ 1 μ := indicatorConstLp 1 hs (measure_ne_top μ s) 1
  letI : MulAction SL2R (Lp ℝ 1 μ) := MulAction.compHom _ slKoopmanHom
  have hIso : ∀ g : SL2R, Isometry (fun v : Lp ℝ 1 μ => g • v) := by
    intro g
    exact isometry_smul (Lp ℝ 1 μ) (slKoopmanHom g)
  have hCont : Continuous (fun g : SL2R => g • v) := by
    change Continuous (fun g : SL2R => slKoopmanHom g • v)
    exact continuous_slKoopmanHom.smul continuous_const
  have hUv : ∀ t : ℝ, slUpper t • v = v := by
    intro t
    change DomMulAct.mk ((slUpper t)⁻¹) • v = v
    rw [slUpper_inv]
    change DomMulAct.mk (slUpper (-t)) • indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ) = _
    rw [DomMulAct.mk_smul_indicatorConstLp]
    exact (indicatorConstLp_inj _ _ hs _ (one_ne_zero : (1 : ℝ) ≠ 0)).mpr (hU (-t))
  have hfull := sl_upper_fixed_all hIso v hCont hUv
  intro g
  have hfix := hfull g⁻¹
  change DomMulAct.mk (g⁻¹)⁻¹ • v = v at hfix
  rw [inv_inv] at hfix
  change DomMulAct.mk g • indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ) = _ at hfix
  rw [DomMulAct.mk_smul_indicatorConstLp] at hfix
  exact (indicatorConstLp_inj _ _ hs _ (one_ne_zero : (1 : ℝ) ≠ 0)).mp hfix

/-- On a finite invariant measure space, invariance under the lower horocycle
subgroup entails invariance under every element of SL₂(ℝ). -/
theorem slLower_ae_invariant_all {s : Set X} (hs : MeasurableSet s)
    (hU : ∀ t : ℝ, (fun x : X => slLower t • x) ⁻¹' s =ᵐ[μ] s) :
    ∀ g : SL2R, (fun x : X => g • x) ⁻¹' s =ᵐ[μ] s := by
  letI : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let v : Lp ℝ 1 μ := indicatorConstLp 1 hs (measure_ne_top μ s) 1
  letI : MulAction SL2R (Lp ℝ 1 μ) := MulAction.compHom _ slKoopmanHom
  have hIso : ∀ g : SL2R, Isometry (fun v : Lp ℝ 1 μ => g • v) := by
    intro g
    exact isometry_smul (Lp ℝ 1 μ) (slKoopmanHom g)
  have hCont : Continuous (fun g : SL2R => g • v) := by
    change Continuous (fun g : SL2R => slKoopmanHom g • v)
    exact continuous_slKoopmanHom.smul continuous_const
  have hUv : ∀ t : ℝ, slLower t • v = v := by
    intro t
    change DomMulAct.mk ((slLower t)⁻¹) • v = v
    rw [slLower_inv]
    change DomMulAct.mk (slLower (-t)) • indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ) = _
    rw [DomMulAct.mk_smul_indicatorConstLp]
    exact (indicatorConstLp_inj _ _ hs _ (one_ne_zero : (1 : ℝ) ≠ 0)).mpr (hU (-t))
  have hfull := sl_lower_fixed_all hIso v hCont hUv
  intro g
  have hfix := hfull g⁻¹
  change DomMulAct.mk (g⁻¹)⁻¹ • v = v at hfix
  rw [inv_inv] at hfix
  change DomMulAct.mk g • indicatorConstLp 1 hs (measure_ne_top μ s) (1 : ℝ) = _ at hfix
  rw [DomMulAct.mk_smul_indicatorConstLp] at hfix
  exact (indicatorConstLp_inj _ _ hs _ (one_ne_zero : (1 : ℝ) ≠ 0)).mp hfix

/-- Mautner upgrades ergodicity of the whole group action to the
horocycle subgroup on every finite invariant measure space. -/
theorem slUpper_ae_invariant_const [ErgodicSMul SL2R X μ]
    {s : Set X} (hs : MeasurableSet s)
    (hU : ∀ t : ℝ, (fun x : X => slUpper t • x) ⁻¹' s =ᵐ[μ] s) :
    EventuallyConst s (ae μ) :=
  aeconst_of_forall_preimage_smul_ae_eq SL2R hs.nullMeasurableSet
    (slUpper_ae_invariant_all hs hU)

end
end
end Paper14.Background
