import Paper14.Background.HorocycleErgodic
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Inv

open Matrix MeasureTheory Measure Filter Set Topology
open scoped Matrix ENNReal
namespace Paper14.Background
noncomputable section

abbrev SL2Coordinates := Fin 3 → ℝ

def slChart (z : SL2Coordinates) : SL2R :=
  if hz : z 0≠0 then
    ⟨!![z 0,z 1; -z 2*z 0,(z 0)⁻¹-z 2*z 1],by
      simp only [Matrix.det_fin_two]
      change z 0*((z 0)⁻¹-z 2*z 1)-z 1*(-z 2*z 0)=1
      field_simp [hz]
      ring⟩
  else 1

def slCoordinates (g : SL2R) : SL2Coordinates := ![g 0 0,g 0 1,-g 1 0/g 0 0]

lemma slCoordinates_chart {z : SL2Coordinates} (hz : z 0≠0) : slCoordinates (slChart z)=z := by
  ext i
  fin_cases i <;> simp [slCoordinates,slChart,hz]

lemma slChart_coordinates {g : SL2R} (hg : g 0 0≠0) : slChart (slCoordinates g)=g := by
  have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using g.property
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slChart,slCoordinates,hg]
  all_goals field_simp [hg]
  all_goals nlinarith

lemma measurable_slEntry (i j : Fin 2) : Measurable (fun g : SL2R => g i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_subtype_coe)

lemma measurable_slCoordinates : Measurable slCoordinates := by
  apply measurable_pi_lambda
  intro i
  fin_cases i
  · simpa [slCoordinates] using measurable_slEntry 0 0
  · simpa [slCoordinates] using measurable_slEntry 0 1
  · simpa [slCoordinates] using (measurable_slEntry 1 0).neg.div (measurable_slEntry 0 0)

lemma measurable_slChart : Measurable slChart := by
  suffices hm : Measurable (fun z => (slChart z : Matrix (Fin 2) (Fin 2) ℝ)) by
    exact hm.subtype_mk
  have heq : (fun z => (slChart z : Matrix (Fin 2) (Fin 2) ℝ)) =
      (fun z : SL2Coordinates => if z 0≠0 then !![z 0,z 1; -z 2*z 0,(z 0)⁻¹-z 2*z 1] else 1) := by
    funext z
    by_cases hz : z 0≠0 <;> simp [slChart,hz]
  rw [heq]
  apply Measurable.ite
  · exact (measurableSet_eq_fun (measurable_pi_apply 0) measurable_const).compl
  · apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  · exact measurable_const

/-- Left multiplication in the flat (a,b,t) coordinates on the big cell. -/
def slLeftCoordinates (g : SL2R) (z : SL2Coordinates) : SL2Coordinates :=
  ![z 0*(g 0 0-g 0 1*z 2),
    z 1*(g 0 0-g 0 1*z 2)+g 0 1/z 0,
    (g 1 1*z 2-g 1 0)/(g 0 0-g 0 1*z 2)]

/-- Right multiplication in the same chart. -/
def slRightCoordinates (g : SL2R) (z : SL2Coordinates) : SL2Coordinates :=
  ![z 0*g 0 0+z 1*g 1 0,z 0*g 0 1+z 1*g 1 1,
    z 2-g 1 0/(z 0*(z 0*g 0 0+z 1*g 1 0))]

lemma slCoordinates_left {z : SL2Coordinates} (hz : z 0≠0) (g : SL2R)
    (hg : g 0 0-g 0 1*z 2≠0) :
    slCoordinates (g*slChart z)=slLeftCoordinates g z := by
  ext i
  fin_cases i
  all_goals dsimp [slCoordinates,slLeftCoordinates]
  all_goals simp only [slChart,dif_pos hz,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals dsimp
  all_goals field_simp [hz,hg]
  all_goals ring

lemma slCoordinates_right {z : SL2Coordinates} (hz : z 0≠0) (g : SL2R)
    (hg : z 0*g 0 0+z 1*g 1 0≠0) :
    slCoordinates (slChart z*g)=slRightCoordinates g z := by
  ext i
  fin_cases i
  all_goals dsimp [slCoordinates,slRightCoordinates]
  all_goals simp only [slChart,dif_pos hz,Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals dsimp
  all_goals field_simp [hz,hg]
  all_goals ring

lemma hasFDerivAt_inv_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x : E} (hf : HasFDerivAt f f' x) (hx : f x≠0) :
    HasFDerivAt (fun y => (f y)⁻¹) (-(f x^2)⁻¹ • f') x := by
  convert (hasFDerivAt_inv hx).comp x hf using 1
  ext u
  simp [mul_comm]

abbrev slCoordProj (i : Fin 3) : SL2Coordinates →L[ℝ] ℝ := ContinuousLinearMap.proj i

def slLeftDerivative (g : SL2R) (z : SL2Coordinates) : SL2Coordinates →L[ℝ] SL2Coordinates :=
  let H := g 0 0-g 0 1*z 2
  let dH := -(g 0 1) • slCoordProj 2
  ContinuousLinearMap.pi ![
    z 0 • dH + H • slCoordProj 0,
    (z 1 • dH + H • slCoordProj 1) + g 0 1 • (-(z 0^2)⁻¹ • slCoordProj 0),
    (g 1 1*z 2-g 1 0) • (-(H^2)⁻¹ • dH) + H⁻¹ • (g 1 1 • slCoordProj 2)]

lemma slLeft_hasFDerivAt (g : SL2R) {z : SL2Coordinates} (hz : z 0≠0)
    (hg : g 0 0-g 0 1*z 2≠0) :
    HasFDerivAt (slLeftCoordinates g) (slLeftDerivative g z) z := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) 0 z
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) 1 z
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) 2 z
  have hH : HasFDerivAt (fun y : SL2Coordinates => g 0 0-g 0 1*y 2)
      (-(g 0 1) • slCoordProj 2) z := by
    convert (hasFDerivAt_const (g 0 0) z).sub (h2.const_mul (g 0 1)) using 1 <;> ext u <;> simp [slCoordProj] <;> ring
  have hN : HasFDerivAt (fun y : SL2Coordinates => g 1 1*y 2-g 1 0)
      (g 1 1 • slCoordProj 2) z := by
    simpa using (h2.const_mul (g 1 1)).sub_const (g 1 0)
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · simpa [slLeftCoordinates,slLeftDerivative,slCoordProj,neg_smul,smul_neg] using h0.fun_mul hH
  · convert (h1.fun_mul hH).add ((hasFDerivAt_inv_real h0 hz).const_mul (g 0 1)) using 1 <;>
      ext u <;> simp [slLeftCoordinates,slLeftDerivative,slCoordProj,div_eq_mul_inv] <;> ring
  · convert hN.fun_mul (hasFDerivAt_inv_real hH hg) using 1 <;>
      ext u <;> simp [slLeftCoordinates,slLeftDerivative,slCoordProj,div_eq_mul_inv] <;> ring

lemma slLeftDerivative_det (g : SL2R) {z : SL2Coordinates}
    (hg : g 0 0-g 0 1*z 2≠0) : (slLeftDerivative g z).toLinearMap.det=1 := by
  have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using g.property
  rw [← LinearMap.det_toMatrix',Matrix.det_fin_three]
  simp [LinearMap.toMatrix'_apply,slLeftDerivative,slCoordProj]
  field_simp [hg]
  nlinarith [hd]

def slRightDerivative (g : SL2R) (z : SL2Coordinates) : SL2Coordinates →L[ℝ] SL2Coordinates :=
  let H := z 0*g 0 0+z 1*g 1 0
  let dH := g 0 0 • slCoordProj 0+g 1 0 • slCoordProj 1
  ContinuousLinearMap.pi ![
    dH,
    g 0 1 • slCoordProj 0+g 1 1 • slCoordProj 1,
    slCoordProj 2-g 1 0 • (-((z 0*H)^2)⁻¹ • (z 0 • dH + H • slCoordProj 0))]

lemma slRight_hasFDerivAt (g : SL2R) {z : SL2Coordinates} (hz : z 0≠0)
    (hg : z 0*g 0 0+z 1*g 1 0≠0) :
    HasFDerivAt (slRightCoordinates g) (slRightDerivative g z) z := by
  have h0 := hasFDerivAt_apply (𝕜 := ℝ) 0 z
  have h1 := hasFDerivAt_apply (𝕜 := ℝ) 1 z
  have h2 := hasFDerivAt_apply (𝕜 := ℝ) 2 z
  have hH := (h0.const_mul (g 0 0)).add (h1.const_mul (g 1 0))
  have hJ := (h0.const_mul (g 0 1)).add (h1.const_mul (g 1 1))
  apply hasFDerivAt_pi'.mpr
  intro i
  fin_cases i
  · simpa [slRightCoordinates,slRightDerivative,slCoordProj,mul_comm] using hH
  · simpa [slRightCoordinates,slRightDerivative,slCoordProj,mul_comm] using hJ
  · simpa [slRightCoordinates,slRightDerivative,slCoordProj,div_eq_mul_inv,mul_comm,neg_smul,smul_neg] using
      h2.sub ((hasFDerivAt_inv_real (h0.fun_mul hH) (mul_ne_zero hz (by simpa [mul_comm] using hg))).const_mul (g 1 0))

lemma slRightDerivative_det (g : SL2R) (z : SL2Coordinates) :
    (slRightDerivative g z).toLinearMap.det=1 := by
  have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using g.property
  rw [← LinearMap.det_toMatrix',Matrix.det_fin_three]
  simpa [LinearMap.toMatrix'_apply,slRightDerivative,slCoordProj,mul_comm] using hd

end
end Paper14.Background
