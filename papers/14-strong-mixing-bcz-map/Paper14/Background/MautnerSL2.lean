import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Matrix Filter Topology
open scoped Matrix MatrixGroups
namespace Paper14.Background
noncomputable section

abbrev SL2R := Matrix.SpecialLinearGroup (Fin 2) ℝ

def slUpper (t : ℝ) : SL2R := ⟨!![1,t;0,1],by simp [Matrix.det_fin_two]⟩
def slLower (s : ℝ) : SL2R := ⟨!![1,0;s,1],by simp [Matrix.det_fin_two]⟩
def slDiagonal (r : ℝ) (hr : r≠0) : SL2R := ⟨!![r,0;0,r⁻¹],by simp [Matrix.det_fin_two,hr]⟩

lemma slUpper_zero : slUpper 0=1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [slUpper,Matrix.SpecialLinearGroup.coe_one]

lemma slLower_zero : slLower 0=1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [slLower,Matrix.SpecialLinearGroup.coe_one]

lemma continuous_slUpper : Continuous slUpper := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

lemma continuous_slLower : Continuous slLower := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

lemma sl_bruhat_bridge {t r : ℝ} (ht : t≠0) (hr : r≠0) :
    slUpper t*slLower ((r-1)/t)=slLower (((r-1)/t)/r)*slDiagonal r hr*slUpper (t/r) := by
  apply Subtype.ext
  change !![1,t;0,1]*!![1,0;(r-1)/t,1]=
    (!![1,0;((r-1)/t)/r,1]*!![r,0;0,r⁻¹])*!![1,t/r;0,1]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp [ht,hr] <;> ring

lemma sl_diagonal_lower {r : ℝ} (hr : r≠0) (s : ℝ) :
    slDiagonal r hr*slLower s=slLower (s/r^2)*slDiagonal r hr := by
  apply Subtype.ext
  change !![r,0;0,r⁻¹]*!![1,0;s,1]=!![1,0;s/r^2,1]*!![r,0;0,r⁻¹]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> field_simp [hr] <;> ring

lemma sl_gauss_factorization (g : SL2R) (ha : g 0 0≠0) :
    g=slLower (g 1 0/g 0 0)*slDiagonal (g 0 0) ha*slUpper (g 0 1/g 0 0) := by
  have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by simpa only [Matrix.det_fin_two] using g.property
  apply Subtype.ext
  change (g : Matrix (Fin 2) (Fin 2) ℝ)=
    (!![1,0;g 1 0/g 0 0,1]*!![g 0 0,0;0,(g 0 0)⁻¹])*!![1,g 0 1/g 0 0;0,1]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  all_goals field_simp [ha]
  all_goals nlinarith



lemma slUpper_inv (t : ℝ) : (slUpper t)⁻¹=slUpper (-t) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (!![1,t;0,1]*!![1,-t;0,1] : Matrix (Fin 2) (Fin 2) ℝ)=1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma slLower_inv (t : ℝ) : (slLower t)⁻¹=slLower (-t) := by
  apply inv_eq_of_mul_eq_one_right
  apply Subtype.ext
  change (!![1,0;t,1]*!![1,0;-t,1] : Matrix (Fin 2) (Fin 2) ℝ)=1
  ext i j
  fin_cases i <;> fin_cases j <;> simp

def slWeyl : SL2R := ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩

lemma sl_upper_weyl (t : ℝ) : slUpper t*slWeyl=slWeyl*slLower (-t) := by
  apply Subtype.ext
  change (!![1,t;0,1]*!![0,-1;1,0] : Matrix (Fin 2) (Fin 2) ℝ)=
    !![0,-1;1,0]*!![1,0;-t,1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

section IsometricAction
variable {X : Type*} [MetricSpace X] [MulAction SL2R X]
variable (hiso : ∀ g : SL2R, Isometry (fun v : X => g • v))
variable (x : X) (hcont : Continuous (fun g : SL2R => g • x))
variable (hU : ∀ t : ℝ, slUpper t • x = x)
include hiso hcont hU

lemma sl_upper_fixed_diagonal {r : ℝ} (hr : r ≠ 0) :
    slDiagonal r hr • x = x := by
  let t : ℕ → ℝ := fun n => (n : ℝ) + 1
  have ht : Tendsto t atTop atTop := by
    simpa [t, Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have ht0 : ∀ n, t n ≠ 0 := fun n => ne_of_gt (by dsimp [t]; positivity)
  let s : ℕ → ℝ := fun n => (r-1)/t n
  have hs : Tendsto s atTop (𝓝 0) := tendsto_const_nhds.div_atTop ht
  have hsr : Tendsto (fun n => s n/r) atTop (𝓝 0) := by
    simpa using hs.div_const r
  have hLs : Tendsto (fun n => slLower (s n)) atTop (𝓝 1) := by
    simpa [slLower_zero] using continuous_slLower.continuousAt.tendsto.comp hs
  have hLsr : Tendsto (fun n => slLower (s n/r)*slDiagonal r hr)
      atTop (𝓝 (slDiagonal r hr)) := by
    simpa [slLower_zero] using
      ((continuous_slLower.continuousAt.tendsto.comp hsr).mul_const (slDiagonal r hr))
  have hleft : Tendsto (fun n => dist (slLower (s n) • x) x) atTop (𝓝 0) := by
    simpa using (hcont.tendsto 1 |>.comp hLs).dist (tendsto_const_nhds (x := x))
  have hright : Tendsto (fun n => dist ((slLower (s n/r)*slDiagonal r hr) • x) x)
      atTop (𝓝 (dist (slDiagonal r hr • x) x)) :=
    (hcont.tendsto (slDiagonal r hr) |>.comp hLsr).dist tendsto_const_nhds
  have heq : ∀ n, dist ((slLower (s n/r)*slDiagonal r hr) • x) x =
      dist (slLower (s n) • x) x := by
    intro n
    calc
      dist ((slLower (s n/r)*slDiagonal r hr) • x) x =
          dist ((slLower (s n/r)*slDiagonal r hr*slUpper (t n/r)) • x) x := by
        simp only [MulAction.mul_smul, hU]
      _ = dist ((slUpper (t n)*slLower (s n)) • x) x := by
        rw [← sl_bruhat_bridge (ht0 n) hr]
      _ = dist (slLower (s n) • x) x := by
        rw [MulAction.mul_smul]
        calc
          dist (slUpper (t n) • (slLower (s n) • x)) x =
              dist (slUpper (t n) • (slLower (s n) • x)) (slUpper (t n) • x) := by
            rw [hU]
          _ = _ := (hiso (slUpper (t n))).dist_eq _ _
  have hz : dist (slDiagonal r hr • x) x = 0 :=
    tendsto_nhds_unique hright (hleft.congr fun n => (heq n).symm)
  exact dist_eq_zero.mp hz

lemma sl_upper_fixed_lower (s : ℝ) : slLower s • x = x := by
  let t : ℕ → ℝ := fun n => (n : ℝ) + 1
  have ht : Tendsto t atTop atTop := by
    simpa [t, Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have ht0 : ∀ n, t n ≠ 0 := fun n => ne_of_gt (by dsimp [t]; positivity)
  have hs : Tendsto (fun n => s/(t n)^2) atTop (𝓝 0) := by
    have hi := tendsto_inv_atTop_zero.comp ht
    simpa [div_eq_mul_inv, inv_pow] using tendsto_const_nhds.mul (hi.pow 2)
  have hlim : Tendsto (fun n => dist (slLower (s/(t n)^2) • x) x) atTop (𝓝 0) := by
    have hL : Tendsto (fun n => slLower (s/(t n)^2)) atTop (𝓝 1) := by
      simpa [slLower_zero] using continuous_slLower.continuousAt.tendsto.comp hs
    simpa using (hcont.tendsto 1 |>.comp hL).dist (tendsto_const_nhds (x := x))
  have heq : ∀ n, dist (slLower (s/(t n)^2) • x) x = dist (slLower s • x) x := by
    intro n
    have hA := sl_upper_fixed_diagonal hiso x hcont hU (ht0 n)
    calc
      dist (slLower (s/(t n)^2) • x) x =
          dist ((slLower (s/(t n)^2)*slDiagonal (t n) (ht0 n)) • x) x := by
        rw [MulAction.mul_smul, hA]
      _ = dist ((slDiagonal (t n) (ht0 n)*slLower s) • x) x := by
        rw [sl_diagonal_lower]
      _ = dist (slLower s • x) x := by
        rw [MulAction.mul_smul]
        calc
          dist (slDiagonal (t n) (ht0 n) • (slLower s • x)) x =
              dist (slDiagonal (t n) (ht0 n) • (slLower s • x))
                (slDiagonal (t n) (ht0 n) • x) := by rw [hA]
          _ = _ := (hiso (slDiagonal (t n) (ht0 n))).dist_eq _ _
  exact dist_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds (hlim.congr heq))

/-- Mautner's phenomenon for continuous isometric actions of SL₂(ℝ). -/
theorem sl_upper_fixed_all : ∀ g : SL2R, g • x = x := by
  have hgood : ∀ g : SL2R, g 0 0 ≠ 0 → g • x = x := by
    intro g hg
    rw [sl_gauss_factorization g hg, MulAction.mul_smul, MulAction.mul_smul, hU,
      sl_upper_fixed_diagonal hiso x hcont hU hg,
      sl_upper_fixed_lower hiso x hcont hU]
  intro g
  by_cases hg : g 0 0 ≠ 0
  · exact hgood g hg
  · have hz : g 0 0 = 0 := not_ne_iff.mp hg
    have h10 : g 1 0 ≠ 0 := by
      have hd : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
        simpa only [Matrix.det_fin_two] using g.property
      intro h
      simp [hz,h] at hd
    have hm : (slUpper 1*g) 0 0 ≠ 0 := by
      simpa [Matrix.SpecialLinearGroup.coe_mul,slUpper,Matrix.mul_fin_two,Matrix.vecMul,Fin.sum_univ_two,Matrix.vecHead,Matrix.vecTail,hz] using h10
    have hfix := hgood (slUpper 1*g) hm
    apply (hiso (slUpper 1)).injective
    simpa only [MulAction.mul_smul,hU] using hfix


omit hU in
/-- The lower horocycle subgroup has the same Mautner property. -/
theorem sl_lower_fixed_all (hL : ∀ t : ℝ,slLower t • x=x) : ∀ g : SL2R,g • x=x := by
  let y := slWeyl • x
  have hCy : Continuous (fun g : SL2R => g • y) := by
    simpa only [y,← MulAction.mul_smul] using hcont.comp (continuous_id.mul continuous_const)
  have hUy : ∀ t : ℝ,slUpper t • y=y := by
    intro t
    dsimp [y]
    rw [← MulAction.mul_smul,sl_upper_weyl,MulAction.mul_smul,hL]
  have hall := sl_upper_fixed_all hiso y hCy hUy
  intro g
  apply (hiso slWeyl).injective
  have hfix := hall (slWeyl*g*slWeyl⁻¹)
  simpa only [y,MulAction.mul_smul,inv_smul_smul] using hfix

end IsometricAction
end
end Paper14.Background
