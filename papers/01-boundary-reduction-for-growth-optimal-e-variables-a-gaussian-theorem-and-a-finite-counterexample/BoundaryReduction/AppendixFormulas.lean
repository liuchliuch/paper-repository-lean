import BoundaryReduction.NinePointTheorem
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
open Real Set BigOperators
open scoped Classical
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
namespace BoundaryReduction.NinePoint
noncomputable def Za (t : ℝ) : ℝ := ε+w*(2*cosh t+2+4*cosh (ρ*t))
noncomputable def Zd (t : ℝ) : ℝ := ε+w*(4*cosh t+2*cosh (2*ρ*t)+2)
lemma appendix_A5 (t : ℝ) (i : Fin 4) : Z (t • axisNormal i) = Za t := by
  fin_cases i <;> simp [Z,un,dot,coord,p0,axisNormal,Za,cosh_eq,
    Fin.sum_univ_succ,Fin.succ,smul_eq_mul,mul_comm,mul_left_comm,mul_assoc] <;> ring
lemma appendix_A6 (t : ℝ) (i : Fin 4) : Z (t • diagNormal i) = Zd t := by
  fin_cases i <;> simp [Z,un,dot,coord,p0,diagNormal,Zd,cosh_eq,
    Fin.sum_univ_succ,Fin.succ,smul_eq_mul,mul_comm,mul_left_comm,mul_assoc,
    show (t*ρ+t*ρ) = 2*ρ*t by ring, show (-t*ρ+-t*ρ) = -(2*ρ*t) by ring,
    show (-t*ρ+t*ρ) = 0 by ring, show (t*ρ+-t*ρ) = 0 by ring] <;> ring
noncomputable def q0 (t : ℝ) := ε/2*(1/Za t+1/Zd t)
noncomputable def qa (t : ℝ) := w/8*((2*cosh t+2)/Za t+(4*cosh t)/Zd t)
noncomputable def qd (t : ℝ) := w/8*((4*cosh (ρ*t))/Za t+(2*cosh (2*ρ*t)+2)/Zd t)
lemma comp_Z (t : ℝ) (k : Fin 8) : Z (t • compNormal k) = if k.val < 4 then Za t else Zd t := by
  fin_cases k
  · change Z (t • axisNormal 0) = Za t
    exact appendix_A5 t 0
  · change Z (t • axisNormal 1) = Za t
    exact appendix_A5 t 1
  · change Z (t • axisNormal 2) = Za t
    exact appendix_A5 t 2
  · change Z (t • axisNormal 3) = Za t
    exact appendix_A5 t 3
  · change Z (t • diagNormal 0) = Zd t
    exact appendix_A6 t 0
  · change Z (t • diagNormal 1) = Zd t
    exact appendix_A6 t 1
  · change Z (t • diagNormal 2) = Zd t
    exact appendix_A6 t 2
  · change Z (t • diagNormal 3) = Zd t
    exact appendix_A6 t 3
lemma appendix_A7 (t : ℝ) : Qt t 0 = q0 t := by
  unfold Qt compPt pt
  simp_rw [comp_Z]
  simp [Qt,compPt,pt,un,comp_Z,dot,coord,p0,q0,Fin.sum_univ_succ,Fin.succ]
  ring
lemma appendix_A8 (t : ℝ) (i : Fin 4) : Qt t (axisTarget i) = qa t := by
  unfold Qt compPt pt
  simp_rw [comp_Z]
  fin_cases i <;> simp [Qt,compPt,pt,un,comp_Z,compNormal,dot,coord,p0,axisTarget,axisNormal,diagNormal,qa,cosh_eq,
    Fin.sum_univ_succ,Fin.succ,smul_eq_mul,mul_comm,mul_left_comm,mul_assoc] <;> ring
lemma appendix_A9 (t : ℝ) (i : Fin 4) : Qt t (diagTarget i) = qd t := by
  unfold Qt compPt pt
  simp_rw [comp_Z]
  fin_cases i <;> simp [Qt,compPt,pt,un,comp_Z,compNormal,dot,coord,p0,diagTarget,axisNormal,diagNormal,qd,cosh_eq,
    Fin.sum_univ_succ,Fin.succ,smul_eq_mul,mul_comm,mul_left_comm,mul_assoc,
    show (t*ρ+t*ρ) = 2*ρ*t by ring, show (-t*ρ+-t*ρ) = -(2*ρ*t) by ring,
    show (-t*ρ+t*ρ) = 0 by ring, show (t*ρ+-t*ρ) = 0 by ring] <;> ring
lemma Qt_group_mass (t : ℝ) (y : Fin 9) : Qt t y =
    if y.val = 0 then q0 t else if y.val ≤ 4 then qa t else qd t := by
  fin_cases y
  · exact appendix_A7 t
  · convert appendix_A8 t 0 using 1 <;> norm_num [axisTarget,diagTarget,Fin.ext_iff]
  · convert appendix_A8 t 1 using 1 <;> norm_num [axisTarget,diagTarget,Fin.ext_iff]
  · convert appendix_A8 t 2 using 1 <;> norm_num [axisTarget,diagTarget,Fin.ext_iff]
  · convert appendix_A8 t 3 using 1 <;> norm_num [axisTarget,diagTarget,Fin.ext_iff]
  · convert appendix_A9 t 0 using 1 <;> norm_num [axisTarget,diagTarget,Fin.ext_iff]
  · convert appendix_A9 t 1 using 1 <;> norm_num [axisTarget,diagTarget,Fin.ext_iff]
  · convert appendix_A9 t 2 using 1 <;> norm_num [axisTarget,diagTarget,Fin.ext_iff]
  · convert appendix_A9 t 3 using 1 <;> norm_num [axisTarget,diagTarget,Fin.ext_iff]
lemma appendix_A10 (t : ℝ) : FinProb.klPos (mixtureProb t) baseProb =
    q0 t*log (q0 t/ε)+4*qa t*log (qa t/w)+4*qd t*log (qd t/w) := by
  simp only [FinProb.klPos,mixtureProb,baseProb]
  simp_rw [Qt_group_mass]
  norm_num [Fin.sum_univ_succ,Fin.succ,p0]
  ring
noncomputable def ma (t : ℝ) := w*(2*sinh t+4*ρ*sinh (ρ*t))/Za t
noncomputable def mdCoord (t : ℝ) := w*(2*sinh t+2*ρ*sinh (2*ρ*t))/Zd t
lemma axis_mean_vector (t : ℝ) : esMean (pt (t • axisNormal 0)) = toES (ma t,0) := by
  unfold esMean
  simp_rw [pt,appendix_A5]
  ext i
  fin_cases i <;> simp [un,dot,coord,p0,axisNormal,ma,sinh_eq,toES,
    Fin.sum_univ_succ,Fin.succ,smul_eq_mul,mul_comm,mul_left_comm,mul_assoc] <;> ring
lemma diag_mean_vector (t : ℝ) : esMean (pt (t • diagNormal 0)) = toES (mdCoord t,mdCoord t) := by
  unfold esMean
  simp_rw [pt,appendix_A6]
  ext i
  fin_cases i <;> simp [un,dot,coord,p0,diagNormal,mdCoord,sinh_eq,toES,
    Fin.sum_univ_succ,Fin.succ,smul_eq_mul,mul_comm,mul_left_comm,mul_assoc,
    show (t*ρ+t*ρ) = 2*ρ*t by ring, show (-t*ρ+-t*ρ) = -(2*ρ*t) by ring,
    show (-t*ρ+t*ρ) = 0 by ring, show (t*ρ+-t*ρ) = 0 by ring] <;> ring
lemma ma_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ ma t := by
  have hZ : 0 < Za t := by rw [← appendix_A5 t 0]; exact Z_pos _
  have hs : 0 ≤ sinh t := sinh_nonneg_iff.mpr ht
  have hsr : 0 ≤ sinh (ρ*t) := sinh_nonneg_iff.mpr (mul_nonneg ρ_pos.le ht)
  have hw := w_pos
  have hr := ρ_pos
  unfold ma
  positivity
lemma mdCoord_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ mdCoord t := by
  have hZ : 0 < Zd t := by rw [← appendix_A6 t 0]; exact Z_pos _
  have hs : 0 ≤ sinh t := sinh_nonneg_iff.mpr ht
  have hsr : 0 ≤ sinh (2*ρ*t) := sinh_nonneg_iff.mpr (mul_nonneg (mul_nonneg (by norm_num) ρ_pos.le) ht)
  have hw := w_pos
  have hr := ρ_pos
  unfold mdCoord
  positivity
lemma appendix_A11 (t : ℝ) (ht : 0 ≤ t) : ‖esMean (pt (t • axisNormal 0))‖ =
    w*(2*sinh t+4*ρ*sinh (ρ*t))/Za t := by
  rw [axis_mean_vector,norm_toES]
  simp only [euclNorm,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,add_zero,sqrt_sq_eq_abs,
    abs_of_nonneg (ma_nonneg t ht)]
  rfl
lemma appendix_A12 (t : ℝ) (ht : 0 ≤ t) : ‖esMean (pt (t • diagNormal 0))‖ =
    sqrt 2*w*(2*sinh t+2*ρ*sinh (2*ρ*t))/Zd t := by
  rw [diag_mean_vector,norm_toES]
  change sqrt ((mdCoord t)^2+(mdCoord t)^2) = _
  rw [show (mdCoord t)^2+(mdCoord t)^2 = 2*(mdCoord t)^2 by ring,
    sqrt_mul (by norm_num : (0:ℝ) ≤ 2),sqrt_sq_eq_abs,abs_of_nonneg (mdCoord_nonneg t ht)]
  unfold mdCoord
  ring
end BoundaryReduction.NinePoint
