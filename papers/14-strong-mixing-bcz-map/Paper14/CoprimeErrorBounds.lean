import Paper14.CoprimeAsymptotic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries

open Filter Topology Finset
namespace Paper14
noncomputable section

lemma nat_div_cast_error {d : ℕ} (hd : 0 < d) (n : ℕ) :
    |((n/d : ℕ) : ℝ)-(n : ℝ)/(d : ℝ)| ≤ 1 := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hfloor : ⌊(n : ℝ)/(d : ℝ)⌋₊ = n/d := Nat.floor_div_eq_div n d
  have hl := Nat.floor_le (div_nonneg (Nat.cast_nonneg n) hdr.le)
  have hu := Nat.lt_floor_add_one ((n : ℝ)/(d : ℝ))
  rw [hfloor] at hl hu
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma appendix_p_card_eq (n d : ℕ) :
    (((Finset.Ioc (n/6) (n/3)).filter (fun p => d ∣ p)).card : ℝ) =
      ((n/(3*d) : ℕ) : ℝ)-((n/(6*d) : ℕ) : ℝ) := by
  rw [Ioc_filter_dvd_card,Nat.cast_sub (Nat.div_le_div_right (show n/6 ≤ n/3 by omega))]
  simp only [Nat.div_div_eq_div_mul]

lemma appendix_q_card_eq (n d : ℕ) :
    (((Finset.Ioc ((n-1)/2) n).filter (fun q => d ∣ q)).card : ℝ) =
      ((n/d : ℕ) : ℝ)-(((n-1)/(2*d) : ℕ) : ℝ) := by
  rw [Ioc_filter_dvd_card,Nat.cast_sub (Nat.div_le_div_right
    (show (n-1)/2 ≤ n from (Nat.div_le_self _ _).trans (Nat.sub_le _ _)))]
  simp only [Nat.div_div_eq_div_mul]

lemma appendix_p_card_error (n : ℕ) {d : ℕ} (hd : 0 < d) :
    |(((Finset.Ioc (n/6) (n/3)).filter (fun p => d ∣ p)).card : ℝ)-
      (n : ℝ)/(6*(d : ℝ))| ≤ 2 := by
  have h3 := nat_div_cast_error (by omega : 0 < 3*d) n
  have h6 := nat_div_cast_error (by omega : 0 < 6*d) n
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have heq : (n : ℝ)/(3*(d : ℝ))-(n : ℝ)/(6*(d : ℝ)) = (n : ℝ)/(6*(d : ℝ)) := by field_simp; ring
  rw [appendix_p_card_eq]
  push_cast at h3 h6
  obtain ⟨h3l,h3u⟩ := abs_le.mp h3
  obtain ⟨h6l,h6u⟩ := abs_le.mp h6
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma appendix_q_card_error {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    |(((Finset.Ioc ((n-1)/2) n).filter (fun q => d ∣ q)).card : ℝ)-
      (n : ℝ)/(2*(d : ℝ))| ≤ 3 := by
  have h1 := nat_div_cast_error hd n
  have h2 := nat_div_cast_error (by omega : 0 < 2*d) (n-1)
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hshift : (1 : ℝ)/(2*(d : ℝ)) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  have heq : (n : ℝ)/(d : ℝ)-(((n-1 : ℕ) : ℝ)/(2*(d : ℝ))) =
      (n : ℝ)/(2*(d : ℝ))+1/(2*(d : ℝ)) := by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
    field_simp
    <;> ring
  rw [appendix_q_card_eq]
  push_cast at h2
  obtain ⟨h1l,h1u⟩ := abs_le.mp h1
  obtain ⟨h2l,h2u⟩ := abs_le.mp h2
  have hs0 : (0 : ℝ) ≤ 1/(2*(d : ℝ)) := by positivity
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma appendix_q_card_le (n : ℕ) {d : ℕ} (hd : 0 < d) :
    (((Finset.Ioc ((n-1)/2) n).filter (fun q => d ∣ q)).card : ℝ) ≤ (n : ℝ)/(d : ℝ) := by
  rw [appendix_q_card_eq]
  exact (sub_le_self _ (Nat.cast_nonneg _)).trans Nat.cast_div_le

/-- Uniform actual two-window product error for the original Appendix A
Möbius summand. -/
lemma appendix_product_error {n d : ℕ} (hn : 0 < n) (hd : 0 < d) :
    |(((Finset.Ioc (n/6) (n/3)).filter (fun p => d ∣ p)).card : ℝ)*
      (((Finset.Ioc ((n-1)/2) n).filter (fun q => d ∣ q)).card : ℝ)-
      (n : ℝ)^2/(12*(d : ℝ)^2)| ≤ 3*(n : ℝ)/(d : ℝ) := by
  let P : ℝ := (((Finset.Ioc (n/6) (n/3)).filter (fun p => d ∣ p)).card : ℝ)
  let Q : ℝ := (((Finset.Ioc ((n-1)/2) n).filter (fun q => d ∣ q)).card : ℝ)
  let p : ℝ := (n : ℝ)/(6*(d : ℝ))
  let q : ℝ := (n : ℝ)/(2*(d : ℝ))
  have hP : |P-p| ≤ 2 := appendix_p_card_error n hd
  have hQ : |Q-q| ≤ 3 := appendix_q_card_error hn hd
  have hQ0 : 0 ≤ Q := Nat.cast_nonneg _
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hQle : Q ≤ (n : ℝ)/(d : ℝ) := appendix_q_card_le n hd
  have heq : P*Q-(n : ℝ)^2/(12*(d : ℝ)^2) = (P-p)*Q+p*(Q-q) := by dsimp [p,q]; ring
  change |P*Q-(n : ℝ)^2/(12*(d : ℝ)^2)| ≤ _
  rw [heq]
  calc _ ≤ |(P-p)*Q|+|p*(Q-q)| := abs_add_le _ _
       _ = |P-p| * Q+p * |Q-q| := by rw [abs_mul,abs_mul,abs_of_nonneg hQ0,abs_of_nonneg hp0]
       _ ≤ 2*((n : ℝ)/(d : ℝ))+p*3 :=
          add_le_add (mul_le_mul hP hQle hQ0 (by norm_num)) (mul_le_mul_of_nonneg_left hQ hp0)
       _ ≤ _ := by
         dsimp [p]
         have heq : (n : ℝ)/(6*(d : ℝ)) = ((n : ℝ)/(d : ℝ))/6 := by ring
         rw [heq]
         have hnd : (0 : ℝ) ≤ (n : ℝ)/(d : ℝ) := by positivity
         have hrhs : 3*(n : ℝ)/(d : ℝ) = 3*((n : ℝ)/(d : ℝ)) := by ring
         rw [hrhs]
         nlinarith

end
end Paper14
