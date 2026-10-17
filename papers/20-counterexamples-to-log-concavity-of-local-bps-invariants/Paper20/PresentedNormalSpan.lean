import Paper20.PresentedTower
import Paper20.HeckeTailSlide

namespace Paper20.PresentedHecke
open Paper20.HeckeNormalForm
noncomputable section
set_option maxHeartbeats 6000000
set_option maxRecDepth 10000

section Ring
variable (R : Type*) [CommRing R] (z : R)

/-- Each generator times a genuine tower normal word reduces into the
same finite normal-word span, using the exact four coset-word identities. -/
theorem generator_normalWord_mem (n : ℕ) (hspan : normalSpan R z n=⊤)
    (i : Fin n) (c : Code (n+1)) :
    generator R (n+1) z i*normalWord R z (n+1) c ∈ normalSpan R z (n+1) := by
  rcases c with ⟨j,b⟩
  change generator R (n+1) z i*
    (tailProduct (generator R (n+1) z) j.val*inclusion R n z (normalWord R z n b)) ∈ _
  rw [← mul_assoc]
  by_cases hfar : i.val+1 < j.val
  · rw [gen_tail_far (generator R (n+1) z) (generator_commute R (n+1) z) i j.val hfar]
    have hi : i.val < n-1 := by have := j.isLt; omega
    have he : inclusion R n z (generator R n z ⟨i.val,hi⟩)=generator R (n+1) z i := by
      rw [inclusion_generator]
      exact congrArg (generator R (n+1) z) (Fin.ext rfl)
    rw [mul_assoc,← he,← map_mul]
    exact tail_lower_mem R z n hspan j _
  · by_cases hpre : j.val=i.val+1
    · rw [gen_tail_predecessor (generator R (n+1) z) i j.val hpre]
      exact normalWord_mem R z (n+1) (i.castSucc,b)
    · by_cases hsame : i.val=j.val
      · rw [← hsame,gen_tail_same z (generator R (n+1) z)
          (fun a => by simpa only [pow_two] using generator_quadratic R (n+1) z a) i,
          add_mul,smul_mul_assoc]
        apply (normalSpan R z (n+1)).add_mem
        · apply (normalSpan R z (n+1)).smul_mem
          exact normalWord_mem R z (n+1) (i.castSucc,b)
        · exact normalWord_mem R z (n+1) (⟨i.val+1,by have := i.isLt; omega⟩,b)
      · have hji : j.val < i.val := by omega
        rw [gen_tail_slide (generator R (n+1) z) (generator_braid R (n+1) z)
          (generator_commute R (n+1) z) i j.val hji]
        have hi : i.val-1 < n-1 := by have := i.isLt; omega
        have he : inclusion R n z (generator R n z ⟨i.val-1,hi⟩)=
            generator R (n+1) z ⟨i.val-1,by have := i.isLt; omega⟩ := by
          rw [inclusion_generator]
        rw [mul_assoc,← he,← map_mul]
        exact tail_lower_mem R z n hspan j _

/-- Generator multiplication preserves the whole normal span, by actual
linearity from its proved effect on every finite normal word. -/
theorem generator_normalSpan_mem (n : ℕ) (hspan : normalSpan R z n=⊤)
    (i : Fin n) (a : Presented R (n+1) z) (ha : a ∈ normalSpan R z (n+1)) :
    generator R (n+1) z i*a ∈ normalSpan R z (n+1) := by
  change a ∈ Submodule.span R (Set.range (normalWord R z (n+1))) at ha
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c,rfl⟩ := hx
    exact generator_normalWord_mem R z n hspan i c
  | zero => rw [mul_zero]; exact (normalSpan R z (n+1)).zero_mem
  | add a b ha hb ia ib => rw [mul_add]; exact (normalSpan R z (n+1)).add_mem ia ib
  | smul c a ha ia => rw [mul_smul_comm]; exact (normalSpan R z (n+1)).smul_mem c ia

/-- The quotient's actual generator induction converts left-generator
stability and the identity into a complete spanning theorem. -/
theorem span_top_of_generator_stability (n : ℕ) (S : Submodule R (Presented R n z))
    (h1 : (1:Presented R n z) ∈ S)
    (hg : ∀ i a, a ∈ S → generator R n z i*a ∈ S) : S=⊤ := by
  have hpres : ∀ x : Presented R n z, ∀ a, a ∈ S → x*a ∈ S := by
    intro x
    apply induction_on R n z (P:=fun x => ∀ a, a ∈ S → x*a ∈ S) ?_ ?_ ?_ ?_ x
    · intro r a ha
      rw [Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul]
      exact S.smul_mem r ha
    · exact hg
    · intro x y hx hy a ha
      rw [mul_assoc]
      exact hx _ (hy _ ha)
    · intro x y hx hy a ha
      rw [add_mul]
      exact S.add_mem (hx a ha) (hy a ha)
  apply top_unique
  intro x hx
  simpa only [mul_one] using hpres x 1 h1

/-- The honest Hecke presentation is spanned by the explicit factorial
family of actual tower words. This proves a dimension bound rather than
assuming the concrete canonical model's dimension transfers to a quotient. -/
theorem normalSpan_eq_top (n : ℕ) : normalSpan R z n=⊤ := by
  induction n with
  | zero =>
    apply span_top_of_generator_stability R z 0 _ (normalSpan_one R z 0)
    intro i a ha
    exact Fin.elim0 i
  | succ n ih =>
    apply span_top_of_generator_stability R z (n+1) _ (normalSpan_one R z (n+1))
    intro i a ha
    exact generator_normalSpan_mem R z n ih i a ha

end Ring
end
end Paper20.PresentedHecke
