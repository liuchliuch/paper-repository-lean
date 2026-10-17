import Paper15.ModelIntegration
import Paper15.OutputLaw

noncomputable section
namespace Paper15
open MeasureTheory Finset BigOperators
attribute [local instance] TriangleModel.mX TriangleModel.mY TriangleModel.mZ
  TriangleModel.isProbX TriangleModel.isProbY TriangleModel.isProbZ

def binarySign (i : Fin 2) : ℝ := if i=0 then 1 else -1
lemma binarySign_legal (i : Fin 2) : legalSign (binarySign i) := by
  unfold binarySign
  split_ifs
  · exact legalSign.one
  · exact legalSign.neg_one

def binaryKernel (a b c x y z : ℝ) : ℝ := ((1+a*x)/2)*((1+b*y)/2)*((1+c*z)/2)

lemma binary_moment_inversion (x y z : ℝ) (u : Fin 3) :
    momentAt x y z u = ∑a : Fin 2,∑b : Fin 2,∑c : Fin 2,
      momentAt (binarySign a) (binarySign b) (binarySign c) u *
        binaryKernel (binarySign a) (binarySign b) (binarySign c) x y z := by
  fin_cases u <;> simp [Fin.sum_univ_two,binarySign,momentAt,binaryKernel] <;> ring

lemma pt_moments (t : ℝ) (u : Fin 3) :
    (∑a : Fin 2,∑b : Fin 2,∑c : Fin 2,
      momentAt (binarySign a) (binarySign b) (binarySign c) u *
        p_t t (binarySign a) (binarySign b) (binarySign c)) =
    if u=1 then t else 0 := by
  fin_cases u <;> simp [Fin.sum_univ_two,binarySign,momentAt,p_t] <;> ring

namespace TriangleModel
variable {M : TriangleModel}
lemma Good.div {f : M.X → M.Y → M.Z → ℝ} (hf : M.Good f) (c : ℝ) :
    M.Good (fun x y z => f x y z/c) := by
  convert (Good.const (M:=M) c⁻¹).mul hf using 1 <;> funext x y z <;> ring

variable (M : TriangleModel)
lemma goodKernel (a b c : ℝ) : M.Good (fun x y z => binaryKernel a b c (M.condA y z) (M.condB z x) (M.condC x y)) :=
  (((Good.const (M:=M) 1).add ((Good.const (M:=M) a).mul M.goodA)).div 2 |>.mul
    (((Good.const (M:=M) 1).add ((Good.const (M:=M) b).mul M.goodB)).div 2) |>.mul
    (((Good.const (M:=M) 1).add ((Good.const (M:=M) c).mul M.goodC)).div 2))

lemma good_sum {ι : Type*} (s : Finset ι) (f : ι → M.X → M.Y → M.Z → ℝ)
    (hf : ∀i∈s,M.Good (f i)) : M.Good (fun x y z => ∑i∈s,f i x y z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Good.const (M:=M) 0
  | @insert i s hi ih =>
    simp_rw [sum_insert hi]
    exact (hf i (by simp)).add (ih (fun j hj => hf j (by simp [hj])))

lemma expect_sum {ι : Type*} (s : Finset ι) (f : ι → M.X → M.Y → M.Z → ℝ)
    (hf : ∀i∈s,M.Good (f i)) :
    M.expect (fun x y z => ∑i∈s,f i x y z)=∑i∈s,M.expect (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expect]
  | @insert i s hi ih =>
    simp_rw [sum_insert hi]
    rw [M.expect_add (hf i (by simp)) (M.good_sum s f (fun j hj => hf j (by simp [hj]))),
      ih (fun j hj => hf j (by simp [hj]))]

lemma aggregate_from_output (u : Fin 3) : M.aggregate.vec u =
    ∑a : Fin 2,∑b : Fin 2,∑c : Fin 2,
      momentAt (binarySign a) (binarySign b) (binarySign c) u *
        M.output (binarySign a) (binarySign b) (binarySign c) := by
  rw [M.aggregate_vec_expect]
  have he : (fun x y z => momentAt (M.condA y z) (M.condB z x) (M.condC x y) u) =
      (fun x y z => ∑a : Fin 2,∑b : Fin 2,∑c : Fin 2,
        momentAt (binarySign a) (binarySign b) (binarySign c) u *
          binaryKernel (binarySign a) (binarySign b) (binarySign c) (M.condA y z) (M.condB z x) (M.condC x y)) := by
    funext x y z
    exact binary_moment_inversion _ _ _ u
  rw [he]
  rw [M.expect_sum]
  · apply sum_congr rfl
    intro a _
    rw [M.expect_sum]
    · apply sum_congr rfl
      intro b _
      rw [M.expect_sum]
      · apply sum_congr rfl
        intro c _
        exact M.expect_mul _ (M.goodKernel _ _ _)
      · intro c _
        exact (Good.const (M:=M) _).mul (M.goodKernel _ _ _)
    · intro b _
      -- A finite sum of good kernels is good.
      classical
      fin_cases b <;> simp only [Fin.sum_univ_two] <;>
        exact ((Good.const (M:=M) _).mul (M.goodKernel _ _ _)).add
          ((Good.const (M:=M) _).mul (M.goodKernel _ _ _))
  · intro a _
    simp only [Fin.sum_univ_two]
    exact (((Good.const (M:=M) _).mul (M.goodKernel _ _ _)).add
      ((Good.const (M:=M) _).mul (M.goodKernel _ _ _))).add
      (((Good.const (M:=M) _).mul (M.goodKernel _ _ _)).add
      ((Good.const (M:=M) _).mul (M.goodKernel _ _ _)))
end TriangleModel

theorem triangleLocal_implies_aggregate {t : ℝ} (h : IsTriangleLocal t) : IsAggregateRealizable t := by
  obtain ⟨M,hM⟩:=h
  have hm (u : Fin 3) : M.aggregate.vec u=if u=1 then t else 0 := by
    rw [M.aggregate_from_output]
    simp_rw [hM _ _ _ (binarySign_legal _) (binarySign_legal _) (binarySign_legal _)]
    exact pt_moments t u
  exact ⟨M,hm 0,by simpa [AggregateMoments.vec] using hm 1,hm 2⟩
end Paper15
