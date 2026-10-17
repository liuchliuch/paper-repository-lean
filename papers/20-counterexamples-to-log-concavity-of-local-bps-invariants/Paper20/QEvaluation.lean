import Paper20.PhiEvaluation
import Paper20.PolynomialLink

namespace Paper20
noncomputable section
set_option maxHeartbeats 2000000

theorem peval_foldrInner (c2 : ℤ) (ev : Bool) (Rs : List ℚ) (h : ℕ)
    (idxs : List ℕ) (x : ℚ) :
    peval (foldrInner c2 ev Rs h idxs) x =
      (idxs.map (fun j => Rs.getD (h-j) 0*peval (Apoly c2 ev j) x)).sum := by
  induction idxs with
  | nil => rfl
  | cons j js ih =>
    simpa only [foldrInner, List.foldr_cons, peval_padd, peval_psmul,
      List.map_cons, List.sum_cons] using congrArg (fun y =>
        Rs.getD (h-j) 0*peval (Apoly c2 ev j) x+y) ih

theorem peval_sumPoly (ps : List (List ℚ)) (x : ℚ) :
    peval (sumPoly ps) x = (ps.map (fun p => peval p x)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simpa [sumPoly, peval_padd] using congrArg (fun y => peval p x+y) ih

/-- Evaluation of the exact constructed Q, retaining its actual partition
enumeration, hook series and polynomial numerator. -/
theorem Qcoeff_evaluation (r h k : ℕ) :
    peval (Qcoeff r h) ((k:ℚ)*(k+1)) = (1/(r.factorial:ℚ))*
      ((partitionsOf r).map (fun ps => ((dimOf r ps)^2:ℕ)*
        ((List.range (h+1)).map (fun j =>
          (Rseries (hooksOf ps) (partsEvenHooks ps) h).getD (h-j) 0 *
          (Phi.contentNumerator (contentOf ps).natAbs k).coeff j)).sum)).sum := by
  rw [Qcoeff, peval_psmul, peval_sumPoly]
  congr 1
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ps hp
  dsimp only [Function.comp_apply, partQ]
  rw [peval_psmul, innerSum, peval_foldrInner]
  simp only [Phi.Apoly_eval_content, partsContent_eq_contentOf, partsHooks_eq_hooksOf,
    partsDim_eq_dimOf, Function.comp_apply, pow_two]

end
end Paper20
