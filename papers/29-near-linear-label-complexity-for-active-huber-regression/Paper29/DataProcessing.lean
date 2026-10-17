import Paper29.Transcript

noncomputable section
open scoped BigOperators Classical
namespace Paper29.Transcript.Law

/-- Gibbs nonnegativity for literal finite Shannon mutual information. -/
theorem information_nonneg {Ω S T : Type*} [Fintype Ω] [Fintype S] [Fintype T]
    (P : Law Ω) (X : Ω → S) (Y : Ω → T) : 0 ≤ P.information X Y := by
  rw [P.information_eq_joint_sum]
  have hpoint (s : S) (t : T) :
      P.mass (fun ω => (X ω,Y ω)) (s,t)-P.mass X s*P.mass Y t ≤
      P.mass (fun ω => (X ω,Y ω)) (s,t)*
        (Real.log (P.mass (fun ω => (X ω,Y ω)) (s,t))-Real.log (P.mass X s)-Real.log (P.mass Y t)) := by
    let p := P.mass (fun ω => (X ω,Y ω)) (s,t)
    let q := P.mass X s*P.mass Y t
    have hp0 : 0 ≤ p := P.mass_nonneg _ _
    have hq0 : 0 ≤ q := mul_nonneg (P.mass_nonneg _ _) (P.mass_nonneg _ _)
    by_cases hz : p=0
    · change p-q ≤ p*_
      rw [hz,zero_mul,zero_sub]
      linarith
    · have hp : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hz)
      have hs : 0 < P.mass X s := by
        have h := Finset.single_le_sum (s:=Finset.univ)
          (fun u _ => P.mass_nonneg (fun ω => (X ω,Y ω)) (s,u)) (Finset.mem_univ t)
        rw [P.sum_pair_mass_right] at h
        exact hp.trans_le h
      have ht : 0 < P.mass Y t := by
        have h := Finset.single_le_sum (s:=Finset.univ)
          (fun u _ => P.mass_nonneg (fun ω => (X ω,Y ω)) (u,t)) (Finset.mem_univ s)
        rw [P.sum_pair_mass_left] at h
        exact hp.trans_le h
      have hq : 0 < q := mul_pos hs ht
      have hl := Real.log_le_sub_one_of_pos (div_pos hq hp)
      rw [Real.log_div hq.ne' hp.ne',show Real.log q = Real.log (P.mass X s)+Real.log (P.mass Y t) from
        Real.log_mul hs.ne' ht.ne'] at hl
      have hm := mul_le_mul_of_nonneg_left hl hp.le
      have he : p*(q/p-1)=q-p := by field_simp
      rw [he] at hm
      change p-q ≤ _
      dsimp [p] at hm
      nlinarith only [hm]
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun s _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun t _ => hpoint s t))
  have he : (∑ (s : S),∑ (t : T), (P.mass (fun ω => (X ω,Y ω)) (s,t)-P.mass X s*P.mass Y t)) = 0 := by
    simp only [Finset.sum_sub_distrib,P.sum_pair_mass_right,← Finset.mul_sum,P.mass_total,mul_one,sub_self,Finset.sum_const_zero]
  rw [he] at hs
  exact hs

theorem conditionalInformation_nonneg {Ω S T H : Type*}
    [Fintype Ω] [Fintype S] [Fintype T] [Fintype H]
    (P : Law Ω) (X : Ω → S) (Y : Ω → T) (history : Ω → H) :
    0 ≤ P.conditionalInformation X Y history := by
  apply Finset.sum_nonneg
  intro h _
  by_cases hz : P.mass history h=0
  · simp [hz]
  · have hp : 0 < P.mass history h := lt_of_le_of_ne (P.mass_nonneg _ _) (Ne.symm hz)
    exact mul_nonneg hp.le (by
      rw [P.localInformation_eq_condition_information X Y history h hp]
      exact information_nonneg _ _ _)

/-- Adjoining a deterministic function of an observation changes no fibers. -/
theorem information_adjoin_function {Ω S T U : Type*}
    [Fintype Ω] [Fintype S] [Fintype T] [Fintype U]
    (P : Law Ω) (X : Ω → S) (Y : Ω → T) (f : T → U) :
    P.information X (fun ω => (f (Y ω),Y ω)) = P.information X Y := by
  unfold information
  apply Finset.sum_congr rfl
  intro ω _
  have hobs : P.mass (fun η => (f (Y η),Y η)) (f (Y ω),Y ω) = P.mass Y (Y ω) := by
    apply P.mass_eq_of_fibers
    intro η
    simp only [Prod.mk.injEq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨congrArg f h,h⟩
  have hjoint : P.mass (fun η => (X η,(f (Y η),Y η))) (X ω,(f (Y ω),Y ω)) =
      P.mass (fun η => (X η,Y η)) (X ω,Y ω) := by
    apply P.mass_eq_of_fibers
    intro η
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨hx,_,hy⟩; exact ⟨hx,hy⟩
    · rintro ⟨hx,hy⟩; exact ⟨hx,congrArg f hy,hy⟩
  rw [hobs,hjoint]

/-- Standard data processing, derived from the finite chain rule and Gibbs. -/
theorem information_data_processing {Ω S T U : Type*}
    [Fintype Ω] [Fintype S] [Fintype T] [Fintype U]
    (P : Law Ω) (X : Ω → S) (Y : Ω → T) (f : T → U) :
    P.information X (fun ω => f (Y ω)) ≤ P.information X Y := by
  have hc := P.information_chain_rule X Y (fun ω => f (Y ω))
  rw [P.information_adjoin_function X Y f] at hc
  have hn := P.conditionalInformation_nonneg X Y (fun ω => f (Y ω))
  linarith

end Paper29.Transcript.Law
