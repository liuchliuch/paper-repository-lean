import K44K35Free.Geometry
import K44K35Free.NormCounts
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-! A finite averaging proof for the monic quartic used in Lemma 6. -/
namespace K44K35Free.Geometry

open Polynomial Finset
open scoped BigOperators

variable {F : Type*} [Field F]

noncomputable section

theorem quarticPolynomial_eq_ofFn [DecidableEq F] (c : Quartic F) :
    quarticPolynomial c = X ^ 4 + Polynomial.ofFn 4 c := by
  simp only [quarticPolynomial, Polynomial.ofFn_eq_sum_monomial,
    Polynomial.C_mul_X_pow_eq_monomial]

theorem qPolynomial_natDegree_le (a : Fin 3 → F) :
    (qPolynomial a).natDegree ≤ 2 := by
  unfold qPolynomial
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · exact Polynomial.natDegree_mul_le.trans (by simp)
  · exact Polynomial.natDegree_mul_le.trans (by simp)

theorem quarticPolynomial_natDegree_le [DecidableEq F] (c : Quartic F) :
    (quarticPolynomial c).natDegree ≤ 4 := by
  rw [quarticPolynomial_eq_ofFn]
  exact Polynomial.natDegree_add_le_of_degree_le (by simp)
    (Nat.le_of_lt (Polynomial.ofFn_natDegree_lt (by omega) c))

@[simp] theorem quarticPolynomial_coeff_four [DecidableEq F] (c : Quartic F) :
    (quarticPolynomial c).coeff 4 = 1 := by
  simp [quarticPolynomial_eq_ofFn]

@[simp] theorem quarticPolynomial_natDegree [DecidableEq F] (c : Quartic F) :
    (quarticPolynomial c).natDegree = 4 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (quarticPolynomial_natDegree_le c)
  simp

theorem quarticPolynomial_monic [DecidableEq F] (c : Quartic F) :
    (quarticPolynomial c).Monic := by
  change (quarticPolynomial c).leadingCoeff = 1
  rw [← Polynomial.coeff_natDegree, quarticPolynomial_natDegree]
  exact quarticPolynomial_coeff_four c

theorem sectionPolynomial_natDegree_le [DecidableEq F] (α : F) (c : Quartic F)
    (g : GraphData F) : (sectionPolynomial α c g).natDegree ≤ 4 := by
  unfold sectionPolynomial
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le
    · apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le (quarticPolynomial_natDegree_le c)
      exact Polynomial.natDegree_pow_le.trans (by
        have := qPolynomial_natDegree_le g.A
        omega)
    · exact Polynomial.natDegree_mul_le.trans (by
        have := Polynomial.natDegree_pow_le (p := qPolynomial g.B) (n := 2)
        have := qPolynomial_natDegree_le g.B
        simp only [Polynomial.natDegree_C] at *
        omega)
  · exact (qPolynomial_natDegree_le g.C).trans (by omega)

/-- The leading coefficient depends only on the two quadratic coefficients. -/
def sectionLeading (α : F) (g : GraphData F) : F :=
  1 + g.A 2 ^ 2 - α * g.B 2 ^ 2

theorem coeff_sectionPolynomial_four [DecidableEq F] (α : F) (c : Quartic F)
    (g : GraphData F) :
    (sectionPolynomial α c g).coeff 4 = sectionLeading α g := by
  have hs (a : Fin 3 → F) : (qPolynomial a ^ 2).coeff 4 = a 2 ^ 2 := by
    rw [pow_two, show 4 = 2 + 2 by rfl,
      Polynomial.coeff_mul_add_eq_of_natDegree_le
        (qPolynomial_natDegree_le a) (qPolynomial_natDegree_le a)]
    simp [qPolynomial, pow_two]
  have hc : (qPolynomial g.C).coeff 4 = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((qPolynomial_natDegree_le _).trans_lt (by omega))
  simp [sectionPolynomial, quarticPolynomial_eq_ofFn,
    sectionLeading, hs, hc]

theorem sectionPolynomial_ne_zero [DecidableEq F] (α : F) (c : Quartic F)
    (g : GraphData F) (h : sectionLeading α g ≠ 0) :
    sectionPolynomial α c g ≠ 0 := by
  intro hz
  apply h
  rw [← coeff_sectionPolynomial_four α c g, hz]
  simp

/-- Any polynomial of degree at most four with this plane's leading
coefficient arises from exactly one choice of the four free coefficients. -/
theorem sectionPolynomial_surjective [DecidableEq F] (α : F) (g : GraphData F)
    (p : F[X]) (hd : p.natDegree ≤ 4)
    (h4 : p.coeff 4 = sectionLeading α g) :
    ∃ c : Quartic F, sectionPolynomial α c g = p := by
  let z : Quartic F := 0
  let d := p - sectionPolynomial α z g
  have hd4 : d.natDegree ≤ 4 :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le hd (sectionPolynomial_natDegree_le α z g))
  have hdcoeff : d.coeff 4 = 0 := by
    simp [d, h4, coeff_sectionPolynomial_four]
  have hdl : d.natDegree < 4 := by
    by_cases hz : d = 0
    · simp [hz]
    · have hn : d.natDegree ≠ 4 := by
        intro he
        have hc := Polynomial.leadingCoeff_ne_zero.mpr hz
        rw [← Polynomial.coeff_natDegree, he, hdcoeff] at hc
        exact hc rfl
      omega
  refine ⟨Polynomial.toFn 4 d, ?_⟩
  have hr := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt hdl
  simp only [sectionPolynomial, quarticPolynomial_eq_ofFn] at hr ⊢
  have hz : Polynomial.ofFn 4 z = 0 := by simp [z]
  change X ^ 4 + Polynomial.ofFn 4 (Polynomial.toFn 4 d) + _ - _ - _ = p
  rw [hr]
  simp only [d, sectionPolynomial, quarticPolynomial_eq_ofFn, hz]
  ring

theorem sectionPolynomial_injective [DecidableEq F] (α : F) (g : GraphData F) :
    Function.Injective (fun c : Quartic F => sectionPolynomial α c g) := by
  intro c d h
  have ho : Polynomial.ofFn 4 c = Polynomial.ofFn 4 d := by
    simp only [sectionPolynomial, quarticPolynomial_eq_ofFn] at h
    linear_combination h
  exact Polynomial.injective_ofFn 4 ho

/-- Scalar multiples of the squarefree split quartics are counted by
four-element subsets of the field. -/
def splitQuartic (ℓ : F) (R : Finset F) : F[X] :=
  Polynomial.C ℓ * ∏ r ∈ R, (X - Polynomial.C r)

theorem splitQuartic_eval_eq_zero_iff [DecidableEq F] (ℓ : F) (hℓ : ℓ ≠ 0)
    (R : Finset F) (x : F) : (splitQuartic ℓ R).eval x = 0 ↔ x ∈ R := by
  simp only [splitQuartic, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    mul_eq_zero, hℓ, false_or, Finset.prod_eq_zero_iff, sub_eq_zero]
  constructor
  · rintro ⟨i, hi, hix⟩
    exact hix ▸ hi
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem splitQuartic_natDegree_le (ℓ : F) (R : Finset F) (hR : R.card = 4) :
    (splitQuartic ℓ R).natDegree ≤ 4 := by
  exact Polynomial.natDegree_mul_le.trans (by simp [hR])

theorem splitQuartic_coeff_four (ℓ : F) (R : Finset F) (hR : R.card = 4) :
    (splitQuartic ℓ R).coeff 4 = ℓ := by
  have hm : (∏ r ∈ R, (X - Polynomial.C r : F[X])).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_sub_C _)
  have hd : (∏ r ∈ R, (X - Polynomial.C r : F[X])).natDegree = 4 := by simp [hR]
  simp only [splitQuartic, Polynomial.coeff_C_mul]
  rw [← hd, hm.coeff_natDegree, mul_one]

theorem splitQuartic_injective [DecidableEq F] (ℓ : F) (hℓ : ℓ ≠ 0) :
    Function.Injective (splitQuartic ℓ : Finset F → F[X]) := by
  intro R S h
  ext x
  rw [← splitQuartic_eval_eq_zero_iff ℓ hℓ R x,
    ← splitQuartic_eval_eq_zero_iff ℓ hℓ S x, h]

/-- The four-element subsets, with no ordering or root multiplicities. -/
abbrev FourSet (F : Type*) := {R : Finset F // R.card = 4}

theorem card_fourSet [Fintype F] [DecidableEq F] :
    Fintype.card (FourSet F) = (Fintype.card F).choose 4 := by
  have he : FourSet F ≃ (Finset.univ.powersetCard 4 : Finset (Finset F)) :=
    Equiv.subtypeEquivRight (fun R => by simp)
  rw [Fintype.card_congr he, Fintype.card_coe, Finset.card_powersetCard,
    Finset.card_univ]

def quarticForRoots [DecidableEq F] (α : F) (g : GraphData F) (R : FourSet F) :
    Quartic F :=
  Classical.choose (sectionPolynomial_surjective α g (splitQuartic (sectionLeading α g) R.val)
    (splitQuartic_natDegree_le _ _ R.property)
    (splitQuartic_coeff_four _ _ R.property))

theorem sectionPolynomial_quarticForRoots [DecidableEq F] (α : F) (g : GraphData F)
    (R : FourSet F) :
    sectionPolynomial α (quarticForRoots α g R) g = splitQuartic (sectionLeading α g) R.val :=
  Classical.choose_spec (sectionPolynomial_surjective α g
    (splitQuartic (sectionLeading α g) R.val)
    (splitQuartic_natDegree_le _ _ R.property)
    (splitQuartic_coeff_four _ _ R.property))

theorem quarticForRoots_injective [DecidableEq F] (α : F) (g : GraphData F)
    (hg : sectionLeading α g ≠ 0) : Function.Injective (quarticForRoots α g) := by
  intro R S h
  apply Subtype.ext
  apply splitQuartic_injective _ hg
  rw [← sectionPolynomial_quarticForRoots, ← sectionPolynomial_quarticForRoots, h]

def polynomialRootSet [Fintype F] (p : F[X]) : Finset F := by
  classical
  exact Finset.univ.filter (fun x => p.eval x = 0)

@[simp] theorem mem_polynomialRootSet [Fintype F] (p : F[X]) (x : F) :
    x ∈ polynomialRootSet p ↔ p.eval x = 0 := by
  classical
  simp [polynomialRootSet]

theorem polynomialRootSet_splitQuartic [Fintype F] [DecidableEq F]
    (ℓ : F) (hℓ : ℓ ≠ 0) (R : Finset F) :
    polynomialRootSet (splitQuartic ℓ R) = R := by
  ext x
  simp [splitQuartic_eval_eq_zero_iff ℓ hℓ]

theorem quarticForRoots_four_roots [Fintype F] [DecidableEq F]
    (α : F) (g : GraphData F) (hg : sectionLeading α g ≠ 0) (R : FourSet F) :
    (polynomialRootSet (sectionPolynomial α (quarticForRoots α g R) g)).card = 4 := by
  rw [sectionPolynomial_quarticForRoots, polynomialRootSet_splitQuartic _ hg]
  exact R.property

/-- The nine graph-plane coefficients separated into the two coefficients
that determine the leading term, and seven unrestricted coefficients. -/
def graphDataEquiv : GraphData F ≃ (F × F) × (Fin 7 → F) where
  toFun g := ((g.A 2, g.B 2), ![g.A 0, g.A 1, g.B 0, g.B 1, g.C 0, g.C 1, g.C 2])
  invFun p := ⟨![p.2 0, p.2 1, p.1.1], ![p.2 2, p.2 3, p.1.2],
    ![p.2 4, p.2 5, p.2 6]⟩
  left_inv g := by
    cases g with
    | mk A B C =>
      have ha : ![A 0, A 1, A 2] = A := by ext i; fin_cases i <;> rfl
      have hb : ![B 0, B 1, B 2] = B := by ext i; fin_cases i <;> rfl
      have hc : ![C 0, C 1, C 2] = C := by ext i; fin_cases i <;> rfl
      change GraphData.mk ![A 0, A 1, A 2] ![B 0, B 1, B 2] ![C 0, C 1, C 2] = _
      rw [ha, hb, hc]
  right_inv p := by
    rcases p with ⟨⟨a, b⟩, r⟩
    apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> rfl

theorem card_graphData [Fintype F] :
    Fintype.card (GraphData F) = Fintype.card F ^ 9 := by
  rw [Fintype.card_congr (graphDataEquiv (F := F))]
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  ring

def goodGraphData [Fintype F] (α : F) : Finset (GraphData F) := by
  classical
  exact Finset.univ.filter (fun g => sectionLeading α g ≠ 0)

@[simp] theorem mem_goodGraphData [Fintype F] (α : F) (g : GraphData F) :
    g ∈ goodGraphData α ↔ sectionLeading α g ≠ 0 := by
  classical
  simp [goodGraphData]

theorem card_badGraphData [Fintype F] [DecidableEq F] (α : F) (hα : IsNonsquare α)
    (hF : ringChar F ≠ 2) :
    (Finset.univ.filter (fun g : GraphData F => sectionLeading α g = 0)).card =
      (Fintype.card F + 1) * Fintype.card F ^ 7 := by
  classical
  letI : Fintype (NormFiber α (-1)) := by unfold NormFiber; infer_instance
  let e : {g : GraphData F // sectionLeading α g = 0} ≃
      NormFiber α (-1) × (Fin 7 → F) :=
    { toFun := fun g => ⟨⟨(graphDataEquiv g.val).1, by
        have := g.property
        change 1 + g.val.A 2 ^ 2 - α * g.val.B 2 ^ 2 = 0 at this
        change g.val.A 2 ^ 2 - α * g.val.B 2 ^ 2 = -1
        linear_combination this⟩, (graphDataEquiv g.val).2⟩
      invFun := fun p => ⟨graphDataEquiv.symm (p.1.val, p.2), by
        have := p.1.property
        change 1 + p.1.val.1 ^ 2 - α * p.1.val.2 ^ 2 = 0
        linear_combination this⟩
      left_inv := by
        intro g
        apply Subtype.ext
        exact graphDataEquiv.symm_apply_apply g.val
      right_inv := by
        rintro ⟨p, r⟩
        refine Prod.ext ?_ ?_
        · apply Subtype.ext
          change (graphDataEquiv (graphDataEquiv.symm (p.val, r))).1 = p.val
          exact congrArg Prod.fst (graphDataEquiv.apply_symm_apply (p.val, r))
        · change (graphDataEquiv (graphDataEquiv.symm (p.val, r))).2 = r
          exact congrArg Prod.snd (graphDataEquiv.apply_symm_apply (p.val, r)) }
  rw [← Fintype.card_subtype, Fintype.card_congr e, Fintype.card_prod]
  rw [← Nat.card_eq_fintype_card (α := NormFiber α (-1)), card_norm_neg_one hα hF]
  simp [Fintype.card_fun]

theorem card_goodGraphData [Fintype F] [DecidableEq F] (α : F) (hα : IsNonsquare α)
    (hF : ringChar F ≠ 2) :
    (goodGraphData α).card =
      Fintype.card F ^ 9 - (Fintype.card F + 1) * Fintype.card F ^ 7 := by
  classical
  have hc := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (GraphData F)))
    (p := fun g => sectionLeading α g = 0)
  rw [Finset.card_univ, card_graphData, card_badGraphData α hα hF] at hc
  have he : (Finset.univ.filter (fun g : GraphData F => ¬sectionLeading α g = 0)).card =
      (goodGraphData α).card := by
    congr 1
    ext g
    simp [goodGraphData]
  omega

theorem natDegree_lt_four_of_coeff_four_zero (p : F[X]) (hd : p.natDegree ≤ 4)
    (hc : p.coeff 4 = 0) : p.natDegree < 4 := by
  by_cases hz : p = 0
  · simp [hz]
  · have hn : p.natDegree ≠ 4 := by
      intro he
      have hn := Polynomial.leadingCoeff_ne_zero.mpr hz
      rw [← Polynomial.coeff_natDegree, he, hc] at hn
      exact hn rfl
    omega

theorem sectionPolynomial_eq_split_rootSet [Fintype F] [DecidableEq F]
    (α : F) (c : Quartic F) (g : GraphData F) (hg : sectionLeading α g ≠ 0)
    (hr : (polynomialRootSet (sectionPolynomial α c g)).card = 4) :
    sectionPolynomial α c g =
      splitQuartic (sectionLeading α g) (polynomialRootSet (sectionPolynomial α c g)) := by
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _
    (polynomialRootSet (sectionPolynomial α c g))
  · intro x hx
    have hx0 := (mem_polynomialRootSet _ _).mp hx
    simp only [Polynomial.eval_sub, hx0]
    rw [(splitQuartic_eval_eq_zero_iff _ hg _ _).mpr hx]
    simp
  · rw [hr]
    apply natDegree_lt_four_of_coeff_four_zero
    · exact (Polynomial.natDegree_sub_le _ _).trans
        (max_le (sectionPolynomial_natDegree_le α c g)
          (splitQuartic_natDegree_le _ _ hr))
    · simp [coeff_sectionPolynomial_four, splitQuartic_coeff_four _ _ hr]

def richQuartics [Fintype F] (α : F) (g : GraphData F) : Finset (Quartic F) := by
  classical
  exact Finset.univ.filter (fun c => (polynomialRootSet (sectionPolynomial α c g)).card = 4)

@[simp] theorem mem_richQuartics [Fintype F] (α : F) (g : GraphData F) (c : Quartic F) :
    c ∈ richQuartics α g ↔ (polynomialRootSet (sectionPolynomial α c g)).card = 4 := by
  classical
  simp [richQuartics]

theorem card_richQuartics [Fintype F] [DecidableEq F] (α : F) (g : GraphData F)
    (hg : sectionLeading α g ≠ 0) :
    (richQuartics α g).card = (Fintype.card F).choose 4 := by
  let e : FourSet F ≃ (richQuartics α g) :=
    { toFun := fun R => ⟨quarticForRoots α g R,
        (mem_richQuartics _ _ _).mpr (quarticForRoots_four_roots α g hg R)⟩
      invFun := fun c => ⟨polynomialRootSet (sectionPolynomial α c.val g),
        (mem_richQuartics _ _ _).mp c.property⟩
      left_inv := by
        intro R
        apply Subtype.ext
        change polynomialRootSet (sectionPolynomial α (quarticForRoots α g R) g) = R.val
        rw [sectionPolynomial_quarticForRoots, polynomialRootSet_splitQuartic _ hg]
      right_inv := by
        intro c
        apply Subtype.ext
        apply sectionPolynomial_injective α g
        dsimp only
        rw [sectionPolynomial_quarticForRoots]
        exact (sectionPolynomial_eq_split_rootSet α c.val g hg
          ((mem_richQuartics _ _ _).mp c.property)).symm }
  rw [← Fintype.card_coe, ← Fintype.card_congr e, card_fourSet]

def richGraphData [Fintype F] (α : F) (c : Quartic F) : Finset (GraphData F) := by
  classical
  exact (goodGraphData α).filter
    (fun g => (polynomialRootSet (sectionPolynomial α c g)).card = 4)

@[simp] theorem mem_richGraphData [Fintype F] (α : F) (c : Quartic F) (g : GraphData F) :
    g ∈ richGraphData α c ↔ sectionLeading α g ≠ 0 ∧
      (polynomialRootSet (sectionPolynomial α c g)).card = 4 := by
  classical
  simp [richGraphData]

/-- The exact finite double count underlying equation (12). -/
theorem sum_richGraphData [Fintype F] [DecidableEq F] (α : F) :
    ∑ c : Quartic F, (richGraphData α c).card =
      (goodGraphData α).card * (Fintype.card F).choose 4 := by
  classical
  calc
    ∑ c : Quartic F, (richGraphData α c).card =
        ∑ c : Quartic F, ∑ g ∈ goodGraphData α,
          if (polynomialRootSet (sectionPolynomial α c g)).card = 4 then 1 else 0 := by
      simp only [richGraphData, Finset.card_filter]
    _ = ∑ g ∈ goodGraphData α, (richQuartics α g).card := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      simp only [richQuartics, Finset.card_filter]
    _ = (goodGraphData α).card * (Fintype.card F).choose 4 := by
      apply Finset.sum_const_nat
      intro g hg
      exact card_richQuartics α g ((mem_goodGraphData α g).mp hg)

theorem sum_richGraphData_exact [Fintype F] [DecidableEq F] (α : F)
    (hα : IsNonsquare α) (hF : ringChar F ≠ 2) :
    ∑ c : Quartic F, (richGraphData α c).card =
      (Fintype.card F ^ 9 - (Fintype.card F + 1) * Fintype.card F ^ 7) *
        (Fintype.card F).choose 4 := by
  rw [sum_richGraphData, card_goodGraphData α hα hF]

theorem card_graphPlane_section [Fintype F] (α : F) (c : Quartic F)
    (g : GraphData F) :
    (planeSection α c (graphPlane g)).card =
      (polynomialRootSet (sectionPolynomial α c g)).card := by
  classical
  let e : (planeSection α c (graphPlane g)) ≃
      (polynomialRootSet (sectionPolynomial α c g)) :=
    { toFun := fun p => ⟨p.val 0, (mem_polynomialRootSet _ _).mpr
        ((point_mem_graphPlane_iff α c g p.val).mp
          ((mem_section α c (graphPlane g) p.val).mp p.property)).2.2⟩
      invFun := fun x => ⟨![x.val, (qPolynomial g.A).eval x.val, (qPolynomial g.B).eval x.val],
        (mem_section _ _ _ _).mpr ((point_mem_graphPlane_iff _ _ _ _).mpr
          ⟨rfl, rfl, (mem_polynomialRootSet _ _).mp x.property⟩)⟩
      left_inv := by
        intro p
        apply Subtype.ext
        have hp := (point_mem_graphPlane_iff α c g p.val).mp
          ((mem_section _ _ _ _).mp p.property)
        funext i
        fin_cases i
        · rfl
        · exact hp.1.symm
        · exact hp.2.1.symm
      right_inv := by intro x; apply Subtype.ext; rfl }
  exact (Fintype.card_coe _).symm.trans ((Fintype.card_congr e).trans (Fintype.card_coe _))

theorem graphPlane_not_fiberExceptional (g : GraphData F) :
    ¬FiberExceptional (graphPlane g) := by
  rintro ⟨d, hd⟩
  have hm := hd (LinearMap.mem_range_self (graphMap g) ![0, 1, 0])
  have hx : (graphMap g ![0, 1, 0]) 1 = d * (graphMap g ![0, 1, 0]) 0 := hm.1
  simpa [graphMap] using hx

theorem richGraphData_not_exceptional [Fintype F] [DecidableEq F]
    (α : F) (c : Quartic F) {g : GraphData F} (hg : g ∈ richGraphData α c) :
    ¬Exceptional α c (graphPlane g) := by
  rcases (mem_richGraphData _ _ _).mp hg with ⟨hℓ, _⟩
  rintro (⟨g', he, hz⟩ | hf)
  · have heq := graphPlane_injective he
    subst g'
    exact sectionPolynomial_ne_zero α c g hℓ hz
  · exact graphPlane_not_fiberExceptional g hf

/-- A concrete finite family of genuine projective planes. -/
def richPlanes [Fintype F] (α : F) (c : Quartic F) : Finset (Plane F) := by
  classical
  exact (richGraphData α c).image graphPlane

theorem card_richPlanes [Fintype F] (α : F) (c : Quartic F) :
    (richPlanes α c).card = (richGraphData α c).card := by
  classical
  exact Finset.card_image_of_injective _ graphPlane_injective

theorem richPlanes_spec [Fintype F] [DecidableEq F] (α : F) (c : Quartic F)
    {E : Plane F} (hE : E ∈ richPlanes α c) :
    ¬Exceptional α c E ∧ (planeSection α c E).card = 4 := by
  classical
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hE
  refine ⟨richGraphData_not_exceptional α c hg, ?_⟩
  rw [card_graphPlane_section]
  exact ((mem_richGraphData _ _ _).mp hg).2

/-- An explicit uniform estimate for the four-subset probability. -/
theorem choose_four_lower_bound (q : ℕ) (hq : 8 ≤ q) :
    q ^ 4 ≤ 384 * q.choose 4 := by
  have he := Nat.descFactorial_eq_factorial_mul_choose q 4
  norm_num [Nat.descFactorial_succ] at he
  have h0 : q ≤ 2 * q := by omega
  have h1 : q ≤ 2 * (q - 1) := by omega
  have h2 : q ≤ 2 * (q - 2) := by omega
  have h3 : q ≤ 2 * (q - 3) := by omega
  calc
    q ^ 4 = q * q * q * q := by ring
    _ ≤ (2 * q) * (2 * (q - 1)) * (2 * (q - 2)) * (2 * (q - 3)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h0 h1) h2) h3
    _ = 384 * q.choose 4 := by nlinarith [he]

theorem goodGraphData_lower_bound [Fintype F] [DecidableEq F]
    (α : F) (hα : IsNonsquare α) (hF : ringChar F ≠ 2)
    (hq : 8 ≤ Fintype.card F) :
    Fintype.card F ^ 9 ≤ 2 * (goodGraphData α).card := by
  let q := Fintype.card F
  have hq' : 8 ≤ q := hq
  have hsmall : 2 * (q + 1) ≤ q ^ 2 := by nlinarith
  have hbad : 2 * ((q + 1) * q ^ 7) ≤ q ^ 9 := by
    have hh := Nat.mul_le_mul_right (q ^ 7) hsmall
    nlinarith [hh]
  have hle : (q + 1) * q ^ 7 ≤ q ^ 9 := by omega
  rw [card_goodGraphData α hα hF]
  change q ^ 9 ≤ 2 * (q ^ 9 - (q + 1) * q ^ 7)
  omega

/-- Some quartic attains the finite average. The factor 768 is absolute. -/
theorem exists_many_richGraphData [Fintype F] [DecidableEq F]
    (α : F) (hα : IsNonsquare α) (hF : ringChar F ≠ 2)
    (hq : 8 ≤ Fintype.card F) :
    ∃ c : Quartic F, Fintype.card F ^ 9 ≤ 768 * (richGraphData α c).card := by
  classical
  let q := Fintype.card F
  obtain ⟨c, _, hc⟩ := Finset.exists_max_image Finset.univ
    (fun c : Quartic F => (richGraphData α c).card) Finset.univ_nonempty
  refine ⟨c, ?_⟩
  have hs : (∑ d : Quartic F, (richGraphData α d).card) ≤
      q ^ 4 * (richGraphData α c).card := by
    calc
      (∑ d : Quartic F, (richGraphData α d).card) ≤
          ∑ _d : Quartic F, (richGraphData α c).card :=
        Finset.sum_le_sum hc
      _ = q ^ 4 * (richGraphData α c).card := by simp [q, Quartic]
  have hprod := Nat.mul_le_mul (goodGraphData_lower_bound α hα hF hq)
    (choose_four_lower_bound q hq)
  have hh : q ^ 4 * q ^ 9 ≤ q ^ 4 * (768 * (richGraphData α c).card) := by
    calc
      q ^ 4 * q ^ 9 = q ^ 9 * q ^ 4 := by ring
      _ ≤ (2 * (goodGraphData α).card) * (384 * q.choose 4) := hprod
      _ = 768 * (∑ d : Quartic F, (richGraphData α d).card) := by
        rw [sum_richGraphData]
        ring
      _ ≤ 768 * (q ^ 4 * (richGraphData α c).card) := Nat.mul_le_mul_left _ hs
      _ = q ^ 4 * (768 * (richGraphData α c).card) := by ring
  exact Nat.le_of_mul_le_mul_left hh (by positivity)

/-- Lemma 6 with an explicit absolute constant and an explicit threshold.
Every counted object is a three-dimensional vector subspace of `F⁶`,
outside the exceptional family, with exactly four of the paper's points. -/
theorem lemma_6_many_four_point_sections [Fintype F] [DecidableEq F]
    (α : F) (hα : IsNonsquare α) (hF : ringChar F ≠ 2)
    (hq : 8 ≤ Fintype.card F) :
    ∃ c : Quartic F, Fintype.card F ^ 9 ≤ 768 * (richPlanes α c).card ∧
      ∀ E ∈ richPlanes α c, ¬Exceptional α c E ∧ (planeSection α c E).card = 4 := by
  obtain ⟨c, hc⟩ := exists_many_richGraphData α hα hF hq
  exact ⟨c, by rwa [card_richPlanes], fun _ hE => richPlanes_spec α c hE⟩

end
end K44K35Free.Geometry
