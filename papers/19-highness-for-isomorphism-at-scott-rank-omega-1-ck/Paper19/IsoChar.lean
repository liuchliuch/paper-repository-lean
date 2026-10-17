import Paper19.BooleanGroup

/-!
# Lemma 4: isomorphism characterization (Section 3)
-/

namespace Paper19

open scoped symmDiff

variable {T : Tree}

/-! ## Translation map -/

def translateDom {T : Tree} (h : ℕ → Finset Node) (x : Dom T) : Dom T :=
  match x with
  | .idx k => .idx k
  | .vec n F => .vec n (F ∆ h n)

@[simp] theorem translateDom_idx {T : Tree} (h : ℕ → Finset Node) (k : ℕ) :
    translateDom h (Dom.idx k : Dom T) = Dom.idx k :=
  rfl

@[simp] theorem translateDom_vec {T : Tree} (h : ℕ → Finset Node) (n : ℕ)
    (F : Finset Node) :
    translateDom h (Dom.vec n F : Dom T) = Dom.vec n (F ∆ h n) :=
  rfl

theorem translateDom_self {T : Tree} (h : ℕ → Finset Node) (x : Dom T) :
    translateDom h (translateDom h x) = x := by
  cases x with
  | idx k => rfl
  | vec n F => simp [translateDom, symmDiff_cancel]

theorem translateDom_bijective {T : Tree} (h : ℕ → Finset Node) :
    Function.Bijective (translateDom h (T := T)) := by
  refine ⟨fun a b hab => ?_, fun y => ⟨translateDom h y, translateDom_self h y⟩⟩
  have h1 := congrArg (translateDom h) hab
  simpa [translateDom_self] using h1

theorem translateDom_index_eq {T : Tree} (h : ℕ → Finset Node) (x : Dom T)
    (hx : isIndex x) : translateDom h x = x := by
  cases x with
  | idx k => rfl
  | vec n F => exact absurd hx (by simp [isIndex])

theorem translateDom_succ {T : Tree} (h : ℕ → Finset Node) (x : Dom T) :
    translateDom h (Dom.succ x) = Dom.succ (translateDom h x) := by
  cases x with
  | idx k => rfl
  | vec n F => rfl

theorem translateDom_levelOf {T : Tree} (h : ℕ → Finset Node) (x : Dom T) :
    translateDom h (Dom.levelOf x) = Dom.levelOf (translateDom h x) := by
  cases x with
  | idx k => rfl
  | vec n F => rfl

theorem translateDom_cA (c : CoherentIso T) :
    (translateDom (T := T) c.h Dom.cA : Dom T) = Dom.cB := by
  show (Dom.vec 0 (∅ ∆ c.h 0) : Dom T) = (Dom.vec 0 {[]})
  rw [c.root, empty_symmDiff_fin]

theorem translateDom_cA_aut (c : CoherentAut T) :
    (translateDom (T := T) c.h Dom.cA : Dom T) = Dom.cA := by
  show (Dom.vec 0 (∅ ∆ c.h 0) : Dom T) = (Dom.vec 0 ∅)
  rw [c.root, empty_symmDiff_fin]

/-! ## Preservation of `D` -/

theorem isD_translate_of {T : Tree} (h : ℕ → Finset Node) (k F F' : Dom T)
    (hd : isD k F F') :
    isD (translateDom h k) (translateDom h F) (translateDom h F') := by
  unfold isD at hd
  obtain ⟨code, n, n', G, G', H, hk, hF, hF', hnn', hcode, hH, hdiff⟩ := hd
  refine ⟨code, n, n, G ∆ h n, G' ∆ h n, H, ?_, ?_, ?_, rfl, hcode, hH, ?_⟩
  · rw [hk]
    rfl
  · rw [hF]
    rfl
  · rw [hF', hnn']
    rfl
  · rw [hdiff, hnn']
    rw [symmDiff_assoc, symmDiff_comm H, ← symmDiff_assoc]

theorem isD_translate {T : Tree} (h : ℕ → Finset Node) (k F F' : Dom T) :
    isD k F F' ↔ isD (translateDom h k) (translateDom h F) (translateDom h F') := by
  constructor
  · exact isD_translate_of h k F F'
  · intro hd
    have hd2 := isD_translate_of h (translateDom h k) (translateDom h F)
      (translateDom h F') hd
    simpa [translateDom_self] using hd2

theorem lemma4_preservesD (c : CoherentIso T) :
    ∀ (k : Dom T) (n : ℕ) (F F' : Finset Node),
      isD k (.vec n F) (.vec n F') →
        isD k (.vec n (c.act n F)) (.vec n (c.act n F')) := by
  intro k n F F' hd
  have hd' := isD_translate_of c.h k (.vec n F : Dom T) (.vec n F' : Dom T) hd
  cases k with
  | idx m =>
    have h1 : translateDom c.h (Dom.vec n F : Dom T) = Dom.vec n (c.act n F) := rfl
    have h2 : translateDom c.h (Dom.vec n F' : Dom T) = Dom.vec n (c.act n F') := rfl
    rw [h1, h2] at hd'
    exact hd'
  | vec m G =>
    unfold isD at hd
    obtain ⟨code, n1, n2, G1, G2, H, hk, _, _, _, _, _, _⟩ := hd
    simp at hk

/-! ## Forward direction of Lemma 4 -/

theorem lemma4_act_self (c : CoherentIso T) :
    ∀ n F, c.act n (c.act n F) = F :=
  fun n F => CoherentIso.act_self c n F

theorem lemma4_aut_act_self (c : CoherentAut T) :
    ∀ n F, c.act n (c.act n F) = F :=
  fun n F => CoherentAut.act_self c n F

theorem lemma4_iso_root (c : CoherentIso T) : c.h 0 = {[]} :=
  c.root

theorem lemma4_aut_root (c : CoherentAut T) : c.h 0 = ∅ :=
  c.root

theorem lemma4_hom_proj (c : CoherentIso T) (n : ℕ)
    {F : Finset Node} (hF : LenN1 n F) (hh : LenN1 n (c.h (n + 1))) :
    proj T n (c.act (n + 1) F) = c.act n (proj T n F) :=
  CoherentIso.act_proj c n hF hh

/-! ## Structure isomorphisms -/

def IsStructIso (T : Tree) (c₁ c₂ : Dom T) (f : Dom T → Dom T) : Prop :=
  Function.Bijective f ∧
    (∀ x, isIndex x ↔ isIndex (f x)) ∧
    (∀ x, isIndex x → f x = x) ∧
    (∀ x, f (Dom.succ x) = Dom.succ (f x)) ∧
    (∀ x, f (Dom.projD x) = Dom.projD (f x)) ∧
    (∀ x, f (Dom.levelOf x) = Dom.levelOf (f x)) ∧
    (∀ k F F', isD k F F' ↔ isD (f k) (f F) (f F')) ∧
    f c₁ = c₂

/-! ## Converse direction -/

def hOfIso {T : Tree} (f : Dom T → Dom T) (n : ℕ) : Finset Node :=
  match f (.vec n ∅) with
  | .vec _ H => H
  | .idx _ => ∅

theorem hOfIso_translate {T : Tree} (h : ℕ → Finset Node) (n : ℕ) :
    hOfIso (T := T) (translateDom h) n = h n := by
  show (match (Dom.vec n (∅ ∆ h n) : Dom T) with
    | .vec _ H => H
    | .idx _ => ∅) = h n
  rw [empty_symmDiff_fin]

theorem finsetCode_empty : finsetCode (∅ : Finset Node) = 0 := by
  unfold finsetCode
  simp

theorem iso_on_empty {T : Tree} (f : Dom T → Dom T)
    (hi : IsStructIso T Dom.cA Dom.cB f) (n : ℕ) :
    f (.vec n ∅ : Dom T) = .vec n (hOfIso f n) := by
  obtain ⟨H0, hH0⟩ : ∃ H, f (.vec n ∅ : Dom T) = .vec n H := by
    cases hfe : f (.vec n ∅ : Dom T) with
    | idx k =>
      have : isIndex (f (.vec n ∅ : Dom T)) := by rw [hfe]; trivial
      have : isIndex (.vec n ∅ : Dom T) := (hi.2.1 _).2 this
      simp [isIndex] at this
    | vec m H =>
      have hlv := hi.2.2.2.2.2.1 (.vec n ∅ : Dom T)
      have hlv1 : Dom.levelOf (.vec n ∅ : Dom T) = .idx n := rfl
      rw [hlv1] at hlv
      have hfix : f (.idx n) = .idx n := hi.2.2.1 _ (by simp [isIndex])
      rw [hfix, hfe] at hlv
      have hlv2 : Dom.levelOf (.vec m H : Dom T) = .idx m := rfl
      rw [hlv2] at hlv
      simp at hlv
      subst hlv
      exact ⟨H, rfl⟩
  have h0 : hOfIso (T := T) f n = H0 := by
    unfold hOfIso
    rw [hH0]
  rw [hH0, h0]

theorem iso_on_GMem {T : Tree} (f : Dom T → Dom T)
    (hi : IsStructIso T Dom.cA Dom.cB f)
    {n : ℕ} {F : Finset Node} (hF : ∀ σ ∈ F, σ ∈ level (STree T) n) :
    ∃ H, encIndex n H = encIndex n F ∧ (∀ σ ∈ H, σ ∈ level (STree T) n) ∧
      f (.vec n F) = .vec n (hOfIso f n ∆ H) := by
  have hfidx : ∀ k, f (.idx k) = .idx k :=
    fun k => hi.2.2.1 _ (by simp [isIndex])
  have h0 := iso_on_empty f hi n
  have hd : isD (.idx (encIndex n F)) (.vec n ∅ : Dom T) (.vec n F) := by
    refine ⟨encIndex n F, n, n, ∅, F, F, rfl, rfl, rfl, rfl, rfl, hF, ?_⟩
    rw [empty_symmDiff_fin]
  have hd' := (hi.2.2.2.2.2.2.1 _ _ _).1 hd
  rw [hfidx, h0] at hd'
  obtain ⟨HF, hHF⟩ : ∃ K, f (.vec n F) = .vec n K := by
    cases hfe : f (.vec n F) with
    | idx k =>
      have : isIndex (f (.vec n F)) := by rw [hfe]; trivial
      have : isIndex (.vec n F) := (hi.2.1 _).2 this
      simp [isIndex] at this
    | vec m K =>
      have hlv := hi.2.2.2.2.2.1 (.vec n F : Dom T)
      have hlv1 : Dom.levelOf (.vec n F : Dom T) = .idx n := rfl
      rw [hlv1, hfidx, hfe] at hlv
      have hlv2 : Dom.levelOf (.vec m K : Dom T) = .idx m := rfl
      rw [hlv2] at hlv
      simp at hlv
      subst hlv
      exact ⟨K, rfl⟩
  rw [hHF] at hd'
  obtain ⟨code, n', n'', G, G', H', hk', hF', hF'', hnn', hcode, hH', hdiff⟩ := hd'
  simp at hk' hF' hF''
  have hn : n = n' := hF'.1
  have hG : hOfIso f n = G := hF'.2
  have hn2 : n = n'' := hF''.1
  have hKG : HF = G' := hF''.2
  subst hn
  subst hn2
  subst hG
  subst hKG
  refine ⟨H', ?_, ?_, ?_⟩
  · have : encIndex n F = encIndex n H' := hk'.trans hcode
    exact this.symm
  · intro σ hσ
    exact hH' σ hσ
  · rw [hHF, hdiff]

theorem iso_root {T : Tree} (f : Dom T → Dom T)
    (hi : IsStructIso T Dom.cA Dom.cB f) : hOfIso f 0 = ({[]} : Finset Node) := by
  have hf := hi.2.2.2.2.2.2.2
  have hA : Dom.cA = (.vec 0 ∅ : Dom T) := rfl
  have hB : Dom.cB = (.vec 0 {[]} : Dom T) := rfl
  rw [hA, hB] at hf
  have h0 := iso_on_empty f hi 0
  rw [h0] at hf
  have hvec := hf
  have hfin := congrArg
    (fun x : Dom T => match x with | .vec _ H => H | .idx _ => ∅) hvec
  simpa using hfin

theorem iso_coherence {T : Tree} (f : Dom T → Dom T)
    (hi : IsStructIso T Dom.cA Dom.cB f) (n : ℕ) :
    proj T n (hOfIso f (n + 1)) = hOfIso f n := by
  have hp := hi.2.2.2.2.1 (.vec (n + 1) ∅ : Dom T)
  have h1 : Dom.projD (.vec (n + 1) ∅ : Dom T) = (.vec n ∅ : Dom T) := by
    show (Dom.vec n (proj T n ∅) : Dom T) = (Dom.vec n ∅)
    rw [proj_empty]
  rw [h1] at hp
  have h0 := iso_on_empty f hi n
  have h1' := iso_on_empty f hi (n + 1)
  rw [h1', h0] at hp
  have hfin := congrArg
    (fun x : Dom T => match x with | .vec _ H => H | .idx _ => ∅) hp
  simpa using hfin.symm

end Paper19
