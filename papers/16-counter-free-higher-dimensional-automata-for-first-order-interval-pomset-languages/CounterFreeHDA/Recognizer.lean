import CounterFreeHDA.Category

/-! The ordered syntactic category, Lemma 2.1.  The source category is not
assumed finite.  Its finite quotient is constructed from contextual language
inclusion, using a given finite recognising functor only to prove finiteness
and the exponent law. -/

namespace CounterFreeHDA
namespace Recognition

universe u v w z

structure Cat (O : Type u) where
  Hom : O → O → Type v
  id : ∀ U, Hom U U
  comp : ∀ {U V W}, Hom U V → Hom V W → Hom U W
  id_comp : ∀ {U V} (p : Hom U V), comp (id U) p = p
  comp_id : ∀ {U V} (p : Hom U V), comp p (id V) = p
  assoc : ∀ {U V W Z} (p : Hom U V) (q : Hom V W) (r : Hom W Z),
    comp (comp p q) r = comp p (comp q r)

namespace Cat

def pow {O : Type u} (A : Cat.{u,v} O) {U : O} (p : A.Hom U U) : ℕ → A.Hom U U
  | 0 => A.id U
  | n + 1 => A.comp (A.pow p n) p

end Cat

def ofFinite {O : Type u} (D : FinCat.{u,v} O) : Cat O where
  Hom := D.Hom
  id := D.id
  comp := D.comp
  id_comp := D.id_comp
  comp_id := D.comp_id
  assoc := D.assoc

structure Functor {O : Type u} {O' : Type w} (A : Cat.{u,v} O) (D : Cat.{w,z} O') where
  obj : O → O'
  map : ∀ {U V}, A.Hom U V → D.Hom (obj U) (obj V)
  map_id : ∀ U, map (A.id U) = D.id (obj U)
  map_comp : ∀ {U V W} (p : A.Hom U V) (q : A.Hom V W),
    map (A.comp p q) = D.comp (map p) (map q)

namespace Syntactic

variable {O : Type u} (A : Cat.{u,v} O)
variable (L : ∀ {U V}, A.Hom U V → Prop)

/-- Equation (2), with all contexts represented in the original category. -/
def Below {U V} (p q : A.Hom U V) : Prop :=
  ∀ {S T} (a : A.Hom S U) (b : A.Hom V T),
    L (A.comp (A.comp a q) b) → L (A.comp (A.comp a p) b)

theorem below_refl {U V} (p : A.Hom U V) : Below A L p p := fun {_ _} _ _ h => h

theorem below_trans {U V} {p q r : A.Hom U V}
    (hpq : Below A L p q) (hqr : Below A L q r) : Below A L p r :=
  fun {_ _} a b h => hpq a b (hqr a b h)

theorem below_comp {U V W} {p p' : A.Hom U V} {q q' : A.Hom V W}
    (hp : Below A L p p') (hq : Below A L q q') :
    Below A L (A.comp p q) (A.comp p' q') := by
  intro S T a b h
  have hq' := hq (A.comp a p') b
  have hp' := hp a (A.comp q b)
  simp only [A.assoc] at h hq' hp' ⊢
  exact hp' (hq' h)

def equiv {U V} : Setoid (A.Hom U V) where
  r p q := Below A L p q ∧ Below A L q p
  iseqv := ⟨fun p => ⟨below_refl A L p, below_refl A L p⟩,
    fun h => ⟨h.2, h.1⟩,
    fun h h' => ⟨below_trans A L h.1 h'.1, below_trans A L h'.2 h.2⟩⟩

abbrev Arrow (U V : O) := Quotient (equiv A L (U := U) (V := V))

def qcomp {U V W} (p : Arrow A L U V) (q : Arrow A L V W) : Arrow A L U W :=
  Quotient.liftOn₂ p q (fun p q => Quotient.mk _ (A.comp p q)) (by
    intro p p' q q' hp hq
    exact Quotient.sound ⟨below_comp A L hp.1 hq.1, below_comp A L hp.2 hq.2⟩)

def qle {U V} (p q : Arrow A L U V) : Prop :=
  Quotient.liftOn₂ p q (Below A L) (by
    intro p p' q q' hp hq
    apply propext
    exact ⟨fun h => below_trans A L hp.2 (below_trans A L h hq.1),
      fun h => below_trans A L hp.1 (below_trans A L h hq.2)⟩)

def accepted {U V} (p : Arrow A L U V) : Prop :=
  Quotient.liftOn p (fun p => L p) (by
    intro p q h
    apply propext
    have h₁ := h.1 (A.id U) (A.id V)
    have h₂ := h.2 (A.id U) (A.id V)
    simpa only [A.id_comp, A.comp_id] using Iff.intro h₂ h₁)

variable {O' : Type w} (D : FinCat.{w,z} O')
variable (G : Functor A (ofFinite D))
variable (K : ∀ {U V}, D.Hom U V → Prop)
variable (recognises : ∀ {U V} (p : A.Hom U V), L p ↔ K (G.map p))

include recognises in
theorem equivalent_of_image_eq {U V} {p q : A.Hom U V} (h : G.map p = G.map q) :
    (equiv A L).r p q := by
  have key : ∀ {S T} (a : A.Hom S U) (b : A.Hom V T),
      L (A.comp (A.comp a p) b) ↔ L (A.comp (A.comp a q) b) := by
    intro S T a b
    rw [recognises, recognises, G.map_comp, G.map_comp, G.map_comp, G.map_comp, h]
  exact ⟨fun {_ _} a b => (key a b).mpr, fun {_ _} a b => (key a b).mp⟩

noncomputable def imageRepresentative {U V}
    (d : Set.range (G.map (U := U) (V := V))) : A.Hom U V :=
  Classical.choose d.property

theorem imageRepresentative_spec {U V}
    (d : Set.range (G.map (U := U) (V := V))) :
    G.map (imageRepresentative A D G d) = d.val := Classical.choose_spec d.property

include recognises in
/-- Finiteness comes from the original recogniser, not an assumed finite source. -/
theorem finite_arrow (U V : O) : Finite (Arrow A L U V) := by
  classical
  letI : Fintype ((ofFinite D).Hom (G.obj U) (G.obj V)) := D.homFintype _ _
  let f : Set.range (G.map (U := U) (V := V)) → Arrow A L U V :=
    fun d => Quotient.mk _ (imageRepresentative A D G d)
  apply Finite.of_surjective f
  intro q
  induction q using Quotient.inductionOn with
  | _ p =>
    refine ⟨⟨G.map p, ⟨p, rfl⟩⟩, ?_⟩
    apply Quotient.sound
    apply equivalent_of_image_eq A L D G K recognises
    exact imageRepresentative_spec A D G _

noncomputable def category : FinCat O where
  Hom := Arrow A L
  homFintype U V := by
    letI := finite_arrow A L D G K recognises U V
    exact Fintype.ofFinite _
  homDecEq _ _ := Classical.decEq _
  id U := Quotient.mk _ (A.id U)
  comp := qcomp A L
  id_comp p := by
    induction p using Quotient.inductionOn with
    | _ p => change Quotient.mk _ (A.comp (A.id _) p) = _; rw [A.id_comp]
  comp_id p := by
    induction p using Quotient.inductionOn with
    | _ p => change Quotient.mk _ (A.comp p (A.id _)) = _; rw [A.comp_id]
  assoc p q r := by
    induction p using Quotient.inductionOn with
    | _ p =>
      induction q using Quotient.inductionOn with
      | _ q =>
        induction r using Quotient.inductionOn with
        | _ r => change Quotient.mk _ (A.comp (A.comp p q) r) = Quotient.mk _ (A.comp p (A.comp q r)); rw [A.assoc]

noncomputable def order : (category A L D G K recognises).IsOrdered where
  homLE := qle A L
  homLE_refl p := by
    induction p using Quotient.inductionOn with
    | _ p => exact below_refl A L p
  homLE_trans := by
    intro U V p q r
    induction p using Quotient.inductionOn with
    | _ p =>
      induction q using Quotient.inductionOn with
      | _ q =>
        induction r using Quotient.inductionOn with
        | _ r => exact below_trans A L
  homLE_antisymm := by
    intro U V p q
    induction p using Quotient.inductionOn with
    | _ p =>
      induction q using Quotient.inductionOn with
      | _ q => exact fun h h' => Quotient.sound ⟨h, h'⟩
  comp_mono_left := by
    intro U V W p p' q
    induction p using Quotient.inductionOn with
    | _ p =>
      induction p' using Quotient.inductionOn with
      | _ p' =>
        induction q using Quotient.inductionOn with
        | _ q => exact fun hp => below_comp A L hp (below_refl A L q)
  comp_mono_right := by
    intro U V W p q q'
    induction p using Quotient.inductionOn with
    | _ p =>
      induction q using Quotient.inductionOn with
      | _ q =>
        induction q' using Quotient.inductionOn with
        | _ q' => exact below_comp A L (below_refl A L p)

noncomputable def quotientFunctor : Functor A (ofFinite (category A L D G K recognises)) where
  obj := id
  map p := Quotient.mk _ p
  map_id _ := rfl
  map_comp _ _ := rfl

theorem accepted_lower {U V} {p q : Arrow A L U V}
    (hq : accepted A L q) (hpq : qle A L p q) : accepted A L p := by
  induction p using Quotient.inductionOn with
  | _ p =>
    induction q using Quotient.inductionOn with
    | _ q =>
      have h := hpq (A.id U) (A.id V)
      simpa only [A.id_comp, A.comp_id] using h (by simpa only [A.id_comp, A.comp_id] using hq)

theorem quotient_pow {U} (p : A.Hom U U) (n : ℕ) :
    FinCat.pow (C := category A L D G K recognises) (Quotient.mk _ p) n =
      Quotient.mk _ (A.pow p n) := by
  induction n with
  | zero => rfl
  | succ n ih => change qcomp A L _ _ = _; rw [ih]; rfl

theorem map_pow {U} (p : A.Hom U U) (n : ℕ) :
    G.map (A.pow p n) = D.pow (G.map p) n := by
  induction n with
  | zero => exact G.map_id U
  | succ n ih => change G.map (A.comp _ _) = _; rw [G.map_comp, ih]; rfl

theorem aperiodic {h : ℕ} (hD : D.AperiodicExponent h) :
    (category A L D G K recognises).AperiodicExponent h := by
  intro U p
  induction p using Quotient.inductionOn with
  | _ p =>
    rw [quotient_pow, quotient_pow]
    apply Quotient.sound
    apply equivalent_of_image_eq A L D G K recognises
    rw [map_pow, map_pow]
    exact hD (G.obj U) (G.map p)

/-- Lemma 2.1(d): contextual monotonicity follows from gluing compatibility
and downward closure.  No compatibility of the original recogniser with
subsumption is assumed. -/
theorem monotone_of_downward
    (sub : ∀ {U V}, A.Hom U V → A.Hom U V → Prop)
    (sub_context : ∀ {U V S T} {p q : A.Hom U V}, sub p q →
      ∀ (a : A.Hom S U) (b : A.Hom V T),
        sub (A.comp (A.comp a p) b) (A.comp (A.comp a q) b))
    (downward : ∀ {U V} {p q : A.Hom U V}, sub p q → L q → L p)
    {U V} {p q : A.Hom U V} (hpq : sub p q) :
    qle A L (Quotient.mk _ p) (Quotient.mk _ q) := by
  intro S T a b h
  exact downward (sub_context hpq a b) h

end Syntactic

/-- The output vocabulary of Lemma 2.1; every field is constructed below. -/
structure OrderedRecognizer {O : Type u} (A : Cat.{u,v} O)
    (L : ∀ {U V}, A.Hom U V → Prop)
    (sub : ∀ {U V}, A.Hom U V → A.Hom U V → Prop) (h : ℕ) where
  C : FinCat.{u,v} O
  order : C.IsOrdered
  map : ∀ {U V}, A.Hom U V → C.Hom U V
  map_id : ∀ U, map (A.id U) = C.id U
  map_comp : ∀ {U V W} (p : A.Hom U V) (q : A.Hom V W),
    map (A.comp p q) = C.comp (map p) (map q)
  J : ∀ {U V}, Set (C.Hom U V)
  recognises : ∀ {U V} (p : A.Hom U V), L p ↔ map p ∈ J
  lower : ∀ U V, IsLowerSet order.homLE (J (U := U) (V := V))
  monotone : ∀ {U V} {p q : A.Hom U V}, sub p q → order.homLE (map p) (map q)
  aperiodic : C.AperiodicExponent h

/-- **Lemma 2.1**, the ordered recogniser constructed from the given finite
recognising functor. The only language hypotheses are downward closure and
compatibility of subsumption with contexts. In particular, the recognising
functor may identify objects and need not preserve any order. -/
noncomputable def lemma_2_1
    {O : Type u} (A : Cat.{u,v} O)
    (L : ∀ {U V}, A.Hom U V → Prop)
    (sub : ∀ {U V}, A.Hom U V → A.Hom U V → Prop)
    (sub_context : ∀ {U V S T} {p q : A.Hom U V}, sub p q →
      ∀ (a : A.Hom S U) (b : A.Hom V T),
        sub (A.comp (A.comp a p) b) (A.comp (A.comp a q) b))
    (downward : ∀ {U V} {p q : A.Hom U V}, sub p q → L q → L p)
    {O' : Type w} (D : FinCat.{w,z} O') (G : Functor A (ofFinite D))
    (K : ∀ {U V}, Set (D.Hom U V))
    (recognises : ∀ {U V} (p : A.Hom U V), L p ↔ G.map p ∈ K)
    {h : ℕ} (hD : D.AperiodicExponent h) : OrderedRecognizer A L sub h where
  C := Syntactic.category A L D G (fun p => p ∈ K) recognises
  order := Syntactic.order A L D G (fun p => p ∈ K) recognises
  map p := Quotient.mk _ p
  map_id _ := rfl
  map_comp _ _ := rfl
  J := {p | Syntactic.accepted A L p}
  recognises _ := Iff.rfl
  lower _ _ := fun _ _ hq hpq => Syntactic.accepted_lower A L hq hpq
  monotone := Syntactic.monotone_of_downward A L sub sub_context downward
  aperiodic := Syntactic.aperiodic A L D G (fun p => p ∈ K) recognises hD

end Recognition
end CounterFreeHDA
