import CounterFreeHDA.EffectiveSTImage

namespace CounterFreeHDA.Cubical.Effective
universe u v
variable {Lab : Type u} {k : ℕ} [Fintype Lab] [DecidableEq Lab]
attribute [local instance] faceFintype faceDecidableEq lowerDecidable upperDecidable
variable (C : FinCat.{u,v} (Cube Lab k)) (image : ∀ {U V}, Step U V → C.Hom U V)
    (K : ∀ {U V}, Finset (C.Hom U V))

/-- The finite context test uses only actually generated left/right images,
so unreachable arrows in the supplied category introduce no extra tests. -/
def ContextBelow {U V : Cube Lab k} (p q : C.Hom U V) : Prop :=
  ∀ (S T : Cube Lab k) (a : C.Hom S U) (b : C.Hom V T),
    (⟨U,a⟩ : ImageState C S) ∈ imageEnum C image S →
    (⟨T,b⟩ : ImageState C V) ∈ imageEnum C image V →
    C.comp (C.comp a q) b ∈ K (U := S) (V := T) → C.comp (C.comp a p) b ∈ K (U := S) (V := T)

instance contextBelowDecidable {U V : Cube Lab k} (p q : C.Hom U V) :
    Decidable (ContextBelow C image K p q) := by
  unfold ContextBelow
  refine @Fintype.decidableForallFintype _ _ (fun S => ?_) inferInstance
  refine @Fintype.decidableForallFintype _ _ (fun T => ?_) inferInstance
  refine @Fintype.decidableForallFintype _ _ (fun a => ?_) inferInstance
  refine @Fintype.decidableForallFintype _ _ (fun b => ?_) inferInstance
  infer_instance

variable (L : ∀ {U V : Cube Lab k}, Word U V → Prop)
    (recognises : ∀ {U V} (p : Word U V), L p ↔ wordImage C image p ∈ K)

include recognises in
/-- The executable finite context test is exactly the paper's syntactic
preorder quantified over all (unbounded) ST contexts. -/
theorem contextBelow_iff {U V : Cube Lab k} (p q : Word U V) :
    ContextBelow C image K (wordImage C image p) (wordImage C image q) ↔
      Recognition.Syntactic.Below (STCategory.category Lab k) L p q := by
  constructor
  · intro H S T a b hq
    apply (recognises _).mpr
    have hq' := (recognises _).mp hq
    change wordImage C image ((a.append q).append b) ∈ K at hq'
    change wordImage C image ((a.append p).append b) ∈ K
    simp only [STCategory.fold_append] at hq' ⊢
    exact H S T _ _ (imageEnum_complete C image a) (imageEnum_complete C image b) hq'
  · intro H S T a b ha hb hq
    obtain ⟨wa,hwa⟩ := (imageEnum_iff C image a).mp ha
    obtain ⟨wb,hwb⟩ := (imageEnum_iff C image b).mp hb
    have hq' : L ((wa.append q).append wb) := by
      apply (recognises _).mpr
      simpa only [STCategory.fold_append,hwa,hwb] using hq
    have hp := (recognises _).mp (H wa wb hq')
    change wordImage C image ((wa.append p).append wb) ∈ K at hp
    simpa only [STCategory.fold_append,hwa,hwb] using hp

/-- A constructive decision procedure for the contextual preorder; the
proof of correctness introduces no additional runtime input. -/
def belowDecision {U V : Cube Lab k} (p q : Word U V) :
    Decidable (Recognition.Syntactic.Below (STCategory.category Lab k) L p q) :=
  decidable_of_iff (ContextBelow C image K (wordImage C image p) (wordImage C image q))
    (contextBelow_iff C image K L recognises p q)

end CounterFreeHDA.Cubical.Effective
