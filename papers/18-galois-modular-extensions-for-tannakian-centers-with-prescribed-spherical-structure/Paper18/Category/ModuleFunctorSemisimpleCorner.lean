import Paper18.Category.ModuleFunctorSemisimpleCornerHom

/-! # Actual extension of strong module endofunctors along a coreflection -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.ModuleFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M] [MonoidalLeftAction C M]
  [∀ c : C, (MonoidalLeftAction.actionLeft M c).Additive]
  [∀ c : C, (MonoidalLeftAction.actionLeft M c).Linear ℂ]
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N] [MonoidalLeftAction C N]
  [∀ c : C, (MonoidalLeftAction.actionLeft N c).Additive]
  [∀ c : C, (MonoidalLeftAction.actionLeft N c).Linear ℂ]
  (I : Bundled C M N) [I.toFunctor.Full] [I.toFunctor.Faithful]
  (P : Bundled C N M) (adj : I.toFunctor ⊣ P.toFunctor)
  [IsModuleNatural C adj.unit] [IsModuleNatural C adj.counit]

/-- Genuine extension by the actual projection and inclusion. -/
def cornerExtension : Bundled C M M ⥤ Bundled C N N where
  obj F :=
    { toFunctor := (P.toFunctor ⋙ F.toFunctor) ⋙ I.toFunctor
      leftLinear := inferInstance
      additive := inferInstance
      linear := inferInstance }
  map τ := ⟨Functor.whiskerRight (Functor.whiskerLeft P.toFunctor τ.val) I.toFunctor,
    show IsModuleNatural C (Functor.whiskerRight
      (Functor.whiskerLeft P.toFunctor τ.val) I.toFunctor) from inferInstance⟩
  map_id F := by
    apply Subtype.ext
    ext n
    change I.toFunctor.map (𝟙 _) = 𝟙 _
    exact I.toFunctor.map_id _
  map_comp τ σ := by
    apply Subtype.ext
    ext n
    change I.toFunctor.map (τ.val.app (P.toFunctor.obj n) ≫ σ.val.app (P.toFunctor.obj n)) = _
    exact I.toFunctor.map_comp _ _

instance cornerExtension_additive : (cornerExtension I P).Additive where
  map_add := by
    intro F G τ σ
    apply Subtype.ext
    ext n
    exact I.toFunctor.map_add
instance cornerExtension_linear : (cornerExtension I P).Linear ℂ where
  map_smul τ z := by
    apply Subtype.ext
    ext n
    exact I.toFunctor.map_smul z _

def cornerExtension_faithful : (cornerExtension I P).Faithful where
  map_injective {F G} τ σ h := by
    apply Subtype.ext
    apply cornerPreWhisker_injective I.toFunctor P.toFunctor adj F.toFunctor G.toFunctor
    apply ((Functor.whiskeringRight N M N).obj I.toFunctor).map_injective
    exact congrArg (fun a => a.val) h

/-- Pull back the genuine target transformation, then restrict through the
actual coreflection unit. Every compatibility is derived by cancellation. -/
def cornerExtensionPreimage {F G : Bundled C M M}
    (τ : (cornerExtension I P).obj F ⟶ (cornerExtension I P).obj G) : F ⟶ G :=
  ⟨cornerPrePreimage I.toFunctor P.toFunctor adj F.toFunctor G.toFunctor
    (cornerPostPreimage I.toFunctor (P.toFunctor ⋙ F.toFunctor) (P.toFunctor ⋙ G.toFunctor) τ.val),
    show IsModuleNatural C (cornerPrePreimage I.toFunctor P.toFunctor adj F.toFunctor G.toFunctor
      (cornerPostPreimage I.toFunctor (P.toFunctor ⋙ F.toFunctor)
        (P.toFunctor ⋙ G.toFunctor) τ.val)) from inferInstance⟩

omit [IsModuleNatural C adj.counit] in
@[simp]
lemma cornerExtension_map_preimage {F G : Bundled C M M}
    (τ : (cornerExtension I P).obj F ⟶ (cornerExtension I P).obj G) :
    (cornerExtension I P).map (cornerExtensionPreimage I P adj τ) = τ := by
  apply Subtype.ext
  change Functor.whiskerRight (Functor.whiskerLeft P.toFunctor
    (cornerPrePreimage I.toFunctor P.toFunctor adj F.toFunctor G.toFunctor
      (cornerPostPreimage I.toFunctor (P.toFunctor ⋙ F.toFunctor)
        (P.toFunctor ⋙ G.toFunctor) τ.val))) I.toFunctor = τ.val
  rw [cornerPrePreimage_whisker]
  apply NatTrans.ext
  funext n
  exact I.toFunctor.map_preimage _

def cornerExtension_full : (cornerExtension I P).Full where
  map_surjective τ := ⟨cornerExtensionPreimage I P adj τ, cornerExtension_map_preimage I P adj τ⟩

/-- Actual full faithfulness of the genuine extension functor. -/
def cornerExtensionFullyFaithful : (cornerExtension I P).FullyFaithful := by
  letI := cornerExtension_faithful I P adj
  letI := cornerExtension_full I P adj
  exact Functor.FullyFaithful.ofFullyFaithful _

end Paper18.Category.ModuleFunctor
