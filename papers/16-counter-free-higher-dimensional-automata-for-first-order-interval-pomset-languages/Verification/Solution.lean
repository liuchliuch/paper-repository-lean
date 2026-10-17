import CounterFreeHDA

universe u v w z
open CounterFreeHDA CounterFreeHDA.Cubical CounterFreeHDA.LowerSetAction
noncomputable section
namespace Verification

theorem lemma_2_2 {Obj : Type u} {C : FinCat Obj} (ord : C.IsOrdered)
    {S U V W : Obj} (I : Set (C.Hom S U))
    (hI : IsLowerSet (fun x y => ord.homLE x y) I)
    (P : C.Hom U V) (Q : C.Hom V W) :
    act ord I (C.id U) = I ∧
    act ord (act ord I P) Q = act ord I (C.comp P Q) ∧
    (∀ {ι : Type*} (f : ι → Set (C.Hom S U)),
        act ord (⋃ i, f i) P = ⋃ i, act ord (f i) P) ∧
    (∀ {P' Q' : C.Hom U V}, ord.homLE P' Q' → act ord I P' ⊆ act ord I Q') :=
  CounterFreeHDA.Paper.lemma_2_2 ord I hI P Q

theorem lemma_3_2 {V : Type u} {G : AcyclicDigraph V}
    {A : V → Type v} [∀ v, CompleteLattice (A v)]
    (f : ∀ ⦃x y : V⦄, G.arc x y → JoinHom (A x) (A y))
    (B : Set V) (aB : ∀ v, A v) :
    (∃ a : ∀ v, A v, (∀ v ∈ B, a v = aB v) ∧
        (∀ ⦃x y⦄ (e : G.arc x y), (f e).toFun (a x) ≤ a y)) ↔
      (∀ ⦃x y⦄ (p : AcyclicDigraph.Path G x y), x ∈ B → y ∈ B →
        pathApply f p (aB x) ≤ aB y) :=
  CounterFreeHDA.lemma_3_2 f B aB

theorem lemma_3_3 {Lab : Type u} {k : ℕ}
    (C : FinCat.{u,v} (Cube Lab k)) (ord : C.IsOrdered)
    (image : ∀ {U V}, Step U V → C.Hom U V)
    (X : Precubical.{u,w} Lab k) (S : Cube Lab k) :
    Nonempty (Map X (ideal C ord image S) ≃ Coloring C ord image X S) :=
  ⟨CounterFreeHDA.Cubical.lemma_3_3 C ord image X S⟩

theorem face_extension {Lab : Type u} {k : ℕ}
    (C : FinCat.{u,v} (Cube Lab k)) (ord : C.IsOrdered)
    (image : ∀ {U V}, Step U V → C.Hom U V)
    (X : Precubical.{u,w} Lab k) (S : Cube Lab k)
    (B : ∀ U, Set (X.Cell U)) (aB : ∀ U, X.Cell U → Set (C.Hom S U))
    (lowerB : ∀ U (x : X.Cell U), IsLowerSet ord.homLE (aB U x)) :
    (∃ m : Map X (ideal C ord image S),
      ∀ U (x : X.Cell U), x ∈ B U → (m.app x).top = aB U x) ↔
    BoundaryCompatible C ord image X S B aB :=
  CounterFreeHDA.Cubical.exists_extending_map_iff C ord image X S B aB lowerB

theorem gluing {Lab : Type u} {P Q : PomsetData Lab}
    (m : GlueMatch P Q) (hP : IsIntervalPom P) (hQ : IsIntervalPom Q) :
    IsIntervalPom (glueData P Q m) :=
  CounterFreeHDA.glueData_isIntervalPom m hP hQ

theorem corner {Lab : Type u} (P : PomsetData Lab)
    (α : Fin P.srcLen → Status) (β : Fin P.tgtLen → Status)
    (hP : IsIntervalPom P) (hc : Corners.Compatible P α β) :
    IsIntervalPom (Corners.data P α β hc) :=
  CounterFreeHDA.Corners.isIntervalPom P α β hP hc

theorem lemma_4_1_actual {Lab : Type u} {U : Interface Lab}
    (P : EndoPom U) {k n : ℕ} (hk : U.1 ≤ k) (hn : k ≤ n) (i j : Fin U.1) :
    (P.pow n).Shared i j ↔ i = j ∧ P.Shared i i :=
  CounterFreeHDA.EndoPom.lemma_4_1_actual P hk hn i j

theorem lemma_4_2_actual {Lab : Type u} {U : Interface Lab}
    (P : EndoPom U) {k n : ℕ} (hk : U.1 ≤ k) (hproper : U.1 < P.pom.n) (hn : k+1 ≤ n) :
    ∃ e : Fin (P.pow n).pom.n,
      ¬ (P.pow n).pom.val.inSrc e ∧ ¬ (P.pow n).pom.val.inTgt e :=
  CounterFreeHDA.lemma_4_2_actual P hk hproper hn

theorem actual_power_size {Lab : Type u} {U : Interface Lab}
    (P : EndoPom U) (n : ℕ) :
    (P.pow n).pom.n = U.1 + n * (P.pom.n - U.1) :=
  CounterFreeHDA.EndoPom.size_pow P n

theorem appendix_original {a : Fin 3}
    {r : Appendix.BRel (Appendix.size a) (Appendix.size a)}
    (h : Appendix.Generated (a := a) (b := a) r) : Appendix.pow r 3 = Appendix.pow r 4 :=
  CounterFreeHDA.Appendix.original_counter_free h

theorem appendix_residual :
    ¬ ∃ N, 1 ≤ N ∧ Appendix.pow Appendix.residualA N = Appendix.pow Appendix.residualA (N+1) :=
  CounterFreeHDA.Appendix.residual_not_counter_free

theorem lemma_4_2_full {Lab : Type u} {U : Interface Lab}
    (P : EndoPom U) (hne : ¬ IntervalPomIso P.pom (identityPom Lab U.1 U.2))
    {k n : ℕ} (hk : U.1 ≤ k) (hn : k+1 ≤ n) :
    ∃ e : Fin (P.pow n).pom.n,
      ¬ (P.pow n).pom.val.inSrc e ∧ ¬ (P.pow n).pom.val.inTgt e :=
  CounterFreeHDA.EndoPom.lemma_4_2_full P hne hk hn

theorem remark_2_4 {Lab : Type u} [Fintype Lab] {k : ℕ}
    (C : FinCat.{u,v} (Cube Lab k)) (ord : C.IsOrdered)
    (image : ∀ {U V}, Step U V → C.Hom U V)
    (J : ∀ {S U}, Set (C.Hom S U)) :
    Fintype.card (Σ U, (idealHDA C ord image J).Cell U) ≤
      (Fintype.card (Cube Lab k)) ^ 2 * 2 ^ (Fintype.card (AllMor C) * 3 ^ k) :=
  CounterFreeHDA.Cubical.remark_2_4 C ord image J

theorem lemma_2_1_general
    {O : Type u} (A : Recognition.Cat.{u,v} O)
    (L : ∀ {U V}, A.Hom U V → Prop)
    (sub : ∀ {U V}, A.Hom U V → A.Hom U V → Prop)
    (sub_context : ∀ {U V S T} {p q : A.Hom U V}, sub p q →
      ∀ (a : A.Hom S U) (b : A.Hom V T),
        sub (A.comp (A.comp a p) b) (A.comp (A.comp a q) b))
    (downward : ∀ {U V} {p q : A.Hom U V}, sub p q → L q → L p)
    {O' : Type w} (D : FinCat.{w,z} O') (G : Recognition.Functor A (Recognition.ofFinite D))
    (K : ∀ {U V}, Set (D.Hom U V))
    (recognises : ∀ {U V} (p : A.Hom U V), L p ↔ G.map p ∈ K)
    {h : ℕ} (hD : D.AperiodicExponent h) :
    Nonempty (Recognition.OrderedRecognizer A L sub h) :=
  ⟨Recognition.lemma_2_1 A L sub sub_context downward D G K recognises hD⟩

theorem st_representation {Lab : Type u} {k : ℕ}
    (P : PomsetData Lab) (hP : IsIntervalPom P) (hw : P.WidthLE k) :
    STRepresented (k := k) P :=
  CounterFreeHDA.Cubical.st_representation P hP hw

theorem lemma_3_1_b {Lab : Type u} {k : ℕ}
    {U V : Cube Lab k} {Y : Precubical.{u,v} Lab k}
    (A : Arrow U V) (hw : A.pom.val.WidthLE k) (x : Y.Cell U) (y : Y.Cell V) :
    y ∈ Y.dPom x A.pom ↔ ∃ a : Map (track A.pom.val) Y,
      a.app A.sourceCell = x ∧ a.app A.targetCell = y :=
  CounterFreeHDA.Cubical.Arrow.lemma_3_1_b A hw x y

theorem gluing_iso {Lab : Type u} {P P' Q Q' : PomsetData Lab}
    (φ : PomsetIso P P') (ψ : PomsetIso Q Q') (m : GlueMatch P Q) (m' : GlueMatch P' Q') :
    Nonempty (PomsetIso (glueData P Q m) (glueData P' Q' m')) :=
  ⟨PomsetIso.glueIso φ ψ m m'⟩

theorem lemma_3_1_a {Lab : Type u} {k : ℕ} {U V : Cube Lab k}
    (A B : Arrow U V) (hw : A.pom.val.WidthLE k) :
    B.targetCell ∈ (track B.pom.val).dPom B.sourceCell A.pom ↔ A.pom ⊑ₛ B.pom :=
  CounterFreeHDA.Cubical.Arrow.lemma_3_1_a A B hw

theorem lemma_3_5_compatible {Lab : Type u} {k : ℕ}
    (P : PomsetData Lab) (hP : IsIntervalPom P) (hs : P.srcLen ≤ k) (ht : P.tgtLen ≤ k)
    {U V : Cube Lab k} (α : Face U (sourceCube P hs)) (β : Face V (targetCube P ht))
    (hc : Corners.Compatible P α.status β.status) (A : Arrow U V) (hw : A.pom.val.WidthLE k) :
    ((tau P hP ht).face β) ∈ (track P).dPom ((iota P hP hs).face α) A.pom ↔
      A.pom ⊑ₛ (CornerFaces.arrow P hP hs ht α β hc).pom :=
  CounterFreeHDA.Cubical.lemma_3_5_compatible P hP hs ht α β hc A hw

theorem word_label_width {Lab : Type u} {k : ℕ}
    {U V : Cube Lab k} (p : Word U V) : p.label.pom.val.WidthLE k :=
  CounterFreeHDA.Cubical.Word.label_width p

theorem lemma_2_1_actual {Lab : Type u} {k h : ℕ}
    {L : Set (IntervalPom Lab)} (G : FinitePomsetRecognizer.{u,v} (k := k) L h)
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L) :
    Nonempty (OrderedPomsetRecognizer.{u,u} (k := k) L h) :=
  ⟨G.ordered downward⟩

theorem proposition_3_4 {Lab : Type u} {k h : ℕ} {L : Set (IntervalPom Lab)}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h)
    (withinWidth : ∀ P ∈ L, P.val.WidthLE k) : F.hda.LangPom = L :=
  F.language_eq withinWidth

theorem proposition_3_6 {Lab : Type u} {k h : ℕ} {L : Set (IntervalPom Lab)}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h) (P : PomsetData Lab) (hP : IsIntervalPom P)
    (hw : P.WidthLE k) (hs : P.srcLen ≤ k) (ht : P.tgtLen ≤ k) {S : Cube Lab k}
    (x : IdealDiagram F.C F.order F.stepImage S (sourceCube P hs))
    (y : IdealDiagram F.C F.order F.stepImage S (targetCube P ht))
    (hint : ∃ e, ¬ P.inSrc e ∧ ¬ P.inTgt e) :
    y ∈ (ideal F.C F.order F.stepImage S).dPom x ⟨P,hP⟩ ↔ Endpoint.Criterion F P hP hs ht x y hw :=
  Endpoint.lemma_3_6 F P hP hw hs ht x y hint

theorem actual_gluing_assoc {Lab : Type u} {k : ℕ} {U V W Z : Cube Lab k}
    (A : BoundedArrow U V) (B : BoundedArrow V W) (C : BoundedArrow W Z) :
    Nonempty (PomsetIso ((A.comp B).comp C).pom.val (A.comp (B.comp C)).pom.val) :=
  ⟨BoundedArrow.assocIso A B C⟩

theorem actual_gluing_subsumption {Lab : Type u} {k : ℕ} {U V W : Cube Lab k}
    (A A' : BoundedArrow U V) (B B' : BoundedArrow V W)
    (ha : A.pom ⊑ₛ A'.pom) (hb : B.pom ⊑ₛ B'.pom) : (A.comp B).pom ⊑ₛ (A'.comp B').pom :=
  BoundedArrow.subsumption_comp A A' B B' ha hb

theorem actual_power_blocks {Lab : Type u} {k : ℕ} {U : Cube Lab k}
    (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE k) (n : ℕ) (hn : 2*k ≤ n) :
    Nonempty (PomsetIso (((P.boundedPower hw k).comp (P.boundedPower hw (n-2*k))).comp (P.boundedPower hw k)).pom.val
      (P.pow n).pom.val) :=
  ⟨P.powerBlockIso hw n hn⟩

theorem lemma_4_3 {Lab : Type u} {k : ℕ} {U A B : Cube Lab k}
    (P : EndoPom (cubeInterface U)) (α : Face A U) (β : Face B U)
    (hc : P.StableCompatible α β) (hw : P.pom.val.WidthLE k) (n : ℕ) (hn : 2*k ≤ n) :
    Nonempty (PomsetIso (((P.leftFactor α β hc hw).comp
      ((P.boundaryReduced α β hw).boundedPower (P.boundaryReduced_width α β hw) (n-2*k))).comp
      (P.rightFactor α β hc hw)).pom.val
      ((P.boundedPower hw n).toArrow.corner (P.width_pow hw n) α β
        (P.power_compatible α β hc hw (by omega))).pom.val) :=
  ⟨P.lemma_4_3 α β hc hw n hn⟩

theorem corollary_4_4 {Lab : Type u} {k h : ℕ} {L : Set (IntervalPom Lab)}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h) {U A B : Cube Lab k}
    (P : EndoPom (cubeInterface U)) (hw : P.pom.val.WidthLE k)
    (α : Face A U) (β : Face B U) (hc : P.StableCompatible α β)
    (n : ℕ) (hn : 2*k+h ≤ n) :
    F.map ((P.boundedPower hw n).toArrow.corner (P.width_pow hw n) α β
      (P.power_compatible α β hc hw (by omega))) =
    F.map ((P.boundedPower hw (n+1)).toArrow.corner (P.width_pow hw (n+1)) α β
      (P.power_compatible α β hc hw (by omega))) :=
  F.corollary_4_4 P hw α β hc n hn

theorem full_power_stable {Lab : Type u} {k h : ℕ} {L : Set (IntervalPom Lab)}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h) {U : Cube Lab k}
    (P : EndoPom (cubeInterface U)) (x y : F.hda.Cell U) (n : ℕ)
    (hn : 2*k+h ≤ n) (hi : k+1 ≤ n) :
    y ∈ F.hda.toPrecubical.dPom x (P.pow n).pom ↔
    y ∈ F.hda.toPrecubical.dPom x (P.pow (n+1)).pom :=
  F.full_power_stable P x y n hn hi

theorem counter_free_actual_hda {Lab : Type u} {k h : ℕ} {L : Set (IntervalPom Lab)}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h) : F.hda.toPrecubical.CounterFreePom :=
  F.counterFreePom

theorem theorem_1_1 {Lab : Type u} [Fintype Lab] {k h : ℕ} {L : Set (IntervalPom Lab)}
    (G : FinitePomsetRecognizer.{u,v} (k := k) L h)
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L)
    (withinWidth : ∀ P ∈ L, P.val.WidthLE k) :
    ∃ X : HDA.{u,u} Lab k, Finite (Σ U, X.Cell U) ∧ X.LangPom = L ∧ X.toPrecubical.CounterFreePom :=
  CounterFreeHDA.Cubical.theorem_1_1_core G downward withinWidth

theorem theorem_1_1_uniform {Lab : Type u} [Fintype Lab] {k h : ℕ} {L : Set (IntervalPom Lab)}
    (G : FinitePomsetRecognizer.{u,v} (k := k) L h) (hh : 1 ≤ h)
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L) (withinWidth : ∀ P ∈ L, P.val.WidthLE k) :
    ∃ X : HDA.{u,u} Lab k, Finite (Σ U, X.Cell U) ∧ X.LangPom = L ∧ X.toPrecubical.CounterFreePom ∧
      ∀ n, 2*k+h ≤ n → ∀ (U : Cube Lab k) (x : X.Cell U) (P : EndoPom (cubeInterface U)),
        X.toPrecubical.dPom (V := U) x (P.pow n).pom = X.toPrecubical.dPom x (P.pow (n+1)).pom :=
  CounterFreeHDA.Cubical.theorem_1_1 G hh downward withinWidth

theorem effective_realization {Lab : Type u} [Fintype Lab] [DecidableEq Lab]
    {k h : ℕ} {L : Set (IntervalPom Lab)} (G : FinitePomsetRecognizer.{u,v} (k := k) L h)
    (image : ∀ {U V}, Step U V → G.D.Hom U V) (himage : ∀ {U V} (s : Step U V), image s = G.stepImage s)
    (K : ∀ {U V}, Finset (G.D.Hom U V)) (hK : ∀ {U V} (a : G.D.Hom U V), a ∈ K ↔ a ∈ G.K)
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L) (withinWidth : ∀ P ∈ L, P.val.WidthLE k) :
    Finite (Σ U, (Effective.tableHDA G.D image K).Cell U) ∧ (Effective.tableHDA G.D image K).LangPom = L ∧
      (Effective.tableHDA G.D image K).toPrecubical.CounterFreePom :=
  G.effective_realization image himage K hK downward withinWidth

theorem effective_cell_codes {Lab : Type u} [Fintype Lab] [DecidableEq Lab] {k : ℕ}
    (C : FinCat.{u,v} (Cube Lab k)) (image : ∀ {U V}, Step U V → C.Hom U V)
    (K : ∀ {U V}, Finset (C.Hom U V)) (U : Cube Lab k) :
    Function.Bijective (Effective.decodeCell C image K (U := U)) :=
  Effective.decodeCell_bijective C image K U

theorem effective_generated_image {Lab : Type u} [Fintype Lab] [DecidableEq Lab] {k : ℕ}
    (C : FinCat.{u,v} (Cube Lab k)) (image : ∀ {U V}, Step U V → C.Hom U V)
    {U V : Cube Lab k} (a : C.Hom U V) :
    (⟨V,a⟩ : Effective.ImageState C U) ∈ Effective.imageEnum C image U ↔ ∃ p : Word U V, wordImage C image p = a :=
  Effective.imageEnum_iff C image a

theorem effective_context_tests {Lab : Type u} [Fintype Lab] [DecidableEq Lab] {k : ℕ}
    (C : FinCat.{u,v} (Cube Lab k)) (image : ∀ {U V}, Step U V → C.Hom U V)
    (K : ∀ {U V}, Finset (C.Hom U V)) (L : ∀ {U V : Cube Lab k}, Word U V → Prop)
    (recognises : ∀ {U V} (p : Word U V), L p ↔ wordImage C image p ∈ K)
    {U V : Cube Lab k} (p q : Word U V) :
    Effective.ContextBelow C image K (wordImage C image p) (wordImage C image q) ↔
      Recognition.Syntactic.Below (STCategory.category Lab k) L p q :=
  Effective.contextBelow_iff C image K L recognises p q

theorem appendix_actual_original : Appendix.Actual.originalHDA.toPrecubical.CounterFreePom :=
  Appendix.Actual.original_counterFreePom

theorem appendix_completion_counter : ¬ Appendix.Completion.completionHDA.toPrecubical.CounterFreePom :=
  Appendix.Completion.completion_not_counterFreePom

theorem appendix_actual_language_eq :
    Appendix.Actual.originalHDA.LangPom = Appendix.Completion.completionHDA.LangPom :=
  Appendix.Compare.actual_language_equality

theorem appendix_eight_cells : Fintype.card (Σ U, Appendix.Actual.originalHDA.Cell U) = 8 :=
  Appendix.Actual.eight_cells

theorem appendix_ten_cells : Fintype.card (Σ U, Appendix.Completion.completionHDA.Cell U) = 10 :=
  Appendix.Completion.ten_cells

theorem corollary_1_2_new {Lab : Type u} [Fintype Lab] {k : ℕ} {L : Set (IntervalPom Lab)}
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L) (withinWidth : ∀ P ∈ L, P.val.WidthLE k)
    (hL : AperiodicallyRecognisable (k := k) L) : CounterFreeRecognisable (k := k) L :=
  CounterFreeHDA.Cubical.corollary_1_2_new_direction downward withinWidth hL

theorem first_order_iso {Lab : Type u} {P Q : PomsetData Lab} (e : PomsetIso P Q)
    {n : ℕ} (φ : FirstOrder.Formula Lab n) (ρ : Fin n → Fin P.n) :
    φ.Holds Q (e.toEquiv ∘ ρ) ↔ φ.Holds P ρ :=
  FirstOrder.Formula.holds_iso e φ ρ

theorem original_functor_realization {Lab : Type u} [Fintype Lab]
    {k h : ℕ} {L : Set (IntervalPom Lab)} {O : Type v} (D : FinCat.{v,w} O)
    (G : Recognition.Functor (PomsetCategory.category Lab k) (Recognition.ofFinite D))
    (K : ∀ {U V}, Set (D.Hom U V))
    (recognises : ∀ {U V} (A : BoundedArrow U V), A.pom ∈ L ↔ G.map (PomsetCategory.mk A) ∈ K)
    (hD : D.AperiodicExponent h) (hh : 1 ≤ h)
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L) (withinWidth : ∀ P ∈ L, P.val.WidthLE k) :
    ∃ X : HDA.{u,u} Lab k, Finite (Σ U, X.Cell U) ∧ X.LangPom = L ∧ X.toPrecubical.CounterFreePom ∧
      ∀ n, 2*k+h ≤ n → ∀ (U : Cube Lab k) (x : X.Cell U) (P : EndoPom (cubeInterface U)),
        X.toPrecubical.dPom (V := U) x (P.pow n).pom = X.toPrecubical.dPom x (P.pow (n+1)).pom :=
  CounterFreeHDA.Cubical.theorem_1_1_fromFunctor D G K recognises hD hh downward withinWidth

theorem actual_residual_classification {U : Appendix.Residual.UCube}
    (P : Appendix.Residual.Prefix U) :
    ∃ r : Appendix.Residual.Kind U, Appendix.Residual.prefixResidual P = Appendix.Residual.residualLanguage U r :=
  Appendix.Residual.actual_residual_exhaustiveness P

theorem residual_reachability (U : Appendix.Residual.UCube) (r : Appendix.Residual.Kind U) :
    ∃ P : Appendix.Residual.Prefix U, Appendix.Residual.prefixResidual P = Appendix.Residual.residualLanguage U r :=
  Appendix.Residual.every_residual_reachable U r

theorem residual_distinctness (U : Appendix.Residual.UCube) :
    Function.Injective (Appendix.Residual.residualLanguage U) :=
  Appendix.Residual.residualLanguage_injective U

theorem residual_action {U V : Appendix.Residual.UCube} (s : Step U V) (r : Appendix.Residual.Kind U) :
    Appendix.Residual.rightAction (Appendix.Residual.residualLanguage U r) (BoundedArrow.ofStep s) =
      Appendix.Residual.residualLanguage V (Appendix.Residual.stepKind s r) :=
  Appendix.Residual.elementary_residual_action s r

theorem profile_actual_deletion {U : Appendix.Residual.UCube} (P : Appendix.Residual.Prefix U)
    (D : Finset (Fin U.dim)) :
    Nonempty (PomsetIso (Appendix.Residual.deletedPrefix P D).pom.val
      (Deletion.data P.pom.val (Appendix.Residual.targetKeep P D))) :=
  ⟨Appendix.Residual.deletedPrefixIso P D⟩

theorem profile_update {U V : Appendix.Residual.UCube} (P : Appendix.Residual.Prefix U)
    (s : Step U V) : Appendix.Residual.profileCode (P.comp (BoundedArrow.ofStep s)) =
      Appendix.Residual.updateCode s (Appendix.Residual.profileCode P) :=
  Appendix.Residual.profileCode_update P s

theorem live_profile_exhaustiveness {U : Appendix.Residual.UCube} (P : Appendix.Residual.Prefix U)
    (hl : Appendix.Residual.liveCode U (Appendix.Residual.profileCode P)) :
    ∃ i : Fin (Appendix.Completion.profileSize U.1), Appendix.Residual.profileCode P = Appendix.Residual.templateCode U i :=
  Appendix.Residual.live_profile_exhaustive P hl

theorem live_profile_reachability (U : Appendix.Residual.UCube) (i : Fin (Appendix.Completion.profileSize U.1)) :
    ∃ P : Appendix.Residual.Prefix U, Appendix.Residual.profileCode P = Appendix.Residual.templateCode U i :=
  Appendix.Residual.live_profile_reachable U i

theorem canonical_profile_lower {U V : Appendix.Residual.UCube} (f : Face U V)
    (hf : f.Lower) (x : Appendix.Residual.LiveActualProfile V) :
    (Appendix.Residual.canonicalProfileHDA.face f x).val.val = Appendix.Residual.lowerCode f x.val.val :=
  Appendix.Residual.canonical_lower f hf x

theorem canonical_profile_upper {U V : Appendix.Residual.UCube} (f : Face U V)
    (hf : f.Upper) (hd : V.dim = U.dim+1) (x : Appendix.Residual.LiveActualProfile V) :
    (Appendix.Residual.canonicalProfileHDA.face f x).val.val = Appendix.Residual.updateCode (.stop f hf hd) x.val.val :=
  Appendix.Residual.canonical_upper f hf hd x

theorem canonical_profile_language :
    Appendix.Residual.canonicalProfileHDA.LangPom = Appendix.Completion.completionHDA.LangPom :=
  Appendix.Residual.canonical_language_eq

theorem canonical_profile_counter : ¬ Appendix.Residual.canonicalProfileHDA.toPrecubical.CounterFreePom :=
  Appendix.Residual.canonical_not_counterFree

theorem full_profile_dead_no_return {U V : Appendix.Residual.UCube} {p : Word U V}
    {x : Appendix.Residual.ActualProfile U} {y : Appendix.Residual.ActualProfile V}
    (hr : Appendix.Residual.FullProfileRun p x y) (hx : ¬ Appendix.Residual.liveCode U x.val) :
    ¬ Appendix.Residual.liveCode V y.val :=
  Appendix.Residual.dead_no_return hr hx

theorem full_profile_counter : ¬ ∃ N : ℕ, 1 ≤ N ∧
    ∀ (U : Appendix.Residual.UCube) (x : Appendix.Residual.ActualProfile U) (P : EndoPom (cubeInterface U)),
      Appendix.Residual.fullProfileDPom (V := U) x (P.pow N).pom = Appendix.Residual.fullProfileDPom x (P.pow (N+1)).pom :=
  Appendix.Residual.full_completion_no_exponent

theorem explicit_appendix_language :
    Appendix.Actual.originalHDA.LangPom = {P | Appendix.Residual.ExplicitLanguage P} :=
  Appendix.Residual.explicit_language_formula

theorem actual_concurrent_pair : Appendix.Residual.cPom.pom.n = 2 ∧
    ∀ e f, ¬ Appendix.Residual.cPom.pom.prec e f :=
  ⟨Appendix.Residual.concurrent_block_size Appendix.Residual.cWord_concurrent,Appendix.Residual.concurrent_block_prec Appendix.Residual.cWord_concurrent⟩

theorem appendix_exact_exponents : ∀ i : Fin 14,
    1 ≤ Appendix.leastExponent i ∧ Appendix.leastExponent i ≤ 3 ∧
    Appendix.pow (Appendix.edgeMonoid i) (Appendix.leastExponent i) = Appendix.pow (Appendix.edgeMonoid i) (Appendix.leastExponent i+1) ∧
    (∀ q : Fin 4, 1 ≤ q.val → q.val < Appendix.leastExponent i →
      Appendix.pow (Appendix.edgeMonoid i) q.val ≠ Appendix.pow (Appendix.edgeMonoid i) (q.val+1)) :=
  Appendix.exact_least_exponents

theorem appendix_exact_products : ∀ i,
    Appendix.comp (Appendix.edgeMonoid i) Appendix.D = Appendix.edgeMonoid (Appendix.timesD i) ∧
    Appendix.comp (Appendix.edgeMonoid i) Appendix.K = Appendix.edgeMonoid (Appendix.timesK i) :=
  Appendix.exact_right_products

theorem appendix_last_product :
    Appendix.comp (Appendix.comp Appendix.D (Appendix.pow Appendix.K 3)) Appendix.D = Appendix.comp Appendix.K (Appendix.pow Appendix.D 2) ∧
    Appendix.comp (Appendix.comp Appendix.D (Appendix.pow Appendix.K 3)) Appendix.D ≠ Appendix.comp (Appendix.pow Appendix.K 2) Appendix.D :=
  Appendix.last_product_distinguishes_elements

theorem interface_specific_bound {Lab : Type u} {k h : ℕ} {L : Set (IntervalPom Lab)}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h) (hh : 1 ≤ h)
    (U : Cube Lab k) (x : F.hda.Cell U) (P : EndoPom (cubeInterface U))
    (n : ℕ) (hn : 2*U.dim+h ≤ n) :
    F.hda.toPrecubical.dPom (V := U) x (P.pow n).pom = F.hda.toPrecubical.dPom x (P.pow (n+1)).pom :=
  F.interface_endpoint_stable hh U x P n hn

theorem empty_interface_bound {Lab : Type u} {k h : ℕ} {L : Set (IntervalPom Lab)}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h) (hh : 1 ≤ h)
    (U : Cube Lab k) (hr : U.dim = 0) (x : F.hda.Cell U) (P : EndoPom (cubeInterface U))
    (n : ℕ) (hn : h ≤ n) :
    F.hda.toPrecubical.dPom (V := U) x (P.pow n).pom = F.hda.toPrecubical.dPom x (P.pow (n+1)).pom :=
  F.empty_interface_endpoint_stable hh U hr x P n hn

theorem effective_interface_bound {Lab : Type u} [Fintype Lab] [DecidableEq Lab]
    {k h : ℕ} {L : Set (IntervalPom Lab)} (G : FinitePomsetRecognizer.{u,v} (k := k) L h)
    (image : ∀ {U V}, Step U V → G.D.Hom U V)
    (himage : ∀ {U V} (s : Step U V), image s = G.stepImage s)
    (K : ∀ {U V}, Finset (G.D.Hom U V)) (hK : ∀ {U V} (a : G.D.Hom U V), a ∈ K ↔ a ∈ G.K)
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L) (hh : 1 ≤ h)
    (U : Cube Lab k) (x : (Effective.tableHDA G.D image K).Cell U) (P : EndoPom (cubeInterface U))
    (n : ℕ) (hn : 2*U.dim+h ≤ n) :
    (Effective.tableHDA G.D image K).toPrecubical.dPom (V := U) x (P.pow n).pom =
      (Effective.tableHDA G.D image K).toPrecubical.dPom x (P.pow (n+1)).pom :=
  G.effective_interface_uniform_bound downward image himage K hK hh U x P n hn

theorem original_functor_interface_bound {Lab : Type u} [Fintype Lab]
    {k h : ℕ} {L : Set (IntervalPom Lab)} {O : Type v} (D : FinCat.{v,w} O)
    (G : Recognition.Functor (PomsetCategory.category Lab k) (Recognition.ofFinite D))
    (K : ∀ {U V}, Set (D.Hom U V))
    (recognises : ∀ {U V} (A : BoundedArrow U V), A.pom ∈ L ↔ G.map (PomsetCategory.mk A) ∈ K)
    (hD : D.AperiodicExponent h) (hh : 1 ≤ h)
    (downward : ∀ {P Q}, P ⊑ₛ Q → Q ∈ L → P ∈ L)
    (withinWidth : ∀ P ∈ L, P.val.WidthLE k) :
    ∃ X : HDA.{u,u} Lab k, Finite (Σ U, X.Cell U) ∧ X.LangPom = L ∧ X.toPrecubical.CounterFreePom ∧
      ∀ (U : Cube Lab k) (x : X.Cell U) (P : EndoPom (cubeInterface U)) (n : ℕ),
        2*U.dim+h ≤ n → X.toPrecubical.dPom (V := U) x (P.pow n).pom = X.toPrecubical.dPom x (P.pow (n+1)).pom :=
  theorem_1_1_fromFunctor_interface D G K recognises hD hh downward withinWidth

end Verification
