import Paper18.Category.DrinfeldEquivalenceMapEquivalence
import Paper18.Category.DrinfeldLinear

/-! # Linearity of actual tensor-equivalence transport on centers -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory
universe v u v' u'
namespace Paper18.Category.DrinfeldEquivalence
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  {D : Type u'} [Category.{v'} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  (F : C ⥤ D) [F.Monoidal] [F.IsEquivalence]

instance map_additive [F.Additive] : (map F).Additive where
  map_add := by intro X Y f g; apply Center.Hom.ext; exact Functor.map_add F

instance map_linear [F.Additive] [F.Linear ℂ] : (map F).Linear ℂ where
  map_smul := by intro X Y f c; apply Center.Hom.ext; exact Functor.map_smul F c f.f

instance equivalence_additive [F.Additive] : (equivalence F).functor.Additive :=
  inferInstanceAs (map F).Additive

instance equivalence_linear [F.Additive] [F.Linear ℂ] : (equivalence F).functor.Linear ℂ :=
  inferInstanceAs ((map F).Linear ℂ)

end Paper18.Category.DrinfeldEquivalence
