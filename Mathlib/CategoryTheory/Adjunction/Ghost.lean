/-
Copyright (c) 2025 Ghost Adjunction Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: [Author Name]
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.MorphismProperty.Basic

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category

variable {R : Type u₁} {C : Type u₂} [Category.{v₁} R] [Category.{v₂} C]

/-- A Ghost Adjunction consists of an adjunction together with a class of morphisms
called "ghost morphisms", characterized as those morphisms that become isomorphisms
under the left adjoint functor. -/
structure GhostAdj (R C : Type*) [Category R] [Category C] where
  P        : R ⥤ C
  R'       : C ⥤ R
  adj      : P ⊣ R'
  ghost    : MorphismProperty R
  ghost_def :
    ∀ {X Y : R} (f : X ⟶ Y), ghost f ↔ IsIso (P.map f)

namespace GhostAdj

variable {R C : Type*} [Category R] [Category C]
variable (GA : GhostAdj R C)

open MorphismProperty

/-- Ghost morphisms are closed under composition. -/
lemma ghost_comp {X Y Z : R} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : GA.ghost f) (hg : GA.ghost g) :
    GA.ghost (f ≫ g) := by
  have hf_iso : IsIso (GA.P.map f) := (GA.ghost_def f).1 hf
  have hg_iso : IsIso (GA.P.map g) := (GA.ghost_def g).1 hg
  have hfg_iso : IsIso (GA.P.map (f ≫ g)) := by
    simpa [Functor.map_comp] using IsIso.comp_isIso
  exact (GA.ghost_def (f ≫ g)).2 hfg_iso

end GhostAdj

end CategoryTheory
