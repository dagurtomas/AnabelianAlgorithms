/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

module

public import AnabelianAlgorithms.Examples.MochizukiThm.PointedEtalePi1.Basic

/-!
# Pointed arithmetic étale fundamental groups: outer functoriality

This file proves the identity and composition laws for pointed arithmetic `π₁` maps after passing
to the quotient by target-inner conjugacy.
-/

@[expose] public section

universe u uG

namespace Anabelian
namespace Examples
namespace MochizukiLocalProP
namespace ProperHyperbolicCurveHomStandalone

open CategoryTheory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry
open Opposite
open TopologicalSpace
open Order
open scoped FintypeCatDiscrete

section PointedEtalePi1OuterFunctoriality

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Pullback of finite-étale covers along the identity is naturally isomorphic to the identity
functor. -/
noncomputable def finiteEtalePullbackIdIso (X : Scheme.{u}) :
    AlgebraicGeometry.FiniteEtale.pullback (𝟙 X) ≅ 𝟭 (AlgebraicGeometry.FiniteEtale X) :=
  NatIso.ofComponents (fun A ↦
    MorphismProperty.Over.isoMk (asIso (Limits.pullback.fst A.hom (𝟙 X))) (by
      simpa using (Limits.pullback.condition :
        Limits.pullback.fst A.hom (𝟙 X) ≫ A.hom =
          Limits.pullback.snd A.hom (𝟙 X) ≫ 𝟙 X)))
    (fun {A B} g ↦ by
      apply MorphismProperty.Over.Hom.ext
      change ((AlgebraicGeometry.FiniteEtale.pullback (𝟙 X)).map g).left ≫
          (asIso (Limits.pullback.fst B.hom (𝟙 X))).hom =
        (asIso (Limits.pullback.fst A.hom (𝟙 X))).hom ≫ g.left
      rw [MorphismProperty.Over.pullback_map_left]
      simp)

/-- The induced comparison between the pulled-back fiber functor along `𝟙 X` and the original
fiber functor. -/
noncomputable def finiteEtalePullbackIdFiberIso {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X) :
    AlgebraicGeometry.FiniteEtale.pullback (𝟙 X) ⋙
        AlgebraicGeometry.FiniteEtale.fiber ξ ≅ AlgebraicGeometry.FiniteEtale.fiber ξ :=
  Functor.isoWhiskerRight (finiteEtalePullbackIdIso X)
      (AlgebraicGeometry.FiniteEtale.fiber ξ) ≪≫
    Functor.leftUnitor (AlgebraicGeometry.FiniteEtale.fiber ξ)

lemma mapAut_finiteEtalePullbackId {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (x : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ)) :
    Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
      ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale X)
        (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
        (AlgebraicGeometry.FiniteEtale.pullback (𝟙 X))) x =
      (finiteEtalePullbackIdFiberIso ξ).symm.conjAut x := by
  ext A a
  simp [Functor.mapAut, Iso.conj_apply, finiteEtalePullbackIdFiberIso,
    finiteEtalePullbackIdIso]

/-- The inner automorphism measuring the identity coherence for `pointedEtalePi1Map`. -/
noncomputable def pointedEtalePi1MapIdConjugator {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X) :
    Aut (AlgebraicGeometry.FiniteEtale.fiber ξ) :=
  fiberCompIso ξ (𝟙 X) ≪≫ finiteEtalePullbackIdFiberIso ξ

lemma pointedEtalePi1Map_id_apply {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (x : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ)) :
    (pointedEtalePi1Map ξ (𝟙 X)) x =
      (pointedEtalePi1MapIdConjugator ξ).symm.conjAut x := by
  change (fiberCompIso ξ (𝟙 X)).symm.conjAut
      (Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
        ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale X)
          (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
          (AlgebraicGeometry.FiniteEtale.pullback (𝟙 X))) x) =
    (pointedEtalePi1MapIdConjugator ξ).symm.conjAut x
  rw [mapAut_finiteEtalePullbackId]
  simp [pointedEtalePi1MapIdConjugator, Iso.trans_conjAut]
  rfl

/-- Pulling back finite-étale covers along a composite identifies with the iterated pullback,
after whiskering by the source fiber functor. -/
noncomputable def finiteEtalePullbackCompFiberIso {X Y Z : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    AlgebraicGeometry.FiniteEtale.pullback (f ≫ g) ⋙
        AlgebraicGeometry.FiniteEtale.fiber ξ ≅
      AlgebraicGeometry.FiniteEtale.pullback g ⋙
        AlgebraicGeometry.FiniteEtale.pullback f ⋙
          AlgebraicGeometry.FiniteEtale.fiber ξ :=
  Functor.isoWhiskerRight
      (MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) f g)
      (AlgebraicGeometry.FiniteEtale.fiber ξ) ≪≫
    Functor.associator (AlgebraicGeometry.FiniteEtale.pullback g)
      (AlgebraicGeometry.FiniteEtale.pullback f)
      (AlgebraicGeometry.FiniteEtale.fiber ξ)

lemma mapAut_finiteEtalePullbackComp {X Y Z : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ)) :
    Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
      ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
        (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
        (AlgebraicGeometry.FiniteEtale.pullback (f ≫ g))) x =
      (finiteEtalePullbackCompFiberIso ξ f g).symm.conjAut
        (Functor.mapAut
          (AlgebraicGeometry.FiniteEtale.pullback f ⋙
            AlgebraicGeometry.FiniteEtale.fiber ξ)
          ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
            (AlgebraicGeometry.FiniteEtale Y) FintypeCat).obj
            (AlgebraicGeometry.FiniteEtale.pullback g))
          (Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
            ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Y)
              (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
              (AlgebraicGeometry.FiniteEtale.pullback f)) x)) := by
  ext A a
  simp [Functor.mapAut, Iso.conj_apply, finiteEtalePullbackCompFiberIso]

/-- The middle automorphism obtained by functoriality of `mapAut` along two pullbacks. -/
noncomputable def pointedEtalePi1MapCompMiddle {X Y Z : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ)) :
    Aut (AlgebraicGeometry.FiniteEtale.pullback g ⋙
      AlgebraicGeometry.FiniteEtale.pullback f ⋙
        AlgebraicGeometry.FiniteEtale.fiber ξ) :=
  Functor.mapAut
    (AlgebraicGeometry.FiniteEtale.pullback f ⋙
      AlgebraicGeometry.FiniteEtale.fiber ξ)
    ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
      (AlgebraicGeometry.FiniteEtale Y) FintypeCat).obj
      (AlgebraicGeometry.FiniteEtale.pullback g))
    (Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
      ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Y)
        (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
        (AlgebraicGeometry.FiniteEtale.pullback f)) x)

/-- The one-step path from the iterated pullback fiber functor to the fiber of `ξ ≫ (f ≫ g)`. -/
noncomputable def pointedEtalePi1MapCompIsoLeft {X Y Z : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    AlgebraicGeometry.FiniteEtale.pullback g ⋙
        AlgebraicGeometry.FiniteEtale.pullback f ⋙
          AlgebraicGeometry.FiniteEtale.fiber ξ ≅
      AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ (f ≫ g)) :=
  (finiteEtalePullbackCompFiberIso ξ f g).symm ≪≫ (fiberCompIso ξ (f ≫ g)).symm

/-- The two-step path from the iterated pullback fiber functor through `ξ ≫ f` to the final
fiber functor. -/
noncomputable def pointedEtalePi1MapCompIsoRight {X Y Z : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    AlgebraicGeometry.FiniteEtale.pullback g ⋙
        AlgebraicGeometry.FiniteEtale.pullback f ⋙
          AlgebraicGeometry.FiniteEtale.fiber ξ ≅
      AlgebraicGeometry.FiniteEtale.fiber ((ξ ≫ f) ≫ g) :=
  (((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
      (AlgebraicGeometry.FiniteEtale Y) FintypeCat).obj
      (AlgebraicGeometry.FiniteEtale.pullback g)).mapIso (fiberCompIso ξ f)).symm ≪≫
    (fiberCompIso (ξ ≫ f) g).symm

lemma pointedEtalePi1Map_comp_left_apply {X Y Z : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Z]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ)) :
    (pointedEtalePi1Map ξ (f ≫ g)) x =
      (pointedEtalePi1MapCompIsoLeft ξ f g).conjAut
        (pointedEtalePi1MapCompMiddle ξ f g x) := by
  change (fiberCompIso ξ (f ≫ g)).symm.conjAut
      (Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
        ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
          (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
          (AlgebraicGeometry.FiniteEtale.pullback (f ≫ g))) x) =
    (pointedEtalePi1MapCompIsoLeft ξ f g).conjAut
      (pointedEtalePi1MapCompMiddle ξ f g x)
  rw [mapAut_finiteEtalePullbackComp]
  simp [pointedEtalePi1MapCompIsoLeft, pointedEtalePi1MapCompMiddle, Iso.trans_conjAut]

lemma mapAut_finiteEtalePullback_conj_fiberCompIso {X Y Z : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Aut (AlgebraicGeometry.FiniteEtale.pullback f ⋙
      AlgebraicGeometry.FiniteEtale.fiber ξ)) :
    Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f))
      ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
        (AlgebraicGeometry.FiniteEtale Y) FintypeCat).obj
        (AlgebraicGeometry.FiniteEtale.pullback g))
      ((fiberCompIso ξ f).symm.conjAut x) =
    ((((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
          (AlgebraicGeometry.FiniteEtale Y) FintypeCat).obj
          (AlgebraicGeometry.FiniteEtale.pullback g)).mapIso
        (fiberCompIso ξ f)).symm).conjAut
      (Functor.mapAut (AlgebraicGeometry.FiniteEtale.pullback f ⋙
          AlgebraicGeometry.FiniteEtale.fiber ξ)
        ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
          (AlgebraicGeometry.FiniteEtale Y) FintypeCat).obj
          (AlgebraicGeometry.FiniteEtale.pullback g)) x) := by
  exact
    (Functor.map_conjAut
      ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
        (AlgebraicGeometry.FiniteEtale Y) FintypeCat).obj
        (AlgebraicGeometry.FiniteEtale.pullback g))
      (fiberCompIso ξ f).symm x)

lemma pointedEtalePi1Map_comp_right_apply {X Y Z : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y] [ConnectedSpace Z]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ)) :
    (pointedEtalePi1Map ξ f ≫ pointedEtalePi1Map (ξ ≫ f) g) x =
      (pointedEtalePi1MapCompIsoRight ξ f g).conjAut
        (pointedEtalePi1MapCompMiddle ξ f g x) := by
  change (pointedEtalePi1Map (ξ := ξ ≫ f) g)
      ((fiberCompIso ξ f).symm.conjAut
        (Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
          ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Y)
            (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
            (AlgebraicGeometry.FiniteEtale.pullback f)) x)) =
    (pointedEtalePi1MapCompIsoRight ξ f g).conjAut
      (pointedEtalePi1MapCompMiddle ξ f g x)
  change (fiberCompIso (ξ ≫ f) g).symm.conjAut
      (Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f))
        ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
          (AlgebraicGeometry.FiniteEtale Y) FintypeCat).obj
          (AlgebraicGeometry.FiniteEtale.pullback g))
        ((fiberCompIso ξ f).symm.conjAut
          (Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
            ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Y)
              (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
              (AlgebraicGeometry.FiniteEtale.pullback f)) x))) =
    (pointedEtalePi1MapCompIsoRight ξ f g).conjAut
      (pointedEtalePi1MapCompMiddle ξ f g x)
  rw [mapAut_finiteEtalePullback_conj_fiberCompIso]
  simp [pointedEtalePi1MapCompIsoRight, pointedEtalePi1MapCompMiddle, Iso.trans_conjAut]

/-- The inner automorphism comparing the one-step and two-step pullback paths for composition. -/
noncomputable def pointedEtalePi1MapCompConjugator {X Y Z : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    Aut (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ (f ≫ g))) :=
  (pointedEtalePi1MapCompIsoLeft ξ f g).symm ≪≫
    pointedEtalePi1MapCompIsoRight ξ f g

/-- `pointedEtalePi1Map` sends identity morphisms to identity morphisms in the outer quotient. -/
theorem pointedEtalePi1Map_id_outer {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X) :
    let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
    Q.map (pointedEtalePi1Map ξ (𝟙 X)) = Q.map (𝟙 (pointedEtalePi1 ξ)) := by
  intro Q
  apply CategoryTheory.Quotient.sound
  dsimp [profiniteGrpOuterRel]
  use pointedEtalePi1MapIdConjugator ξ
  intro x
  dsimp [pointedEtalePi1] at x ⊢
  change (ContinuousMonoidHom.id (Aut (AlgebraicGeometry.FiniteEtale.fiber ξ))) x =
    Iso.symm (pointedEtalePi1MapIdConjugator ξ) ≪≫
      (pointedEtalePi1Map ξ (𝟙 X)) x ≪≫ pointedEtalePi1MapIdConjugator ξ
  rw [pointedEtalePi1Map_id_apply]
  ext
  simp [Iso.conj_apply]

/-- `pointedEtalePi1Map` is functorial for composition in the outer quotient. -/
theorem pointedEtalePi1Map_comp_outer {X Y Z : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y] [ConnectedSpace Z]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
    Q.map (pointedEtalePi1Map ξ (f ≫ g)) =
      Q.map (pointedEtalePi1Map ξ f ≫ pointedEtalePi1Map (ξ ≫ f) g) := by
  intro Q
  apply CategoryTheory.Quotient.sound
  dsimp [profiniteGrpOuterRel]
  use pointedEtalePi1MapCompConjugator ξ f g
  intro x
  dsimp [pointedEtalePi1] at x ⊢
  change (pointedEtalePi1Map ξ f ≫ pointedEtalePi1Map (ξ ≫ f) g) x =
    Iso.symm (pointedEtalePi1MapCompConjugator ξ f g) ≪≫
      (pointedEtalePi1Map ξ (f ≫ g)) x ≪≫
        pointedEtalePi1MapCompConjugator ξ f g
  rw [pointedEtalePi1Map_comp_left_apply, pointedEtalePi1Map_comp_right_apply]
  dsimp [pointedEtalePi1]
  ext
  simp [pointedEtalePi1MapCompConjugator, Iso.conj_apply]

end PointedEtalePi1OuterFunctoriality
end ProperHyperbolicCurveHomStandalone
end MochizukiLocalProP
end Examples
end Anabelian
