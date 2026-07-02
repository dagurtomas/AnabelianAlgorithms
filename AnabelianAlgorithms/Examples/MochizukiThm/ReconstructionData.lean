/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

module

import all AnabelianAlgorithms.Linter.NonstandardAxioms
public import AnabelianAlgorithms.Examples.MochizukiThm.PointedEtalePi1
public import Mathlib.CategoryTheory.Profunctor.Basic

/-!
# Profinite reconstruction data for the Mochizuki Hom-form example

This file turns point-indexed arithmetic `π₁` objects into the invariant and algorithm profunctors
for proper hyperbolic curves over a fixed `p`-adic local field.  The only theorem boundary here is
openness of the point-indexed outer `π₁` map.
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

/-! ## Data category and universe transport -/

/-- The augmented profinite data category over the base Galois group `Γ_K`. -/
abbrev properHyperbolicCurveData {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : Type (u + 1) :=
  OpenAugProfiniteOver (baseGalois K)

/-- A data object, transported to the large universe used by pointed finite-étale `π₁`. -/
noncomputable def openAugProfiniteULift {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (G : properHyperbolicCurveData K) :
    OpenAugProfiniteOver (baseGaloisLarge K) :=
  { obj := CostructuredArrow.mk (uliftProfiniteGrpMap G.asAug.hom) }

/-- A data morphism, transported to the large universe used by pointed finite-étale `π₁`. -/
noncomputable def openAugProfiniteULiftMap {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {G H : properHyperbolicCurveData K} (f : G ⟶ H) :
    openAugProfiniteULift K G ⟶ openAugProfiniteULift K H :=
  { hom := CostructuredArrow.homMk (uliftProfiniteGrpMap f.hom.left) (by
      change uliftProfiniteGrpMap f.hom.left ≫ uliftProfiniteGrpMap H.asAug.hom =
        uliftProfiniteGrpMap G.asAug.hom
      rw [← uliftProfiniteGrpMap_comp]
      exact congrArg uliftProfiniteGrpMap f.hom.w)
    property := uliftProfiniteGrpMap_isOpenMap f.hom.left f.property }

@[simp]
theorem openAugProfiniteULiftMap_id {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} (G : properHyperbolicCurveData K) :
    openAugProfiniteULiftMap (𝟙 G) = 𝟙 (openAugProfiniteULift K G) := by
  ext x
  cases x
  rfl

@[simp]
theorem openAugProfiniteULiftMap_comp {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {G H I : properHyperbolicCurveData K}
    (f : G ⟶ H) (g : H ⟶ I) :
    openAugProfiniteULiftMap (f ≫ g) = openAugProfiniteULiftMap f ≫ openAugProfiniteULiftMap g := by
  ext x
  cases x
  rfl

/-- The pointed arithmetic `π₁` object associated to an explicit geometric point, in the same
large-universe augmented category as lifted data objects. -/
noncomputable def pointedEtalePi1ObjLarge {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : ProperHyperbolicCurveOver K)
    (ξ : CurveGeometricPointOver K X) : OpenAugProfiniteOver (baseGaloisLarge K) :=
  { obj := CostructuredArrow.mk
      (properHyperbolicCurvePointedEtalePi1ToBaseLarge K X ξ ≫
        (baseGaloisPointedEtalePi1Iso K).inv) }

/-- Outer homomorphisms over the large-universe base comparison. -/
abbrev LargeOuterHomOver {p : ℕ} [Fact p.Prime] (K : PadicLocalFieldCat.{u} p)
    (A B : OpenAugProfiniteOver (baseGaloisLarge K)) : Type (u + 1) :=
  OuterHomOver A B

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The pointed curve-to-base augmentation is compatible with morphisms of curves after
quotienting profinite-group morphisms by target inner conjugacy. -/
theorem pointedEtalePi1Map_toBase_outer {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X Y : ProperHyperbolicCurveOver K}
    (ξ : CurveGeometricPointOver K X) (f : X ⟶ Y) :
    let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
    Q.map (pointedEtalePi1Map ξ.point f.hom.hom.left) ≫
        Q.map (properHyperbolicCurvePointedEtalePi1ToBaseLarge K Y (ξ.map f)) =
      Q.map (properHyperbolicCurvePointedEtalePi1ToBaseLarge K X ξ) := by
  intro Q
  change (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map
        (pointedEtalePi1Map ξ.point f.hom.hom.left) ≫
      (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map
        (properHyperbolicCurvePointedEtalePi1ToBaseLarge K Y (ξ.map f)) =
    (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map
      (properHyperbolicCurvePointedEtalePi1ToBaseLarge K X ξ)
  rw [properHyperbolicCurvePointedEtalePi1ToBaseLarge_outer_map (K := K) (X := Y)
    (ξ := ξ.map f)]
  rw [properHyperbolicCurvePointedEtalePi1ToBaseLarge_outer_map (K := K) (X := X) (ξ := ξ)]
  let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
  change Q.map (pointedEtalePi1Map ξ.point f.hom.hom.left) ≫
      (Q.map (pointedEtalePi1Map (ξ.map f).point Y.toOver.hom) ≫
        Q.map (eqToHom (congrArg pointedEtalePi1 (ξ.map f).map_to_base))) =
    Q.map (pointedEtalePi1Map ξ.point X.toOver.hom) ≫
      Q.map (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base))
  rw [← Category.assoc]
  rw [← Q.map_comp]
  change Q.map (pointedEtalePi1Map ξ.point f.hom.hom.left ≫
        pointedEtalePi1Map (ξ.point ≫ f.hom.hom.left) Y.toOver.hom) ≫
      Q.map (eqToHom (congrArg pointedEtalePi1 (ξ.map f).map_to_base)) =
    Q.map (pointedEtalePi1Map ξ.point X.toOver.hom) ≫
      Q.map (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base))
  have hcomp := pointedEtalePi1Map_comp_outer ξ.point f.hom.hom.left Y.toOver.hom
  dsimp only at hcomp
  rw [← hcomp]
  rw [← Q.map_comp, ← Q.map_comp]
  apply congrArg Q.map
  exact pointedEtalePi1Map_toBase_raw ξ f

/-! ## Point-indexed outer maps -/

/-- The point-indexed outer `π₁` map induced by a morphism of curves.

This is point-indexed functoriality: the source point is input data and the target point is its
pushforward.  No curve base point is selected globally. -/
noncomputable def pointedEtalePi1OuterMapLarge {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X Y : ProperHyperbolicCurveOver K}
    (ξ : CurveGeometricPointOver K X) (f : X ⟶ Y) :
    LargeOuterHomOver K (pointedEtalePi1ObjLarge K X ξ)
      (pointedEtalePi1ObjLarge K Y (ξ.map f)) := by
  let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
  exact CostructuredArrow.homMk (Q.map (pointedEtalePi1Map ξ.point f.hom.hom.left)) (by
    change Q.map (pointedEtalePi1Map ξ.point f.hom.hom.left) ≫
        Q.map ((properHyperbolicCurvePointedEtalePi1ToBaseLarge K Y (ξ.map f)) ≫
          (baseGaloisPointedEtalePi1Iso K).inv) =
      Q.map ((properHyperbolicCurvePointedEtalePi1ToBaseLarge K X ξ) ≫
        (baseGaloisPointedEtalePi1Iso K).inv)
    rw [Q.map_comp, Q.map_comp]
    rw [← Category.assoc]
    have h := pointedEtalePi1Map_toBase_outer ξ f
    dsimp only at h
    rw [h])

/-- Point-indexed arithmetic `π₁` maps are open. -/
axiom pointedEtalePi1OuterMapLarge_isOpen {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X Y : ProperHyperbolicCurveOver K}
    (ξ : CurveGeometricPointOver K X) (f : X ⟶ Y) :
    IsOpenOuterHomOver (pointedEtalePi1OuterMapLarge ξ f)

/-- Point-indexed arithmetic `π₁` sends identity morphisms to identity outer morphisms. -/
@[simp]
theorem pointedEtalePi1OuterMapLarge_id {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X : ProperHyperbolicCurveOver K}
    (ξ : CurveGeometricPointOver K X) :
    pointedEtalePi1OuterMapLarge ξ (𝟙 X) =
      𝟙 (openAugProfiniteAsOuter (pointedEtalePi1ObjLarge K X ξ)) := by
  apply CostructuredArrow.hom_ext
  change (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map
      (pointedEtalePi1Map ξ.point (𝟙 X.toScheme)) =
    𝟙 ((CategoryTheory.Quotient.functor profiniteGrpOuterRel).obj (pointedEtalePi1 ξ.point))
  have h := pointedEtalePi1Map_id_outer ξ.point
  dsimp only at h
  simpa using h

/-- Point-indexed arithmetic `π₁` maps are functorial for composition. -/
@[simp]
theorem pointedEtalePi1OuterMapLarge_comp {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X Y Z : ProperHyperbolicCurveOver K}
    (ξ : CurveGeometricPointOver K X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    pointedEtalePi1OuterMapLarge ξ (f ≫ g) =
      pointedEtalePi1OuterMapLarge ξ f ≫ pointedEtalePi1OuterMapLarge (ξ.map f) g := by
  apply CostructuredArrow.hom_ext
  let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
  change Q.map (pointedEtalePi1Map ξ.point (f.hom.hom.left ≫ g.hom.hom.left)) =
    Q.map (pointedEtalePi1Map ξ.point f.hom.hom.left) ≫
      Q.map (pointedEtalePi1Map (ξ.point ≫ f.hom.hom.left) g.hom.hom.left)
  rw [← Q.map_comp]
  have h := pointedEtalePi1Map_comp_outer ξ.point f.hom.hom.left g.hom.hom.left
  dsimp only at h
  simpa using h

set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency true

/-! ## Pointed representatives -/

/-- Pointed representatives for maps from a data object to the unpointed arithmetic `π₁` of `X`.

A representative chooses a geometric point as ordinary element data.  The remaining construction
boundary is the quotient/change-of-point torsor identifying these representatives up to inner
conjugacy; no representative is selected by axiom. -/
abbrev PointedInvariantDatum {p : ℕ} [Fact p.Prime] (K : PadicLocalFieldCat.{u} p)
    (X : ProperHyperbolicCurveOver K) (G : properHyperbolicCurveData K) : Type (u + 1) :=
  Σ ξ : CurveGeometricPointOver K X,
    LargeOuterHomOver K (openAugProfiniteULift K G) (pointedEtalePi1ObjLarge K X ξ)

/-- Map pointed invariant representatives along a curve morphism and a data morphism. -/
noncomputable def pointedInvariantDatumMap {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X Y : ProperHyperbolicCurveOver K}
    {G H : properHyperbolicCurveData K} (f : X ⟶ Y) (g : G ⟶ H) :
    PointedInvariantDatum K X H ⟶ PointedInvariantDatum K Y G :=
  ↾fun a ↦ ⟨a.1.map f,
    openAugProfiniteAsOuterMap (openAugProfiniteULiftMap g) ≫ a.2 ≫
      pointedEtalePi1OuterMapLarge a.1 f⟩

/-- Identity law for `pointedInvariantDatumMap`. -/
@[simp]
theorem pointedInvariantDatumMap_id {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} (X : ProperHyperbolicCurveOver K)
    (G : properHyperbolicCurveData K) :
    pointedInvariantDatumMap (𝟙 X) (𝟙 G) = 𝟙 (PointedInvariantDatum K X G) := by
  ext ⟨ξ, φ⟩ <;> simp [pointedInvariantDatumMap]

/-- Composition law for `pointedInvariantDatumMap`. -/
theorem pointedInvariantDatumMap_comp {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X Y Z : ProperHyperbolicCurveOver K}
    {G H I : properHyperbolicCurveData K} (f : X ⟶ Y) (f' : Y ⟶ Z)
    (g : G ⟶ H) (g' : H ⟶ I) :
    pointedInvariantDatumMap (f ≫ f') (g ≫ g') =
      pointedInvariantDatumMap f g' ≫ pointedInvariantDatumMap f' g := by
  ext ⟨ξ, φ⟩ <;> simp [pointedInvariantDatumMap]

/-- Pointwise representatives for open maps out of the unpointed arithmetic `π₁` of `X`.

Using pointwise families avoids choosing a lift of a target geometric point when precomposing along
`X ⟶ Y`: a family over all points of `Y` can be evaluated at the pushed-forward point of `X`. -/
abbrev PointwiseAlgorithmDatum {p : ℕ} [Fact p.Prime] (K : PadicLocalFieldCat.{u} p)
    (G : properHyperbolicCurveData K) (X : ProperHyperbolicCurveOver K) : Type (u + 1) :=
  (ξ : CurveGeometricPointOver K X) →
    { φ : LargeOuterHomOver K (pointedEtalePi1ObjLarge K X ξ) (openAugProfiniteULift K G) //
      IsOpenOuterHomOver φ }

/-- Map pointwise algorithm representatives along a data morphism and a curve morphism. -/
noncomputable def pointwiseAlgorithmDatumMap {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {G H : properHyperbolicCurveData K}
    {X Y : ProperHyperbolicCurveOver K} (f : G ⟶ H) (g : X ⟶ Y) :
    PointwiseAlgorithmDatum K G Y ⟶ PointwiseAlgorithmDatum K H X :=
  ↾fun a ξ ↦
    ⟨pointedEtalePi1OuterMapLarge ξ g ≫ (a (ξ.map g)).1 ≫
        openAugProfiniteAsOuterMap (openAugProfiniteULiftMap f), by
      have hpre : IsOpenOuterHomOver
          (pointedEtalePi1OuterMapLarge ξ g ≫ (a (ξ.map g)).1) :=
        isOpenOuterHomOver_comp (pointedEtalePi1OuterMapLarge_isOpen ξ g) (a (ξ.map g)).2
      have hcomp := isOpenOuterHomOver_comp
        (φ := pointedEtalePi1OuterMapLarge ξ g ≫ (a (ξ.map g)).1)
        (ψ := openAugProfiniteAsOuterMap (openAugProfiniteULiftMap f))
        hpre (isOpenOuterHomOver_of_openAugProfiniteHom (openAugProfiniteULiftMap f))
      simpa using hcomp⟩

/-- Identity law for `pointwiseAlgorithmDatumMap`. -/
@[simp]
theorem pointwiseAlgorithmDatumMap_id {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} (G : properHyperbolicCurveData K)
    (X : ProperHyperbolicCurveOver K) :
    pointwiseAlgorithmDatumMap (𝟙 G) (𝟙 X) = 𝟙 (PointwiseAlgorithmDatum K G X) := by
  apply ConcreteCategory.hom_ext
  intro a
  funext ξ
  apply Subtype.ext
  apply CostructuredArrow.hom_ext
  change (pointedEtalePi1OuterMapLarge ξ (𝟙 X) ≫ (a (ξ.map (𝟙 X))).1 ≫
      openAugProfiniteAsOuterMap (openAugProfiniteULiftMap (𝟙 G))).left = (a ξ).1.left
  simp

/-- Composition law for `pointwiseAlgorithmDatumMap`. -/
theorem pointwiseAlgorithmDatumMap_comp {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {G H I : properHyperbolicCurveData K}
    {X Y Z : ProperHyperbolicCurveOver K} (f : G ⟶ H) (f' : H ⟶ I)
    (g : X ⟶ Y) (g' : Y ⟶ Z) :
    pointwiseAlgorithmDatumMap (f ≫ f') (g ≫ g') =
      pointwiseAlgorithmDatumMap f g' ≫ pointwiseAlgorithmDatumMap f' g := by
  apply ConcreteCategory.hom_ext
  intro a
  funext ξ
  apply Subtype.ext
  apply CostructuredArrow.hom_ext
  change (pointedEtalePi1OuterMapLarge ξ (g ≫ g') ≫
      (a (ξ.map (g ≫ g'))).1 ≫
      openAugProfiniteAsOuterMap (openAugProfiniteULiftMap (f ≫ f'))).left =
    (pointedEtalePi1OuterMapLarge ξ g ≫
      (pointedEtalePi1OuterMapLarge (ξ.map g) g' ≫
        (a ((ξ.map g).map g')).1 ≫
        openAugProfiniteAsOuterMap (openAugProfiniteULiftMap f)) ≫
      openAugProfiniteAsOuterMap (openAugProfiniteULiftMap f')).left
  simp [openAugProfiniteULiftMap_comp]

/-! ## Invariant and algorithm profunctors -/

/-- The full arithmetic étale `π₁` invariant profunctor for proper hyperbolic curves over `K`.

This is no longer an opaque axiom: its values are pointed representatives, and the named remaining
boundaries say how those representatives descend to the unpointed/change-of-point torsor. -/
noncomputable def properHyperbolicCurveInvariant {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    Profunctor.{u + 1} (ProperHyperbolicCurveOver K) (properHyperbolicCurveData K) :=
  .ofCore {
    obj X G := PointedInvariantDatum K X G
    map f g := pointedInvariantDatumMap f g
    map_id X G := pointedInvariantDatumMap_id X G
    map_comp f f' g g' := pointedInvariantDatumMap_comp f f' g g' }

/-- The open-outer-hom algorithm profunctor attached to full arithmetic étale `π₁`.

This is no longer an opaque axiom: its values are pointwise open outer maps out of each pointed
fiber-functor representative. -/
noncomputable def properHyperbolicCurveAlgorithm {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    Profunctor.{u + 1} (properHyperbolicCurveData K) (ProperHyperbolicCurveOver K) :=
  .ofCore {
    obj G X := PointwiseAlgorithmDatum K G X
    map f g := pointwiseAlgorithmDatumMap f g
    map_id G X := pointwiseAlgorithmDatumMap_id G X
    map_comp f f' g g' := pointwiseAlgorithmDatumMap_comp f f' g g' }

end ProperHyperbolicCurveHomStandalone
end MochizukiLocalProP
end Examples
end Anabelian
