/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

module

public import AnabelianAlgorithms.Examples.MochizukiThm.PointedEtalePi1.OuterFunctoriality

/-!
# Pointed arithmetic étale fundamental groups of proper hyperbolic curves

This file attaches the pointed arithmetic `π₁` construction to the proper-hyperbolic-curve
category, including the comparison with the base absolute Galois group and compatibility with
curve morphisms.
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

noncomputable def baseGeometricPoint {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : Spec (.of (AlgebraicClosure K)) ⟶ baseScheme K :=
  Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))

/-- The large-universe full pointed étale fundamental group of `Spec K`. -/
noncomputable def basePointedEtalePi1Large {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : ProfiniteGrp.{u + 1} :=
  pointedEtalePi1 (baseGeometricPoint K)

/-- The base absolute Galois group.  The comparison with the pointed étale
`π₁(Spec K, Spec K̄)` is a theorem-level comparison, not a global base-point choice in this
Hom-form statement. -/
noncomputable def baseGalois {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : ProfiniteGrp.{u} :=
  InfiniteGalois.profiniteGalGrp K (AlgebraicClosure K)

/-- The large-universe copy of the base absolute Galois group. -/
noncomputable def baseGaloisLarge {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : ProfiniteGrp.{u + 1} :=
  uliftProfiniteGrp (baseGalois K)

/-- Comparison between the usual absolute Galois group and the pointed finite-étale
`π₁(Spec K, Spec K̄)`. -/
noncomputable def baseGaloisPointedEtalePi1Iso {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : baseGaloisLarge K ≅ basePointedEtalePi1Large K :=
  show AlgebraicGeometry.FiniteEtale.uliftProfiniteGrp
      (AlgebraicGeometry.FiniteEtale.galProfiniteGrp K (AlgebraicClosure K)) ≅
    ProfiniteGrp.of (Aut (AlgebraicGeometry.FiniteEtale.fiber
      (AlgebraicGeometry.FiniteEtale.baseGeom K (AlgebraicClosure K)))) from
    AlgebraicGeometry.FiniteEtale.galUliftAutFiberIso K (AlgebraicClosure K)

namespace ProperHyperbolicCurveOver

variable {p : ℕ} [Fact p.Prime] {K : PadicLocalFieldCat.{u} p}

/-- Proper hyperbolic curves are connected as schemes. -/
instance connectedSpace (X : ProperHyperbolicCurveOver K) : ConnectedSpace X.toScheme := by
  letI : GeometricallyConnected X.toOver.hom := X.obj.property.geometricallyConnected
  exact GeometricallyConnected.connectedSpace_of_subsingleton (f := X.toOver.hom)

/-- A proper hyperbolic curve has at least two points. -/
instance nontrivialSpace (X : ProperHyperbolicCurveOver K) : Nontrivial X.toScheme := by
  haveI : SmoothOfRelativeDimension 1 X.toOver.hom := X.smoothOfRelativeDimension
  exact scheme_nontrivial_of_smoothOfRelativeDimension_one_to_Spec_field K X.toOver.hom

/-- In an irreducible proper hyperbolic curve, the generic point is not closed. -/
theorem genericPoint_not_isClosed (X : ProperHyperbolicCurveOver K)
    [IrreducibleSpace X.toScheme] :
    ¬ IsClosed ({genericPoint X.toScheme} : Set X.toScheme) := by
  intro hclosed
  have hclosure : closure ({genericPoint X.toScheme} : Set X.toScheme) =
      ({genericPoint X.toScheme} : Set X.toScheme) := hclosed.closure_eq
  have huniv : closure ({genericPoint X.toScheme} : Set X.toScheme) = Set.univ :=
    (genericPoint_spec X.toScheme).def
  have hsingle_univ : ({genericPoint X.toScheme} : Set X.toScheme) = Set.univ := by
    rw [← hclosure, huniv]
  have hsub : Subsingleton X.toScheme := ⟨fun x y ↦ by
    have hx : x ∈ ({genericPoint X.toScheme} : Set X.toScheme) := by
      rw [hsingle_univ]
      trivial
    have hy : y ∈ ({genericPoint X.toScheme} : Set X.toScheme) := by
      rw [hsingle_univ]
      trivial
    rw [Set.mem_singleton_iff] at hx hy
    exact hx.trans hy.symm⟩
  exact not_subsingleton X.toScheme hsub

/-- Finite fibers for dominant morphisms of proper hyperbolic curves, conditional only on the
remaining irreducibility bridge for the two curves. -/
theorem hom_finite_fibers_of_irreducible
    {X Y : ProperHyperbolicCurveOver K} (f : X ⟶ Y)
    [IrreducibleSpace X.toScheme] [IrreducibleSpace Y.toScheme] :
    ∀ y : Y.toScheme, (f.hom.hom.left ⁻¹' {y}).Finite :=
  hom_finite_fibers_of_irreducible_of_generic_not_closed f (genericPoint_not_isClosed Y)

/-- Local quasi-finiteness for dominant morphisms of proper hyperbolic curves, conditional on the
remaining irreducibility bridge for the two curves. -/
theorem hom_locallyQuasiFinite_of_irreducible
    {X Y : ProperHyperbolicCurveOver K} (f : X ⟶ Y)
    [IrreducibleSpace X.toScheme] [IrreducibleSpace Y.toScheme] :
    LocallyQuasiFinite f.hom.hom.left :=
  (hom_locallyQuasiFinite_iff_finite_preimage_singleton f).2
    (hom_finite_fibers_of_irreducible f)

/-- Finiteness for dominant morphisms of proper hyperbolic curves, conditional on the remaining
irreducibility bridge for the two curves. -/
theorem hom_isFinite_of_irreducible
    {X Y : ProperHyperbolicCurveOver K} (f : X ⟶ Y)
    [IrreducibleSpace X.toScheme] [IrreducibleSpace Y.toScheme] :
    IsFinite f.hom.hom.left :=
  hom_isFinite_of_locallyQuasiFinite f (hom_locallyQuasiFinite_of_irreducible f)

end ProperHyperbolicCurveOver

/-- A geometric point of a proper hyperbolic curve over the fixed algebraic closure of `K`.

This is ordinary input data, not a globally selected base point.  The unpointed arithmetic `π₁`
profunctors below must package the usual independence of this choice. -/
structure CurveGeometricPointOver {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : ProperHyperbolicCurveOver K) where
  point : Spec (.of (AlgebraicClosure K)) ⟶ X.toScheme
  map_to_base : point ≫ X.toOver.hom = baseGeometricPoint K

namespace CurveGeometricPointOver

variable {p : ℕ} [Fact p.Prime] {K : PadicLocalFieldCat.{u} p}
variable {X Y Z : ProperHyperbolicCurveOver K}

/-- Push a geometric point forward along a morphism of curves over `K`. -/
noncomputable def map (ξ : CurveGeometricPointOver K X) (f : X ⟶ Y) :
    CurveGeometricPointOver K Y where
  point := ξ.point ≫ f.hom.hom.left
  map_to_base := by
    rw [Category.assoc]
    rw [f.hom.hom.w]
    exact ξ.map_to_base

@[simp]
theorem map_id (ξ : CurveGeometricPointOver K X) : map ξ (𝟙 X) = ξ :=
  rfl

@[simp]
theorem map_comp (ξ : CurveGeometricPointOver K X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    map ξ (f ≫ g) = map (map ξ f) g :=
  rfl

end CurveGeometricPointOver

/-- The large-universe pointed étale `π₁` attached to a chosen geometric point.  This is useful
for describing the intended semantics of the point-free profunctor, but the Hom-form statement does
not select such a point globally. -/
noncomputable def properHyperbolicCurvePointedEtalePi1Large {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : ProperHyperbolicCurveOver K)
    (ξ : CurveGeometricPointOver K X) : ProfiniteGrp.{u + 1} :=
  pointedEtalePi1 ξ.point

/-- The large-universe augmentation from a pointed curve `π₁` to the pointed base `π₁`. -/
noncomputable def properHyperbolicCurvePointedEtalePi1ToBaseLarge {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : ProperHyperbolicCurveOver K)
    (ξ : CurveGeometricPointOver K X) :
    properHyperbolicCurvePointedEtalePi1Large K X ξ ⟶ basePointedEtalePi1Large K :=
  show pointedEtalePi1 ξ.point ⟶ pointedEtalePi1 (baseGeometricPoint K) from
    pointedEtalePi1Map ξ.point X.toOver.hom ≫
      (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base) :
        pointedEtalePi1 (ξ.point ≫ X.toOver.hom) ⟶ pointedEtalePi1 (baseGeometricPoint K))

@[simp]
theorem properHyperbolicCurvePointedEtalePi1ToBaseLarge_eq {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : ProperHyperbolicCurveOver K)
    (ξ : CurveGeometricPointOver K X) :
    properHyperbolicCurvePointedEtalePi1ToBaseLarge K X ξ =
      pointedEtalePi1Map ξ.point X.toOver.hom ≫
        (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base) :
          pointedEtalePi1 (ξ.point ≫ X.toOver.hom) ⟶ pointedEtalePi1 (baseGeometricPoint K)) :=
  rfl

/-- Transport a pointed `π₁` map across an equality of scheme morphisms by the matching
`eqToHom` on the target pointed `π₁`. -/
lemma pointedEtalePi1Map_eqToHom {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) {f g : X ⟶ Y} (h : f = g) :
    pointedEtalePi1Map ξ f ≫
      (eqToHom (congrArg pointedEtalePi1 (congrArg (fun t : X ⟶ Y ↦ ξ ≫ t) h)) :
        pointedEtalePi1 (ξ ≫ f) ⟶ pointedEtalePi1 (ξ ≫ g)) =
    pointedEtalePi1Map ξ g := by
  subst h
  simp

/-- Raw compatibility of the curve-to-base pointed `π₁` maps with morphisms over the base,
with the dependent target equalities expressed by `eqToHom`. -/
theorem pointedEtalePi1Map_toBase_raw {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X Y : ProperHyperbolicCurveOver K}
    (ξ : CurveGeometricPointOver K X) (f : X ⟶ Y) :
    pointedEtalePi1Map ξ.point (f.hom.hom.left ≫ Y.toOver.hom) ≫
        (eqToHom (congrArg pointedEtalePi1 (ξ.map f).map_to_base) :
          pointedEtalePi1 ((ξ.map f).point ≫ Y.toOver.hom) ⟶
            pointedEtalePi1 (baseGeometricPoint K)) =
      pointedEtalePi1Map ξ.point X.toOver.hom ≫
        (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base) :
          pointedEtalePi1 (ξ.point ≫ X.toOver.hom) ⟶
            pointedEtalePi1 (baseGeometricPoint K)) := by
  let e : ξ.point ≫ (f.hom.hom.left ≫ Y.toOver.hom) = ξ.point ≫ X.toOver.hom :=
    congrArg (fun t : X.toScheme ⟶ baseScheme K ↦ ξ.point ≫ t) f.hom.hom.w
  calc
    pointedEtalePi1Map ξ.point (f.hom.hom.left ≫ Y.toOver.hom) ≫
        (eqToHom (congrArg pointedEtalePi1 (ξ.map f).map_to_base) :
          pointedEtalePi1 ((ξ.map f).point ≫ Y.toOver.hom) ⟶
            pointedEtalePi1 (baseGeometricPoint K))
        = pointedEtalePi1Map ξ.point (f.hom.hom.left ≫ Y.toOver.hom) ≫
          ((eqToHom (congrArg pointedEtalePi1 e) :
              pointedEtalePi1 (ξ.point ≫ (f.hom.hom.left ≫ Y.toOver.hom)) ⟶
                pointedEtalePi1 (ξ.point ≫ X.toOver.hom)) ≫
            (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base) :
              pointedEtalePi1 (ξ.point ≫ X.toOver.hom) ⟶
                pointedEtalePi1 (baseGeometricPoint K))) := by
            rw [eqToHom_trans]
            rfl
    _ = (pointedEtalePi1Map ξ.point (f.hom.hom.left ≫ Y.toOver.hom) ≫
          (eqToHom (congrArg pointedEtalePi1 e) :
              pointedEtalePi1 (ξ.point ≫ (f.hom.hom.left ≫ Y.toOver.hom)) ⟶
                pointedEtalePi1 (ξ.point ≫ X.toOver.hom))) ≫
            (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base) :
              pointedEtalePi1 (ξ.point ≫ X.toOver.hom) ⟶
                pointedEtalePi1 (baseGeometricPoint K)) := by
          rw [Category.assoc]
    _ = pointedEtalePi1Map ξ.point X.toOver.hom ≫
        (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base) :
          pointedEtalePi1 (ξ.point ≫ X.toOver.hom) ⟶
            pointedEtalePi1 (baseGeometricPoint K)) := by
          rw [pointedEtalePi1Map_eqToHom ξ.point f.hom.hom.w]

/-- In the outer quotient, the chosen curve-to-base augmentation is represented by the raw
scheme-map `π₁` morphism followed by the `eqToHom` transport to the fixed base point. -/
theorem properHyperbolicCurvePointedEtalePi1ToBaseLarge_outer_map {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X : ProperHyperbolicCurveOver K}
    (ξ : CurveGeometricPointOver K X) :
    (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map
        (properHyperbolicCurvePointedEtalePi1ToBaseLarge K X ξ) =
      (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map
          (pointedEtalePi1Map ξ.point X.toOver.hom) ≫
        (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map
          (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base)) := by
  let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
  change Q.map
      (show pointedEtalePi1 ξ.point ⟶ pointedEtalePi1 (baseGeometricPoint K) from
        pointedEtalePi1Map ξ.point X.toOver.hom ≫
          (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base) :
            pointedEtalePi1 (ξ.point ≫ X.toOver.hom) ⟶ pointedEtalePi1 (baseGeometricPoint K))) = _
  rw [Q.map_comp]
end ProperHyperbolicCurveHomStandalone
end MochizukiLocalProP
end Examples
end Anabelian
