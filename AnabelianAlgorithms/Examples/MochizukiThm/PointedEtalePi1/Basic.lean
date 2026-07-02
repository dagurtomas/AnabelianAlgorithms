/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

module

public import AnabelianAlgorithms.Examples.MochizukiThm.AugmentedProfinite
public import AnabelianAlgorithms.Examples.MochizukiThm.FromPi1.FundamentalGroup.Galois
public import Mathlib.CategoryTheory.Galois.Equivalence
public import Mathlib.Topology.Algebra.Module.TransferInstance

/-!
# Pointed arithmetic étale fundamental groups: basic constructions

This file defines pointed finite-étale fiber fundamental groups, the maps induced by scheme
morphisms, and the finite-index image statement for finite-étale morphisms.
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

/-! ## Automorphisms of finite-fiber functors -/

/-- Precomposition with a functor is continuous on automorphism groups of finite-set-valued
functors. This is the left-whiskering analogue of mathlib's
`continuous_mapAut_whiskeringRight`. -/
lemma continuous_mapAut_whiskeringLeft {C D : Type*} [Category C] [Category D]
    (F : C ⥤ FintypeCat.{u}) (L : D ⥤ C) :
    Continuous (((Functor.whiskeringLeft D C FintypeCat).obj L).mapAut F) := by
  rw [Topology.IsInducing.continuous_iff (autEmbedding_isClosedEmbedding _).isInducing,
    continuous_pi_iff]
  intro Y
  change Continuous fun a ↦ autEmbedding F a (L.obj Y)
  fun_prop

/-- Conjugation by a natural isomorphism is continuous on automorphism groups. -/
lemma continuous_conjAut {C : Type*} [Category C] {F G : C ⥤ FintypeCat.{u}}
    (e : F ≅ G) : Continuous e.conjAut := by
  rw [Topology.IsInducing.continuous_iff (autEmbedding_isClosedEmbedding _).isInducing,
    continuous_pi_iff]
  intro X
  have hcont : Continuous (fun a : Aut F ↦ autEmbedding F a X) := by fun_prop
  have hc : Continuous (fun b : Aut (F.obj X) ↦ (e.app X).conjAut b) := by fun_prop
  convert hc.comp hcont using 1
  rfl

/-! ## Universe transport for profinite groups -/

/-- The multiplicative homeomorphism from a small model of a profinite group to the group. -/
noncomputable def shrinkContinuousMulEquiv (G : ProfiniteGrp.{u + 1}) [Small.{u} G] :
    Shrink.{u} G ≃ₜ* G where
  __ := (Shrink.homeomorph G).symm
  map_mul' x y := by
    change (equivShrink G).symm (x * y) =
      (equivShrink G).symm x * (equivShrink G).symm y
    simp

noncomputable instance shrinkIsTopologicalGroup (G : ProfiniteGrp.{u + 1}) [Small.{u} G] :
    IsTopologicalGroup (Shrink.{u} G) :=
  (shrinkContinuousMulEquiv G).isTopologicalGroup

noncomputable instance shrinkCompactSpace (G : ProfiniteGrp.{u + 1}) [Small.{u} G] :
    CompactSpace (Shrink.{u} G) :=
  Homeomorph.compactSpace (Shrink.homeomorph G)

noncomputable instance shrinkTotallyDisconnectedSpace (G : ProfiniteGrp.{u + 1}) [Small.{u} G] :
    TotallyDisconnectedSpace (Shrink.{u} G) :=
  Homeomorph.totallyDisconnectedSpace (Shrink.homeomorph G)

/-- A small-universe profinite model of a profinite group living one universe higher. -/
noncomputable def shrinkProfiniteGrp (G : ProfiniteGrp.{u + 1}) [Small.{u} G] : ProfiniteGrp.{u} :=
  ProfiniteGrp.of (Shrink.{u} G)

/-- A continuous homomorphism induces a homomorphism between small-universe profinite models. -/
noncomputable def shrinkProfiniteGrpMap {G H : ProfiniteGrp.{u + 1}} [Small.{u} G]
    [Small.{u} H] (f : G ⟶ H) : shrinkProfiniteGrp G ⟶ shrinkProfiniteGrp H :=
  ProfiniteGrp.ofHom {
    toMonoidHom := {
      toFun x := equivShrink H (f ((equivShrink G).symm x))
      map_one' := by
        apply (equivShrink H).symm.injective
        simp
      map_mul' x y := by
        apply (equivShrink H).symm.injective
        simp [map_mul] }
    continuous_toFun := by
      change Continuous ((Shrink.homeomorph H) ∘ f ∘ (Shrink.homeomorph G).symm)
      fun_prop }

noncomputable instance uliftTotallyDisconnectedSpace (G : ProfiniteGrp.{u}) :
    TotallyDisconnectedSpace (ULift.{u + 1, u} G) :=
  Homeomorph.totallyDisconnectedSpace (Homeomorph.ulift.symm : G ≃ₜ ULift.{u + 1, u} G)

/-- A large-universe copy of a profinite group. -/
noncomputable def uliftProfiniteGrp (G : ProfiniteGrp.{u}) : ProfiniteGrp.{u + 1} :=
  ProfiniteGrp.of (ULift.{u + 1, u} G)

/-- A continuous homomorphism induces a homomorphism between large-universe copies. -/
noncomputable def uliftProfiniteGrpMap {G H : ProfiniteGrp.{u}} (f : G ⟶ H) :
    uliftProfiniteGrp G ⟶ uliftProfiniteGrp H :=
  ProfiniteGrp.ofHom {
    toMonoidHom := {
      toFun x := ULift.up (f x.down)
      map_one' := by
        ext
        simp
      map_mul' x y := by
        ext
        simp [map_mul] }
    continuous_toFun := by
      change Continuous (ULift.up ∘ (f : G → H) ∘ ULift.down)
      fun_prop }

@[simp]
theorem uliftProfiniteGrpMap_id (G : ProfiniteGrp.{u}) :
    uliftProfiniteGrpMap (𝟙 G) = 𝟙 (uliftProfiniteGrp G) := by
  ext x
  cases x
  rfl

@[simp]
theorem uliftProfiniteGrpMap_comp {G H I : ProfiniteGrp.{u}} (f : G ⟶ H) (g : H ⟶ I) :
    uliftProfiniteGrpMap (f ≫ g) = uliftProfiniteGrpMap f ≫ uliftProfiniteGrpMap g := by
  ext x
  cases x
  rfl

/-- Openness is preserved by passage to large-universe copies. -/
theorem uliftProfiniteGrpMap_isOpenMap {G H : ProfiniteGrp.{u}} (f : G ⟶ H)
    (hf : IsOpenMap f) : IsOpenMap (uliftProfiniteGrpMap f) := by
  change IsOpenMap (ULift.up ∘ (f : G → H) ∘ ULift.down)
  exact Homeomorph.ulift.symm.isOpenMap.comp (hf.comp Homeomorph.ulift.isOpenMap)

/-! ## Pointed finite-étale fundamental groups -/

/-- The full pointed étale fundamental group of a pointed connected scheme. -/
noncomputable def pointedEtalePi1 {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X) :
    ProfiniteGrp.{u + 1} :=
  ProfiniteGrp.of (Aut (AlgebraicGeometry.FiniteEtale.fiber ξ))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pullback of finite étale covers identifies the fiber at `ξ ≫ f` with the pulled-back fiber. -/
noncomputable def fiberCompIso {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) :
    AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f) ≅
      AlgebraicGeometry.FiniteEtale.pullback f ⋙ AlgebraicGeometry.FiniteEtale.fiber ξ :=
  let e := MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) ξ f
  NatIso.ofComponents (fun A ↦ (AlgebraicGeometry.FiniteEtale.forgetScheme Ω).mapIso (e.app A))
    (fun {A B} g ↦ by
      dsimp [AlgebraicGeometry.FiniteEtale.fiber]
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg ((AlgebraicGeometry.FiniteEtale.forgetScheme Ω).map)
        (e.hom.naturality g))

/-- The homomorphism on full pointed étale fundamental groups induced by a scheme morphism. -/
noncomputable def pointedEtalePi1Map {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) :
    pointedEtalePi1 ξ ⟶ pointedEtalePi1 (ξ ≫ f) :=
  ProfiniteGrp.ofHom {
    toMonoidHom := (fiberCompIso ξ f).symm.conjAut.toMonoidHom.comp
      (Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
        ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Y)
          (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
          (AlgebraicGeometry.FiniteEtale.pullback f)))
    continuous_toFun := (continuous_conjAut (fiberCompIso ξ f).symm).comp
      (continuous_mapAut_whiskeringLeft (AlgebraicGeometry.FiniteEtale.fiber ξ)
        (AlgebraicGeometry.FiniteEtale.pullback f)) }

/-- Stabilizers of points in finite-étale fibers are open in the pointed étale fundamental group. -/
theorem pointedEtalePi1_stabilizer_isOpen {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X)
    (A : AlgebraicGeometry.FiniteEtale X) (a : (AlgebraicGeometry.FiniteEtale.fiber ξ).obj A) :
    IsOpen (MulAction.stabilizer (Aut (AlgebraicGeometry.FiniteEtale.fiber ξ)) a :
      Set (Aut (AlgebraicGeometry.FiniteEtale.fiber ξ))) := by
  exact stabilizer_isOpen _ _

/-- If the range of a pointed étale `π₁` map contains a fiber-point stabilizer, then it has
finite index. -/
theorem pointedEtalePi1Map_finiteIndex_range_of_stabilizer_le
    {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y)
    (A : AlgebraicGeometry.FiniteEtale Y)
    (a : (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).obj A)
    (hstab : MulAction.stabilizer (Aut (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f))) a ≤
      MonoidHom.range (pointedEtalePi1Map ξ f).hom.toMonoidHom) :
    Subgroup.FiniteIndex (MonoidHom.range (pointedEtalePi1Map ξ f).hom.toMonoidHom) := by
  exact ProfiniteGrp.finiteIndex_range_of_open_subgroup_le (pointedEtalePi1Map ξ f)
    (pointedEtalePi1_stabilizer_isOpen (ξ ≫ f) A a) hstab

/-- A finite-étale morphism, viewed as a finite-étale cover of its target. -/
noncomputable def finiteEtaleCoverOfIsFiniteEtale {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFiniteEtale f] : AlgebraicGeometry.FiniteEtale Y :=
  MorphismProperty.Over.mk ⊤ f inferInstance

/-! ## Finite-étale test covers -/

/-- The terminal finite-étale cover of a scheme, represented by the identity morphism. -/
noncomputable def finiteEtaleTerminal (X : Scheme.{u}) : AlgebraicGeometry.FiniteEtale X :=
  MorphismProperty.Over.mk ⊤ (𝟙 X)
    (MorphismProperty.id_mem (@IsFiniteEtale : MorphismProperty Scheme.{u}) X)

@[simp]
lemma finiteEtaleTerminal_hom (X : Scheme.{u}) : (finiteEtaleTerminal X).hom = 𝟙 X := rfl

@[simp]
lemma finiteEtaleTerminal_left (X : Scheme.{u}) : (finiteEtaleTerminal X).left = X := rfl

/-- The identity finite-étale cover is terminal. -/
noncomputable def finiteEtaleTerminal_isTerminal (X : Scheme.{u}) :
    CategoryTheory.Limits.IsTerminal (finiteEtaleTerminal X) := by
  refine CategoryTheory.Limits.IsTerminal.ofUniqueHom (fun A ↦ ?_) (fun A g ↦ ?_)
  · refine MorphismProperty.Over.homMk A.hom ?_
    exact Category.comp_id A.hom
  · apply MorphismProperty.Over.Hom.ext
    change g.left = A.hom
    have hw := g.w
    change g.left ≫ 𝟙 X = A.hom ≫ 𝟙 X at hw
    exact hw.trans (Category.comp_id A.hom)

/-- The fiber of the terminal finite-étale cover is a singleton. -/
@[reducible]
noncomputable def finiteEtaleTerminal_fiber_unique {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X) :
    Unique ((AlgebraicGeometry.FiniteEtale.fiber ξ).obj (finiteEtaleTerminal X)) := by
  have hT : CategoryTheory.Limits.IsTerminal (finiteEtaleTerminal X) :=
    finiteEtaleTerminal_isTerminal X
  have hFT : CategoryTheory.Limits.IsTerminal
      ((AlgebraicGeometry.FiniteEtale.fiber ξ).obj (finiteEtaleTerminal X)) :=
    CategoryTheory.Limits.IsTerminal.isTerminalObj
      (AlgebraicGeometry.FiniteEtale.fiber ξ) (finiteEtaleTerminal X) hT
  exact CategoryTheory.Limits.Concrete.uniqueOfTerminalOfPreserves
    ((AlgebraicGeometry.FiniteEtale.fiber ξ).obj (finiteEtaleTerminal X)) hFT

/-- The unique point of the fiber of the terminal finite-étale cover. -/
noncomputable def finiteEtaleTerminalFiberPoint {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X) :
    (AlgebraicGeometry.FiniteEtale.fiber ξ).obj (finiteEtaleTerminal X) := by
  letI := finiteEtaleTerminal_fiber_unique ξ
  exact default

/-- The diagonal section of the pullback of a finite-étale cover by itself. -/
noncomputable def finiteEtaleSelfPullbackDiagonal {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFiniteEtale f] :
    finiteEtaleTerminal X ⟶
      (AlgebraicGeometry.FiniteEtale.pullback f).obj (finiteEtaleCoverOfIsFiniteEtale f) := by
  refine MorphismProperty.Over.homMk (Limits.pullback.lift (𝟙 X) (𝟙 X) ?_) ?_
  · change 𝟙 X ≫ f = 𝟙 X ≫ f
    rfl
  · dsimp [AlgebraicGeometry.FiniteEtale.pullback, finiteEtaleCoverOfIsFiniteEtale,
      finiteEtaleTerminal]
    change Limits.pullback.lift (𝟙 X) (𝟙 X)
        (by simp : 𝟙 X ≫ f = 𝟙 X ≫ f) ≫ Limits.pullback.snd f f = 𝟙 X
    exact Limits.pullback.lift_snd _ _ _

/-- The canonical point of the fiber of a finite-étale cover `f : X ⟶ Y` above a point
`ξ : Spec Ω ⟶ X`, viewed over the composite point of `Y`. -/
noncomputable def finiteEtaleSelfFiberPoint {X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) [IsFiniteEtale f] :
    (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).obj (finiteEtaleCoverOfIsFiniteEtale f) :=
  (fiberCompIso ξ f).inv.app (finiteEtaleCoverOfIsFiniteEtale f)
    ((AlgebraicGeometry.FiniteEtale.fiber ξ).map (finiteEtaleSelfPullbackDiagonal f)
      (finiteEtaleTerminalFiberPoint ξ))

/-- The canonical finite-étale-cover stabilizer is open.  This is the open subgroup expected to
witness finite-index image in the finite-étale case once the stabilizer-containment step is
proved. -/
theorem finiteEtaleSelfFiberPoint_stabilizer_isOpen {X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) [IsFiniteEtale f] :
    IsOpen (MulAction.stabilizer (Aut (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)))
      (finiteEtaleSelfFiberPoint ξ f) :
        Set (Aut (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)))) :=
  pointedEtalePi1_stabilizer_isOpen (ξ ≫ f) (finiteEtaleCoverOfIsFiniteEtale f)
    (finiteEtaleSelfFiberPoint ξ f)

/-- For a finite-étale morphism, containment of the canonical fiber-point stabilizer in the range
of the pointed `π₁` map implies finite-index image. -/
theorem pointedEtalePi1Map_finiteIndex_range_of_isFiniteEtale_of_stabilizer_le
    {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) [IsFiniteEtale f]
    (hstab : MulAction.stabilizer (Aut (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)))
      (finiteEtaleSelfFiberPoint ξ f) ≤
        MonoidHom.range (pointedEtalePi1Map ξ f).hom.toMonoidHom) :
    Subgroup.FiniteIndex (MonoidHom.range (pointedEtalePi1Map ξ f).hom.toMonoidHom) :=
  pointedEtalePi1Map_finiteIndex_range_of_stabilizer_le ξ f
    (finiteEtaleCoverOfIsFiniteEtale f) (finiteEtaleSelfFiberPoint ξ f) hstab

@[simp]
lemma pointedEtalePi1Map_hom_app {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y)
    (τ : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ))
    (A : AlgebraicGeometry.FiniteEtale Y) :
    ((pointedEtalePi1Map ξ f).hom τ).hom.app A =
      (fiberCompIso ξ f).hom.app A ≫
        τ.hom.app ((AlgebraicGeometry.FiniteEtale.pullback f).obj A) ≫
          (fiberCompIso ξ f).inv.app A :=
  rfl

/-! ## Open stabilizers and finite-index image -/

set_option linter.unusedFintypeInType false in
/-- The finite quotient by an open subgroup, shrunk to a prescribed universe, is a continuous
finite action. -/
lemma quotientOpenSubgroup_shrink_action_isContinuous {G : Type uG}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : OpenSubgroup G) [Fintype (G ⧸ V.toSubgroup)] :
    (Action.FintypeCat.ofMulAction G
      (FintypeCat.of (Shrink.{u, uG} (G ⧸ V.toSubgroup)))).IsContinuous := by
  rw [Action.isContinuous_def]
  haveI : DiscreteTopology
      ↑((forget₂ (Action FintypeCat G) TopCat).obj
        (Action.FintypeCat.ofMulAction G
          (FintypeCat.of (Shrink.{u, uG} (G ⧸ V.toSubgroup))))) := ⟨rfl⟩
  rw [continuous_prod_of_discrete_right]
  intro y
  haveI : DiscreteTopology
      ↑((forget₂ FintypeCat TopCat).obj
        (Action.FintypeCat.ofMulAction G
          (FintypeCat.of (Shrink.{u, uG} (G ⧸ V.toSubgroup)))).V) := ⟨rfl⟩
  rw [continuous_discrete_rng]
  intro x
  obtain ⟨y', rfl⟩ := (equivShrink.{u, uG} (G ⧸ V.toSubgroup)).surjective y
  obtain ⟨x', rfl⟩ := (equivShrink.{u, uG} (G ⧸ V.toSubgroup)).surjective x
  induction y' using Quotient.inductionOn with
  | h a =>
      induction x' using Quotient.inductionOn with
      | h b =>
          have hopen : IsOpen ((fun m : G ↦ (m * a)⁻¹ * b) ⁻¹' (V.toSubgroup : Set G)) := by
            exact V.isOpen.preimage (by fun_prop)
          convert hopen using 1
          ext m
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          change (m • (equivShrink.{u, uG} (G ⧸ V.toSubgroup)
                (⟦a⟧ : G ⧸ V.toSubgroup)) =
              equivShrink.{u, uG} (G ⧸ V.toSubgroup) ⟦b⟧) ↔
            (m * a)⁻¹ * b ∈ V.toSubgroup
          rw [← equivShrink_smul]
          change (equivShrink.{u, uG} (G ⧸ V.toSubgroup)
              (⟦m * a⟧ : G ⧸ V.toSubgroup) =
              equivShrink.{u, uG} (G ⧸ V.toSubgroup) ⟦b⟧) ↔
            (m * a)⁻¹ * b ∈ V.toSubgroup
          rw [(equivShrink.{u, uG} (G ⧸ V.toSubgroup)).apply_eq_iff_eq]
          rw [Quotient.eq]
          rw [QuotientGroup.leftRel_apply]

/-- The finite quotient by an open subgroup as a continuous action in a prescribed universe. -/
noncomputable def quotientOpenSubgroupShrinkContAction {G : Type uG}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : OpenSubgroup G) [Fintype (G ⧸ V.toSubgroup)] :
    ContAction FintypeCat.{u} G :=
  ⟨Action.FintypeCat.ofMulAction G
      (FintypeCat.of (Shrink.{u, uG} (G ⧸ V.toSubgroup))),
    quotientOpenSubgroup_shrink_action_isContinuous V⟩

set_option linter.unusedFintypeInType false in
lemma quotientOpenSubgroupShrink_base_fixed_iff {G : Type uG}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : OpenSubgroup G) [Fintype (G ⧸ V.toSubgroup)] (g : G) :
    g • (equivShrink.{u, uG} (G ⧸ V.toSubgroup) (⟦(1 : G)⟧ : G ⧸ V.toSubgroup)) =
        equivShrink.{u, uG} (G ⧸ V.toSubgroup) (⟦(1 : G)⟧ : G ⧸ V.toSubgroup) ↔
      g ∈ V.toSubgroup := by
  rw [← equivShrink_smul]
  rw [(equivShrink.{u, uG} (G ⧸ V.toSubgroup)).apply_eq_iff_eq]
  change (⟦g * 1⟧ : G ⧸ V.toSubgroup) = ⟦(1 : G)⟧ ↔ g ∈ V.toSubgroup
  rw [Quotient.eq]
  rw [QuotientGroup.leftRel_apply]
  simp

/-- A fiber point fixed by the full pointed étale fundamental group comes from a section of the
finite-étale cover. -/
noncomputable def finiteEtaleSectionOfFixedFiberPoint {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (B : AlgebraicGeometry.FiniteEtale X)
    (b : (AlgebraicGeometry.FiniteEtale.fiber ξ).obj B)
    (hb : ∀ τ : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ), τ.hom.app B b = b) :
    finiteEtaleTerminal X ⟶ B := by
  let F := AlgebraicGeometry.FiniteEtale.fiber ξ
  let T := finiteEtaleTerminal X
  let h : (functorToAction F).obj T ⟶ (functorToAction F).obj B :=
    { hom := FintypeCat.homMk (fun _ ↦ b)
      comm := by
        intro τ
        ext t
        change b = τ.hom.app B b
        exact (hb τ).symm }
  exact (functorToAction F).preimage h

@[simp]
lemma finiteEtaleSectionOfFixedFiberPoint_fiber {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (B : AlgebraicGeometry.FiniteEtale X)
    (b : (AlgebraicGeometry.FiniteEtale.fiber ξ).obj B)
    (hb : ∀ τ : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ), τ.hom.app B b = b) :
    (AlgebraicGeometry.FiniteEtale.fiber ξ).map
      (finiteEtaleSectionOfFixedFiberPoint ξ B b hb) (finiteEtaleTerminalFiberPoint ξ) = b := by
  let F := AlgebraicGeometry.FiniteEtale.fiber ξ
  let T := finiteEtaleTerminal X
  let h : (functorToAction F).obj T ⟶ (functorToAction F).obj B :=
    { hom := FintypeCat.homMk (fun _ ↦ b)
      comm := by
        intro τ
        ext t
        change b = τ.hom.app B b
        exact (hb τ).symm }
  change (F.map ((functorToAction F).preimage h)) (finiteEtaleTerminalFiberPoint ξ) = b
  have hmap : (functorToAction F).map ((functorToAction F).preimage h) = h :=
    (functorToAction F).map_preimage h
  have hhom : ((functorToAction F).map ((functorToAction F).preimage h)).hom = h.hom :=
    congrArg Action.Hom.hom hmap
  exact ConcreteCategory.congr_hom hhom (finiteEtaleTerminalFiberPoint ξ)

/-- If a target automorphism fixes a point of a finite-étale cover, then the corresponding source
automorphism fixes the transported point on the pullback cover. -/
lemma pointedEtalePi1Map_fixed_pullback_point {X Y : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y)
    (A : AlgebraicGeometry.FiniteEtale Y)
    (b : (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).obj A)
    (τ : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ))
    (hb : ((pointedEtalePi1Map ξ f).hom τ).hom.app A b = b) :
    τ.hom.app ((AlgebraicGeometry.FiniteEtale.pullback f).obj A)
      ((fiberCompIso ξ f).hom.app A b) =
    (fiberCompIso ξ f).hom.app A b := by
  have hb' : ((fiberCompIso ξ f).hom.app A ≫
      τ.hom.app ((AlgebraicGeometry.FiniteEtale.pullback f).obj A) ≫
        (fiberCompIso ξ f).inv.app A) b = b := by
    simpa using hb
  have hcong := congrArg ((fiberCompIso ξ f).hom.app A) hb'
  let y := τ.hom.app ((AlgebraicGeometry.FiniteEtale.pullback f).obj A)
      ((fiberCompIso ξ f).hom.app A b)
  have hinvhom : (fiberCompIso ξ f).hom.app A ((fiberCompIso ξ f).inv.app A y) = y := by
    have h := ConcreteCategory.congr_hom (Iso.inv_hom_id ((fiberCompIso ξ f).app A)) y
    change (fiberCompIso ξ f).hom.app A ((fiberCompIso ξ f).inv.app A y) = y at h
    exact h
  change (fiberCompIso ξ f).hom.app A ((fiberCompIso ξ f).inv.app A y) =
    (fiberCompIso ξ f).hom.app A b at hcong
  rw [hinvhom] at hcong
  exact hcong

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A point of a finite-étale cover whose pullback fiber point is fixed by the source fundamental
group is the image of the canonical self-fiber point under a morphism out of the cover `f`. -/
lemma finiteEtaleSelfFiberPoint_map_of_fixed_pullback_point {X Y : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) [IsFiniteEtale f]
    (A : AlgebraicGeometry.FiniteEtale Y)
    (b : (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).obj A)
    (hx : ∀ τ : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ),
      τ.hom.app ((AlgebraicGeometry.FiniteEtale.pullback f).obj A)
        ((fiberCompIso ξ f).hom.app A b) = (fiberCompIso ξ f).hom.app A b) :
    ∃ m : finiteEtaleCoverOfIsFiniteEtale f ⟶ A,
      (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).map m (finiteEtaleSelfFiberPoint ξ f) = b := by
  let adj := MorphismProperty.Over.mapPullbackAdj (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ f
    (show IsFiniteEtale f from inferInstance) trivial
  let s := finiteEtaleSectionOfFixedFiberPoint ξ ((AlgebraicGeometry.FiniteEtale.pullback f).obj A)
    ((fiberCompIso ξ f).hom.app A b) hx
  let m : finiteEtaleCoverOfIsFiniteEtale f ⟶ A :=
    (adj.homEquiv (finiteEtaleTerminal X) A).symm s
  refine ⟨m, ?_⟩
  have hdiag :
      finiteEtaleSelfPullbackDiagonal f ≫
        (AlgebraicGeometry.FiniteEtale.pullback f).map m = s := by
    have hm : adj.unit.app (finiteEtaleTerminal X) ≫
        (AlgebraicGeometry.FiniteEtale.pullback f).map m = s := by
      simpa [m] using (adj.homEquiv_unit (finiteEtaleTerminal X) A m).symm
    have hunit : adj.unit.app (finiteEtaleTerminal X) = finiteEtaleSelfPullbackDiagonal f := rfl
    rw [← hunit]
    exact hm
  have hs_fiber :
      (AlgebraicGeometry.FiniteEtale.fiber ξ).map s (finiteEtaleTerminalFiberPoint ξ) =
        (show (AlgebraicGeometry.FiniteEtale.fiber ξ).obj
            ((AlgebraicGeometry.FiniteEtale.pullback f).obj A) from
          (fiberCompIso ξ f).hom.app A b) := by
    simp [s]
  have hself : (fiberCompIso ξ f).hom.app (finiteEtaleCoverOfIsFiniteEtale f)
      (finiteEtaleSelfFiberPoint ξ f) =
      (AlgebraicGeometry.FiniteEtale.fiber ξ).map (finiteEtaleSelfPullbackDiagonal f)
        (finiteEtaleTerminalFiberPoint ξ) := by
    let z := (AlgebraicGeometry.FiniteEtale.fiber ξ).map (finiteEtaleSelfPullbackDiagonal f)
        (finiteEtaleTerminalFiberPoint ξ)
    change (fiberCompIso ξ f).hom.app (finiteEtaleCoverOfIsFiniteEtale f)
      ((fiberCompIso ξ f).inv.app (finiteEtaleCoverOfIsFiniteEtale f) z) = z
    have h := ConcreteCategory.congr_hom
      (Iso.inv_hom_id ((fiberCompIso ξ f).app (finiteEtaleCoverOfIsFiniteEtale f))) z
    change (fiberCompIso ξ f).hom.app (finiteEtaleCoverOfIsFiniteEtale f)
      ((fiberCompIso ξ f).inv.app (finiteEtaleCoverOfIsFiniteEtale f) z) = z at h
    exact h
  have hright : ((fiberCompIso ξ f).hom.app (finiteEtaleCoverOfIsFiniteEtale f) ≫
        (AlgebraicGeometry.FiniteEtale.fiber ξ).map
          ((AlgebraicGeometry.FiniteEtale.pullback f).map m))
        (finiteEtaleSelfFiberPoint ξ f) = (fiberCompIso ξ f).hom.app A b := by
    change (AlgebraicGeometry.FiniteEtale.fiber ξ).map
        ((AlgebraicGeometry.FiniteEtale.pullback f).map m)
      ((fiberCompIso ξ f).hom.app (finiteEtaleCoverOfIsFiniteEtale f)
        (finiteEtaleSelfFiberPoint ξ f)) = _
    rw [hself]
    calc
      (AlgebraicGeometry.FiniteEtale.fiber ξ).map
          ((AlgebraicGeometry.FiniteEtale.pullback f).map m)
          ((AlgebraicGeometry.FiniteEtale.fiber ξ).map (finiteEtaleSelfPullbackDiagonal f)
            (finiteEtaleTerminalFiberPoint ξ))
          = (AlgebraicGeometry.FiniteEtale.fiber ξ).map
              (finiteEtaleSelfPullbackDiagonal f ≫ (AlgebraicGeometry.FiniteEtale.pullback f).map m)
                (finiteEtaleTerminalFiberPoint ξ) := by
              rw [Functor.map_comp_apply]
      _ = (AlgebraicGeometry.FiniteEtale.fiber ξ).map s (finiteEtaleTerminalFiberPoint ξ) := by
              rw [hdiag]
      _ = (fiberCompIso ξ f).hom.app A b := hs_fiber
  have hnat := (fiberCompIso ξ f).hom.naturality m
  have h_congr := ConcreteCategory.congr_hom hnat (finiteEtaleSelfFiberPoint ξ f)
  have hhom : (fiberCompIso ξ f).hom.app A
      ((AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).map m (finiteEtaleSelfFiberPoint ξ f)) =
      (fiberCompIso ξ f).hom.app A b := by
    change (fiberCompIso ξ f).hom.app A
        ((AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).map m (finiteEtaleSelfFiberPoint ξ f)) =
      ((fiberCompIso ξ f).hom.app (finiteEtaleCoverOfIsFiniteEtale f) ≫
        (AlgebraicGeometry.FiniteEtale.fiber ξ).map
          ((AlgebraicGeometry.FiniteEtale.pullback f).map m))
        (finiteEtaleSelfFiberPoint ξ f) at h_congr
    exact h_congr.trans hright
  have hinj : Function.Injective (fun x ↦ (fiberCompIso ξ f).hom.app A x) := by
    intro x y hxy
    have h := congrArg ((fiberCompIso ξ f).inv.app A) hxy
    change (fiberCompIso ξ f).inv.app A ((fiberCompIso ξ f).hom.app A x) =
      (fiberCompIso ξ f).inv.app A ((fiberCompIso ξ f).hom.app A y) at h
    have hx' : (fiberCompIso ξ f).inv.app A ((fiberCompIso ξ f).hom.app A x) = x := by
      have h' := ConcreteCategory.congr_hom (Iso.hom_inv_id ((fiberCompIso ξ f).app A)) x
      change (fiberCompIso ξ f).inv.app A ((fiberCompIso ξ f).hom.app A x) = x at h'
      exact h'
    have hy' : (fiberCompIso ξ f).inv.app A ((fiberCompIso ξ f).hom.app A y) = y := by
      have h' := ConcreteCategory.congr_hom (Iso.hom_inv_id ((fiberCompIso ξ f).app A)) y
      change (fiberCompIso ξ f).inv.app A ((fiberCompIso ξ f).hom.app A y) = y at h'
      exact h'
    rw [hx', hy'] at h
    exact h
  exact hinj hhom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For a finite-étale morphism, the stabilizer of the canonical self-fiber point is contained in
the image of the pointed étale `π₁` map. -/
theorem finiteEtaleSelfFiberPoint_stabilizer_le_range {X Y : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) [IsFiniteEtale f] :
    MulAction.stabilizer (Aut (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)))
        (finiteEtaleSelfFiberPoint ξ f) ≤
      MonoidHom.range (pointedEtalePi1Map ξ f).hom.toMonoidHom := by
  intro σ hσ
  let FY := AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)
  let FX := AlgebraicGeometry.FiniteEtale.fiber ξ
  let G := Aut FY
  let R : Subgroup G := MonoidHom.range (pointedEtalePi1Map ξ f).hom.toMonoidHom
  by_contra hσR
  have hRclosed : IsClosed (R : Set G) := by
    have hcompact : IsCompact (R : Set G) := by
      change IsCompact (Set.range ((pointedEtalePi1Map ξ f).hom : Aut FX → G))
      simpa [Set.image_univ] using
        isCompact_univ.image (pointedEtalePi1Map ξ f).hom.continuous_toFun
    exact hcompact.isClosed
  obtain ⟨Vsub, hVopen, hRV, hσV⟩ :=
    ProfiniteGrp.exists_open_subgroup_of_closed_subgroup_not_mem R hRclosed hσR
  let V : OpenSubgroup G := ⟨Vsub, hVopen⟩
  haveI : Finite (G ⧸ V.toSubgroup) := V.toSubgroup.quotient_finite_of_isOpen V.isOpen'
  haveI : Fintype (G ⧸ V.toSubgroup) := Fintype.ofFinite _
  let Q : ContAction FintypeCat.{u} G := quotientOpenSubgroupShrinkContAction.{u, u+1} V
  obtain ⟨A, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := functorToContAction FY) Q
  let q0 : Q.obj.V := equivShrink.{u, u+1} (G ⧸ V.toSubgroup) (⟦(1 : G)⟧ : G ⧸ V.toSubgroup)
  let b : FY.obj A := e.inv.hom.hom q0
  have hpre_fixed (τ : Aut FX) : ((pointedEtalePi1Map ξ f).hom τ).hom.app A b = b := by
    have hmemR : (pointedEtalePi1Map ξ f).hom τ ∈ R := ⟨τ, rfl⟩
    have hmemV : (pointedEtalePi1Map ξ f).hom τ ∈ V.toSubgroup := hRV hmemR
    have hq : ((pointedEtalePi1Map ξ f).hom τ : G) • q0 = q0 := by
      exact (quotientOpenSubgroupShrink_base_fixed_iff.{u, u+1} V
        ((pointedEtalePi1Map ξ f).hom τ)).mpr hmemV
    have hcomm := e.inv.hom.comm ((pointedEtalePi1Map ξ f).hom τ)
    have h := ConcreteCategory.congr_hom hcomm q0
    change e.inv.hom.hom (ConcreteCategory.hom (Q.obj.ρ ((pointedEtalePi1Map ξ f).hom τ)) q0) =
        ((pointedEtalePi1Map ξ f).hom τ).hom.app A (e.inv.hom.hom q0) at h
    rw [show ConcreteCategory.hom (Q.obj.ρ ((pointedEtalePi1Map ξ f).hom τ)) q0 =
        ((pointedEtalePi1Map ξ f).hom τ : G) • q0 by rfl, hq] at h
    exact h.symm
  have hx : ∀ τ : Aut FX,
      τ.hom.app ((AlgebraicGeometry.FiniteEtale.pullback f).obj A)
        ((fiberCompIso ξ f).hom.app A b) = (fiberCompIso ξ f).hom.app A b := by
    intro τ
    exact pointedEtalePi1Map_fixed_pullback_point ξ f A b τ (hpre_fixed τ)
  obtain ⟨m, hm⟩ := finiteEtaleSelfFiberPoint_map_of_fixed_pullback_point ξ f A b hx
  have hbσ : σ.hom.app A b = b := by
    have hnat := σ.hom.naturality m
    have h := ConcreteCategory.congr_hom hnat (finiteEtaleSelfFiberPoint ξ f)
    change σ.hom.app A
        ((AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).map m (finiteEtaleSelfFiberPoint ξ f)) =
      (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).map m
        (σ.hom.app (finiteEtaleCoverOfIsFiniteEtale f) (finiteEtaleSelfFiberPoint ξ f)) at h
    have hσa : σ.hom.app (finiteEtaleCoverOfIsFiniteEtale f) (finiteEtaleSelfFiberPoint ξ f) =
        finiteEtaleSelfFiberPoint ξ f := by
      exact (MulAction.mem_stabilizer_iff.mp hσ)
    rw [hm, hσa, hm] at h
    exact h
  have hqσ : (σ : G) • q0 = q0 := by
    have hcomm := e.hom.hom.comm σ
    have h := ConcreteCategory.congr_hom hcomm b
    change e.hom.hom.hom (σ.hom.app A b) =
        ConcreteCategory.hom (Q.obj.ρ σ) (e.hom.hom.hom b) at h
    rw [hbσ] at h
    have hinv : e.hom.hom.hom b = q0 := by
      have h' := ConcreteCategory.congr_hom
        (congrArg (fun k : Q ⟶ Q ↦ k.hom.hom) e.inv_hom_id) q0
      change ((e.inv.hom.hom ≫ e.hom.hom.hom) : Q.obj.V ⟶ Q.obj.V) q0 = q0 at h'
      simpa [b] using h'
    rw [hinv] at h
    change q0 = (σ : G) • q0 at h
    exact h.symm
  exact hσV ((quotientOpenSubgroupShrink_base_fixed_iff.{u, u+1} V σ).mp hqσ)

/-- Finite-étale morphisms induce finite-index image on pointed étale fundamental groups. -/
theorem pointedEtalePi1Map_finiteIndex_range_of_isFiniteEtale
    {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) [IsFiniteEtale f] :
    Subgroup.FiniteIndex (MonoidHom.range (pointedEtalePi1Map ξ f).hom.toMonoidHom) :=
  pointedEtalePi1Map_finiteIndex_range_of_isFiniteEtale_of_stabilizer_le ξ f
    (finiteEtaleSelfFiberPoint_stabilizer_le_range ξ f)
end ProperHyperbolicCurveHomStandalone
end MochizukiLocalProP
end Examples
end Anabelian
