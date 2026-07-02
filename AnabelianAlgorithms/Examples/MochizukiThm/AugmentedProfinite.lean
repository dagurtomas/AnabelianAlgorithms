/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.Topology.Algebra.Group.OpenMapping
public import Mathlib.Topology.Baire.LocallyCompactRegular
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Augmented profinite groups and outer morphisms

This file contains the profinite-group scaffolding used by the standalone Mochizuki statement:
open-map criteria for profinite homomorphisms, the example-local outer quotient of profinite
groups, augmented profinite groups over a fixed base, and the corresponding open outer morphisms.
-/

@[expose] public section

universe u uG

namespace ProfiniteGrp

open TopologicalSpace

/-- A profinite-group homomorphism is open if its range is open. -/
theorem isOpenMap_of_open_range {G H : ProfiniteGrp.{u}}
    (φ : G ⟶ H) (hφ : IsOpen (Set.range (φ : G → H))) : IsOpenMap φ := by
  let φrange : G →* φ.hom.range := φ.hom.toMonoidHom.rangeRestrict
  have hφ' : IsOpen (φ.hom.range : Set H) := by
    convert hφ
    ext y
    rfl
  haveI : BaireSpace φ.hom.range := hφ'.baireSpace
  have hφrange_surj : Function.Surjective φrange :=
    φ.hom.toMonoidHom.rangeRestrict_surjective
  have hφrange_cont : Continuous φrange := by
    change Continuous fun x : G ↦ (⟨φ x, x, rfl⟩ : φ.hom.range)
    exact φ.hom.continuous_toFun.subtype_mk (fun x ↦ ⟨x, rfl⟩)
  have hφrange_open : IsOpenMap φrange :=
    MonoidHom.isOpenMap_of_sigmaCompact φrange hφrange_surj hφrange_cont
  have hsubtype_open : IsOpenMap ((↑) : φ.hom.range → H) := hφ'.isOpenMap_subtype_val
  change IsOpenMap (((↑) : φ.hom.range → H) ∘ φrange)
  exact hsubtype_open.comp hφrange_open

/-- A profinite-group homomorphism has finite-index range if its range contains an open subgroup. -/
theorem finiteIndex_range_of_open_subgroup_le {G H : ProfiniteGrp.{u}} (φ : G ⟶ H)
    {U : Subgroup H} (hUopen : IsOpen (U : Set H))
    (hU : U ≤ MonoidHom.range φ.hom.toMonoidHom) :
    Subgroup.FiniteIndex (MonoidHom.range φ.hom.toMonoidHom) := by
  haveI : Subgroup.FiniteIndex U := by
    haveI : Finite (H ⧸ U) := U.quotient_finite_of_isOpen hUopen
    exact Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.finiteIndex_of_le hU

/-- In a profinite group, a closed subgroup can be separated from an outside element by an
open subgroup containing it. -/
theorem exists_open_subgroup_of_closed_subgroup_not_mem {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (R : Subgroup G) (hRclosed : IsClosed (R : Set G)) {σ : G} (hσ : σ ∉ R) :
    ∃ V : Subgroup G, IsOpen (V : Set G) ∧ R ≤ V ∧ σ ∉ V := by
  let Rclosed : ClosedSubgroup G := { toSubgroup := R, isClosed' := hRclosed }
  have hEq := ProfiniteGrp.closedSubgroup_eq_sInf_open Rclosed
  have hσsInf : σ ∉ sInf {N : Subgroup G | IsOpen (N : Set G) ∧ R ≤ N} := by
    intro hmem
    apply hσ
    have hmem' : σ ∈ (Rclosed : Subgroup G) := by
      rw [hEq]
      exact hmem
    exact hmem'
  rw [Subgroup.mem_sInf] at hσsInf
  push Not at hσsInf
  obtain ⟨V, hV⟩ := hσsInf
  exact ⟨V, hV.1.1, hV.1.2, hV.2⟩

/-- A profinite-group homomorphism with finite-index range is open. -/
theorem isOpenMap_of_finiteIndex_range {G H : ProfiniteGrp.{u}}
    (φ : G ⟶ H) [Subgroup.FiniteIndex (MonoidHom.range φ.hom.toMonoidHom)] :
    IsOpenMap φ := by
  have hcompact : IsCompact (φ.hom.range : Set H) := by
    convert isCompact_univ.image φ.hom.continuous_toFun using 1
    ext y
    simp
  have hopen : IsOpen (φ.hom.range : Set H) :=
    φ.hom.range.isOpen_of_isClosed_of_finiteIndex hcompact.isClosed
  apply isOpenMap_of_open_range φ
  convert hopen
  ext y
  rfl

end ProfiniteGrp

namespace Anabelian
namespace Examples
namespace MochizukiLocalProP
namespace ProperHyperbolicCurveHomStandalone

open CategoryTheory

/-! ## Augmented profinite groups and outer morphisms -/

/-- Two morphisms of profinite groups are outer-equivalent if they differ by conjugation by an
 element of the target. -/
def profiniteGrpOuterRel : HomRel ProfiniteGrp.{u} :=
  fun {G H} f g ↦ ∃ h : H, ∀ x : G, g x = h * f x * h⁻¹

/-- Outer-equivalence is a congruence on the category of profinite groups. -/
instance profiniteGrpOuterRelCongruence : Congruence profiniteGrpOuterRel where
  comp_left := by
    intro _ _ _ f _ _ ⟨h, hh⟩
    exact ⟨h, fun x ↦ hh (f x)⟩
  comp_right := by
    intro _ _ _ _ _ g ⟨h, hh⟩
    exact ⟨g h, fun x ↦ by simp [hh x]⟩
  equivalence {_ _} := by
    refine ⟨fun _ ↦ ⟨1, fun x ↦ by simp⟩, ?_, ?_⟩
    · intro _ _ ⟨h, hh⟩
      exact ⟨h⁻¹, fun x ↦ by rw [hh x]; group⟩
    · intro _ _ _ ⟨h, hh⟩ ⟨i, hi⟩
      exact ⟨i * h, fun x ↦ by rw [hi x, hh x]; group⟩

/-- Profinite groups with morphisms quotiented by inner conjugation in the target. -/
abbrev ProfiniteGrpOuter : Type (u + 1) :=
  CategoryTheory.Quotient profiniteGrpOuterRel

/-- View an actual profinite group as an object of the outer quotient category. -/
noncomputable abbrev profiniteAsOuter (G : ProfiniteGrp.{u}) : ProfiniteGrpOuter.{u} :=
  (CategoryTheory.Quotient.functor profiniteGrpOuterRel).obj G

/-- Augmented profinite groups over a fixed profinite group. -/
abbrev AugProfiniteOver (G : ProfiniteGrp.{u}) : Type (u + 1) :=
  CostructuredArrow (𝟭 ProfiniteGrp.{u}) G

/-- Open continuous morphisms of augmented profinite groups over a fixed base. -/
def openAugProfiniteMorphismProperty (Γ : ProfiniteGrp.{u}) :
    MorphismProperty (AugProfiniteOver Γ) :=
  fun _ _ f ↦ IsOpenMap f.left

/-- Open augmented morphisms are multiplicative. -/
instance openAugProfiniteMorphismProperty_isMultiplicative (Γ : ProfiniteGrp.{u}) :
    (openAugProfiniteMorphismProperty Γ).IsMultiplicative where
  id_mem _ := .id
  comp_mem _ _ hf hg := hg.comp hf

/-- Augmented profinite groups over a fixed base, with only open morphisms. -/
abbrev OpenAugProfiniteOver (Γ : ProfiniteGrp.{u}) : Type (u + 1) :=
  WideSubcategory (openAugProfiniteMorphismProperty Γ)

namespace OpenAugProfiniteOver

/-- Forget to the ambient augmented profinite group. -/
noncomputable abbrev asAug {Γ : ProfiniteGrp.{u}} (A : OpenAugProfiniteOver Γ) :
    AugProfiniteOver Γ :=
  A.obj

/-- Forget to the underlying profinite group. -/
noncomputable abbrev asProfinite {Γ : ProfiniteGrp.{u}} (A : OpenAugProfiniteOver Γ) :
    ProfiniteGrp.{u} :=
  A.asAug.left

/-- The augmentation to the fixed base group. -/
noncomputable abbrev augmentation {Γ : ProfiniteGrp.{u}} (A : OpenAugProfiniteOver Γ) :
    A.asProfinite ⟶ Γ :=
  A.asAug.hom

/-- Morphisms commute with the augmentation. -/
@[reassoc (attr := simp)]
theorem hom_w {Γ : ProfiniteGrp.{u}} {A B : OpenAugProfiniteOver Γ} (f : A ⟶ B) :
    f.hom.left ≫ B.asAug.hom = A.asAug.hom :=
  f.hom.w

/-- The underlying continuous homomorphism of a data morphism is open. -/
theorem hom_isOpenMap {Γ : ProfiniteGrp.{u}} {A B : OpenAugProfiniteOver Γ}
    (f : A ⟶ B) : IsOpenMap f.hom.left :=
  f.property

end OpenAugProfiniteOver

/-- A morphism in the outer profinite-group category is open if it has an open representative before
quotienting by target conjugation. -/
def IsOpenOuterHom {G H : ProfiniteGrpOuter.{u}} (φ : G ⟶ H) : Prop :=
  ∃ f : G.as ⟶ H.as,
    (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map f = φ ∧ IsOpenMap f

/-- Identity outer morphisms are open. -/
theorem isOpenOuterHom_id (G : ProfiniteGrpOuter.{u}) : IsOpenOuterHom (𝟙 G) :=
  ⟨𝟙 G.as, rfl, .id⟩

/-- Open outer morphisms are closed under composition. -/
theorem isOpenOuterHom_comp {G H I : ProfiniteGrpOuter.{u}} {φ : G ⟶ H} {ψ : H ⟶ I}
    (hφ : IsOpenOuterHom φ) (hψ : IsOpenOuterHom ψ) : IsOpenOuterHom (φ ≫ ψ) := by
  obtain ⟨f, rfl, hf⟩ := hφ
  obtain ⟨g, rfl, hg⟩ := hψ
  exact ⟨f ≫ g, rfl, hg.comp hf⟩

/-- Augmented outer profinite groups over a fixed outer base. -/
abbrev AugProfiniteOuterOver (Γ : ProfiniteGrpOuter.{u}) : Type (u + 1) :=
  CostructuredArrow (𝟭 ProfiniteGrpOuter.{u}) Γ

/-- View an augmented profinite group as an augmented object in the outer quotient category. -/
noncomputable def augProfiniteAsOuter {Γ : ProfiniteGrp.{u}}
    (A : AugProfiniteOver Γ) : AugProfiniteOuterOver (profiniteAsOuter Γ) :=
  CostructuredArrow.mk ((CategoryTheory.Quotient.functor profiniteGrpOuterRel).map A.hom)

/-- The outer augmented morphism induced by a morphism of augmented profinite groups. -/
noncomputable def augProfiniteAsOuterMap {Γ : ProfiniteGrp.{u}}
    {A B : AugProfiniteOver Γ} (f : A ⟶ B) :
    augProfiniteAsOuter A ⟶ augProfiniteAsOuter B := by
  let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
  exact CostructuredArrow.homMk (Q.map f.left) (by
    change Q.map f.left ≫ Q.map B.hom = Q.map A.hom
    have hw : f.left ≫ B.hom = A.hom := by
      exact f.w
    rw [← Q.map_comp, hw]
    rfl)

@[simp]
theorem augProfiniteAsOuterMap_id {Γ : ProfiniteGrp.{u}} (A : AugProfiniteOver Γ) :
    augProfiniteAsOuterMap (𝟙 A) = 𝟙 (augProfiniteAsOuter A) := by
  apply CostructuredArrow.hom_ext
  simp [augProfiniteAsOuterMap]
  rfl

@[simp]
theorem augProfiniteAsOuterMap_comp {Γ : ProfiniteGrp.{u}}
    {A B C : AugProfiniteOver Γ} (f : A ⟶ B) (g : B ⟶ C) :
    augProfiniteAsOuterMap (f ≫ g) = augProfiniteAsOuterMap f ≫ augProfiniteAsOuterMap g := by
  apply CostructuredArrow.hom_ext
  simp [augProfiniteAsOuterMap]
  rfl

/-- View an open augmented profinite group as an augmented object in the outer quotient category. -/
noncomputable abbrev openAugProfiniteAsOuter {Γ : ProfiniteGrp.{u}}
    (A : OpenAugProfiniteOver Γ) : AugProfiniteOuterOver (profiniteAsOuter Γ) :=
  augProfiniteAsOuter A.asAug

/-- The outer augmented morphism induced by an open augmented morphism. -/
noncomputable abbrev openAugProfiniteAsOuterMap {Γ : ProfiniteGrp.{u}}
    {A B : OpenAugProfiniteOver Γ} (f : A ⟶ B) :
    openAugProfiniteAsOuter A ⟶ openAugProfiniteAsOuter B :=
  augProfiniteAsOuterMap f.hom

@[simp]
theorem openAugProfiniteAsOuterMap_id {Γ : ProfiniteGrp.{u}} (A : OpenAugProfiniteOver Γ) :
    openAugProfiniteAsOuterMap (𝟙 A) = 𝟙 (openAugProfiniteAsOuter A) := by
  simp [openAugProfiniteAsOuterMap]

@[simp]
theorem openAugProfiniteAsOuterMap_comp {Γ : ProfiniteGrp.{u}}
    {A B C : OpenAugProfiniteOver Γ} (f : A ⟶ B) (g : B ⟶ C) :
    openAugProfiniteAsOuterMap (f ≫ g) =
      openAugProfiniteAsOuterMap f ≫ openAugProfiniteAsOuterMap g := by
  simp [openAugProfiniteAsOuterMap]

/-- Outer morphisms of augmented profinite groups over the same base. -/
abbrev OuterHomOver {Γ : ProfiniteGrp.{u}} (A B : OpenAugProfiniteOver Γ) : Type u :=
  openAugProfiniteAsOuter A ⟶ openAugProfiniteAsOuter B

/-- Openness for outer morphisms over the base. -/
def IsOpenOuterHomOver {Γ : ProfiniteGrp.{u}} {A B : OpenAugProfiniteOver Γ}
    (φ : OuterHomOver A B) : Prop :=
  IsOpenOuterHom φ.left

/-- Open outer morphisms over the base are closed under composition. -/
theorem isOpenOuterHomOver_comp {Γ : ProfiniteGrp.{u}} {A B C : OpenAugProfiniteOver Γ}
    {φ : OuterHomOver A B} {ψ : OuterHomOver B C}
    (hφ : IsOpenOuterHomOver φ) (hψ : IsOpenOuterHomOver ψ) :
    IsOpenOuterHomOver (φ ≫ ψ) := by
  dsimp [IsOpenOuterHomOver] at hφ hψ ⊢
  simpa using isOpenOuterHom_comp hφ hψ

/-- Open augmented morphisms give open outer morphisms over the base. -/
theorem isOpenOuterHomOver_of_openAugProfiniteHom {Γ : ProfiniteGrp.{u}}
    {A B : OpenAugProfiniteOver Γ} (f : A ⟶ B) :
    IsOpenOuterHomOver (openAugProfiniteAsOuterMap f) := by
  dsimp [IsOpenOuterHomOver, openAugProfiniteAsOuterMap, augProfiniteAsOuterMap]
  exact ⟨f.hom.left, rfl, f.property⟩
end ProperHyperbolicCurveHomStandalone
end MochizukiLocalProP
end Examples
end Anabelian
