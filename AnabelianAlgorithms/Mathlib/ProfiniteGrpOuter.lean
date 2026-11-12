/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic


/-!
# Outer profinite groups

This file defines the quotient category of profinite groups by target-inner conjugation.  It is used
by the example statements and by reusable absolute-Galois scaffolding, so it lives outside the
example namespace.
-/

@[expose] public section

universe u

namespace Anabelian

open CategoryTheory

/--
Two morphisms of profinite groups are outer-equivalent if they differ by conjugation by an element
of the target.
-/
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

/-- The outer isomorphism represented by an actual profinite-group isomorphism. -/
noncomputable def profiniteIsoAsOuter {G H : ProfiniteGrp.{u}} (e : G ≅ H) :
    profiniteAsOuter G ≅ profiniteAsOuter H :=
  (CategoryTheory.Quotient.functor profiniteGrpOuterRel).mapIso e

@[simp]
theorem profiniteIsoAsOuter_refl (G : ProfiniteGrp.{u}) :
    profiniteIsoAsOuter (Iso.refl G) = Iso.refl (profiniteAsOuter G) :=
  rfl

@[simp]
theorem profiniteIsoAsOuter_trans {G H I : ProfiniteGrp.{u}} (e : G ≅ H) (e' : H ≅ I) :
    profiniteIsoAsOuter (e ≪≫ e') = profiniteIsoAsOuter e ≪≫ profiniteIsoAsOuter e' :=
  rfl

/-- If conjugating both source and target by isomorphisms makes two quotient maps equal, then the
original quotient maps are equal. -/
theorem quotient_map_cancel_conjugated {G G' H H' : ProfiniteGrp.{u}}
    (i : G ≅ G') (j : H ≅ H') (f g : G ⟶ H)
    (h : (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map
      (i.inv ≫ f ≫ j.hom) =
      (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map
        (i.inv ≫ g ≫ j.hom)) :
    (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map f =
      (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map g := by
  let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
  calc
    Q.map f = Q.map i.hom ≫ Q.map (i.inv ≫ f ≫ j.hom) ≫ Q.map j.inv := by
      simp [Q.map_comp, Category.assoc]
    _ = Q.map i.hom ≫ Q.map (i.inv ≫ g ≫ j.hom) ≫ Q.map j.inv := by rw [h]
    _ = Q.map g := by
      simp [Q.map_comp, Category.assoc]

/--
Every outer isomorphism of profinite groups admits an actual profinite-group isomorphism
representative.

Choose a continuous homomorphism representing the forward map in the quotient.  Its inverse in the
quotient is represented by another continuous homomorphism, and the two composites differ from the
identity by inner automorphisms.  These inner automorphism relations make the forward map bijective,
so the forgetful functor from profinite groups reflects that it is an isomorphism.
-/
noncomputable def profiniteOuterIsoRepresentative {G H : ProfiniteGrp.{u}}
    (α : profiniteAsOuter G ≅ profiniteAsOuter H) : G ≅ H := by
  let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
  let f : G ⟶ H := Classical.choose (Q.map_surjective α.hom)
  have hf : Q.map f = α.hom := Classical.choose_spec (Q.map_surjective α.hom)
  let g : H ⟶ G := Classical.choose (Q.map_surjective α.inv)
  have hg : Q.map g = α.inv := Classical.choose_spec (Q.map_surjective α.inv)
  have hfg_eq : Q.map (f ≫ g) = Q.map (𝟙 G) := by
    rw [Q.map_comp, hf, hg, α.hom_inv_id]
    rfl
  have hgf_eq : Q.map (g ≫ f) = Q.map (𝟙 H) := by
    rw [Q.map_comp, hf, hg, α.inv_hom_id]
    rfl
  have hfg_rel : profiniteGrpOuterRel (f ≫ g) (𝟙 G) :=
    (CategoryTheory.Quotient.functor_map_eq_iff profiniteGrpOuterRel (f ≫ g) (𝟙 G)).1 hfg_eq
  have hgf_rel : profiniteGrpOuterRel (g ≫ f) (𝟙 H) :=
    (CategoryTheory.Quotient.functor_map_eq_iff profiniteGrpOuterRel (g ≫ f) (𝟙 H)).1 hgf_eq
  have hbij : Function.Bijective f := by
    constructor
    · intro x y hxy
      rcases hfg_rel with ⟨a, ha⟩
      calc
        x = a * (f ≫ g) x * a⁻¹ := ha x
        _ = a * (f ≫ g) y * a⁻¹ := by simp [hxy]
        _ = y := (ha y).symm
    · intro y
      rcases hgf_rel with ⟨b, hb⟩
      refine ⟨g (b * y * b⁻¹), ?_⟩
      have hy := hb (b * y * b⁻¹)
      change (g ≫ f) (b * y * b⁻¹) = y
      have hy' := congrArg (fun z : H ↦ b⁻¹ * z * b) hy
      symm
      simpa [mul_assoc] using hy'
  haveI : IsIso f := by
    have : IsIso ((forget ProfiniteGrp).map f) :=
      (CategoryTheory.isIso_iff_bijective ((forget ProfiniteGrp).map f)).2 hbij
    exact isIso_of_reflects_iso f (forget ProfiniteGrp)
  exact asIso f

/-- The chosen representative maps to the original outer isomorphism. -/
theorem profiniteIsoAsOuter_outerIsoRepresentative {G H : ProfiniteGrp.{u}}
    (α : profiniteAsOuter G ≅ profiniteAsOuter H) :
    profiniteIsoAsOuter (profiniteOuterIsoRepresentative α) = α := by
  let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
  dsimp [profiniteIsoAsOuter, profiniteOuterIsoRepresentative]
  ext
  exact Classical.choose_spec (Q.map_surjective α.hom)

/-- The quotient functor is full after passing to cores. -/
noncomputable instance profiniteAsOuterFunctorCoreFull :
    (CategoryTheory.Quotient.functor profiniteGrpOuterRel :
      ProfiniteGrp.{u} ⥤ ProfiniteGrpOuter.{u}).core.Full where
  map_surjective {X Y} f := by
    refine ⟨⟨profiniteOuterIsoRepresentative f.iso⟩, ?_⟩
    apply Core.hom_ext
    change (profiniteIsoAsOuter (profiniteOuterIsoRepresentative f.iso)).hom = f.iso.hom
    exact congrArg Iso.hom (profiniteIsoAsOuter_outerIsoRepresentative f.iso)

/-- The quotient functor is essentially surjective after passing to cores. -/
noncomputable instance profiniteAsOuterFunctorCoreEssSurj :
    (CategoryTheory.Quotient.functor profiniteGrpOuterRel :
      ProfiniteGrp.{u} ⥤ ProfiniteGrpOuter.{u}).core.EssSurj where
  mem_essImage Y := by
    refine ⟨⟨Y.of.as⟩, ⟨?_⟩⟩
    exact Core.isoMk (eqToIso rfl)

/-- Augmented profinite groups over a fixed profinite group. -/
abbrev AugProfiniteOver (G : ProfiniteGrp.{u}) : Type (u + 1) :=
  CostructuredArrow (𝟭 ProfiniteGrp.{u}) G

end Anabelian
