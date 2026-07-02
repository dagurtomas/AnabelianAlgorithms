/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import AnabelianAlgorithms.Linter.NonstandardAxioms
import AnabelianLib.Framework.IsoForm
import AnabelianAlgorithms.Mathlib.NumberField.AbsoluteGalois.NumberFieldCat


/-!
# Standalone Neukirch--Uchida package statement

This file states the profunctor-form Neukirch--Uchida packages without importing
`Anabelian.Examples.Example02NeukirchUchida`.  The invariant and algorithm profunctors are obtained
from the representable outer package by resolving outer profinite groups along actual profinite
groups.  The theorem-level fields are isolated as axioms: the normalized representable
Neukirch--Uchida equivalence.  The co-Yoneda/density comparison for the quotient from actual to
outer profinite groups is supplied by the framework from fullness and essential surjectivity on
cores.
-/

universe u

set_option linter.nonstandardAxioms false

namespace Anabelian
namespace Examples
namespace NeukirchUchidaStandalone

open CategoryTheory
open scoped NumberField

/-- The quotient functor from actual profinite groups to outer profinite groups. -/
noncomputable abbrev profiniteAsOuterFunctor : ProfiniteGrp.{u} ⥤ ProfiniteGrpOuter.{u} :=
  CategoryTheory.Quotient.functor profiniteGrpOuterRel

axiom fullyFaithfulAbsGalNumberField : absGalNumberField.FullyFaithful

/-- The objectwise Neukirch--Uchida equivalence, isolated as the theorem-level axiom. -/
noncomputable abbrev neukirchUchidaHomEquiv (X Y : Core (NumberFieldCat.{u}ᵒᵖ)) :
    (Y ⟶ X) ≃ (absGalNumberField.obj Y ⟶ absGalNumberField.obj X) :=
  fullyFaithfulAbsGalNumberField.homEquiv

/--
The supplied Neukirch--Uchida equivalence is the canonical map induced by the absolute-Galois
functor in its forward direction.
-/
lemma neukirchUchidaHomEquiv_apply
    {X Y : Core (NumberFieldCat.{u}ᵒᵖ)} (f : Y ⟶ X) :
    neukirchUchidaHomEquiv X Y f = absGalNumberField.map f :=
  rfl

/-- Naturality of the axiomatically supplied Neukirch--Uchida equivalence in the target. -/
theorem neukirchUchidaHomEquiv_natural_left
    {X X' Y : Core (NumberFieldCat.{u}ᵒᵖ)} (f : Y ⟶ X) (g : X ⟶ X') :
    neukirchUchidaHomEquiv X' Y (f ≫ g) =
      neukirchUchidaHomEquiv X Y f ≫ absGalNumberField.map g := by
  simp

/-- Naturality of the axiomatically supplied Neukirch--Uchida equivalence in the source. -/
theorem neukirchUchidaHomEquiv_natural_right
    {X Y Y' : Core (NumberFieldCat.{u}ᵒᵖ)} (f : Y ⟶ X) (g : Y' ⟶ Y) :
    neukirchUchidaHomEquiv X Y' (g ≫ f) =
      absGalNumberField.map g ≫ neukirchUchidaHomEquiv X Y f := by
  simp

/-- The representable outer Iso-form package, with the theorem field supplied axiomatically. -/
noncomputable def neukirchUchidaOuterRepresentablePackage :
    RepresentableIsoFormPackage (NumberFieldCat.{u}ᵒᵖ) ProfiniteGrpOuter.{u} where
  I := absGalNumberField
  homEquiv := neukirchUchidaHomEquiv
  homEquiv_apply := neukirchUchidaHomEquiv_apply

/--
The Neukirch--Uchida invariant profunctor with actual profinite groups as data objects, obtained by
resolving the representable outer invariant along the quotient functor from actual profinite groups
to outer profinite groups.
-/
noncomputable def numberFieldInvariant :
    Profunctor.{u + 1} (Core (NumberFieldCat.{u}ᵒᵖ)) (Core ProfiniteGrp.{u}) :=
  RepresentableHomFormPackage.invariantThroughFunctor absGalNumberField
    profiniteAsOuterFunctor.core

/--
The Neukirch--Uchida algorithm profunctor with actual profinite groups as data objects, obtained by
resolving the representable outer invariant along the quotient functor from actual profinite groups
to outer profinite groups.
-/
noncomputable def numberFieldAlgorithm :
    Profunctor.{u + 1} (Core ProfiniteGrp.{u}) (Core (NumberFieldCat.{u}ᵒᵖ)) :=
  RepresentableHomFormPackage.algorithmThroughFunctor absGalNumberField
    profiniteAsOuterFunctor.core

/-- The outer data-Hom profunctor for the representable Neukirch--Uchida package. -/
noncomputable abbrev numberFieldOuterDataHom :
    Profunctor.{u + 1} (Core (NumberFieldCat.{u}ᵒᵖ)) (Core (NumberFieldCat.{u}ᵒᵖ)) :=
  dataHomProfunctor absGalNumberField

/--
The co-Yoneda/density comparison for replacing outer profinite groups by actual profinite groups.
This is the bookkeeping isomorphism associated to the quotient functor `profiniteAsOuterFunctor`.
-/
noncomputable abbrev numberFieldActualDataCoYonedaIso :
    CategoryTheory.Profunctor.comp.{u + 1, u, u + 1, u, u + 1, u, u + 1}
      numberFieldInvariant numberFieldAlgorithm ≅ numberFieldOuterDataHom :=
  RepresentableHomFormPackage.coYonedaDataHomIsoThroughFunctor absGalNumberField
    profiniteAsOuterFunctor.core

/-- The profunctor-form Neukirch--Uchida isomorphism, induced from the representable package. -/
noncomputable def neukirchUchidaIsoIso :
    CategoryTheory.Profunctor.comp.{u + 1, u, u + 1, u, u + 1, u, u + 1}
      numberFieldInvariant numberFieldAlgorithm ≅
      (CategoryTheory.Profunctor.id (C := Core (NumberFieldCat.{u}ᵒᵖ))).ulift1 :=
  numberFieldActualDataCoYonedaIso ≪≫
    neukirchUchidaOuterRepresentablePackage.toRepresentableHomFormPackage.dataHomToIdIso

/-- Statement of Neukirch--Uchida in profunctor-first package form. -/
noncomputable def neukirchUchidaPackage :
    IsoFormPackage (NumberFieldCat.{u}ᵒᵖ) ProfiniteGrp.{u} :=
  RepresentableIsoFormPackage.toIsoFormPackageThrough neukirchUchidaOuterRepresentablePackage
    profiniteAsOuterFunctor

end NeukirchUchidaStandalone
end Examples
end Anabelian
