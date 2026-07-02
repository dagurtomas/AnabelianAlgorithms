/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

module

public import AnabelianAlgorithms.Mathlib.NumberField.AbsoluteGalois.Basic
public import AnabelianAlgorithms.Mathlib.NumberField.NumberFieldCat


/-!
# Absolute Galois groups on the category of number fields

This file packages the chosen-closure absolute Galois group as a functor on number-field objects
and records comparison isomorphisms between raw Lean number fields and their `NumberFieldCat`
representatives.
-/

@[expose] public section

universe u

namespace Anabelian

open CategoryTheory
open scoped NumberField

/-- The absolute Galois group of a number field, as a profinite group. -/
noncomputable def absGalNumberFieldObj (K : NumberFieldCat.{u}) : ProfiniteGrp.{u} :=
  NumberField.absGalProfiniteObj K

/-- The absolute Galois group, viewed in the outer profinite-group category. -/
noncomputable def absGalNumberFieldOuterObj (K : NumberFieldCat.{u}) : ProfiniteGrpOuter.{u} :=
  NumberField.absGalOuterObj K

/-- The isomorphism of profinite absolute Galois groups induced by a number-field isomorphism. -/
noncomputable def absGalNumberFieldIso {K L : NumberFieldCat.{u}} (e : K ≅ L) :
    absGalNumberFieldObj L ≅ absGalNumberFieldObj K :=
  NumberField.GlobalFieldIso.toProfiniteGrpIso (K := L) (L := K) (numberFieldIsoToRingEquiv e)

/-- The outer isomorphism of absolute Galois groups induced by a number-field isomorphism. -/
noncomputable def absGalNumberFieldOuterIso {K L : NumberFieldCat.{u}} (e : K ≅ L) :
    absGalNumberFieldOuterObj L ≅ absGalNumberFieldOuterObj K :=
  NumberField.GlobalFieldIso.toOuterIso (K := L) (L := K) (numberFieldIsoToRingEquiv e)

@[simp]
theorem absGalNumberFieldOuterIso_id (K : NumberFieldCat.{u}) :
    absGalNumberFieldOuterIso (Iso.refl K) = Iso.refl (absGalNumberFieldOuterObj K) := by
  change NumberField.GlobalFieldIso.toOuterIso (K := K) (L := K) (RingEquiv.refl K) =
    Iso.refl (NumberField.absGalOuterObj K)
  exact NumberField.GlobalFieldIso.toOuterIso_refl K

@[simp]
theorem absGalNumberFieldOuterIso_comp {K L M : NumberFieldCat.{u}} (e : K ≅ L)
    (e' : L ≅ M) :
    absGalNumberFieldOuterIso (e ≪≫ e') =
      absGalNumberFieldOuterIso e' ≪≫ absGalNumberFieldOuterIso e := by
  change NumberField.GlobalFieldIso.toOuterIso (K := M) (L := K)
      (numberFieldIsoToRingEquiv (e ≪≫ e')) =
    NumberField.GlobalFieldIso.toOuterIso (numberFieldIsoToRingEquiv e') ≪≫
      NumberField.GlobalFieldIso.toOuterIso (numberFieldIsoToRingEquiv e)
  rw [← numberFieldIsoToRingEquiv_trans e e']
  exact NumberField.GlobalFieldIso.toOuterIso_trans
    (e := numberFieldIsoToRingEquiv e) (e' := numberFieldIsoToRingEquiv e')

/-- Absolute Galois group on number-field objects with scheme-like variance. -/
noncomputable def absGalNumberField : Core (NumberFieldCat.{u}ᵒᵖ) ⥤ Core ProfiniteGrpOuter where
  obj K := ⟨absGalNumberFieldOuterObj K.of.unop⟩
  map {K L} f := ⟨absGalNumberFieldOuterIso f.iso.unop⟩
  map_id K := by
    apply Core.hom_ext
    change (absGalNumberFieldOuterIso (Iso.refl K.of.unop)).hom =
      (Iso.refl (absGalNumberFieldOuterObj K.of.unop)).hom
    simp
  map_comp f g := by
    apply Core.hom_ext
    change (absGalNumberFieldOuterIso (g.iso.unop ≪≫ f.iso.unop)).hom =
      (absGalNumberFieldOuterIso f.iso.unop ≪≫ absGalNumberFieldOuterIso g.iso.unop).hom
    simp

/-- The outer isomorphism represented by a concrete absolute-Galois isomorphism. -/
@[simp]
theorem profiniteIsoAsOuter_absGalNumberFieldIso {K L : NumberFieldCat.{u}} (e : K ≅ L) :
    profiniteIsoAsOuter (absGalNumberFieldIso e) = absGalNumberFieldOuterIso e :=
  rfl

namespace NumberFieldCat

/-- Change the absolute-Galois outer object from the raw field instance to `NumberFieldCat.of`. -/
noncomputable def outerIsoRawToOf (K : Type u) [Field K] [NumberField K] :
    @NumberField.absGalOuterObj K inferInstance inferInstance ≅
      @NumberField.absGalOuterObj K (field (of K)) (numberField (of K)) :=
  @NumberField.GlobalFieldIso.toOuterIso K K
    (inferInstance) (inferInstance) (field (of K)) (numberField (of K))
    (ringEquivOfToRaw K)

@[simp]
theorem toOuterIso_ringEquivOfToRaw_symm (K : Type u) [Field K] [NumberField K] :
    @NumberField.GlobalFieldIso.toOuterIso K K
      (field (of K)) (numberField (of K)) (inferInstance) (inferInstance)
      (ringEquivOfToRaw K).symm = (outerIsoRawToOf K).symm := by
  let β : @NumberField.absGalOuterObj K (field (of K)) (numberField (of K)) ≅
      @NumberField.absGalOuterObj K inferInstance inferInstance :=
    @NumberField.GlobalFieldIso.toOuterIso K K
      (field (of K)) (numberField (of K)) (inferInstance) (inferInstance)
      (ringEquivOfToRaw K).symm
  have htrans := @NumberField.GlobalFieldIso.toOuterIso_trans K K K
    (inferInstance) (inferInstance)
    (field (of K)) (numberField (of K))
    (inferInstance) (inferInstance)
    ((ringEquivOfToRaw K).symm) (ringEquivOfToRaw K)
  have hcomp : outerIsoRawToOf K ≪≫ β = Iso.refl _ := by
    dsimp [β, outerIsoRawToOf]
    rw! [← htrans]
    change NumberField.GlobalFieldIso.toOuterIso (RingEquiv.refl K) = Iso.refl _
    simp
  apply Iso.ext
  dsimp [β] at hcomp ⊢
  exact Iso.inv_ext' (congrArg Iso.hom hcomp)

end NumberFieldCat

end Anabelian
