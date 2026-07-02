/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.NumberTheory.NumberField.Basic


/-!
# The category of number fields

This file defines number fields as the full subcategory of commutative rings whose underlying ring
is a number field in mathlib's sense, together with basic conversions between raw Lean number
fields and categorical number-field objects.
-/

universe u

namespace Anabelian

open CategoryTheory
open scoped NumberField

/-- The object property on commutative rings whose underlying ring is a number field. -/
def numberFieldObjectProperty : ObjectProperty CommRingCat.{u} :=
  fun K ↦ ∃ hK : IsField K, @NumberField K hK.toField

/-- Number fields, as the full subcategory of `CommRingCat` on number-field objects. -/
abbrev NumberFieldCat : Type (u + 1) :=
  numberFieldObjectProperty.FullSubcategory

namespace NumberFieldCat

/-- The inclusion of number fields into commutative rings. -/
abbrev incl : NumberFieldCat.{u} ⥤ CommRingCat.{u} :=
  numberFieldObjectProperty.ι

instance : CoeSort NumberFieldCat.{u} (Type u) :=
  ⟨fun K ↦ K.obj⟩

/-- The field structure on a number-field object, induced by the underlying ring. -/
noncomputable instance field (K : NumberFieldCat.{u}) : Field K :=
  K.property.choose.toField

/-- The number-field structure on a number-field object. -/
noncomputable instance numberField (K : NumberFieldCat.{u}) : NumberField K :=
  K.property.choose_spec

end NumberFieldCat

/-- The ring equivalence underlying an isomorphism of number-field objects. -/
noncomputable def numberFieldIsoToRingEquiv {K L : NumberFieldCat.{u}} (e : K ≅ L) :
    K ≃+* L :=
  (NumberFieldCat.incl.mapIso e).commRingCatIsoToRingEquiv

@[simp]
theorem numberFieldIsoToRingEquiv_refl (K : NumberFieldCat.{u}) :
    numberFieldIsoToRingEquiv (Iso.refl K) = RingEquiv.refl K :=
  rfl

@[simp]
theorem numberFieldIsoToRingEquiv_trans {K L M : NumberFieldCat.{u}} (e : K ≅ L)
    (e' : L ≅ M) :
    (numberFieldIsoToRingEquiv e).trans (numberFieldIsoToRingEquiv e') =
      numberFieldIsoToRingEquiv (e ≪≫ e') :=
  rfl

namespace NumberFieldCat

/-- A raw Lean number field as an object of the category of number fields. -/
noncomputable def of (K : Type u) [Field K] [NumberField K] : NumberFieldCat.{u} where
  obj := CommRingCat.of K
  property := by
    let hFieldK : Field K := inferInstance
    let hNumberFieldK : @NumberField K hFieldK := inferInstance
    let hK : IsField (CommRingCat.of K) := Field.toIsField K
    refine ⟨hK, ?_⟩
    exact @NumberField.of_ringEquiv K (CommRingCat.of K) hFieldK hK.toField (RingEquiv.refl K)
      hNumberFieldK

@[simp]
theorem coe_of (K : Type u) [Field K] [NumberField K] :
    (of K : Type u) = K :=
  rfl

/-- Build an isomorphism of number-field objects from a raw ring equivalence. -/
noncomputable def isoOfRingEquiv {K L : Type u} [Field K] [Field L] [NumberField K]
    [NumberField L] (e : K ≃+* L) : of K ≅ of L :=
  numberFieldObjectProperty.isoMk e.toCommRingCatIso

@[simp]
theorem isoOfRingEquiv_toRingEquiv {K L : Type u} [Field K] [Field L] [NumberField K]
    [NumberField L] (e : K ≃+* L) :
    numberFieldIsoToRingEquiv (isoOfRingEquiv e) = e :=
  rfl

/-- The identity ring equivalence from the `NumberFieldCat.of` field instance to the raw one. -/
noncomputable def ringEquivOfToRaw (K : Type u) [Field K] [NumberField K] :
    @RingEquiv K K
      (letI : Field K := field (of K); inferInstance)
      (inferInstance)
      (letI : Field K := field (of K); inferInstance)
      (inferInstance) :=
  @RingEquiv.mk K K
    (letI : Field K := field (of K); inferInstance)
    (inferInstance)
    (letI : Field K := field (of K); inferInstance)
    (inferInstance)
    (Equiv.refl K) (by intro x y; rfl) (by intro x y; rfl)

end NumberFieldCat

end Anabelian
