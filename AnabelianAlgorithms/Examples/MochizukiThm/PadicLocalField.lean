/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

module

public import Mathlib

/-!
# Finite extensions of `ℚ_[p]`

This file packages finite extensions of the `p`-adic field `ℚ_[p]` as a full subcategory of
`CommAlgCat ℚ_[p]`.  The category is used as the base-field parameter category for the standalone
proper-hyperbolic-curve Hom-form statement.
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

/-! ## Finite extensions of `ℚ_[p]` -/

/-- The object property on `ℚ_[p]`-algebras whose underlying ring is a finite field extension. -/
def padicLocalFieldObjectProperty (p : ℕ) [Fact p.Prime] :
    ObjectProperty (CommAlgCat.{u} ℚ_[p]) :=
  fun K ↦ ∃ hK : IsField K, letI : Field K := hK.toField; FiniteDimensional ℚ_[p] K

/-- Finite extensions of `ℚ_[p]`, as a full subcategory of `CommAlgCat ℚ_[p]`. -/
abbrev PadicLocalFieldCat (p : ℕ) [Fact p.Prime] : Type (u + 1) :=
  (padicLocalFieldObjectProperty.{u} p).FullSubcategory

namespace PadicLocalFieldCat

instance (p : ℕ) [Fact p.Prime] : CoeSort (PadicLocalFieldCat.{u} p) (Type u) :=
  ⟨fun K ↦ K.obj⟩

/-- The field structure on a `p`-adic local field object. -/
noncomputable instance field {p : ℕ} [Fact p.Prime] (K : PadicLocalFieldCat.{u} p) : Field K :=
  K.property.choose.toField

/-- The finite-dimensionality over `ℚ_[p]` stored in a `p`-adic local field object. -/
noncomputable instance finiteDimensional {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : FiniteDimensional ℚ_[p] K :=
  K.property.choose_spec

/-- A finite extension of `ℚ_[p]` has characteristic zero. -/
noncomputable instance charZero {p : ℕ} [Fact p.Prime] (K : PadicLocalFieldCat.{u} p) :
    CharZero K :=
  charZero_of_injective_algebraMap (RingHom.injective (algebraMap ℚ_[p] K))

end PadicLocalFieldCat
end ProperHyperbolicCurveHomStandalone
end MochizukiLocalProP
end Examples
end Anabelian
