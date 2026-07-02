/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

module

import all AnabelianAlgorithms.Linter.NonstandardAxioms
public import AnabelianAlgorithms.Examples.MochizukiThm.ReconstructionData
public import AnabelianLib.Framework.HomForm

/-!
# Standalone Hom-form statement for proper hyperbolic curves over `p`-adic local fields

This file is the entry point for the extracted Mochizuki-style Hom-form package.  The supporting
constructions live in smaller files:

* `PadicLocalField` packages finite extensions of `ℚ_[p]`.
* `StructureSheafCohomology` defines the arithmetic-genus input.
* `ProperHyperbolicCurve` defines the curve category and curve finiteness lemmas.
* `AugmentedProfinite` defines open augmented profinite groups and outer morphisms.
* `PointedEtalePi1` constructs the point-indexed arithmetic étale `π₁` representatives.
* `ReconstructionData` assembles those representatives into invariant and algorithm profunctors.

The remaining axiom below is the Hom-form theorem identifying the profunctor composite with the
geometric Hom profunctor.
-/

@[expose] public section

set_option linter.nonstandardAxioms false

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

/-! ## Hom-form theorem package -/

noncomputable abbrev properHyperbolicCurveDominantTarget {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    Profunctor.{u + 1} (ProperHyperbolicCurveOver K) (ProperHyperbolicCurveOver K) :=
  (Profunctor.id (C := ProperHyperbolicCurveOver K)).ulift1

/-- The composite profunctor whose elements are coend classes of open outer homomorphisms
`π₁(X) → π₁(Y)` over `Γ_K`. -/
noncomputable abbrev properHyperbolicCurveComposite {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    Profunctor.{u + 1} (ProperHyperbolicCurveOver K) (ProperHyperbolicCurveOver K) :=
  Profunctor.comp.{u + 1} (properHyperbolicCurveInvariant K) (properHyperbolicCurveAlgorithm K)

/-- Special case of Mochizuki's Hom-form theorem for proper hyperbolic curves over `K`. -/
axiom properHyperbolicCurveHomDecodeIso {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    properHyperbolicCurveComposite K ≅ properHyperbolicCurveDominantTarget K

/-- The standalone profunctor reconstruction package for the proper-curve special case. -/
noncomputable def properHyperbolicCurveHomChallenge {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    ProfunctorReconstruction
      (ProperHyperbolicCurveOver K) (properHyperbolicCurveData K) where
  invariant := properHyperbolicCurveInvariant K
  target := properHyperbolicCurveDominantTarget K
  algorithm := properHyperbolicCurveAlgorithm K
  decodeIso := properHyperbolicCurveHomDecodeIso K

/-- The same statement in the standard Hom-form package. -/
noncomputable def properHyperbolicCurveHomFormPackage {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    HomFormPackage (ProperHyperbolicCurveOver K) (properHyperbolicCurveData K) where
  invariant := properHyperbolicCurveInvariant K
  algorithm := properHyperbolicCurveAlgorithm K
  homIso := properHyperbolicCurveHomDecodeIso K

/-- The Hom-form package uses the specified full étale `π₁` invariant. -/
theorem properHyperbolicCurveHomFormPackage_invariant {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    (properHyperbolicCurveHomFormPackage K).invariant = properHyperbolicCurveInvariant K :=
  rfl

/-- The Hom-form package uses the open-outer-hom algorithm. -/
theorem properHyperbolicCurveHomFormPackage_algorithm {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    (properHyperbolicCurveHomFormPackage K).algorithm = properHyperbolicCurveAlgorithm K :=
  rfl

end ProperHyperbolicCurveHomStandalone
end MochizukiLocalProP
end Examples
end Anabelian
