/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

module

public import AnabelianAlgorithms.Mathlib.ProfiniteGrpOuter
public import Mathlib.Algebra.Ring.Aut
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.NumberTheory.NumberField.Basic


/-!
# Axiom-free absolute Galois functoriality for number fields

This file contains the axiom-free part of the absolute-Galois scaffold: conjugation by field
isomorphisms, the profinite absolute Galois group, and its image in the outer profinite-group
category.
-/

@[expose] public section

open CategoryTheory

universe u

namespace NumberField

namespace AbsGalConj

open scoped Topology

variable {K L : Type u} [Field K] [Field L]

/--
Conjugation by an equivalence of algebraic closures, as an equivalence of absolute Galois groups.
-/
noncomputable def mapOfEquiv (e : K ≃+* L)
    (F : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hF : ∀ x : K, F (algebraMap K (AlgebraicClosure K) x) =
      algebraMap L (AlgebraicClosure L) (e x))
    (σ : Gal(AlgebraicClosure L/L)) : Gal(AlgebraicClosure K/K) :=
  AlgEquiv.ofRingEquiv (f := F.trans (σ.toRingEquiv.trans F.symm)) (by
    intro x
    have hFsymm : F.symm (algebraMap L (AlgebraicClosure L) (e x)) =
        algebraMap K (AlgebraicClosure K) x := by
      apply F.injective
      simp [hF]
    simp [hF, hFsymm])

/-- Compatibility of the inverse algebraic-closure equivalence with scalar embeddings. -/
theorem symm_algebraMap (e : K ≃+* L)
    (F : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hF : ∀ x : K, F (algebraMap K (AlgebraicClosure K) x) =
      algebraMap L (AlgebraicClosure L) (e x)) (y : L) :
    F.symm (algebraMap L (AlgebraicClosure L) y) =
      algebraMap K (AlgebraicClosure K) (e.symm y) := by
  apply F.injective
  simp [hF]

/-- The inverse conjugation map associated to `mapOfEquiv`. -/
noncomputable def invMapOfEquiv (e : K ≃+* L)
    (F : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hF : ∀ x : K, F (algebraMap K (AlgebraicClosure K) x) =
      algebraMap L (AlgebraicClosure L) (e x))
    (τ : Gal(AlgebraicClosure K/K)) : Gal(AlgebraicClosure L/L) :=
  mapOfEquiv e.symm F.symm (symm_algebraMap e F hF) τ

/-- Conjugation by an algebraic-closure equivalence as a multiplicative equivalence. -/
noncomputable def mulEquivOfEquiv (e : K ≃+* L)
    (F : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hF : ∀ x : K, F (algebraMap K (AlgebraicClosure K) x) =
      algebraMap L (AlgebraicClosure L) (e x)) :
    Gal(AlgebraicClosure L/L) ≃* Gal(AlgebraicClosure K/K) where
  toFun := mapOfEquiv e F hF
  invFun := invMapOfEquiv e F hF
  left_inv σ := by
    ext x
    dsimp [mapOfEquiv, invMapOfEquiv]
    simp
  right_inv τ := by
    ext x
    dsimp [mapOfEquiv, invMapOfEquiv]
    simp
  map_mul' σ τ := by
    ext x
    dsimp [mapOfEquiv]
    simp [AlgEquiv.mul_apply]

/--
The automorphism of the source algebraic closure comparing two extensions of the same base
field isomorphism.
-/
noncomputable def comparisonAut (e : K ≃+* L)
    (F F' : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hF : ∀ x : K, F (algebraMap K (AlgebraicClosure K) x) =
      algebraMap L (AlgebraicClosure L) (e x))
    (hF' : ∀ x : K, F' (algebraMap K (AlgebraicClosure K) x) =
      algebraMap L (AlgebraicClosure L) (e x)) : Gal(AlgebraicClosure K/K) :=
  AlgEquiv.ofRingEquiv (f := F.trans F'.symm) (by
    intro x
    have hF'symm : F'.symm (algebraMap L (AlgebraicClosure L) (e x)) =
        algebraMap K (AlgebraicClosure K) x := by
      apply F'.injective
      simp [hF']
    simp [hF, hF'symm])

/-- Conjugation maps defined by two extensions differ by inner conjugation. -/
theorem mapOfEquiv_eq_inner (e : K ≃+* L)
    (F F' : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hF : ∀ x : K, F (algebraMap K (AlgebraicClosure K) x) =
      algebraMap L (AlgebraicClosure L) (e x))
    (hF' : ∀ x : K, F' (algebraMap K (AlgebraicClosure K) x) =
      algebraMap L (AlgebraicClosure L) (e x))
    (σ : Gal(AlgebraicClosure L/L)) :
    mapOfEquiv e F' hF' σ =
      comparisonAut e F F' hF hF' * mapOfEquiv e F hF σ *
        (comparisonAut e F F' hF hF')⁻¹ := by
  ext x
  dsimp [comparisonAut, mapOfEquiv]
  simp

/--
The basic open set of automorphisms fixing the chosen finite basis of an intermediate field,
after transporting the basis along an equivalence of algebraic closures.
-/
noncomputable def basisStabilizer (F : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    Set Gal(AlgebraicClosure L/L) :=
  ⋂ i : Fin (Module.finrank K E),
    (MulAction.stabilizer Gal(AlgebraicClosure L/L)
      (F (((Module.finBasis K E) i : E) : AlgebraicClosure K)) :
        Set Gal(AlgebraicClosure L/L))

/-- The finite-basis stabilizer is open in the Krull topology. -/
theorem isOpen_basisStabilizer (F : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    IsOpen (basisStabilizer F E) := by
  dsimp [basisStabilizer]
  exact isOpen_iInter_of_finite fun i ↦ stabilizer_isOpen_of_isIntegral
    (F (((Module.finBasis K E) i : E) : AlgebraicClosure K))

/-- The identity automorphism belongs to the finite-basis stabilizer. -/
theorem one_mem_basisStabilizer (F : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E] :
    (1 : Gal(AlgebraicClosure L/L)) ∈ basisStabilizer F E := by
  simp [basisStabilizer]

/--
If an automorphism fixes the transported finite basis of `E`, then its conjugate fixes `E`.
-/
theorem mapOfEquiv_mem_fixingSubgroup_of_mem_basisStabilizer (e : K ≃+* L)
    (F : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hF : ∀ x : K, F (algebraMap K (AlgebraicClosure K) x) =
      algebraMap L (AlgebraicClosure L) (e x))
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    {σ : Gal(AlgebraicClosure L/L)} (hσ : σ ∈ basisStabilizer F E) :
    mapOfEquiv e F hF σ ∈ E.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let b := Module.finBasis K E
  let xE : E := ⟨x, hx⟩
  have hσ_basis : ∀ i : Fin (Module.finrank K E),
      σ (F ((b i : E) : AlgebraicClosure K)) = F ((b i : E) : AlgebraicClosure K) := by
    intro i
    have hi : σ ∈ MulAction.stabilizer Gal(AlgebraicClosure L/L)
        (F ((b i : E) : AlgebraicClosure K)) := by
      exact Set.mem_iInter.mp hσ i
    simpa using (MulAction.mem_stabilizer_iff.mp hi)
  have hxsum : (∑ i : Fin (Module.finrank K E),
        algebraMap K (AlgebraicClosure K) (b.repr xE i) *
          ((b i : E) : AlgebraicClosure K)) = x := by
    simpa [Algebra.smul_def, b, xE] using
      congrArg (fun y : E ↦ (y : AlgebraicClosure K)) (b.sum_repr xE)
  have hσFx : σ (F x) = F x := by
    calc
      σ (F x) = σ (F (∑ i : Fin (Module.finrank K E),
          algebraMap K (AlgebraicClosure K) (b.repr xE i) *
            ((b i : E) : AlgebraicClosure K))) := by rw [hxsum]
      _ = ∑ i : Fin (Module.finrank K E),
          algebraMap L (AlgebraicClosure L) (e (b.repr xE i)) *
            F ((b i : E) : AlgebraicClosure K) := by
        simp [map_sum, hF, hσ_basis]
      _ = F (∑ i : Fin (Module.finrank K E),
          algebraMap K (AlgebraicClosure K) (b.repr xE i) *
            ((b i : E) : AlgebraicClosure K)) := by
        simp [map_sum, hF]
      _ = F x := by rw [hxsum]
  dsimp [mapOfEquiv]
  change F.symm (σ (F x)) = x
  rw [hσFx]
  exact F.symm_apply_apply x

/-- Conjugation by an algebraic-closure equivalence is continuous for the Krull topology. -/
theorem continuous_mapOfEquiv (e : K ≃+* L)
    (F : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hF : ∀ x : K, F (algebraMap K (AlgebraicClosure K) x) =
      algebraMap L (AlgebraicClosure L) (e x)) :
    Continuous (mapOfEquiv e F hF) := by
  change Continuous (mulEquivOfEquiv e F hF :
    Gal(AlgebraicClosure L/L) → Gal(AlgebraicClosure K/K))
  apply continuous_of_continuousAt_one (mulEquivOfEquiv e F hF)
  rw [continuousAt_def]
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, _hE, hsE⟩ := hs
  apply mem_nhds_iff.mpr
  refine ⟨basisStabilizer F E, ?_, isOpen_basisStabilizer F E, one_mem_basisStabilizer F E⟩
  intro σ hσ
  exact hsE (mapOfEquiv_mem_fixingSubgroup_of_mem_basisStabilizer e F hF E hσ)

/-- The inverse conjugation map is continuous for the Krull topology. -/
theorem continuous_invMapOfEquiv (e : K ≃+* L)
    (F : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hF : ∀ x : K, F (algebraMap K (AlgebraicClosure K) x) =
      algebraMap L (AlgebraicClosure L) (e x)) :
    Continuous (invMapOfEquiv e F hF) := by
  change Continuous (mapOfEquiv e.symm F.symm (symm_algebraMap e F hF))
  exact continuous_mapOfEquiv e.symm F.symm (symm_algebraMap e F hF)

/-- Conjugation by an algebraic-closure equivalence as a continuous multiplicative equivalence. -/
noncomputable def continuousMulEquivOfEquiv (e : K ≃+* L)
    (F : AlgebraicClosure K ≃+* AlgebraicClosure L)
    (hF : ∀ x : K, F (algebraMap K (AlgebraicClosure K) x) =
      algebraMap L (AlgebraicClosure L) (e x)) :
    Gal(AlgebraicClosure L/L) ≃ₜ* Gal(AlgebraicClosure K/K) :=
  ContinuousMulEquiv.mk (mulEquivOfEquiv e F hF)
    (continuous_mapOfEquiv e F hF)
    (continuous_invMapOfEquiv e F hF)

section ArbitraryClosures

variable {ΩK ΩL : Type u} [Field ΩK] [Field ΩL] [Algebra K ΩK] [Algebra L ΩL]

/--
Conjugation by an equivalence of arbitrary algebraic/separable closures, as an equivalence of
Galois groups.  The map is contravariant in the closure equivalence: if `F : ΩK ≃+* ΩL`, then it
sends automorphisms of `ΩL/L` to automorphisms of `ΩK/K` by `F⁻¹ ∘ σ ∘ F`.
-/
noncomputable def closureMapOfEquiv (e : K ≃+* L) (F : ΩK ≃+* ΩL)
    (hF : ∀ x : K, F (algebraMap K ΩK x) = algebraMap L ΩL (e x))
    (σ : Gal(ΩL/L)) : Gal(ΩK/K) :=
  AlgEquiv.ofRingEquiv (f := F.trans (σ.toRingEquiv.trans F.symm)) (by
    intro x
    have hFsymm : F.symm (algebraMap L ΩL (e x)) = algebraMap K ΩK x := by
      apply F.injective
      simp [hF]
    simp [hF, hFsymm])

/-- Compatibility of the inverse arbitrary-closure equivalence with scalar embeddings. -/
theorem closureSymm_algebraMap (e : K ≃+* L) (F : ΩK ≃+* ΩL)
    (hF : ∀ x : K, F (algebraMap K ΩK x) = algebraMap L ΩL (e x)) (y : L) :
    F.symm (algebraMap L ΩL y) = algebraMap K ΩK (e.symm y) := by
  apply F.injective
  simp [hF]

/-- The inverse conjugation map associated to `closureMapOfEquiv`. -/
noncomputable def closureInvMapOfEquiv (e : K ≃+* L) (F : ΩK ≃+* ΩL)
    (hF : ∀ x : K, F (algebraMap K ΩK x) = algebraMap L ΩL (e x))
    (τ : Gal(ΩK/K)) : Gal(ΩL/L) :=
  closureMapOfEquiv e.symm F.symm (closureSymm_algebraMap e F hF) τ

/-- Conjugation by an arbitrary closure equivalence as a multiplicative equivalence. -/
noncomputable def closureMulEquivOfEquiv (e : K ≃+* L) (F : ΩK ≃+* ΩL)
    (hF : ∀ x : K, F (algebraMap K ΩK x) = algebraMap L ΩL (e x)) :
    Gal(ΩL/L) ≃* Gal(ΩK/K) where
  toFun := closureMapOfEquiv e F hF
  invFun := closureInvMapOfEquiv e F hF
  left_inv σ := by
    ext x
    dsimp [closureMapOfEquiv, closureInvMapOfEquiv]
    simp
  right_inv τ := by
    ext x
    dsimp [closureMapOfEquiv, closureInvMapOfEquiv]
    simp
  map_mul' σ τ := by
    ext x
    dsimp [closureMapOfEquiv]
    simp [AlgEquiv.mul_apply]

/--
The basic open set of automorphisms fixing the chosen finite basis of an intermediate field,
after transporting the basis along an arbitrary closure equivalence.
-/
noncomputable def closureBasisStabilizer (F : ΩK ≃+* ΩL)
    (E : IntermediateField K ΩK) [FiniteDimensional K E] : Set Gal(ΩL/L) :=
  ⋂ i : Fin (Module.finrank K E),
    (MulAction.stabilizer Gal(ΩL/L) (F (((Module.finBasis K E) i : E) : ΩK)) :
      Set Gal(ΩL/L))

/-- The finite-basis stabilizer is open in the Krull topology. -/
theorem isOpen_closureBasisStabilizer [Algebra.IsIntegral L ΩL] (F : ΩK ≃+* ΩL)
    (E : IntermediateField K ΩK) [FiniteDimensional K E] :
    IsOpen (closureBasisStabilizer (L := L) F E) := by
  dsimp [closureBasisStabilizer]
  exact isOpen_iInter_of_finite fun i ↦ stabilizer_isOpen_of_isIntegral
    (F (((Module.finBasis K E) i : E) : ΩK))

/-- The identity automorphism belongs to the finite-basis stabilizer. -/
theorem one_mem_closureBasisStabilizer (F : ΩK ≃+* ΩL)
    (E : IntermediateField K ΩK) [FiniteDimensional K E] :
    (1 : Gal(ΩL/L)) ∈ closureBasisStabilizer (L := L) F E := by
  simp [closureBasisStabilizer]

/--
If an automorphism fixes the transported finite basis of `E`, then its conjugate fixes `E`.
-/
theorem closureMapOfEquiv_mem_fixingSubgroup_of_mem_basisStabilizer (e : K ≃+* L)
    (F : ΩK ≃+* ΩL)
    (hF : ∀ x : K, F (algebraMap K ΩK x) = algebraMap L ΩL (e x))
    (E : IntermediateField K ΩK) [FiniteDimensional K E]
    {σ : Gal(ΩL/L)} (hσ : σ ∈ closureBasisStabilizer (L := L) F E) :
    closureMapOfEquiv e F hF σ ∈ E.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let b := Module.finBasis K E
  let xE : E := ⟨x, hx⟩
  have hσ_basis : ∀ i : Fin (Module.finrank K E),
      σ (F ((b i : E) : ΩK)) = F ((b i : E) : ΩK) := by
    intro i
    have hi : σ ∈ MulAction.stabilizer Gal(ΩL/L) (F ((b i : E) : ΩK)) := by
      exact Set.mem_iInter.mp hσ i
    simpa using (MulAction.mem_stabilizer_iff.mp hi)
  have hxsum : (∑ i : Fin (Module.finrank K E),
        algebraMap K ΩK (b.repr xE i) * ((b i : E) : ΩK)) = x := by
    simpa [Algebra.smul_def, b, xE] using
      congrArg (fun y : E ↦ (y : ΩK)) (b.sum_repr xE)
  have hσFx : σ (F x) = F x := by
    calc
      σ (F x) = σ (F (∑ i : Fin (Module.finrank K E),
          algebraMap K ΩK (b.repr xE i) * ((b i : E) : ΩK))) := by rw [hxsum]
      _ = ∑ i : Fin (Module.finrank K E),
          algebraMap L ΩL (e (b.repr xE i)) * F ((b i : E) : ΩK) := by
        simp [map_sum, hF, hσ_basis]
      _ = F (∑ i : Fin (Module.finrank K E),
          algebraMap K ΩK (b.repr xE i) * ((b i : E) : ΩK)) := by
        simp [map_sum, hF]
      _ = F x := by rw [hxsum]
  dsimp [closureMapOfEquiv]
  change F.symm (σ (F x)) = x
  rw [hσFx]
  exact F.symm_apply_apply x

/-- Conjugation by an arbitrary closure equivalence is continuous for the Krull topology. -/
theorem continuous_closureMapOfEquiv [Algebra.IsIntegral L ΩL] (e : K ≃+* L)
    (F : ΩK ≃+* ΩL)
    (hF : ∀ x : K, F (algebraMap K ΩK x) = algebraMap L ΩL (e x)) :
    Continuous (closureMapOfEquiv e F hF) := by
  change Continuous (closureMulEquivOfEquiv e F hF : Gal(ΩL/L) → Gal(ΩK/K))
  apply continuous_of_continuousAt_one (closureMulEquivOfEquiv e F hF)
  rw [continuousAt_def]
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, _hE, hsE⟩ := hs
  apply mem_nhds_iff.mpr
  refine ⟨closureBasisStabilizer (L := L) F E, ?_, isOpen_closureBasisStabilizer (L := L) F E,
    one_mem_closureBasisStabilizer (L := L) F E⟩
  intro σ hσ
  exact hsE (closureMapOfEquiv_mem_fixingSubgroup_of_mem_basisStabilizer e F hF E hσ)

/-- The inverse conjugation map is continuous for the Krull topology. -/
theorem continuous_closureInvMapOfEquiv [Algebra.IsIntegral K ΩK] (e : K ≃+* L)
    (F : ΩK ≃+* ΩL)
    (hF : ∀ x : K, F (algebraMap K ΩK x) = algebraMap L ΩL (e x)) :
    Continuous (closureInvMapOfEquiv e F hF) := by
  change Continuous (closureMapOfEquiv e.symm F.symm (closureSymm_algebraMap e F hF))
  exact continuous_closureMapOfEquiv e.symm F.symm (closureSymm_algebraMap e F hF)

/--
Conjugation by an arbitrary algebraic/separable-closure equivalence as a continuous
multiplicative equivalence.
-/
noncomputable def closureContinuousMulEquivOfEquiv [Algebra.IsIntegral K ΩK]
    [Algebra.IsIntegral L ΩL] (e : K ≃+* L) (F : ΩK ≃+* ΩL)
    (hF : ∀ x : K, F (algebraMap K ΩK x) = algebraMap L ΩL (e x)) :
    Gal(ΩL/L) ≃ₜ* Gal(ΩK/K) :=
  ContinuousMulEquiv.mk (closureMulEquivOfEquiv e F hF)
    (continuous_closureMapOfEquiv e F hF)
    (continuous_closureInvMapOfEquiv e F hF)

end ArbitraryClosures

end AbsGalConj

variable {K L : Type u} [Field K] [NumberField K] [Field L] [NumberField L]

/-- A topological isomorphism of absolute Galois groups. -/
abbrev AbsGalEquiv (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] :
    Type u :=
  Gal(AlgebraicClosure K/K) ≃ₜ* Gal(AlgebraicClosure L/L)

/-- A field isomorphism, with the contravariant orientation used by absolute Galois groups. -/
abbrev GlobalFieldIso (K L : Type u) [Field K] [NumberField K] [Field L] [NumberField L] :
    Type u :=
  L ≃+* K

/-- The profinite absolute Galois group attached to the chosen algebraic closure. -/
noncomputable def absGalProfiniteObj (K : Type u) [Field K] [NumberField K] : ProfiniteGrp.{u} :=
  InfiniteGalois.profiniteGalGrp K (AlgebraicClosure K)

/-- The absolute Galois group, viewed in the outer profinite-group category. -/
noncomputable def absGalOuterObj (K : Type u) [Field K] [NumberField K] :
    Anabelian.ProfiniteGrpOuter.{u} :=
  (CategoryTheory.Quotient.functor Anabelian.profiniteGrpOuterRel).obj (absGalProfiniteObj K)

/-- The outer profinite-group isomorphism represented by a concrete absolute-Galois isomorphism. -/
noncomputable def outerIsoOfAbsGalEquiv (θ : AbsGalEquiv K L) :
    absGalOuterObj K ≅ absGalOuterObj L :=
  (CategoryTheory.Quotient.functor Anabelian.profiniteGrpOuterRel).mapIso
    (ProfiniteGrp.ContinuousMulEquiv.toProfiniteGrpIso θ)

namespace GlobalFieldIso

/-- Extend a global field isomorphism to the chosen algebraic closures. -/
noncomputable def algClosureEquiv (e : GlobalFieldIso K L) :
    AlgebraicClosure L ≃+* AlgebraicClosure K :=
  IsAlgClosure.equivOfEquiv (AlgebraicClosure L) (AlgebraicClosure K) e

@[simp]
theorem algClosureEquiv_algebraMap (e : GlobalFieldIso K L) (x : L) :
    algClosureEquiv e (algebraMap L (AlgebraicClosure L) x) =
      algebraMap K (AlgebraicClosure K) (e x) := by
  simp [algClosureEquiv]

/-- The concrete absolute-Galois isomorphism induced by a global field isomorphism. -/
noncomputable def toAbsGalEquiv (e : GlobalFieldIso K L) : AbsGalEquiv K L :=
  AbsGalConj.continuousMulEquivOfEquiv e (algClosureEquiv e) (algClosureEquiv_algebraMap e)

/-- The profinite-group isomorphism induced by a global field isomorphism. -/
noncomputable def toProfiniteGrpIso (e : GlobalFieldIso K L) :
    absGalProfiniteObj K ≅ absGalProfiniteObj L :=
  ProfiniteGrp.ContinuousMulEquiv.toProfiniteGrpIso e.toAbsGalEquiv

/-- The outer profinite-group isomorphism induced by a global field isomorphism. -/
noncomputable def toOuterIso (e : GlobalFieldIso K L) :
    absGalOuterObj K ≅ absGalOuterObj L :=
  outerIsoOfAbsGalEquiv e.toAbsGalEquiv

/-- The profinite-group map attached to the identity is inner-conjugate to the identity. -/
theorem toProfiniteGrpIso_refl_outerRel (K : Type u) [Field K] [NumberField K] :
    Anabelian.profiniteGrpOuterRel
      ((toProfiniteGrpIso (K := K) (L := K) (RingEquiv.refl K)).hom)
      (𝟙 (absGalProfiniteObj K)) := by
  let eK : GlobalFieldIso K K := RingEquiv.refl K
  let Fid : AlgebraicClosure K ≃+* AlgebraicClosure K := RingEquiv.refl _
  have hFid : ∀ x : K, Fid (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K (AlgebraicClosure K) (eK x) := by
    intro x
    dsimp [Fid, eK]
  let F := algClosureEquiv eK
  let hGal : Gal(AlgebraicClosure K/K) :=
    AbsGalConj.comparisonAut eK F Fid (algClosureEquiv_algebraMap eK) hFid
  let h : absGalProfiniteObj K := hGal
  refine ⟨h, fun σ ↦ ?_⟩
  unfold absGalProfiniteObj InfiniteGalois.profiniteGalGrp at σ h ⊢
  ext y
  rw [show (toProfiniteGrpIso eK).hom = ProfiniteGrp.ofHom (toAbsGalEquiv eK) from rfl]
  rw [ProfiniteGrp.ofHom_apply]
  dsimp [toAbsGalEquiv, AbsGalConj.continuousMulEquivOfEquiv,
    AbsGalConj.mulEquivOfEquiv, AbsGalConj.comparisonAut, AbsGalConj.mapOfEquiv,
    h, hGal, Fid, F]
  simp

@[simp]
theorem toOuterIso_refl (K : Type u) [Field K] [NumberField K] :
    toOuterIso (K := K) (L := K) (RingEquiv.refl K) = Iso.refl (absGalOuterObj K) := by
  apply Iso.ext
  change (CategoryTheory.Quotient.functor Anabelian.profiniteGrpOuterRel).map
      (toProfiniteGrpIso (K := K) (L := K) (RingEquiv.refl K)).hom =
    (CategoryTheory.Quotient.functor Anabelian.profiniteGrpOuterRel).map
      (𝟙 (absGalProfiniteObj K))
  exact CategoryTheory.Quotient.sound Anabelian.profiniteGrpOuterRel
    (toProfiniteGrpIso_refl_outerRel K)

/-- The profinite-group maps attached to a composite are inner-conjugate. -/
theorem toProfiniteGrpIso_trans_outerRel {K L M : Type u}
    [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    (e : GlobalFieldIso L K) (e' : GlobalFieldIso M L) :
    Anabelian.profiniteGrpOuterRel (toProfiniteGrpIso (e.trans e' : GlobalFieldIso M K)).hom
      ((toProfiniteGrpIso e').hom ≫ (toProfiniteGrpIso e).hom) := by
  let eKM : GlobalFieldIso M K := e.trans e'
  let Fcomp := algClosureEquiv eKM
  let Fseq := (algClosureEquiv e).trans (algClosureEquiv e')
  have hFseq : ∀ x : K, Fseq (algebraMap K (AlgebraicClosure K) x) =
      algebraMap M (AlgebraicClosure M) (eKM x) := by
    intro x
    dsimp [Fseq, eKM]
    rw [algClosureEquiv_algebraMap e]
    rw [algClosureEquiv_algebraMap e']
  let hGal : Gal(AlgebraicClosure K/K) :=
    AbsGalConj.comparisonAut eKM Fcomp Fseq (algClosureEquiv_algebraMap eKM) hFseq
  let h : absGalProfiniteObj K := hGal
  refine ⟨h, fun σ ↦ ?_⟩
  unfold absGalProfiniteObj InfiniteGalois.profiniteGalGrp at σ h ⊢
  ext y
  rw [show (toProfiniteGrpIso eKM).hom = ProfiniteGrp.ofHom (toAbsGalEquiv eKM) from rfl]
  rw [ProfiniteGrp.ofHom_apply]
  rw [ProfiniteGrp.comp_apply]
  rw [show (toProfiniteGrpIso e').hom = ProfiniteGrp.ofHom (toAbsGalEquiv e') from rfl]
  rw [ProfiniteGrp.ofHom_apply]
  rw [show (toProfiniteGrpIso e).hom = ProfiniteGrp.ofHom (toAbsGalEquiv e) from rfl]
  rw [ProfiniteGrp.ofHom_apply]
  simp [toAbsGalEquiv, AbsGalConj.continuousMulEquivOfEquiv,
    AbsGalConj.mulEquivOfEquiv, AbsGalConj.comparisonAut, AbsGalConj.mapOfEquiv,
    h, hGal, Fcomp, Fseq]

@[simp]
theorem toOuterIso_trans {K L M : Type u}
    [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]
    (e : GlobalFieldIso L K) (e' : GlobalFieldIso M L) :
    toOuterIso (e.trans e' : GlobalFieldIso M K) = e'.toOuterIso ≪≫ e.toOuterIso := by
  apply Iso.ext
  change (CategoryTheory.Quotient.functor Anabelian.profiniteGrpOuterRel).map
      (toProfiniteGrpIso (e.trans e' : GlobalFieldIso M K)).hom =
    (CategoryTheory.Quotient.functor Anabelian.profiniteGrpOuterRel).map
      ((toProfiniteGrpIso e').hom ≫ (toProfiniteGrpIso e).hom)
  exact CategoryTheory.Quotient.sound Anabelian.profiniteGrpOuterRel
    (toProfiniteGrpIso_trans_outerRel e e')

/--
A global field isomorphism induces an absolute-Galois isomorphism when their induced outer maps
agree.  This quotients the algebraic-closure choice by target-inner conjugation.
-/
def InducesAbsGalEquiv (e : GlobalFieldIso K L) (θ : AbsGalEquiv K L) : Prop :=
  outerIsoOfAbsGalEquiv θ = e.toOuterIso

/-- The chosen concrete representative induces its own outer absolute-Galois isomorphism. -/
theorem induces_toAbsGalEquiv (e : GlobalFieldIso K L) :
    e.InducesAbsGalEquiv e.toAbsGalEquiv :=
  rfl

end GlobalFieldIso

end NumberField
