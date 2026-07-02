/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import AnabelianAlgorithms.Mathlib.FieldTheory.Galois.ULift
import AnabelianAlgorithms.Mathlib.NumberField.AbsoluteGalois.NeukirchUchidaConcrete

/-!
# Lean-evaluation wrapper for the Neukirch-Uchida statement

This file exposes the universe-polymorphic form of the Neukirch-Uchida reconstruction statement.
The concrete absolute-Galois reconstruction helpers live in
`AnabelianAlgorithms.Mathlib.NumberField.AbsoluteGalois.NeukirchUchidaConcrete`.
-/

set_option linter.nonstandardAxioms false

universe u v w z l

open CategoryTheory
open Anabelian
open scoped NumberField

theorem neukirch_uchida_universe_monomorphic {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁']
    [IsSepClosure K₂ K₂'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    ∃! σ : K₂' ≃+* K₁', (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
      ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  refine ⟨adjustedClosureIso ϕ he, ?_, ?_⟩
  · exact ⟨adjustedClosureIso_maps_base_range ϕ he, adjustedClosureIso_induces_phi ϕ he⟩
  · intro τ hτ
    exact closureIso_unique_of_induces_phi ϕ he (σ := τ) (τ := adjustedClosureIso ϕ he)
      hτ.1 (adjustedClosureIso_maps_base_range ϕ he) hτ.2
      (adjustedClosureIso_induces_phi ϕ he)

theorem neukirch_uchida {K₁ : Type u} {K₂ : Type v} {K₁' : Type w} {K₂' : Type z}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁']
    [IsSepClosure K₂ K₂'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    ∃! σ : K₂' ≃+* K₁', (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
      ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm) := by
  letI : NumberField (ULift.{max u v w z} K₁) := uliftNumberField (K := K₁)
  letI : NumberField (ULift.{max u v w z} K₂) := uliftNumberField (K := K₂)
  letI : Algebra (ULift.{max u v w z} K₁) (ULift.{max u v w z} K₁') := uliftAlgebra
  letI : Algebra (ULift.{max u v w z} K₂) (ULift.{max u v w z} K₂') := uliftAlgebra
  haveI : IsSepClosure (ULift.{max u v w z} K₁) (ULift.{max u v w z} K₁') := uliftIsSepClosure
  haveI : IsSepClosure (ULift.{max u v w z} K₂) (ULift.{max u v w z} K₂') := uliftIsSepClosure
  let phiU := liftedPhi ϕ
  have heU : IsHomeomorph phiU := by
    dsimp [phiU]
    exact isHomeomorph_liftedPhi ϕ he
  obtain ⟨sigmaU, hsigmaU, hsigmaUuniq⟩ :=
    neukirch_uchida_universe_monomorphic (K₁ := ULift.{max u v w z} K₁)
      (K₂ := ULift.{max u v w z} K₂) (K₁' := ULift.{max u v w z} K₁')
      (K₂' := ULift.{max u v w z} K₂') phiU heU
  refine ⟨lowerULiftRingEquiv sigmaU, ?_, ?_⟩
  · constructor
    · exact lowerULiftRingEquiv_maps_base_range (K₁ := K₁) (K₂ := K₂) (K₁' := K₁')
        (K₂' := K₂') sigmaU hsigmaU.1
    · intro g
      have h := hsigmaU.2 (galULiftEquiv K₁ K₁' g)
      have hRing := congrArg (fun e : ULift.{max u v w z} K₂' ≃+* ULift.{max u v w z} K₂' ↦
          lowerULiftRingEquiv e) h
      simpa [phiU, lowerULiftRingEquiv_conj] using hRing
  · intro τ hτ
    have hτu_base : (algebraMap (ULift.{max u v w z} K₂) (ULift.{max u v w z} K₂')).range.map
          (uliftRingEquiv τ).toRingHom =
        (algebraMap (ULift.{max u v w z} K₁) (ULift.{max u v w z} K₁')).range :=
      uliftRingEquiv_maps_base_range (K₁ := K₁) (K₂ := K₂) (K₁' := K₁')
        (K₂' := K₂') τ hτ.1
    have hτu_phi : ∀ gU : Gal(ULift.{max u v w z} K₁'/ULift.{max u v w z} K₁),
        phiU gU = (uliftRingEquiv τ).trans (gU.toRingEquiv.trans (uliftRingEquiv τ).symm) := by
      intro gU
      let g : Gal(K₁'/K₁) := (galULiftEquiv K₁ K₁').symm gU
      have hdown := hτ.2 g
      have hlift := congrArg (fun e : K₂' ≃+* K₂' ↦ uliftRingEquiv e) hdown
      have hgU : galULiftEquiv K₁ K₁' g = gU := by
        dsimp [g]
        simp
      have hleft : (phiU gU).toRingEquiv = uliftRingEquiv (ϕ g).toRingEquiv := by
        rw [← hgU]
        rw [show phiU (galULiftEquiv K₁ K₁' g) = galULiftEquiv K₂ K₂' (ϕ g) by
          exact liftedPhi_galULiftEquiv ϕ g]
        exact galULiftEquiv_toRingEquiv K₂ K₂' (ϕ g)
      have hright : uliftRingEquiv (τ.trans (g.toRingEquiv.trans τ.symm)) =
          (uliftRingEquiv τ).trans (gU.toRingEquiv.trans (uliftRingEquiv τ).symm) := by
        rw [← hgU]
        exact galULiftEquiv_conj_toRingEquiv (K₁ := K₁) (K₁' := K₁') (K₂' := K₂') τ g
      rw [hleft]
      exact hlift.trans hright
    have hσeq : uliftRingEquiv τ = sigmaU :=
      hsigmaUuniq (uliftRingEquiv τ) ⟨hτu_base, hτu_phi⟩
    rw [← hσeq]
    simp
