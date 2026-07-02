/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import Mathlib.Algebra.Field.ULift
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic


/-!
# Galois groups and field structures under `ULift`

This file collects reusable `ULift` transport for number-field structures, separable closures,
Galois groups, ring equivalences, and embedded base-field ranges.
-/

universe u v w z l

open Polynomial
open scoped NumberField

/-- Universe-polymorphic transport of algebraic closedness along a field isomorphism. -/
private theorem isAlgClosed_of_ringEquiv' {k : Type u} (k' : Type v) [Field k] [Field k']
    (e : k ≃+* k') [IsAlgClosed k] : IsAlgClosed k' := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hpe : degree (p.map e.symm.toRingHom) ≠ 0 := by
    rw [degree_map]
    exact ne_of_gt (degree_pos_of_irreducible hp)
  rcases IsAlgClosed.exists_root (k := k) (p.map e.symm.toRingHom) hpe with ⟨x, hx⟩
  use e x
  rw [IsRoot] at hx
  apply e.symm.injective
  rw [map_zero, ← hx]
  clear hx hpe hp hmp
  induction p using Polynomial.induction_on <;> simp_all

set_option linter.defProp false in
/-- Transport a number-field structure to a universe lift. -/
@[reducible]
noncomputable def uliftNumberField {K : Type u} [Field K] [NumberField K] :
    NumberField (ULift.{w} K) :=
  NumberField.of_ringEquiv K (ULift.{w} K) (ULift.ringEquiv.symm)

/-- The algebra structure on lifted fields induced by an algebra structure downstairs. -/
@[reducible]
noncomputable def uliftAlgebra {K : Type u} {K' : Type v} [Field K] [Field K']
    [Algebra K K'] : Algebra (ULift.{w} K) (ULift.{w} K') where
  __ := ULift.module
  algebraMap := (algebraMap K K').ulift
  commutes' r x := by
    apply ULift.down_injective
    exact Algebra.commutes r.down x.down
  smul_def' r x := by
    apply ULift.down_injective
    exact Algebra.smul_def' r.down x.down

@[simp]
theorem uliftAlgebra_down_algebraMap {K : Type u} {K' : Type v} [Field K] [Field K']
    [Algebra K K'] (x : ULift.{w} K) :
    letI : Algebra (ULift.{w} K) (ULift.{w} K') := uliftAlgebra
    (algebraMap (ULift.{w} K) (ULift.{w} K') x).down = algebraMap K K' x.down :=
  rfl

set_option linter.defProp false in
/-- Transport a separable-closure structure to a universe lift. -/
@[reducible]
noncomputable def uliftIsSepClosure {K : Type u} {K' : Type v} [Field K] [Field K']
    [NumberField K] [Algebra K K'] [IsSepClosure K K'] :
    letI : Algebra (ULift.{w} K) (ULift.{w} K') := uliftAlgebra
    IsSepClosure (ULift.{w} K) (ULift.{w} K') := by
  letI : Algebra (ULift.{w} K) (ULift.{w} K') := uliftAlgebra
  refine ⟨?_, ?_⟩
  · haveI : IsAlgClosure K K' := inferInstance
    haveI : IsAlgClosed K' := IsAlgClosure.isAlgClosed (R := K) (K := K')
    haveI : IsAlgClosed (ULift.{w} K') :=
      isAlgClosed_of_ringEquiv' (ULift.{w} K')
        (ULift.ringEquiv.symm : K' ≃+* ULift.{w} K')
    infer_instance
  · rw [← Algebra.IsSeparable.iff_of_equiv_equiv
        (e₁ := (ULift.ringEquiv.symm : K ≃+* ULift.{w} K))
        (e₂ := (ULift.ringEquiv.symm : K' ≃+* ULift.{w} K'))]
    · infer_instance
    · ext x
      rfl

section ULiftGalois

variable {K : Type u} {K' : Type v} [Field K] [Field K'] [Algebra K K']

noncomputable local instance : Algebra (ULift.{w} K) (ULift.{w} K') := uliftAlgebra

/-- Lower an intermediate field of the lifted extension. -/
private noncomputable def lowerIntermediateField
    (E : IntermediateField (ULift.{w} K) (ULift.{w} K')) : IntermediateField K K' where
  __ := E.toSubfield.comap (ULift.ringEquiv.symm : K' ≃+* ULift.{w} K').toRingHom
  algebraMap_mem' x := by
    change (ULift.ringEquiv.symm : K' ≃+* ULift.{w} K') (algebraMap K K' x) ∈ E.toSubfield
    change ULift.up (algebraMap K K' x) ∈ E
    have h := E.algebraMap_mem (ULift.up x)
    change algebraMap (ULift.{w} K) (ULift.{w} K') (ULift.up x) ∈ E at h
    exact h

@[simp]
private theorem mem_lowerIntermediateField
    (E : IntermediateField (ULift.{w} K) (ULift.{w} K')) (x : K') :
    x ∈ lowerIntermediateField E ↔ ULift.up x ∈ E :=
  Iff.rfl

private noncomputable def lowerIntermediateFieldRingEquiv
    (E : IntermediateField (ULift.{w} K) (ULift.{w} K')) :
    E ≃+* lowerIntermediateField E where
  toFun x := ⟨x.1.down, by
    change (ULift.ringEquiv.symm : K' ≃+* ULift.{w} K') x.1.down ∈ E.toSubfield
    change ULift.up x.1.down ∈ E
    rw [show ULift.up x.1.down = x.1 by cases x.1; rfl]
    exact x.2⟩
  invFun x := ⟨ULift.up x.1, by
    show ULift.up x.1 ∈ E
    exact x.2⟩
  left_inv x := by ext; cases x.1; rfl
  right_inv x := by ext; rfl
  map_mul' x y := by ext; rfl
  map_add' x y := by ext; rfl

private theorem lowerIntermediateField_finiteDimensional
    (E : IntermediateField (ULift.{w} K) (ULift.{w} K'))
    [FiniteDimensional (ULift.{w} K) E] : FiniteDimensional K (lowerIntermediateField E) := by
  have hfin : Module.finrank (ULift.{w} K) E = Module.finrank K (lowerIntermediateField E) := by
    apply Algebra.finrank_eq_of_equiv_equiv
      (ULift.ringEquiv : ULift.{w} K ≃+* K)
      (lowerIntermediateFieldRingEquiv E)
    ext x
    rfl
  have hpos : 0 < Module.finrank (ULift.{w} K) E :=
    Module.finrank_pos (R := ULift.{w} K) (M := E)
  have hpos' : 0 < Module.finrank K (lowerIntermediateField E) := by
    exact hfin ▸ hpos
  exact FiniteDimensional.of_finrank_pos hpos'

/-- Lift an intermediate field of the original extension. -/
private noncomputable def liftIntermediateField
    (E : IntermediateField K K') : IntermediateField (ULift.{w} K) (ULift.{w} K') where
  __ := E.toSubfield.comap (ULift.ringEquiv : ULift.{w} K' ≃+* K').toRingHom
  algebraMap_mem' x := by
    change algebraMap K K' x.down ∈ E
    exact E.algebraMap_mem x.down

@[simp]
private theorem mem_liftIntermediateField
    (E : IntermediateField K K') (x : ULift.{w} K') :
    x ∈ liftIntermediateField E ↔ x.down ∈ E :=
  Iff.rfl

private noncomputable def liftIntermediateFieldRingEquiv
    (E : IntermediateField K K') : E ≃+* liftIntermediateField E where
  toFun x := ⟨ULift.up x.1, x.2⟩
  invFun x := ⟨x.1.down, x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; cases x.1; rfl
  map_mul' x y := by ext; rfl
  map_add' x y := by ext; rfl

private theorem liftIntermediateField_finiteDimensional
    (E : IntermediateField K K') [FiniteDimensional K E] :
    FiniteDimensional (ULift.{w} K) (@liftIntermediateField.{u, v, w} K K' _ _ _ E) := by
  have hfin : Module.finrank K E =
      Module.finrank (ULift.{w} K) (@liftIntermediateField.{u, v, w} K K' _ _ _ E) := by
    apply Algebra.finrank_eq_of_equiv_equiv
      (ULift.ringEquiv.symm : K ≃+* ULift.{w} K)
      (@liftIntermediateFieldRingEquiv.{u, v, w} K K' _ _ _ E)
    ext x
    rfl
  have hpos : 0 < Module.finrank K E := Module.finrank_pos (R := K) (M := E)
  have hpos' : 0 < Module.finrank (ULift.{w} K)
      (@liftIntermediateField.{u, v, w} K K' _ _ _ E) := by
    exact hfin ▸ hpos
  exact FiniteDimensional.of_finrank_pos hpos'

/-- The multiplicative equivalence on Galois groups induced by `ULift`. -/
private noncomputable def galULiftMulEquiv :
    Gal(K'/K) ≃* Gal(ULift.{w} K'/ULift.{w} K) where
  toFun g :=
    AlgEquiv.ofRingEquiv
      (f := (ULift.ringEquiv : ULift.{w} K' ≃+* K').trans
        (g.toRingEquiv.trans (ULift.ringEquiv.symm : K' ≃+* ULift.{w} K')))
      (by intro x; apply ULift.down_injective; exact g.commutes x.down)
  invFun h :=
    AlgEquiv.ofRingEquiv
      (f := (ULift.ringEquiv.symm : K' ≃+* ULift.{w} K').trans
        (h.toRingEquiv.trans (ULift.ringEquiv : ULift.{w} K' ≃+* K')))
      (by intro x; exact congrArg ULift.down (h.commutes (ULift.up x)))
  left_inv g := by ext x; rfl
  right_inv h := by ext x; rfl
  map_mul' g h := by ext x; rfl

private theorem continuous_galULiftMulEquiv : Continuous (galULiftMulEquiv :
    Gal(K'/K) → Gal(ULift.{w} K'/ULift.{w} K)) := by
  apply continuous_of_continuousAt_one galULiftMulEquiv
  rw [continuousAt_def]
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hEfin, hEs⟩ := hs
  let Edown := lowerIntermediateField E
  haveI : FiniteDimensional K Edown := lowerIntermediateField_finiteDimensional E
  apply mem_nhds_iff.mpr
  refine ⟨(Edown.fixingSubgroup : Set Gal(K'/K)), ?_,
    IntermediateField.fixingSubgroup_isOpen Edown, Edown.fixingSubgroup.one_mem⟩
  intro g hg
  apply hEs
  change g ∈ Edown.fixingSubgroup at hg
  change galULiftMulEquiv g ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff] at hg ⊢
  intro x hx
  have hxdown : x.down ∈ Edown := by
    rw [mem_lowerIntermediateField]
    rw [show ULift.up x.down = x by cases x; rfl]
    exact hx
  have hfix := hg x.down hxdown
  change ULift.up (g x.down) = x
  rw [hfix]

private theorem continuous_galULiftMulEquiv_symm : Continuous ((galULiftMulEquiv :
    Gal(K'/K) ≃* Gal(ULift.{w} K'/ULift.{w} K)).symm :
      Gal(ULift.{w} K'/ULift.{w} K) → Gal(K'/K)) := by
  apply continuous_of_continuousAt_one (galULiftMulEquiv.symm)
  rw [continuousAt_def]
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hEfin, hEs⟩ := hs
  let Eup := @liftIntermediateField.{u, v, w} K K' _ _ _ E
  haveI : FiniteDimensional (ULift.{w} K) Eup :=
    liftIntermediateField_finiteDimensional E
  apply mem_nhds_iff.mpr
  refine ⟨(Eup.fixingSubgroup : Set Gal(ULift.{w} K'/ULift.{w} K)), ?_,
    IntermediateField.fixingSubgroup_isOpen Eup, Eup.fixingSubgroup.one_mem⟩
  intro g hg
  apply hEs
  change g ∈ Eup.fixingSubgroup at hg
  change galULiftMulEquiv.symm g ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff] at hg ⊢
  intro x hx
  have hxup : (ULift.up x : ULift.{w} K') ∈ Eup := by
    rw [mem_liftIntermediateField]
    exact hx
  have hfix := hg (ULift.up x) hxup
  exact congrArg ULift.down hfix

end ULiftGalois

/-- Transport Galois groups through `ULift`, as a continuous multiplicative equivalence. -/
noncomputable def galULiftEquiv (K : Type u) (K' : Type v) [Field K] [Field K'] [Algebra K K'] :
    letI : Algebra (ULift.{w} K) (ULift.{w} K') := uliftAlgebra
    Gal(K'/K) ≃ₜ* Gal(ULift.{w} K'/ULift.{w} K) := by
  letI : Algebra (ULift.{w} K) (ULift.{w} K') := uliftAlgebra
  exact ContinuousMulEquiv.mk (galULiftMulEquiv (K := K) (K' := K'))
    (continuous_galULiftMulEquiv (K := K) (K' := K'))
    (continuous_galULiftMulEquiv_symm (K := K) (K' := K'))

@[simp]
theorem galULiftEquiv_apply_apply (K : Type u) (K' : Type v) [Field K] [Field K']
    [Algebra K K'] (g : Gal(K'/K)) (x : ULift.{w} K') :
    letI : Algebra (ULift.{w} K) (ULift.{w} K') := uliftAlgebra
    galULiftEquiv K K' g x = ULift.up (g x.down) :=
  rfl

/-- The lifted Galois automorphism is conjugation by `ULift.ringEquiv`. -/
theorem galULiftEquiv_toRingEquiv (K : Type u) (K' : Type v) [Field K] [Field K']
    [Algebra K K'] (g : Gal(K'/K)) :
    letI : Algebra (ULift.{w} K) (ULift.{w} K') := uliftAlgebra
    (galULiftEquiv K K' g).toRingEquiv =
      (ULift.ringEquiv : ULift.{w} K' ≃+* K').trans
        (g.toRingEquiv.trans (ULift.ringEquiv.symm : K' ≃+* ULift.{w} K')) :=
  rfl

/-- Lift a ring equivalence to `ULift`. -/
def uliftRingEquiv {R : Type u} {S : Type v} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (e : R ≃+* S) : ULift.{w} R ≃+* ULift.{w} S :=
  (ULift.ringEquiv : ULift.{w} R ≃+* R).trans
    (e.trans (ULift.ringEquiv.symm : S ≃+* ULift.{w} S))

@[simp]
theorem uliftRingEquiv_apply {R : Type u} {S : Type v} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (e : R ≃+* S) (x : ULift.{w} R) :
    uliftRingEquiv e x = ULift.up (e x.down) :=
  rfl

/-- Lower a ring equivalence between `ULift`s. -/
def lowerULiftRingEquiv {R : Type u} {S : Type v} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (e : ULift.{w} R ≃+* ULift.{w} S) : R ≃+* S :=
  (ULift.ringEquiv.symm : R ≃+* ULift.{w} R).trans
    (e.trans (ULift.ringEquiv : ULift.{w} S ≃+* S))

@[simp]
theorem lowerULiftRingEquiv_apply {R : Type u} {S : Type v} [NonUnitalNonAssocSemiring R]
    [NonUnitalNonAssocSemiring S] (e : ULift.{w} R ≃+* ULift.{w} S) (x : R) :
    lowerULiftRingEquiv e x = (e (ULift.up x)).down :=
  rfl

@[simp]
theorem lowerULiftRingEquiv_uliftRingEquiv {R : Type u} {S : Type v}
    [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S] (e : R ≃+* S) :
    lowerULiftRingEquiv (uliftRingEquiv e) = e := by
  ext x
  rfl

@[simp]
theorem uliftRingEquiv_lowerULiftRingEquiv {R : Type u} {S : Type v}
    [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    (e : ULift.{w} R ≃+* ULift.{w} S) :
    uliftRingEquiv (lowerULiftRingEquiv e) = e := by
  ext x
  cases x
  rfl

/-- ULift commutes with ring-equivalence conjugation. -/
theorem uliftRingEquiv_conj {K₁' : Type u} {K₂' : Type v} [Field K₁'] [Field K₂']
    (σ : K₂' ≃+* K₁') (g : K₁' ≃+* K₁') :
    uliftRingEquiv (σ.trans (g.trans σ.symm)) =
      (uliftRingEquiv σ).trans
        ((uliftRingEquiv g).trans (uliftRingEquiv σ).symm) := by
  ext x
  rfl

/-- The `ULift` Galois transport matches closure-isomorphism conjugation pointwise. -/
theorem galULiftEquiv_conj_toRingEquiv {K₁ : Type u} {K₁' : Type v} {K₂' : Type z}
    [Field K₁] [Field K₁'] [Field K₂'] [Algebra K₁ K₁']
    (σ : K₂' ≃+* K₁') (g : Gal(K₁'/K₁)) :
    letI : Algebra (ULift.{w} K₁) (ULift.{w} K₁') := uliftAlgebra
    uliftRingEquiv (σ.trans (g.toRingEquiv.trans σ.symm)) =
      (uliftRingEquiv σ).trans
        ((galULiftEquiv K₁ K₁' g).toRingEquiv.trans (uliftRingEquiv σ).symm) := by
  ext x
  rfl

/-- Membership in the lifted embedded-base-field range is detected after lowering. -/
private theorem mem_lifted_algebraMap_range_iff {K : Type u} {K' : Type v} [Field K]
    [Field K'] [Algebra K K'] (x : ULift.{l} K') :
    letI : Algebra (ULift.{l} K) (ULift.{l} K') := uliftAlgebra
    x ∈ (algebraMap (ULift.{l} K) (ULift.{l} K')).range ↔
      x.down ∈ (algebraMap K K').range := by
  letI : Algebra (ULift.{l} K) (ULift.{l} K') := uliftAlgebra
  constructor
  · intro hx
    obtain ⟨a, ha⟩ := hx
    exact ⟨a.down, congrArg ULift.down ha⟩
  · intro hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨ULift.up a, ?_⟩
    apply ULift.down_injective
    exact ha

/-- Mapping a lifted embedded-base-field range by a lifted ring equivalence lowers to the
corresponding mapped range downstairs. -/
private theorem mem_uliftRingEquiv_mapped_range_iff {K₂ : Type u} {K₁ : Type v}
    {K₂' : Type w} {K₁' : Type z} [Field K₂] [Field K₁] [Field K₂'] [Field K₁']
    [Algebra K₂ K₂'] [Algebra K₁ K₁'] (τ : K₂' ≃+* K₁') (y : ULift.{l} K₁') :
    letI : Algebra (ULift.{l} K₂) (ULift.{l} K₂') := uliftAlgebra
    letI : Algebra (ULift.{l} K₁) (ULift.{l} K₁') := uliftAlgebra
    y ∈ (algebraMap (ULift.{l} K₂) (ULift.{l} K₂')).range.map
        (uliftRingEquiv τ).toRingHom ↔
      y.down ∈ (algebraMap K₂ K₂').range.map τ.toRingHom := by
  letI : Algebra (ULift.{l} K₂) (ULift.{l} K₂') := uliftAlgebra
  letI : Algebra (ULift.{l} K₁) (ULift.{l} K₁') := uliftAlgebra
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := hy
    have hxdown : x.down ∈ (algebraMap K₂ K₂').range :=
      (mem_lifted_algebraMap_range_iff (K := K₂) (K' := K₂') x).1 hx
    exact ⟨x.down, hxdown, congrArg ULift.down hxy⟩
  · intro hy
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨ULift.up x, ?_, ?_⟩
    · exact (mem_lifted_algebraMap_range_iff (K := K₂) (K' := K₂') _).2 hx
    · apply ULift.down_injective
      exact hxy

/-- Lifting a closure isomorphism preserving base ranges preserves the lifted base ranges. -/
theorem uliftRingEquiv_maps_base_range {K₁ : Type u} {K₂ : Type v}
    {K₁' : Type w} {K₂' : Type z} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] (τ : K₂' ≃+* K₁')
    (hτbase : (algebraMap K₂ K₂').range.map τ.toRingHom = (algebraMap K₁ K₁').range) :
    letI : Algebra (ULift.{l} K₁) (ULift.{l} K₁') := uliftAlgebra
    letI : Algebra (ULift.{l} K₂) (ULift.{l} K₂') := uliftAlgebra
    (algebraMap (ULift.{l} K₂) (ULift.{l} K₂')).range.map
        (uliftRingEquiv τ).toRingHom =
      (algebraMap (ULift.{l} K₁) (ULift.{l} K₁')).range := by
  letI : Algebra (ULift.{l} K₁) (ULift.{l} K₁') := uliftAlgebra
  letI : Algebra (ULift.{l} K₂) (ULift.{l} K₂') := uliftAlgebra
  ext y
  rw [mem_uliftRingEquiv_mapped_range_iff (K₂ := K₂) (K₁ := K₁) (K₂' := K₂')
      (K₁' := K₁') (τ := τ) (y := y),
    mem_lifted_algebraMap_range_iff (K := K₁) (K' := K₁')]
  rw [hτbase]

/-- Lowering a lifted closure isomorphism preserving lifted base ranges preserves base ranges. -/
theorem lowerULiftRingEquiv_maps_base_range {K₁ : Type u} {K₂ : Type v}
    {K₁' : Type w} {K₂' : Type z} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] (sigmaU : ULift.{l} K₂' ≃+* ULift.{l} K₁') :
    letI : Algebra (ULift.{l} K₁) (ULift.{l} K₁') := uliftAlgebra
    letI : Algebra (ULift.{l} K₂) (ULift.{l} K₂') := uliftAlgebra
    (algebraMap (ULift.{l} K₂) (ULift.{l} K₂')).range.map sigmaU.toRingHom =
      (algebraMap (ULift.{l} K₁) (ULift.{l} K₁')).range →
    (algebraMap K₂ K₂').range.map (lowerULiftRingEquiv sigmaU).toRingHom =
      (algebraMap K₁ K₁').range := by
  letI : Algebra (ULift.{l} K₁) (ULift.{l} K₁') := uliftAlgebra
  letI : Algebra (ULift.{l} K₂) (ULift.{l} K₂') := uliftAlgebra
  intro hσbase
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := hy
    have hyu : ULift.up y ∈
        (algebraMap (ULift.{l} K₁) (ULift.{l} K₁')).range := by
      rw [← hσbase]
      refine ⟨ULift.up x, ?_, ?_⟩
      · exact (mem_lifted_algebraMap_range_iff (K := K₂) (K' := K₂') _).2 hx
      · apply ULift.down_injective
        exact hxy
    exact (mem_lifted_algebraMap_range_iff (K := K₁) (K' := K₁') (ULift.up y)).1 hyu
  · intro hy
    have hyu : ULift.up y ∈
        (algebraMap (ULift.{l} K₁) (ULift.{l} K₁')).range :=
      (mem_lifted_algebraMap_range_iff (K := K₁) (K' := K₁') (ULift.up y)).2 hy
    rw [← hσbase] at hyu
    obtain ⟨xu, hxubase, hxuy⟩ := hyu
    have hxdown : xu.down ∈ (algebraMap K₂ K₂').range :=
      (mem_lifted_algebraMap_range_iff (K := K₂) (K' := K₂') xu).1 hxubase
    refine ⟨xu.down, hxdown, ?_⟩
    change (sigmaU (ULift.up xu.down)).down = y
    rw [show ULift.up xu.down = xu by cases xu; rfl]
    exact congrArg ULift.down hxuy

@[simp]
theorem lowerULiftRingEquiv_galULiftEquiv_toRingEquiv {K : Type u} {K' : Type v}
    [Field K] [Field K'] [Algebra K K'] (g : Gal(K'/K)) :
    letI : Algebra (ULift.{l} K) (ULift.{l} K') := uliftAlgebra
    lowerULiftRingEquiv (galULiftEquiv K K' g).toRingEquiv = g.toRingEquiv := by
  letI : Algebra (ULift.{l} K) (ULift.{l} K') := uliftAlgebra
  ext x
  rfl

/-- Lowering commutes with ring-equivalence conjugation. -/
theorem lowerULiftRingEquiv_conj {K₁' : Type u} {K₂' : Type v}
    [Field K₁'] [Field K₂'] (sigmaU : ULift.{l} K₂' ≃+* ULift.{l} K₁')
    (gU : ULift.{l} K₁' ≃+* ULift.{l} K₁') :
    lowerULiftRingEquiv (sigmaU.trans (gU.trans sigmaU.symm)) =
      (lowerULiftRingEquiv sigmaU).trans
        ((lowerULiftRingEquiv gU).trans (lowerULiftRingEquiv sigmaU).symm) := by
  ext x
  rfl

private theorem isHomeomorph_galULiftEquiv {K : Type u} {K' : Type v} [Field K]
    [Field K'] [Algebra K K'] :
    letI : Algebra (ULift.{l} K) (ULift.{l} K') := uliftAlgebra
    IsHomeomorph (galULiftEquiv K K' : Gal(K'/K) → Gal(ULift.{l} K'/ULift.{l} K)) := by
  letI : Algebra (ULift.{l} K) (ULift.{l} K') := uliftAlgebra
  exact (galULiftEquiv K K').toHomeomorph.isHomeomorph

private theorem isHomeomorph_galULiftEquiv_symm {K : Type u} {K' : Type v} [Field K]
    [Field K'] [Algebra K K'] :
    letI : Algebra (ULift.{l} K) (ULift.{l} K') := uliftAlgebra
    IsHomeomorph ((galULiftEquiv K K').symm : Gal(ULift.{l} K'/ULift.{l} K) → Gal(K'/K)) := by
  letI : Algebra (ULift.{l} K) (ULift.{l} K') := uliftAlgebra
  exact (galULiftEquiv K K').symm.toHomeomorph.isHomeomorph

/-- The input Galois equivalence transported to lifted Galois groups. -/
noncomputable def liftedPhi {K₁ : Type u} {K₂ : Type v} {K₁' : Type w}
    {K₂' : Type z} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) :
    letI : Algebra (ULift.{l} K₁) (ULift.{l} K₁') := uliftAlgebra
    letI : Algebra (ULift.{l} K₂) (ULift.{l} K₂') := uliftAlgebra
    Gal(ULift.{l} K₁'/ULift.{l} K₁) ≃* Gal(ULift.{l} K₂'/ULift.{l} K₂) := by
  letI : Algebra (ULift.{l} K₁) (ULift.{l} K₁') := uliftAlgebra
  letI : Algebra (ULift.{l} K₂) (ULift.{l} K₂') := uliftAlgebra
  exact (galULiftEquiv K₁ K₁').symm.toMulEquiv.trans
    (ϕ.trans (galULiftEquiv K₂ K₂').toMulEquiv)

@[simp]
theorem liftedPhi_galULiftEquiv {K₁ : Type u} {K₂ : Type v} {K₁' : Type w}
    {K₂' : Type z} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (g : Gal(K₁'/K₁)) :
    letI : Algebra (ULift.{l} K₁) (ULift.{l} K₁') := uliftAlgebra
    letI : Algebra (ULift.{l} K₂) (ULift.{l} K₂') := uliftAlgebra
    liftedPhi ϕ (galULiftEquiv K₁ K₁' g) = galULiftEquiv K₂ K₂' (ϕ g) := by
  letI : Algebra (ULift.{l} K₁) (ULift.{l} K₁') := uliftAlgebra
  letI : Algebra (ULift.{l} K₂) (ULift.{l} K₂') := uliftAlgebra
  rfl

theorem isHomeomorph_liftedPhi {K₁ : Type u} {K₂ : Type v} {K₁' : Type w}
    {K₂' : Type z} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [Algebra K₁ K₁'] [Algebra K₂ K₂'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂))
    (he : IsHomeomorph ϕ) :
    letI : Algebra (ULift.{l} K₁) (ULift.{l} K₁') := uliftAlgebra
    letI : Algebra (ULift.{l} K₂) (ULift.{l} K₂') := uliftAlgebra
    IsHomeomorph (liftedPhi ϕ : Gal(ULift.{l} K₁'/ULift.{l} K₁) →
      Gal(ULift.{l} K₂'/ULift.{l} K₂)) := by
  letI : Algebra (ULift.{l} K₁) (ULift.{l} K₁') := uliftAlgebra
  letI : Algebra (ULift.{l} K₂) (ULift.{l} K₂') := uliftAlgebra
  have hsrc : IsHomeomorph ((galULiftEquiv K₁ K₁').symm :
      Gal(ULift.{l} K₁'/ULift.{l} K₁) → Gal(K₁'/K₁)) :=
    isHomeomorph_galULiftEquiv_symm (K := K₁) (K' := K₁')
  have htgt : IsHomeomorph (galULiftEquiv K₂ K₂' :
      Gal(K₂'/K₂) → Gal(ULift.{l} K₂'/ULift.{l} K₂)) :=
    isHomeomorph_galULiftEquiv (K := K₂) (K' := K₂')
  have hcomp := htgt.comp (he.comp hsrc)
  change IsHomeomorph ((galULiftEquiv K₂ K₂') ∘ (ϕ ∘ ((galULiftEquiv K₁ K₁').symm)))
  exact hcomp
