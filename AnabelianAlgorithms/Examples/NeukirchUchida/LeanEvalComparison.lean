/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

module

import all AnabelianAlgorithms.Linter.NonstandardAxioms
public import AnabelianAlgorithms.Examples.NeukirchUchida.Main
public import AnabelianAlgorithms.Mathlib.FieldTheory.Galois.ULift
public import AnabelianAlgorithms.Mathlib.NumberField.AbsoluteGalois.CenterTrivial
public import AnabelianAlgorithms.Mathlib.NumberField.AbsoluteGalois.Concrete
public import AnabelianAlgorithms.Mathlib.NumberField.AbsoluteGalois.NumberFieldCat


/-!
# Lean-evaluation wrapper for the Neukirch-Uchida statement

This file exposes the universe-polymorphic form of the Neukirch-Uchida reconstruction statement.
The concrete absolute-Galois reconstruction helpers live in
`AnabelianAlgorithms.Mathlib.NumberField.AbsoluteGalois.NeukirchUchidaConcrete`.
-/

@[expose] public section

universe u v w z l

open CategoryTheory
open Anabelian
open Examples.NeukirchUchidaStandalone
open scoped NumberField

/-- The base-field isomorphism recovered by applying standalone NU to the concrete outer class. -/
noncomputable def baseIsoOfConcrete {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    K₂ ≃+* K₁ :=
  let X : Core (NumberFieldCat.{u}ᵒᵖ) :=
    ⟨Opposite.op (NumberFieldCat.of K₂)⟩
  let Y : Core (NumberFieldCat.{u}ᵒᵖ) :=
    ⟨Opposite.op (NumberFieldCat.of K₁)⟩
  let αIso :
      (absGalNumberField.obj Y).of ≅
        (absGalNumberField.obj X).of :=
    (NumberFieldCat.outerIsoRawToOf K₁).symm ≪≫
      outerIsoOfConcrete ϕ he ≪≫
        NumberFieldCat.outerIsoRawToOf K₂
  let α :
      absGalNumberField.obj Y ⟶
        absGalNumberField.obj X :=
    ⟨αIso⟩
  let f : Y ⟶ X :=
    (neukirchUchidaHomEquiv X Y).symm α
  let fRing : @RingEquiv K₂ K₁
      (letI : Field K₂ :=
        NumberFieldCat.field
          (NumberFieldCat.of K₂); inferInstance)
      (letI : Field K₁ :=
        NumberFieldCat.field
          (NumberFieldCat.of K₁); inferInstance)
      (letI : Field K₂ :=
        NumberFieldCat.field
          (NumberFieldCat.of K₂); inferInstance)
      (letI : Field K₁ :=
        NumberFieldCat.field
          (NumberFieldCat.of K₁); inferInstance) :=
    numberFieldIsoToRingEquiv f.iso.unop
  (NumberFieldCat.ringEquivOfToRaw K₂).symm.trans <|
    fRing.trans (NumberFieldCat.ringEquivOfToRaw K₁)

-- The recovered raw base isomorphism induces exactly the raw outer isomorphism represented by `ϕ`.
theorem baseIsoOfConcrete_outerIso {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    NumberField.GlobalFieldIso.toOuterIso (baseIsoOfConcrete ϕ he) = outerIsoOfConcrete ϕ he := by
  let X : Core (NumberFieldCat.{u}ᵒᵖ) := ⟨Opposite.op (NumberFieldCat.of K₂)⟩
  let Y : Core (NumberFieldCat.{u}ᵒᵖ) := ⟨Opposite.op (NumberFieldCat.of K₁)⟩
  let αIso : (absGalNumberField.obj Y).of ≅ (absGalNumberField.obj X).of :=
    (NumberFieldCat.outerIsoRawToOf K₁).symm ≪≫ outerIsoOfConcrete ϕ he ≪≫
      NumberFieldCat.outerIsoRawToOf K₂
  let α : absGalNumberField.obj Y ⟶ absGalNumberField.obj X := ⟨αIso⟩
  let f : Y ⟶ X := (neukirchUchidaHomEquiv X Y).symm α
  have hf_apply : neukirchUchidaHomEquiv X Y f = absGalNumberField.map f :=
    neukirchUchidaHomEquiv_apply f
  have hf_α : neukirchUchidaHomEquiv X Y f = α := by
    dsimp [f]
    exact Equiv.apply_symm_apply (neukirchUchidaHomEquiv X Y) α
  have hmap : absGalNumberField.map f = α := by
    rw [← hf_apply, hf_α]
  let fRing : @RingEquiv K₂ K₁
      (letI : Field K₂ := NumberFieldCat.field (NumberFieldCat.of K₂); inferInstance)
      (letI : Field K₁ := NumberFieldCat.field (NumberFieldCat.of K₁); inferInstance)
      (letI : Field K₂ := NumberFieldCat.field (NumberFieldCat.of K₂); inferInstance)
      (letI : Field K₁ := NumberFieldCat.field (NumberFieldCat.of K₁); inferInstance) :=
    numberFieldIsoToRingEquiv f.iso.unop
  let fOuter : @NumberField.absGalOuterObj K₁
        (NumberFieldCat.field (NumberFieldCat.of K₁))
        (NumberFieldCat.numberField (NumberFieldCat.of K₁)) ≅
      @NumberField.absGalOuterObj K₂
        (NumberFieldCat.field (NumberFieldCat.of K₂))
        (NumberFieldCat.numberField (NumberFieldCat.of K₂)) :=
    @NumberField.GlobalFieldIso.toOuterIso K₁ K₂
      (NumberFieldCat.field (NumberFieldCat.of K₁))
      (NumberFieldCat.numberField (NumberFieldCat.of K₁))
      (NumberFieldCat.field (NumberFieldCat.of K₂))
      (NumberFieldCat.numberField (NumberFieldCat.of K₂))
      fRing
  have hcat : fOuter = αIso := by
    change absGalNumberFieldOuterIso f.iso.unop = αIso
    exact congrArg CategoryTheory.CoreHom.iso hmap
  have hraw : NumberField.GlobalFieldIso.toOuterIso (baseIsoOfConcrete ϕ he) =
      NumberFieldCat.outerIsoRawToOf K₁ ≪≫ fOuter ≪≫
        (NumberFieldCat.outerIsoRawToOf K₂).symm := by
    let e₂ := NumberFieldCat.ringEquivOfToRaw K₂
    let e₁ := NumberFieldCat.ringEquivOfToRaw K₁
    have htrans₁ := @NumberField.GlobalFieldIso.toOuterIso_trans K₂ K₂ K₁
      (inferInstance) (inferInstance)
      (NumberFieldCat.field (NumberFieldCat.of K₂))
      (NumberFieldCat.numberField (NumberFieldCat.of K₂))
      (inferInstance) (inferInstance)
      (e₂.symm) (fRing.trans e₁)
    have htrans₂ := @NumberField.GlobalFieldIso.toOuterIso_trans K₂ K₁ K₁
      (NumberFieldCat.field (NumberFieldCat.of K₂))
      (NumberFieldCat.numberField (NumberFieldCat.of K₂))
      (NumberFieldCat.field (NumberFieldCat.of K₁))
      (NumberFieldCat.numberField (NumberFieldCat.of K₁))
      (inferInstance) (inferInstance)
      fRing e₁
    simp only [baseIsoOfConcrete]
    dsimp [X, Y, αIso, α, f, e₂, fRing, fOuter, e₁]
    change NumberField.GlobalFieldIso.toOuterIso (e₂.symm.trans (fRing.trans e₁)) =
      NumberFieldCat.outerIsoRawToOf K₁ ≪≫ fOuter ≪≫
        (NumberFieldCat.outerIsoRawToOf K₂).symm
    rw! [htrans₁, htrans₂]
    rw [NumberFieldCat.toOuterIso_ringEquivOfToRaw_symm]
    rfl
  rw [hraw, hcat]
  exact iso_conj_cancel (NumberFieldCat.outerIsoRawToOf K₁) (outerIsoOfConcrete ϕ he)
    (NumberFieldCat.outerIsoRawToOf K₂)

/-- Extend the recovered base-field isomorphism to the given separable closures. -/
noncomputable def closureIsoOfBaseIso {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    K₂' ≃+* K₁' :=
  IsAlgClosure.equivOfEquiv K₂' K₁' (baseIsoOfConcrete ϕ he)

@[simp]
theorem closureIsoOfBaseIso_algebraMap {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) (x : K₂) :
    closureIsoOfBaseIso ϕ he (algebraMap K₂ K₂' x) =
      algebraMap K₁ K₁' (baseIsoOfConcrete ϕ he x) := by
  simp [closureIsoOfBaseIso]

/-- The closure isomorphism attached to `baseIsoOfConcrete` sends the embedded base field of
`K₂'` onto the embedded base field of `K₁'`. -/
theorem closureIsoOfBaseIso_maps_base_range {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    (algebraMap K₂ K₂').range.map (closureIsoOfBaseIso ϕ he).toRingHom =
      (algebraMap K₁ K₁').range := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨x, rfl⟩ := hz
    exact ⟨baseIsoOfConcrete ϕ he x, by simp⟩
  · intro hy
    obtain ⟨x, rfl⟩ := hy
    refine ⟨algebraMap K₂ K₂' ((baseIsoOfConcrete ϕ he).symm x),
      ⟨(baseIsoOfConcrete ϕ he).symm x, rfl⟩, ?_⟩
    simp


-- Oriented as `profiniteGrpOuterRel (map induced by ϕ) (map induced by closureIsoOfBaseIso)`,
-- matching the final exact formula before the target-inner adjustment of NUL6.
theorem closureIsoOfBaseIso_outerRel_concrete {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    Anabelian.profiniteGrpOuterRel (profiniteGalIsoOfConcrete ϕ he).hom
      (profiniteGalIsoOfClosureIso (baseIsoOfConcrete ϕ he) (closureIsoOfBaseIso ϕ he)
        (closureIsoOfBaseIso_algebraMap ϕ he)).hom := by
  let Q := CategoryTheory.Quotient.functor Anabelian.profiniteGrpOuterRel
  let i₁ := profiniteGalSepClosureIsoChosen K₁ K₁'
  let i₂ := profiniteGalSepClosureIsoChosen K₂ K₂'
  let e := baseIsoOfConcrete ϕ he
  let σ := closureIsoOfBaseIso ϕ he
  let hσ := closureIsoOfBaseIso_algebraMap ϕ he
  let fϕ := (profiniteGalIsoOfConcrete ϕ he).hom
  let fσ := (profiniteGalIsoOfClosureIso e σ hσ).hom
  let fbase := (NumberField.GlobalFieldIso.toProfiniteGrpIso e).hom
  have hφ_base : Q.map fbase = Q.map (i₁.inv ≫ fϕ ≫ i₂.hom) := by
    have h := congrArg Iso.hom (baseIsoOfConcrete_outerIso ϕ he)
    change Q.map fbase = Q.map (i₁.inv ≫ fϕ ≫ i₂.hom) at h
    exact h
  have hσ_base : Anabelian.profiniteGrpOuterRel fbase (i₁.inv ≫ fσ ≫ i₂.hom) := by
    exact closureIso_outerRel_base e σ hσ
  have hσ_base_eq : Q.map fbase = Q.map (i₁.inv ≫ fσ ≫ i₂.hom) :=
    CategoryTheory.Quotient.sound Anabelian.profiniteGrpOuterRel hσ_base
  have hconj : Q.map (i₁.inv ≫ fϕ ≫ i₂.hom) = Q.map (i₁.inv ≫ fσ ≫ i₂.hom) := by
    rw [← hφ_base, hσ_base_eq]
  have hfg : Q.map fϕ = Q.map fσ :=
    Anabelian.quotient_map_cancel_conjugated i₁ i₂ fϕ fσ hconj
  exact (CategoryTheory.Quotient.functor_map_eq_iff Anabelian.profiniteGrpOuterRel fϕ fσ).1 hfg

/-- The target-inner conjugating element supplied by the NUL5 outer-relation theorem. -/
noncomputable def closureIsoOuterConj {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    Gal(K₂'/K₂) :=
  Classical.choose (closureIsoOfBaseIso_outerRel_concrete ϕ he)

/-- The extracted target-inner conjugating element, translated back to concrete Galois groups. -/
theorem closureIsoOuterConj_spec {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    ∀ g : Gal(K₁'/K₁),
      galEquivOfClosureIso (baseIsoOfConcrete ϕ he) (closureIsoOfBaseIso ϕ he)
        (closureIsoOfBaseIso_algebraMap ϕ he) g =
        closureIsoOuterConj ϕ he * ϕ g * (closureIsoOuterConj ϕ he)⁻¹ := by
  intro g
  have hs := Classical.choose_spec (closureIsoOfBaseIso_outerRel_concrete ϕ he) g
  change galEquivOfClosureIso (baseIsoOfConcrete ϕ he) (closureIsoOfBaseIso ϕ he)
        (closureIsoOfBaseIso_algebraMap ϕ he) g =
        closureIsoOuterConj ϕ he * ϕ g * (closureIsoOuterConj ϕ he)⁻¹ at hs
  exact hs

/-- Adjust `closureIsoOfBaseIso` by the target Galois automorphism from the outer relation. -/
noncomputable def adjustedClosureIso {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    K₂' ≃+* K₁' :=
  (closureIsoOuterConj ϕ he).toRingEquiv.trans (closureIsoOfBaseIso ϕ he)

/-- The adjusted closure isomorphism still maps the embedded base field onto the embedded base. -/
theorem adjustedClosureIso_maps_base_range {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    (algebraMap K₂ K₂').range.map (adjustedClosureIso ϕ he).toRingHom =
      (algebraMap K₁ K₁').range := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := hy
    obtain ⟨x, rfl⟩ := hz
    exact ⟨baseIsoOfConcrete ϕ he x, by simp [adjustedClosureIso, closureIsoOuterConj]⟩
  · intro hy
    obtain ⟨x, rfl⟩ := hy
    refine ⟨algebraMap K₂ K₂' ((baseIsoOfConcrete ϕ he).symm x),
      ⟨(baseIsoOfConcrete ϕ he).symm x, rfl⟩, ?_⟩
    simp [adjustedClosureIso, closureIsoOuterConj]

/-- After the inner adjustment, the closure isomorphism induces exactly the input `ϕ`. -/
theorem adjustedClosureIso_induces_phi {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    ∀ g : Gal(K₁'/K₁),
      ϕ g =
        (adjustedClosureIso ϕ he).trans
          (g.toRingEquiv.trans (adjustedClosureIso ϕ he).symm) := by
  intro g
  let h : Gal(K₂'/K₂) := closureIsoOuterConj ϕ he
  let σ : K₂' ≃+* K₁' := closureIsoOfBaseIso ϕ he
  let e : K₂ ≃+* K₁ := baseIsoOfConcrete ϕ he
  let hσ : ∀ x : K₂, σ (algebraMap K₂ K₂' x) = algebraMap K₁ K₁' (e x) :=
    closureIsoOfBaseIso_algebraMap ϕ he
  have hspec : galEquivOfClosureIso e σ hσ g = h * ϕ g * h⁻¹ := by
    exact closureIsoOuterConj_spec ϕ he g
  have hcalc : h⁻¹ * galEquivOfClosureIso e σ hσ g * h = ϕ g := by
    rw [hspec]
    group
  symm
  calc
    ((adjustedClosureIso ϕ he).trans
        (g.toRingEquiv.trans (adjustedClosureIso ϕ he).symm)) =
        (h⁻¹ * galEquivOfClosureIso e σ hσ g * h).toRingEquiv := by
      ext x
      simp [adjustedClosureIso, h, σ, e, galEquivOfClosureIso,
        NumberField.AbsGalConj.closureContinuousMulEquivOfEquiv,
        NumberField.AbsGalConj.closureMulEquivOfEquiv,
        NumberField.AbsGalConj.closureMapOfEquiv, AlgEquiv.mul_apply]
    _ = (ϕ g).toRingEquiv := by rw [hcalc]


theorem baseIsoOfConcrete_eq_of_outerIso {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    (e : K₂ ≃+* K₁)
    (heOuter : NumberField.GlobalFieldIso.toOuterIso e = outerIsoOfConcrete ϕ he) :
    e = baseIsoOfConcrete ϕ he := by
  let X : Core (NumberFieldCat.{u}ᵒᵖ) := ⟨Opposite.op (NumberFieldCat.of K₂)⟩
  let Y : Core (NumberFieldCat.{u}ᵒᵖ) := ⟨Opposite.op (NumberFieldCat.of K₁)⟩
  let αIso : (absGalNumberField.obj Y).of ≅ (absGalNumberField.obj X).of :=
    (NumberFieldCat.outerIsoRawToOf K₁).symm ≪≫ outerIsoOfConcrete ϕ he ≪≫
      NumberFieldCat.outerIsoRawToOf K₂
  let α : absGalNumberField.obj Y ⟶ absGalNumberField.obj X := ⟨αIso⟩
  let f : Y ⟶ X := (neukirchUchidaHomEquiv X Y).symm α
  let e₂ := NumberFieldCat.ringEquivOfToRaw K₂
  let e₁ := NumberFieldCat.ringEquivOfToRaw K₁
  let fRing : @RingEquiv K₂ K₁
      (letI : Field K₂ := NumberFieldCat.field (NumberFieldCat.of K₂); inferInstance)
      (letI : Field K₁ := NumberFieldCat.field (NumberFieldCat.of K₁); inferInstance)
      (letI : Field K₂ := NumberFieldCat.field (NumberFieldCat.of K₂); inferInstance)
      (letI : Field K₁ := NumberFieldCat.field (NumberFieldCat.of K₁); inferInstance) :=
    e₂.trans (e.trans e₁.symm)
  let fe : Y ⟶ X :=
    ⟨(@NumberFieldCat.isoOfRingEquiv K₂ K₁
      (NumberFieldCat.field (NumberFieldCat.of K₂))
      (NumberFieldCat.field (NumberFieldCat.of K₁))
      (NumberFieldCat.numberField (NumberFieldCat.of K₂))
      (NumberFieldCat.numberField (NumberFieldCat.of K₁)) fRing).op⟩
  have hf_α : neukirchUchidaHomEquiv X Y f = α := by
    dsimp [f]
    exact Equiv.apply_symm_apply (neukirchUchidaHomEquiv X Y) α
  have hfe_α : neukirchUchidaHomEquiv X Y fe = α := by
    rw [neukirchUchidaHomEquiv_apply]
    apply Core.hom_ext
    dsimp [absGalNumberField, fe, α, αIso, fRing]
    change (@NumberField.GlobalFieldIso.toOuterIso K₁ K₂
        (NumberFieldCat.field (NumberFieldCat.of K₁))
        (NumberFieldCat.numberField (NumberFieldCat.of K₁))
        (NumberFieldCat.field (NumberFieldCat.of K₂))
        (NumberFieldCat.numberField (NumberFieldCat.of K₂)) fRing).hom =
      ((NumberFieldCat.outerIsoRawToOf K₁).symm ≪≫ outerIsoOfConcrete ϕ he ≪≫
        NumberFieldCat.outerIsoRawToOf K₂).hom
    have hraw : NumberField.GlobalFieldIso.toOuterIso (e₂.symm.trans (fRing.trans e₁)) =
        NumberFieldCat.outerIsoRawToOf K₁ ≪≫
          @NumberField.GlobalFieldIso.toOuterIso K₁ K₂
            (NumberFieldCat.field (NumberFieldCat.of K₁))
            (NumberFieldCat.numberField (NumberFieldCat.of K₁))
            (NumberFieldCat.field (NumberFieldCat.of K₂))
            (NumberFieldCat.numberField (NumberFieldCat.of K₂)) fRing ≪≫
          (NumberFieldCat.outerIsoRawToOf K₂).symm := by
      have htrans₁ := @NumberField.GlobalFieldIso.toOuterIso_trans K₂ K₂ K₁
        (inferInstance) (inferInstance)
        (NumberFieldCat.field (NumberFieldCat.of K₂))
        (NumberFieldCat.numberField (NumberFieldCat.of K₂))
        (inferInstance) (inferInstance)
        (e₂.symm) (fRing.trans e₁)
      have htrans₂ := @NumberField.GlobalFieldIso.toOuterIso_trans K₂ K₁ K₁
        (NumberFieldCat.field (NumberFieldCat.of K₂))
        (NumberFieldCat.numberField (NumberFieldCat.of K₂))
        (NumberFieldCat.field (NumberFieldCat.of K₁))
        (NumberFieldCat.numberField (NumberFieldCat.of K₁))
        (inferInstance) (inferInstance)
        fRing e₁
      rw! [htrans₁, htrans₂]
      rw [NumberFieldCat.toOuterIso_ringEquivOfToRaw_symm]
      rfl
    have he_raw : e₂.symm.trans (fRing.trans e₁) = e := by
      ext x
      rfl
    have htarget : @NumberField.GlobalFieldIso.toOuterIso K₁ K₂
        (NumberFieldCat.field (NumberFieldCat.of K₁))
        (NumberFieldCat.numberField (NumberFieldCat.of K₁))
        (NumberFieldCat.field (NumberFieldCat.of K₂))
        (NumberFieldCat.numberField (NumberFieldCat.of K₂)) fRing =
        (NumberFieldCat.outerIsoRawToOf K₁).symm ≪≫ outerIsoOfConcrete ϕ he ≪≫
          NumberFieldCat.outerIsoRawToOf K₂ := by
      have h := hraw
      rw [he_raw, heOuter] at h
      calc
        @NumberField.GlobalFieldIso.toOuterIso K₁ K₂
            (NumberFieldCat.field (NumberFieldCat.of K₁))
            (NumberFieldCat.numberField (NumberFieldCat.of K₁))
            (NumberFieldCat.field (NumberFieldCat.of K₂))
            (NumberFieldCat.numberField (NumberFieldCat.of K₂)) fRing =
            (NumberFieldCat.outerIsoRawToOf K₁).symm ≪≫
              (NumberFieldCat.outerIsoRawToOf K₁ ≪≫
                @NumberField.GlobalFieldIso.toOuterIso K₁ K₂
                  (NumberFieldCat.field (NumberFieldCat.of K₁))
                  (NumberFieldCat.numberField (NumberFieldCat.of K₁))
                  (NumberFieldCat.field (NumberFieldCat.of K₂))
                  (NumberFieldCat.numberField (NumberFieldCat.of K₂)) fRing ≪≫
                  (NumberFieldCat.outerIsoRawToOf K₂).symm) ≪≫
                NumberFieldCat.outerIsoRawToOf K₂ := by simp [Iso.trans_assoc]
        _ = (NumberFieldCat.outerIsoRawToOf K₁).symm ≪≫ outerIsoOfConcrete ϕ he ≪≫
              NumberFieldCat.outerIsoRawToOf K₂ := by rw [← h]
    rw [htarget]
  have hfeq : fe = f := by
    apply (neukirchUchidaHomEquiv X Y).injective
    rw [hfe_α, hf_α]
  have hraw_f : baseIsoOfConcrete ϕ he = e₂.symm.trans
      ((numberFieldIsoToRingEquiv f.iso.unop).trans e₁) := by
    dsimp [baseIsoOfConcrete, X, Y, αIso, α, f, e₂, e₁]
  rw [hraw_f]
  have hfring : numberFieldIsoToRingEquiv f.iso.unop = fRing := by
    rw [← hfeq]
    change numberFieldIsoToRingEquiv
        (@NumberFieldCat.isoOfRingEquiv K₂ K₁
          (NumberFieldCat.field (NumberFieldCat.of K₂))
          (NumberFieldCat.field (NumberFieldCat.of K₁))
          (NumberFieldCat.numberField (NumberFieldCat.of K₂))
          (NumberFieldCat.numberField (NumberFieldCat.of K₁)) fRing) = fRing
    rfl
  rw [hfring]
  ext x
  rfl

/-- Any exact closure representative of `ϕ` induces the same base map as `baseIsoOfConcrete`. -/
theorem baseMapOfInduces_eq_baseIsoOfConcrete {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    {σ : K₂' ≃+* K₁'}
    (hσbase : (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range)
    (hσ : ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)) :
    ∀ x : K₂, algebraMap K₁ K₁' (baseIsoOfConcrete ϕ he x) = σ (algebraMap K₂ K₂' x) := by
  let e := baseIsoOfClosureIso σ hσbase
  have hσe : ∀ x : K₂, σ (algebraMap K₂ K₂' x) = algebraMap K₁ K₁' (e x) := by
    intro x
    exact (baseIsoOfClosureIso_algebraMap σ hσbase x).symm
  have hmid : galEquivOfClosureIso e σ hσe = concreteGalEquiv ϕ he := by
    ext g x
    change (σ.trans (g.toRingEquiv.trans σ.symm)) x = (ϕ g) x
    exact congrArg (fun f : K₂' ≃+* K₂' ↦ f x) (hσ g).symm
  have hgal : (galSepClosureEquivChosen K₁ K₁').symm.trans
        ((galEquivOfClosureIso e σ hσe).trans (galSepClosureEquivChosen K₂ K₂')) =
      absGalEquivOfConcrete ϕ he := by
    rw [hmid]
    rfl
  have hOuter : NumberField.GlobalFieldIso.toOuterIso e = outerIsoOfConcrete ϕ he := by
    rw [closureIso_outerIso_base e σ hσe, hgal]
    rfl
  have heq : e = baseIsoOfConcrete ϕ he :=
    baseIsoOfConcrete_eq_of_outerIso ϕ he e hOuter
  intro x
  rw [← heq]
  exact baseIsoOfClosureIso_algebraMap σ hσbase x

/-- Two exact closure representatives of the same `ϕ` are equal. -/
theorem closureIso_unique_of_induces_phi {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ)
    {σ τ : K₂' ≃+* K₁'}
    (hσbase : (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range)
    (hτbase : (algebraMap K₂ K₂').range.map τ.toRingHom = (algebraMap K₁ K₁').range)
    (hσ : ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm))
    (hτ : ∀ g : Gal(K₁'/K₁), ϕ g = τ.trans (g.toRingEquiv.trans τ.symm)) :
    σ = τ := by
  have hσpoint := baseMapOfInduces_eq_baseIsoOfConcrete ϕ he hσbase hσ
  have hτpoint := baseMapOfInduces_eq_baseIsoOfConcrete ϕ he hτbase hτ
  let δ : K₁' ≃+* K₁' := σ.symm.trans τ
  have hδfix : ∀ y : K₁, δ (algebraMap K₁ K₁' y) = algebraMap K₁ K₁' y := by
    intro y
    let x : K₂ := (baseIsoOfConcrete ϕ he).symm y
    have hσx : algebraMap K₁ K₁' y = σ (algebraMap K₂ K₂' x) := by
      simpa [x] using hσpoint x
    have hτx : algebraMap K₁ K₁' y = τ (algebraMap K₂ K₂' x) := by
      simpa [x] using hτpoint x
    dsimp [δ]
    calc
      τ (σ.symm (algebraMap K₁ K₁' y)) = τ (algebraMap K₂ K₂' x) := by
        congr 1
        apply σ.injective
        rw [RingEquiv.apply_symm_apply]
        exact hσx
      _ = algebraMap K₁ K₁' y := hτx.symm
  let δGal : Gal(K₁'/K₁) := AlgEquiv.ofRingEquiv (f := δ) hδfix
  have hδcentral : δGal ∈ Subgroup.center Gal(K₁'/K₁) := by
    rw [Subgroup.mem_center_iff]
    intro g
    ext x
    have hconj : σ.trans (g.toRingEquiv.trans σ.symm) =
        τ.trans (g.toRingEquiv.trans τ.symm) := by
      exact (hσ g).symm.trans (hτ g)
    have hpoint := congrArg (fun f : K₂' ≃+* K₂' ↦ f (σ.symm x)) hconj
    dsimp at hpoint
    apply_fun τ at hpoint
    simpa [δGal, δ, AlgEquiv.mul_apply] using hpoint.symm
  have hδone : δGal = 1 := by
    have hδbot : δGal ∈ (⊥ : Subgroup Gal(K₁'/K₁)) := by
      rw [← numberField_absGal_center_trivial (K := K₁) (K' := K₁')]
      exact hδcentral
    simpa using hδbot
  ext x
  have happ := congrArg (fun f : Gal(K₁'/K₁) ↦ f (σ x)) hδone
  dsimp [δGal, δ] at happ
  simpa using happ.symm

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
