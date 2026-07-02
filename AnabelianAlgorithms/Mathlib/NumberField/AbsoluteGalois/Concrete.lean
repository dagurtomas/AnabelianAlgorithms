/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

module

public import AnabelianAlgorithms.Mathlib.NumberField.AbsoluteGalois.Basic


/-!
# Concrete separable closures for number-field absolute Galois groups

This file contains reusable scaffolding for comparing absolute Galois groups defined using
arbitrary separable closures with the chosen algebraic closures used by
`NumberField.absGalProfiniteObj`.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped NumberField

/-- Compare an arbitrary separable closure of a number field with the chosen algebraic closure. -/
noncomputable def sepClosureEquivAlgClosure
    (K K' : Type u) [Field K] [Field K'] [NumberField K]
    [Algebra K K'] [IsSepClosure K K'] :
    K' ≃+* AlgebraicClosure K :=
  IsAlgClosure.equivOfEquiv K' (AlgebraicClosure K) (RingEquiv.refl K)

@[simp]
theorem sepClosureEquivAlgClosure_algebraMap
    (K K' : Type u) [Field K] [Field K'] [NumberField K]
    [Algebra K K'] [IsSepClosure K K'] (x : K) :
    sepClosureEquivAlgClosure K K' (algebraMap K K' x) =
      algebraMap K (AlgebraicClosure K) x := by
  simp [sepClosureEquivAlgClosure]

@[simp]
theorem sepClosureEquivAlgClosure_symm_algebraMap
    (K K' : Type u) [Field K] [Field K'] [NumberField K]
    [Algebra K K'] [IsSepClosure K K'] (x : K) :
    (sepClosureEquivAlgClosure K K').symm (algebraMap K (AlgebraicClosure K) x) =
      algebraMap K K' x := by
  simp [sepClosureEquivAlgClosure]

/--
Transport an absolute Galois group from an arbitrary separable closure to the chosen algebraic
closure of the same number field.
-/
noncomputable def galSepClosureEquivChosen
    (K K' : Type u) [Field K] [Field K'] [NumberField K]
    [Algebra K K'] [IsSepClosure K K'] :
    Gal(K'/K) ≃ₜ* Gal(AlgebraicClosure K/K) :=
  NumberField.AbsGalConj.closureContinuousMulEquivOfEquiv (RingEquiv.refl K)
    (sepClosureEquivAlgClosure K K').symm (by
      intro x
      simp)

/-- The chosen separable-closure transport is conjugation by `sepClosureEquivAlgClosure`. -/
theorem galSepClosureEquivChosen_apply
    (K K' : Type u) [Field K] [Field K'] [NumberField K]
    [Algebra K K'] [IsSepClosure K K'] (g : Gal(K'/K)) :
    galSepClosureEquivChosen K K' g =
      AlgEquiv.ofRingEquiv
        (f := (sepClosureEquivAlgClosure K K').symm.trans
          (g.toRingEquiv.trans (sepClosureEquivAlgClosure K K')))
        (by
          intro x
          have hs : (sepClosureEquivAlgClosure K K').symm
              (algebraMap K (AlgebraicClosure K) x) = algebraMap K K' x := by
            simp
          simp [hs]) := by
  rfl

@[simp]
theorem galSepClosureEquivChosen_apply_apply
    (K K' : Type u) [Field K] [Field K'] [NumberField K]
    [Algebra K K'] [IsSepClosure K K'] (g : Gal(K'/K)) (x : AlgebraicClosure K) :
    galSepClosureEquivChosen K K' g x =
      sepClosureEquivAlgClosure K K' (g ((sepClosureEquivAlgClosure K K').symm x)) := by
  rfl

/-- The profinite-group isomorphism induced by `galSepClosureEquivChosen`. -/
noncomputable def profiniteGalSepClosureIsoChosen
    (K K' : Type u) [Field K] [Field K'] [NumberField K]
    [Algebra K K'] [IsSepClosure K K'] :
    InfiniteGalois.profiniteGalGrp K K' ≅ NumberField.absGalProfiniteObj K :=
  ProfiniteGrp.ContinuousMulEquiv.toProfiniteGrpIso (galSepClosureEquivChosen K K')


theorem iso_conj_cancel {C : Type*} [Category C] {A B D E : C}
    (i : A ≅ B) (o : A ≅ D) (j : D ≅ E) :
    i ≪≫ (i.symm ≪≫ o ≪≫ j) ≪≫ j.symm = o := by
  rw [← Iso.trans_assoc i (i.symm ≪≫ o ≪≫ j) j.symm]
  rw [← Iso.trans_assoc i i.symm (o ≪≫ j)]
  simp [Iso.trans_assoc]

/-- The input abstract group isomorphism, upgraded to a continuous multiplicative equivalence. -/
noncomputable def concreteGalEquiv {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    Gal(K₁'/K₁) ≃ₜ* Gal(K₂'/K₂) :=
  ContinuousMulEquiv.mk ϕ he.continuous (ϕ.toEquiv.continuous_symm_iff.2 he.isOpenMap)

/-- The profinite-group isomorphism represented by the input concrete Galois equivalence. -/
noncomputable def profiniteGalIsoOfConcrete {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    InfiniteGalois.profiniteGalGrp K₁ K₁' ≅ InfiniteGalois.profiniteGalGrp K₂ K₂' :=
  ProfiniteGrp.ContinuousMulEquiv.toProfiniteGrpIso (concreteGalEquiv ϕ he)

/--
The chosen-closure absolute-Galois equivalence obtained from a concrete separable-closure one.
-/
noncomputable def absGalEquivOfConcrete {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    NumberField.AbsGalEquiv K₁ K₂ :=
  (galSepClosureEquivChosen K₁ K₁').symm.trans <|
    (concreteGalEquiv ϕ he).trans (galSepClosureEquivChosen K₂ K₂')

/-- The raw outer isomorphism represented by the transported concrete Galois isomorphism. -/
noncomputable def outerIsoOfConcrete {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    NumberField.absGalOuterObj K₁ ≅ NumberField.absGalOuterObj K₂ :=
  NumberField.outerIsoOfAbsGalEquiv (absGalEquivOfConcrete ϕ he)

/-- The concrete Galois equivalence induced by a closure isomorphism over a base isomorphism. -/
noncomputable def galEquivOfClosureIso {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (e : K₂ ≃+* K₁) (σ : K₂' ≃+* K₁')
    (hσ : ∀ x : K₂, σ (algebraMap K₂ K₂' x) = algebraMap K₁ K₁' (e x)) :
    Gal(K₁'/K₁) ≃ₜ* Gal(K₂'/K₂) :=
  NumberField.AbsGalConj.closureContinuousMulEquivOfEquiv e σ hσ

/-- The profinite isomorphism induced by a closure isomorphism over a base isomorphism. -/
noncomputable def profiniteGalIsoOfClosureIso {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (e : K₂ ≃+* K₁) (σ : K₂' ≃+* K₁')
    (hσ : ∀ x : K₂, σ (algebraMap K₂ K₂' x) = algebraMap K₁ K₁' (e x)) :
    InfiniteGalois.profiniteGalGrp K₁ K₁' ≅ InfiniteGalois.profiniteGalGrp K₂ K₂' :=
  ProfiniteGrp.ContinuousMulEquiv.toProfiniteGrpIso (galEquivOfClosureIso e σ hσ)

/-- The image of a base element under a closure isomorphism preserving base ranges. -/
theorem exists_base_image_of_maps_base_range {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    {σ : K₂' ≃+* K₁'}
    (hσbase : (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range)
    (x : K₂) : ∃ y : K₁, algebraMap K₁ K₁' y = σ (algebraMap K₂ K₂' x) := by
  have hx : σ (algebraMap K₂ K₂' x) ∈
      (algebraMap K₂ K₂').range.map σ.toRingHom := by
    exact ⟨algebraMap K₂ K₂' x, ⟨x, rfl⟩, rfl⟩
  rw [hσbase] at hx
  simpa using hx

/-- A base element has a preimage under a closure isomorphism preserving base ranges. -/
theorem exists_base_preimage_of_maps_base_range {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    {σ : K₂' ≃+* K₁'}
    (hσbase : (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range)
    (y : K₁) : ∃ x : K₂, σ (algebraMap K₂ K₂' x) = algebraMap K₁ K₁' y := by
  have hy : algebraMap K₁ K₁' y ∈ (algebraMap K₁ K₁').range := ⟨y, rfl⟩
  rw [← hσbase] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨x, rfl⟩ := hz
  exact ⟨x, hzy⟩

/-- The base-field isomorphism induced by a closure isomorphism preserving embedded base ranges. -/
noncomputable def baseIsoOfClosureIso {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    (σ : K₂' ≃+* K₁')
    (hσbase : (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range) :
    K₂ ≃+* K₁ where
  toFun x := Classical.choose (exists_base_image_of_maps_base_range (σ := σ) hσbase x)
  invFun y := Classical.choose (exists_base_preimage_of_maps_base_range (σ := σ) hσbase y)
  left_inv x := by
    have hto := Classical.choose_spec (exists_base_image_of_maps_base_range (σ := σ) hσbase x)
    have hinv := Classical.choose_spec
      (exists_base_preimage_of_maps_base_range (σ := σ) hσbase
        (Classical.choose (exists_base_image_of_maps_base_range (σ := σ) hσbase x)))
    apply FaithfulSMul.algebraMap_injective K₂ K₂'
    apply σ.injective
    exact hinv.trans hto
  right_inv y := by
    have hinv := Classical.choose_spec (exists_base_preimage_of_maps_base_range (σ := σ) hσbase y)
    have hto := Classical.choose_spec
      (exists_base_image_of_maps_base_range (σ := σ) hσbase
        (Classical.choose (exists_base_preimage_of_maps_base_range (σ := σ) hσbase y)))
    apply FaithfulSMul.algebraMap_injective K₁ K₁'
    exact hto.trans hinv
  map_mul' x y := by
    apply FaithfulSMul.algebraMap_injective K₁ K₁'
    have hxy := Classical.choose_spec (exists_base_image_of_maps_base_range (σ := σ) hσbase (x * y))
    have hx := Classical.choose_spec (exists_base_image_of_maps_base_range (σ := σ) hσbase x)
    have hy := Classical.choose_spec (exists_base_image_of_maps_base_range (σ := σ) hσbase y)
    calc
      algebraMap K₁ K₁' (Classical.choose
          (exists_base_image_of_maps_base_range (σ := σ) hσbase (x * y)))
          = σ (algebraMap K₂ K₂' (x * y)) := hxy
      _ = σ (algebraMap K₂ K₂' x) * σ (algebraMap K₂ K₂' y) := by simp
      _ = algebraMap K₁ K₁' (Classical.choose
              (exists_base_image_of_maps_base_range (σ := σ) hσbase x)) *
            algebraMap K₁ K₁' (Classical.choose
              (exists_base_image_of_maps_base_range (σ := σ) hσbase y)) := by
        exact (congrArg₂ (fun a b ↦ a * b) hx hy).symm
      _ = algebraMap K₁ K₁'
            (Classical.choose (exists_base_image_of_maps_base_range (σ := σ) hσbase x) *
              Classical.choose (exists_base_image_of_maps_base_range (σ := σ) hσbase y)) := by simp
  map_add' x y := by
    apply FaithfulSMul.algebraMap_injective K₁ K₁'
    have hxy := Classical.choose_spec (exists_base_image_of_maps_base_range (σ := σ) hσbase (x + y))
    have hx := Classical.choose_spec (exists_base_image_of_maps_base_range (σ := σ) hσbase x)
    have hy := Classical.choose_spec (exists_base_image_of_maps_base_range (σ := σ) hσbase y)
    calc
      algebraMap K₁ K₁' (Classical.choose
          (exists_base_image_of_maps_base_range (σ := σ) hσbase (x + y)))
          = σ (algebraMap K₂ K₂' (x + y)) := hxy
      _ = σ (algebraMap K₂ K₂' x) + σ (algebraMap K₂ K₂' y) := by simp
      _ = algebraMap K₁ K₁' (Classical.choose
              (exists_base_image_of_maps_base_range (σ := σ) hσbase x)) +
            algebraMap K₁ K₁' (Classical.choose
              (exists_base_image_of_maps_base_range (σ := σ) hσbase y)) := by
        exact (congrArg₂ (fun a b ↦ a + b) hx hy).symm
      _ = algebraMap K₁ K₁'
            (Classical.choose (exists_base_image_of_maps_base_range (σ := σ) hσbase x) +
              Classical.choose (exists_base_image_of_maps_base_range (σ := σ) hσbase y)) := by simp

@[simp]
theorem baseIsoOfClosureIso_algebraMap {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂'] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    (σ : K₂' ≃+* K₁')
    (hσbase : (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range)
    (x : K₂) :
    algebraMap K₁ K₁' (baseIsoOfClosureIso σ hσbase x) = σ (algebraMap K₂ K₂' x) :=
  Classical.choose_spec (exists_base_image_of_maps_base_range (σ := σ) hσbase x)

theorem closureIso_outerRel_base {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (e : K₂ ≃+* K₁) (σ : K₂' ≃+* K₁')
    (hσ : ∀ x : K₂, σ (algebraMap K₂ K₂' x) = algebraMap K₁ K₁' (e x)) :
    Anabelian.profiniteGrpOuterRel (NumberField.GlobalFieldIso.toProfiniteGrpIso e).hom
      ((profiniteGalSepClosureIsoChosen K₁ K₁').inv ≫
        (profiniteGalIsoOfClosureIso e σ hσ).hom ≫
          (profiniteGalSepClosureIsoChosen K₂ K₂').hom) := by
  let Fbase := NumberField.GlobalFieldIso.algClosureEquiv e
  let Fseq : AlgebraicClosure K₂ ≃+* AlgebraicClosure K₁ :=
    (sepClosureEquivAlgClosure K₂ K₂').symm.trans (σ.trans (sepClosureEquivAlgClosure K₁ K₁'))
  have hFseq : ∀ x : K₂, Fseq (algebraMap K₂ (AlgebraicClosure K₂) x) =
      algebraMap K₁ (AlgebraicClosure K₁) (e x) := by
    intro x
    dsimp [Fseq]
    simp [hσ]
  let hGal : Gal(AlgebraicClosure K₂/K₂) :=
    NumberField.AbsGalConj.comparisonAut e Fbase Fseq
      (NumberField.GlobalFieldIso.algClosureEquiv_algebraMap e) hFseq
  refine ⟨hGal, fun τ ↦ ?_⟩
  have hinner := NumberField.AbsGalConj.mapOfEquiv_eq_inner e Fbase Fseq
    (NumberField.GlobalFieldIso.algClosureEquiv_algebraMap e) hFseq τ
  change NumberField.AbsGalConj.mapOfEquiv e Fseq hFseq τ =
    hGal * NumberField.AbsGalConj.mapOfEquiv e Fbase
      (NumberField.GlobalFieldIso.algClosureEquiv_algebraMap e) τ * hGal⁻¹
  exact hinner

theorem closureIso_outerIso_base {K₁ K₂ K₁' K₂' : Type u}
    [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂']
    [IsSepClosure K₁ K₁'] [IsSepClosure K₂ K₂']
    (e : K₂ ≃+* K₁) (σ : K₂' ≃+* K₁')
    (hσ : ∀ x : K₂, σ (algebraMap K₂ K₂' x) = algebraMap K₁ K₁' (e x)) :
    NumberField.GlobalFieldIso.toOuterIso e =
      NumberField.outerIsoOfAbsGalEquiv
        ((galSepClosureEquivChosen K₁ K₁').symm.trans
          ((galEquivOfClosureIso e σ hσ).trans (galSepClosureEquivChosen K₂ K₂'))) := by
  apply Iso.ext
  change (CategoryTheory.Quotient.functor Anabelian.profiniteGrpOuterRel).map
      (NumberField.GlobalFieldIso.toProfiniteGrpIso e).hom =
    (CategoryTheory.Quotient.functor Anabelian.profiniteGrpOuterRel).map
      ((profiniteGalSepClosureIsoChosen K₁ K₁').inv ≫
        (profiniteGalIsoOfClosureIso e σ hσ).hom ≫
          (profiniteGalSepClosureIsoChosen K₂ K₂').hom)
  exact CategoryTheory.Quotient.sound Anabelian.profiniteGrpOuterRel
    (closureIso_outerRel_base e σ hσ)
