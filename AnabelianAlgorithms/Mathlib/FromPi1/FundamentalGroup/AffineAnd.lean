/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/

import AnabelianAlgorithms.Linter.NonstandardAxioms
import Mathlib.Algebra.Category.Ring.Under.Property
import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
import AnabelianAlgorithms.Mathlib.FromPi1.FundamentalGroup.AffineColimits


/-
This file was copied and adapted from Christian Merten's `pi1` project
(<https://github.com/chrisflav/pi1>), commit `5c5c0171efc863ce9990171bdf46d7cb5fd582fb`.
-/
/-!
# Limit properties of `P.Over ⊤ X` for `P = affineAnd`

This vendored file records the affine-gluing statements from upstream `pi1` used to construct
finite colimits of finite-étale covers and prove that pullback preserves them.  The `affineAnd`
finite-colimit argument is ported here; the remaining gluing theorem for the category of affine
morphisms is isolated in `AnabelianAlgorithms.Mathlib.FromPi1.FundamentalGroup.AffineColimits`.
-/

set_option linter.nonstandardAxioms false

noncomputable section

universe u

open CategoryTheory Limits
open CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

namespace AffineAnd

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
variable (P : MorphismProperty Scheme.{u}) [HasAffineProperty P (affineAnd Q)]
variable [P.IsStableUnderBaseChange]

variable {X : Scheme.{u}}

instance (f : P.Over ⊤ X) : IsAffineHom f.hom :=
  HasAffineProperty.affineAnd_le_isAffineHom P inferInstance _ f.prop

/-- The forgetful functor to the category of schemes affine over `X`. -/
def toAffine (X : Scheme.{u}) : P.Over ⊤ X ⥤ Affine X where
  obj f := ⟨f.toComma, inferInstance⟩
  map f := ⟨f.toCommaMorphism, trivial, trivial⟩

/-- The forgetful functor to affine morphisms is fully faithful. -/
def toAffineFullyFaithful (X : Scheme.{u}) : (toAffine P X).FullyFaithful where
  preimage f := ⟨f.toCommaMorphism, trivial, trivial⟩

instance : (toAffine P X).Faithful := (toAffineFullyFaithful P X).faithful
instance : (toAffine P X).Full := (toAffineFullyFaithful P X).full

variable (J : Type) [SmallCategory J] [FinCategory J]

lemma _root_.CommRingCat.Under.property_limit_of_hasFiniteProducts_of_hasEqualizers
    (hQi : RingHom.RespectsIso Q) (hQp : RingHom.HasFiniteProducts Q)
    (hQe : RingHom.HasEqualizers Q)
    {R : CommRingCat.{u}} (D : J ⥤ Under R) (h : ∀ j, Q (D.obj j).hom.hom) :
    Q (limit D).hom.hom := by
  have := CommRingCat.Under.hasFiniteLimits hQi hQp hQe
  let D' : J ⥤ (RingHom.toMorphismProperty Q).Under ⊤ R :=
    MorphismProperty.Comma.lift D h (by simp) (by simp)
  let A := limit D'
  have : CreatesFiniteLimits (Under.forget (RingHom.toMorphismProperty Q) ⊤ R) :=
    CommRingCat.Under.createsFiniteLimitsForget hQi hQp hQe R
  let e : (Under.forget _ _ R).obj A ≅ limit D :=
    preservesLimitIso (Under.forget (RingHom.toMorphismProperty Q) ⊤ R) D'
  have := CategoryTheory.Under.w e.hom
  rw [← this, CommRingCat.hom_comp, hQi.cancel_right_isIso]
  exact A.prop

@[implicit_reducible]
noncomputable
def createsFiniteColimits (hQi : RingHom.RespectsIso Q) (hQp : RingHom.HasFiniteProducts Q)
    (hQe : RingHom.HasEqualizers Q) :
    CreatesFiniteColimits (toAffine P X) := by
  constructor
  intro J _ _
  constructor
  intro D
  let D' : J ⥤ Affine X := D ⋙ toAffine P X
  have : HasColimit D' := inferInstance
  have : P (colimit D').hom := by
    rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
    dsimp
    intro U
    simp only [morphismRestrict]
    rw [P.cancel_left_of_respectsIso]
    change P <| ((Affine.pullback U.1.ι).obj (colimit D')).hom
    let i : (Affine.pullback U.1.ι).obj (colimit D') ≅
        colimit (D' ⋙ Affine.pullback U.1.ι) :=
      preservesColimitIso (Affine.pullback U.1.ι) D'
    erw [P.over_iso_iff ((MorphismProperty.Comma.forget _ _ _ _ _).mapIso i)]
    simp only [Comma.forget_obj]
    let i₂ : (Affine.Γ U.1).rightOp.obj (colimit (D' ⋙ Affine.pullback U.1.ι)) ≅
        colimit (D' ⋙ Affine.pullback U.1.ι ⋙ (Affine.Γ U.1).rightOp) :=
      preservesColimitIso (Affine.Γ U.1).rightOp (D' ⋙ Affine.pullback U.1.ι)
    let i₃ : ((Affine.Γ U.1).rightOp.obj (colimit (D' ⋙ Affine.pullback U.1.ι))).unop ≅
        (colimit (D' ⋙ Affine.pullback U.1.ι ⋙ (Affine.Γ U.1).rightOp)).unop :=
      i₂.symm.unop
    let i₄ : ((Affine.Γ U.1).rightOp.obj (colimit (D' ⋙ Affine.pullback U.1.ι))).unop ≅
        limit (D' ⋙ Affine.pullback U.1.ι ⋙ (Affine.Γ U.1).rightOp).leftOp :=
      i₃ ≪≫ (limitLeftOpIsoUnopColimit
        (D' ⋙ Affine.pullback U.1.ι ⋙ (Affine.Γ ↑↑U).rightOp)).symm
    have := CategoryTheory.Under.w i₄.inv
    rw [HasAffineProperty.iff_of_isAffine (P := P)]
    simp only [affineAnd_apply]
    constructor
    · infer_instance
    have heq : (colimit (D' ⋙ Affine.pullback U.1.ι)).hom.appTop =
        ((Affine.Γ U.1).rightOp.obj (colimit (D' ⋙ Affine.pullback U.1.ι))).unop.hom := rfl
    change Q (Scheme.Hom.appTop (colimit (D' ⋙ Affine.pullback U.1.ι)).hom).hom
    rw [heq, ← this]
    change Q ((Under.Hom.right i₄.inv).hom.comp
      ((limit (D' ⋙ Affine.pullback U.1.ι ⋙ (Affine.Γ U.1).rightOp).leftOp).hom.hom)
    )
    rw [hQi.cancel_right_isIso]
    apply _root_.CommRingCat.Under.property_limit_of_hasFiniteProducts_of_hasEqualizers
    · exact hQi
    · exact hQp
    · exact hQe
    · intro ⟨j⟩
      have : P (pullback.snd (D'.obj j).hom U.1.ι) := P.pullback_snd _ _ (D.obj j).prop
      rw [HasAffineProperty.iff_of_isAffine (P := P)] at this
      exact this.2
  exact CategoryTheory.createsColimitOfFullyFaithfulOfIso
    ⟨(colimit D').toComma, this⟩ (eqToIso rfl)

/-- If a scheme morphism property is affine-locally `affineAnd Q`, and `Q` has finite products and
equalizers, then `P.Over ⊤ X` has finite colimits. -/
lemma hasFiniteColimits (hQi : RingHom.RespectsIso Q) (hQp : RingHom.HasFiniteProducts Q)
    (hQe : RingHom.HasEqualizers Q) {X : Scheme.{u}} :
    HasFiniteColimits (P.Over ⊤ X) := by
  constructor
  intro J _ _
  constructor
  intro D
  have := createsFiniteColimits (X := X) P hQi hQp hQe
  apply CategoryTheory.hasColimit_of_created D (toAffine P X)

lemma preservesFiniteColimits_toAffine (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q) :
    PreservesFiniteColimits (toAffine P X) := by
  have := hasFiniteColimits (X := X) P hQi hQp hQe
  have := createsFiniteColimits (X := X) P hQi hQp hQe
  infer_instance

omit [P.IsStableUnderBaseChange] in
@[simps!]
def _root_.AlgebraicGeometry.IsAffineOpen.ΓProp
    (hQi : RingHom.RespectsIso Q)
    {S : Scheme.{u}} {U : S.Opens} (hU : IsAffineOpen U) :
    (P.Over ⊤ S)ᵒᵖ ⥤ (RingHom.toMorphismProperty Q).Under ⊤ Γ(S, U) where
  obj X := MorphismProperty.Under.mk _ (X.unop.hom.app U) <| by
    have : targetAffineLocally (affineAnd Q) X.unop.hom := by
      rw [← HasAffineProperty.eq_targetAffineLocally P]
      exact X.unop.prop
    rw [targetAffineLocally_affineAnd_iff hQi] at this
    exact (this U hU).2
  map {X Y} f := MorphismProperty.Under.homMk
      (f.unop.left.appLE (X.unop.hom ⁻¹ᵁ U) (Y.unop.hom ⁻¹ᵁ U)
      (by
        rw [← Scheme.Hom.comp_preimage]
        change (Y.unop.hom ⁻¹ᵁ U) ≤ (((𝟭 Scheme).map f.unop.left) ≫ X.unop.hom) ⁻¹ᵁ U
        rw [f.unop.w]
        rfl)) <| by
    change Scheme.Hom.app X.unop.hom U ≫
        Scheme.Hom.appLE f.unop.left (X.unop.hom ⁻¹ᵁ U) (Y.unop.hom ⁻¹ᵁ U) _ =
      Scheme.Hom.app Y.unop.hom U
    rw [Scheme.Hom.app_eq_appLE]
    erw [Scheme.Hom.appLE_comp_appLE]
    convert (Scheme.Hom.app_eq_appLE (Y.unop.hom) (U := U)).symm using 1
    all_goals simp
  map_id X := by
    ext : 1
    change Scheme.Hom.appLE (𝟙 X.unop.left) (X.unop.hom ⁻¹ᵁ U) (X.unop.hom ⁻¹ᵁ U) _ = 𝟙 _
    simpa [Scheme.Hom.id_app] using!
      (Scheme.Hom.app_eq_appLE (𝟙 X.unop.left) (U := X.unop.hom ⁻¹ᵁ U)).symm
  map_comp {X Y Z} f g := by
    ext : 1
    change Scheme.Hom.appLE (g.unop.left ≫ f.unop.left) _ _ _ =
      Scheme.Hom.appLE _ _ _ _ ≫ Scheme.Hom.appLE _ _ _ _
    rw [Scheme.Hom.appLE_comp_appLE]


@[simps! obj_hom]
def ΓProp (hQi : RingHom.RespectsIso Q) (S : Scheme.{u}) [IsAffine S] :
    (P.Over ⊤ S)ᵒᵖ ⥤ (RingHom.toMorphismProperty Q).Under ⊤ Γ(S, ⊤) :=
  (isAffineOpen_top S).ΓProp P hQi

omit [P.IsStableUnderBaseChange] in
@[simp]
lemma ΓProp_map_right (hQi : RingHom.RespectsIso Q) (S : Scheme.{u}) [IsAffine S]
    {X Y : (P.Over ⊤ S)ᵒᵖ} (f : X ⟶ Y) :
    ((ΓProp P hQi S).map f).right = f.unop.left.appTop := by
  simpa [ΓProp, IsAffineOpen.ΓProp, Scheme.Hom.appTop] using!
    (Scheme.Hom.app_eq_appLE ..).symm

lemma _root_.AlgebraicGeometry.Scheme.Hom.appTop_bijective_of_isAffine
      {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] :
    Function.Bijective (fun (f : X ⟶ Y) ↦ f.appTop) := by
  refine ⟨fun f g (hfg : f.appTop = g.appTop) ↦ ?_, fun f ↦ ?_⟩
  · have (f : X ⟶ Y) : f = X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv := by
      simp [Scheme.isoSpec_hom_naturality_assoc]
    rw [this f, this g, hfg]
  · use X.isoSpec.hom ≫ Spec.map f ≫ Y.isoSpec.inv
    simp [Scheme.isoSpec]

omit [P.IsStableUnderBaseChange] in
lemma faithful_ΓProp (hQi : RingHom.RespectsIso Q) {S : Scheme.{u}} [IsAffine S] :
    (ΓProp P hQi S).Faithful where
  map_injective := by
    intro ⟨X⟩ ⟨Y⟩ ⟨f⟩ ⟨g⟩ hfg
    have : f = g := by
      ext : 1
      have : IsAffine X.left :=
        @isAffine_of_isAffineHom X.left S X.hom
          (HasAffineProperty.affineAnd_le_isAffineHom P inferInstance X.hom X.prop) inferInstance
      have : IsAffine Y.left :=
        @isAffine_of_isAffineHom Y.left S Y.hom
          (HasAffineProperty.affineAnd_le_isAffineHom P inferInstance Y.hom Y.prop) inferInstance
      apply AlgebraicGeometry.Scheme.Hom.appTop_bijective_of_isAffine.injective
      simpa using congr($(hfg).right)
    rw [this]

omit [P.IsStableUnderBaseChange] in
lemma full_ΓProp (hQi : RingHom.RespectsIso Q) {S : Scheme.{u}} [IsAffine S] :
    (ΓProp P hQi S).Full where
  map_surjective := by
    intro ⟨X⟩ ⟨Y⟩ f
    have : IsAffine ((𝟭 Scheme).obj X.left) :=
      @isAffine_of_isAffineHom X.left S X.hom
        (HasAffineProperty.affineAnd_le_isAffineHom P inferInstance X.hom X.prop) inferInstance
    have : IsAffine ((𝟭 Scheme).obj Y.left) :=
      @isAffine_of_isAffineHom Y.left S Y.hom
        (HasAffineProperty.affineAnd_le_isAffineHom P inferInstance Y.hom Y.prop) inferInstance
    have : IsAffine ((Functor.fromPUnit S).obj X.right) := inferInstanceAs <| IsAffine S
    have : IsAffine Y.left :=
      @isAffine_of_isAffineHom Y.left S Y.hom
        (HasAffineProperty.affineAnd_le_isAffineHom P inferInstance Y.hom Y.prop) inferInstance
    obtain ⟨f', h⟩ := AlgebraicGeometry.Scheme.Hom.appTop_bijective_of_isAffine.surjective f.right
    use (MorphismProperty.Over.homMk f' <| by
      apply AlgebraicGeometry.Scheme.Hom.appTop_bijective_of_isAffine.injective
      simpa [← h] using f.w.symm).op
    ext : 1
    simpa using h

omit [P.IsStableUnderBaseChange] in
lemma essSurj_ΓProp (hQi : RingHom.RespectsIso Q) {S : Scheme.{u}} [IsAffine S] :
    (ΓProp P hQi S).EssSurj where
  mem_essImage R := by
    let X : P.Over ⊤ S := MorphismProperty.Over.mk ⊤ (Spec.map R.hom ≫ S.isoSpec.inv) <| by
      rw [P.cancel_right_of_respectsIso, HasAffineProperty.SpecMap_iff_of_affineAnd (P := P) _ hQi]
      · exact R.prop
      · infer_instance
    refine ⟨⟨X⟩, ⟨Under.isoMk (Scheme.ΓSpecIso _) ?_⟩⟩
    dsimp [X]
    change (S.isoSpec.inv.appTop ≫ (Spec.map R.hom).appTop) ≫
        (Scheme.ΓSpecIso R.right).hom = R.hom
    rw [show S.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(S, ⊤)).inv by simp [Scheme.isoSpec]]
    erw [← Scheme.ΓSpecIso_inv_naturality_assoc]
    simp

omit [P.IsStableUnderBaseChange] in
lemma isEquivalence_ΓProp (hQi : RingHom.RespectsIso Q) {S : Scheme.{u}} [IsAffine S] :
    (ΓProp P hQi S).IsEquivalence where
  faithful := faithful_ΓProp ..
  full := full_ΓProp ..
  essSurj := essSurj_ΓProp ..


attribute [simp] Scheme.Hom.appLE_comp_appLE Scheme.Hom.appLE_comp_appLE_assoc

lemma _root_.AlgebraicGeometry.Scheme.Hom.appLE_top_eq_appTop
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : Y.Opens)) :
    Scheme.Hom.appLE f ⊤ ⊤ e = f.appTop := by
  simpa [Scheme.Hom.appTop] using (Scheme.Hom.app_eq_appLE f (U := ⊤)).symm

set_option maxHeartbeats 0 in
-- This naturality proof is a long affine-pullback/pushout calculation.
noncomputable
def pullbackΓPropIso [(RingHom.toMorphismProperty Q).IsStableUnderCobaseChange]
    (hQi : RingHom.RespectsIso Q) {S T : Scheme.{u}} [IsAffine S]
    [IsAffine T] (f : S ⟶ T) :
    (MorphismProperty.Over.pullback P ⊤ f).op ⋙ ΓProp P hQi S ≅
      ΓProp P hQi T ⋙ MorphismProperty.Under.pushout _ ⊤ f.appTop :=
  NatIso.ofComponents
    (fun X ↦
      haveI : IsAffine X.unop.left :=
        @isAffine_of_isAffineHom X.unop.left T X.unop.hom
          (HasAffineProperty.affineAnd_le_isAffineHom P inferInstance X.unop.hom X.unop.prop)
          inferInstance
      haveI : IsAffine ((𝟭 Scheme).obj X.unop.left) := inferInstanceAs <| IsAffine X.unop.left
      haveI : IsAffine ((Functor.fromPUnit T).obj X.unop.right) := inferInstanceAs <| IsAffine T
      Under.isoMk (Affine.ΓpullbackIsoPushout (X.unop.hom : X.unop.left ⟶ T) f) <| by
        simp [ΓProp, IsAffineOpen.ΓProp]) <| fun {X Y} g ↦ by
    ext : 1
    dsimp [MorphismProperty.Under.pushout]
    haveI : IsAffine ((𝟭 Scheme).obj (Opposite.unop X).left) :=
      @isAffine_of_isAffineHom X.unop.left T X.unop.hom
        (HasAffineProperty.affineAnd_le_isAffineHom P inferInstance X.unop.hom X.unop.prop)
        inferInstance
    haveI : IsAffine ((𝟭 Scheme).obj (Opposite.unop Y).left) :=
      @isAffine_of_isAffineHom Y.unop.left T Y.unop.hom
        (HasAffineProperty.affineAnd_le_isAffineHom P inferInstance Y.unop.hom Y.unop.prop)
        inferInstance
    haveI : IsAffine ((Functor.fromPUnit T).obj (Opposite.unop X).right) :=
      inferInstanceAs <| IsAffine T
    haveI : IsAffine ((Functor.fromPUnit T).obj (Opposite.unop Y).right) :=
      inferInstanceAs <| IsAffine T
    change Scheme.Hom.appLE
        (pullback.lift (pullback.fst Y.unop.hom f ≫ g.unop.left)
          (pullback.snd Y.unop.hom f) _) ⊤ ⊤ _ ≫
        (Affine.ΓpullbackIsoPushout Y.unop.hom f).hom =
      (Affine.ΓpullbackIsoPushout X.unop.hom f).hom ≫
        pushout.desc
          (Scheme.Hom.appLE g.unop.left ⊤ ⊤ _ ≫
            pushout.inl (Scheme.Hom.app Y.unop.hom ⊤) (Scheme.Hom.appTop f))
          (pushout.inr (Scheme.Hom.app Y.unop.hom ⊤) (Scheme.Hom.appTop f)) _
    apply (cancel_epi (Affine.ΓpullbackIsoPushout (X.unop).hom f).inv).1
    apply pushout.hom_ext
    · erw [Affine.inl_ΓpullbackIsoPushout_inv_assoc]
      rw [Scheme.Hom.appLE_top_eq_appTop]
      erw [← Scheme.Hom.comp_appTop_assoc]
      erw [pullback.lift_fst]
      erw [Scheme.Hom.comp_appTop_assoc]
      conv_lhs =>
        rhs
        erw [Affine.app_fst_ΓpullbackIsoPushout_hom]
      erw [Affine.inl_ΓpullbackIsoPushout_inv_assoc]
      erw [Affine.app_fst_ΓpullbackIsoPushout_hom_assoc]
      erw [pushout.inl_desc]
      rw [Scheme.Hom.appLE_top_eq_appTop]
    · erw [Affine.inr_ΓpullbackIsoPushout_inv_assoc]
      rw [Scheme.Hom.appLE_top_eq_appTop]
      erw [← Scheme.Hom.comp_appTop_assoc]
      erw [pullback.lift_snd]
      erw [Affine.app_snd_ΓpullbackIsoPushout_hom]
      erw [Affine.inr_ΓpullbackIsoPushout_inv_assoc]
      erw [Affine.app_snd_ΓpullbackIsoPushout_hom_assoc]
      erw [pushout.inr_desc]

lemma preservesColimitsOfShape_pullback_affine (hQi : RingHom.RespectsIso Q)
    [(RingHom.toMorphismProperty Q).IsStableUnderCobaseChange]
    {S T : Scheme.{u}} [IsAffine S] [IsAffine T] (f : S ⟶ T) {J : Type} [Category J]
    [PreservesLimitsOfShape Jᵒᵖ
      (MorphismProperty.Under.pushout (RingHom.toMorphismProperty Q) ⊤ f.appTop)] :
    PreservesColimitsOfShape J (MorphismProperty.Over.pullback P ⊤ f) := by
  haveI : (ΓProp P hQi S).IsEquivalence := isEquivalence_ΓProp P hQi
  haveI : (ΓProp P hQi T).IsEquivalence := isEquivalence_ΓProp P hQi
  haveI : PreservesLimitsOfShape Jᵒᵖ (ΓProp P hQi T) := inferInstance
  haveI : PreservesLimitsOfShape Jᵒᵖ
      (ΓProp P hQi T ⋙ MorphismProperty.Under.pushout (RingHom.toMorphismProperty Q) ⊤ f.appTop) :=
    CategoryTheory.Limits.comp_preservesLimitsOfShape (J := Jᵒᵖ)
      (ΓProp P hQi T)
      (MorphismProperty.Under.pushout (RingHom.toMorphismProperty Q) ⊤ f.appTop)
  have : PreservesLimitsOfShape Jᵒᵖ ((MorphismProperty.Over.pullback P ⊤ f).op ⋙ ΓProp P hQi S) :=
    preservesLimitsOfShape_of_natIso (J := Jᵒᵖ)
      (F := ΓProp P hQi T ⋙
        MorphismProperty.Under.pushout (RingHom.toMorphismProperty Q) ⊤ f.appTop)
      (G := (MorphismProperty.Over.pullback P ⊤ f).op ⋙ ΓProp P hQi S)
      (pullbackΓPropIso P hQi f).symm
  have : PreservesLimitsOfShape Jᵒᵖ (MorphismProperty.Over.pullback P ⊤ f).op :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (ΓProp P hQi S)
  exact preservesColimitsOfShape_of_op J (MorphismProperty.Over.pullback P ⊤ f)


noncomputable
def _root_.CategoryTheory.Limits.colimit.arrowMkPostIsoOfIso {J C D : Type*} [Category J]
    [Category C] [Category D] (K : J ⥤ C) (F F' : C ⥤ D)
    (e : F ≅ F') [HasColimit K] [HasColimit (K ⋙ F)] [HasColimit (K ⋙ F')] :
    CategoryTheory.Arrow.mk (colimit.post K F) ≅ CategoryTheory.Arrow.mk (colimit.post K F') :=
  Arrow.isoMk (HasColimit.isoOfNatIso <| Functor.isoWhiskerLeft K e) (e.app _) (by
    apply colimit.hom_ext
    intro j
    simp only [CategoryTheory.Arrow.mk_hom, CategoryTheory.Arrow.mk_right]
    erw [HasColimit.isoOfNatIso_ι_hom_assoc]
    conv_lhs =>
      rhs
      rw [colimit.ι_post]
    conv_rhs =>
      erw [colimit.ι_post_assoc]
    exact (e.hom.naturality (colimit.ι K j)).symm)

section LocalAtTarget

variable (P₀ : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P₀]

lemma iff_of_openCover_of_over
    {X Y S : Scheme.{u}} [X.Over S] [Y.Over S]
    (f : X ⟶ Y) [f.IsOver S] (𝒰 : S.OpenCover) :
    P₀ f ↔ ∀ i : 𝒰.I₀,
      P₀ (pullback.map (X ↘ S) (𝒰.f i) (Y ↘ S) (𝒰.f i) f (𝟙 _) (𝟙 _) (by simp) (by simp)) := by
  have heq (i : 𝒰.I₀) :
      dsimp% pullback.snd f ((𝒰.pullback₁ (Y ↘ S)).f i) =
      (pullbackRightPullbackFstIso _ _ _).hom ≫ (pullback.congrHom (by simp) rfl).hom ≫
      pullback.map (X ↘ S) (𝒰.f i) (Y ↘ S) (𝒰.f i) f (𝟙 _) (𝟙 _) (by simp) (by simp) := by
    apply pullback.hom_ext
    · rw [← pullback.condition]
      simp only [pullback.map]
      conv_rhs => rw [Category.assoc]
      conv_rhs =>
        rhs
        rw [Category.assoc]
        rhs
        erw [pullback.lift_fst]
      erw [pullback.lift_fst_assoc]
      simp only [Category.comp_id]
      conv_rhs =>
        rw [← Category.assoc]
        rw [pullbackRightPullbackFstIso_hom_fst]
    · simp only [pullback.map]
      conv_rhs => rw [Category.assoc]
      conv_rhs =>
        rhs
        rw [Category.assoc]
        rhs
        erw [pullback.lift_snd]
      erw [pullback.lift_snd_assoc]
      simp only [Category.comp_id]
      erw [pullbackRightPullbackFstIso_hom_snd]
  refine ⟨fun hf i ↦ ?_, fun H ↦ ?_⟩
  · have : P₀ (pullback.snd f ((𝒰.pullback₁ (Y ↘ S)).f i)) :=
      IsZariskiLocalAtTarget.of_isPullback (.of_hasPullback _ _) hf
    dsimp at this
    rwa [heq, P₀.cancel_left_of_respectsIso, P₀.cancel_left_of_respectsIso] at this
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := P₀) (𝒰.pullback₁ (Y ↘ S))]
    intro i
    dsimp [Scheme.Cover.pullbackHom]
    rw [heq, P₀.cancel_left_of_respectsIso, P₀.cancel_left_of_respectsIso]
    exact H i

variable {W Q₀ : MorphismProperty Scheme.{u}} [Q₀.IsMultiplicative]
variable [W.IsStableUnderBaseChange] [Q₀.IsStableUnderBaseChange]

lemma left_iff_of_openCover
    {S : Scheme.{u}} {X Y : W.Over Q₀ S} {f : X ⟶ Y} (𝒰 : S.OpenCover) :
    P₀ f.left ↔ ∀ i : 𝒰.I₀,
      P₀ ((MorphismProperty.Over.pullback W Q₀ (𝒰.f i)).map f).left :=
  iff_of_openCover_of_over P₀ ..

end LocalAtTarget


lemma _root_.AlgebraicGeometry.Affine.preservesFiniteColimits_pullback_affineOpen
    {S : Scheme.{u}} (V : S.affineOpens) :
    PreservesFiniteColimits (Affine.pullback V.1.ι) := inferInstance

lemma _root_.AlgebraicGeometry.Affine.preservesFiniteColimits_pullback_of_isOpenImmersion
    {X S : Scheme.{u}} (f : X ⟶ S) [IsOpenImmersion f] [IsAffine X] :
    PreservesFiniteColimits (Affine.pullback f) := by
  let V : S.affineOpens := ⟨Scheme.Hom.opensRange f, isAffineOpen_opensRange f⟩
  have hfac : f = f.isoOpensRange.hom ≫ V.1.ι := by
    simp [V, Scheme.Hom.isoOpensRange]
  haveI : IsAffine V.1 := V.property
  haveI : PreservesFiniteColimits (Affine.pullback V.1.ι) :=
    Affine.preservesFiniteColimits_pullback_affineOpen V
  haveI : PreservesFiniteColimits (Affine.pullback f.isoOpensRange.hom) := inferInstance
  haveI : PreservesFiniteColimits (Affine.pullback V.1.ι ⋙ Affine.pullback f.isoOpensRange.hom) :=
    comp_preservesFiniteColimits (Affine.pullback V.1.ι) (Affine.pullback f.isoOpensRange.hom)
  have e : Affine.pullback f ≅ Affine.pullback V.1.ι ⋙ Affine.pullback f.isoOpensRange.hom :=
    MorphismProperty.Over.pullbackCongr hfac ≪≫ MorphismProperty.Over.pullbackComp _ _
  exact preservesFiniteColimits_of_natIso e.symm

def pullbackToAffineIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.Over.pullback P ⊤ f ⋙ toAffine P X ≅ toAffine P Y ⋙ Affine.pullback f :=
  Iso.refl _

lemma preservesFiniteColimits_pullback_of_affine (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [PreservesFiniteColimits (Affine.pullback f)] :
    PreservesFiniteColimits (MorphismProperty.Over.pullback P ⊤ f) := by
  constructor
  intro J _ _
  constructor
  intro D
  haveI : HasFiniteColimits (P.Over ⊤ Y) := hasFiniteColimits P hQi hQp hQe
  haveI : HasFiniteColimits (P.Over ⊤ X) := hasFiniteColimits P hQi hQp hQe
  haveI : PreservesFiniteColimits (toAffine P Y) := by
    have := createsFiniteColimits (X := Y) P hQi hQp hQe
    infer_instance
  haveI : PreservesFiniteColimits (toAffine P X) := by
    have := createsFiniteColimits (X := X) P hQi hQp hQe
    infer_instance
  haveI : PreservesColimitsOfShape J (toAffine P Y) := inferInstance
  haveI : PreservesColimitsOfShape J (Affine.pullback f) := inferInstance
  haveI : PreservesColimitsOfShape J (toAffine P Y ⋙ Affine.pullback f) :=
    CategoryTheory.Limits.comp_preservesColimitsOfShape (J := J) (toAffine P Y) (Affine.pullback f)
  haveI : PreservesColimitsOfShape J (MorphismProperty.Over.pullback P ⊤ f ⋙ toAffine P X) :=
    preservesColimitsOfShape_of_natIso (J := J) (pullbackToAffineIso P f).symm
  haveI : PreservesColimitsOfShape J (MorphismProperty.Over.pullback P ⊤ f) :=
    preservesColimitsOfShape_of_reflects_of_preserves _ (toAffine P X)
  infer_instance

nonrec theorem preservesFiniteColimits_pullback (hQi : RingHom.RespectsIso Q)
    (hQp : RingHom.HasFiniteProducts Q) (hQe : RingHom.HasEqualizers Q)
    [(RingHom.toMorphismProperty Q).IsStableUnderCobaseChange]
    [∀ (R S : CommRingCat.{u}) (f : R ⟶ S), PreservesFiniteLimits
      (MorphismProperty.Under.pushout (RingHom.toMorphismProperty Q) ⊤ f)]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (MorphismProperty.Over.pullback P ⊤ f) := by
  have (S : Scheme.{u}) : HasFiniteColimits (P.Over ⊤ S) := hasFiniteColimits P hQi hQp hQe
  constructor
  intro J _ _
  constructor
  intro D
  suffices h : IsIso (colimit.post D (MorphismProperty.Over.pullback P ⊤ f)).left by
    have : IsIso (colimit.post D (MorphismProperty.Over.pullback P ⊤ f)) := by
      convert isIso_of_reflects_iso _ (MorphismProperty.Over.forget P ⊤ X ⋙ Over.forget X)
      exact h
    apply preservesColimit_of_isIso_post
  change isomorphisms Scheme.{u} (colimit.post D (MorphismProperty.Over.pullback P ⊤ f)).left
  wlog H : IsAffine X ∧ IsAffine Y generalizing X Y D f
  · rename_i hFin
    let ih :
        ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {D : J ⥤ P.Over ⊤ Y},
          IsAffine X ∧ IsAffine Y →
            isomorphisms Scheme (colimit.post D (MorphismProperty.Over.pullback P ⊤ f)).left := this
    let 𝒰X : X.OpenCover :=
      (Scheme.OpenCover.affineRefinement (Y.affineCover.pullback₁ f)).openCover
    rw [left_iff_of_openCover (P₀ := isomorphisms Scheme) 𝒰X]
    intro i
    let uᵢ : Y.affineCover.X i.1 ⟶ Y := Y.affineCover.f i.1
    have _ : PreservesFiniteColimits (toAffine P X) :=
      preservesFiniteColimits_toAffine P hQi hQp hQe
    have _ : PreservesFiniteColimits (toAffine P Y) :=
      preservesFiniteColimits_toAffine P hQi hQp hQe
    haveI : PreservesFiniteColimits (Affine.pullback (𝒰X.f i)) :=
      Affine.preservesFiniteColimits_pullback_of_isOpenImmersion (𝒰X.f i)
    haveI : PreservesFiniteColimits (MorphismProperty.Over.pullback P ⊤ (𝒰X.f i)) :=
      preservesFiniteColimits_pullback_of_affine P hQi hQp hQe (𝒰X.f i)
    rw [← cancel_left_of_respectsIso (isomorphisms Scheme)
      (colimit.post (D ⋙ MorphismProperty.Over.pullback P ⊤ f)
        (MorphismProperty.Over.pullback P ⊤ (𝒰X.f i))).left]
    erw [← MorphismProperty.Comma.comp_left]
    simp only [MorphismProperty.Over.pullback_obj_left, MorphismProperty.Over.pullback_obj_hom,
      colimit.post_post]
    have heq : 𝒰X.f i = (Scheme.OpenCover.fromAffineRefinement _).h₀ i ≫ pullback.fst f uᵢ := by
      convert (Scheme.OpenCover.fromAffineRefinement (Y.affineCover.pullback₁ f)).w₀ i
      all_goals rfl
    let aux : 𝒰X.X i ⟶ Y.affineCover.X i.fst :=
      (Scheme.OpenCover.fromAffineRefinement _).h₀ i ≫ pullback.snd f uᵢ
    haveI : PreservesFiniteColimits (Affine.pullback uᵢ) :=
      Affine.preservesFiniteColimits_pullback_of_isOpenImmersion uᵢ
    haveI : PreservesFiniteColimits (MorphismProperty.Over.pullback P ⊤ uᵢ) :=
      preservesFiniteColimits_pullback_of_affine P hQi hQp hQe uᵢ
    let natiso :
        MorphismProperty.Over.pullback P ⊤ f ⋙ MorphismProperty.Over.pullback P ⊤ (𝒰X.f i) ≅
          MorphismProperty.Over.pullback P ⊤ uᵢ ⋙
            MorphismProperty.Over.pullback P ⊤ aux :=
      (MorphismProperty.Over.pullbackComp _ _).symm ≪≫
        MorphismProperty.Over.pullbackCongr
        (by
          dsimp [aux]
          rw [heq]
          rw [Category.assoc]
          conv_lhs =>
            rhs
            erw [pullback.condition]
          conv_rhs => rw [Category.assoc]) ≪≫
        (MorphismProperty.Over.pullbackComp _ _)
    let e := CategoryTheory.Limits.colimit.arrowMkPostIsoOfIso D _ _ natiso
    have : IsIso ((colimit.post D
        (MorphismProperty.Over.pullback P ⊤ f ⋙
          MorphismProperty.Over.pullback P ⊤ (𝒰X.f i))).left) := by
      have hnAux : IsIso ((colimit.post (D ⋙ MorphismProperty.Over.pullback P ⊤ uᵢ)
          (MorphismProperty.Over.pullback P ⊤ aux)).left) := by
        rw [← isomorphisms.iff]
        exact ih aux (D := D ⋙ MorphismProperty.Over.pullback P ⊤ uᵢ)
          ⟨inferInstance, inferInstance⟩
      haveI : IsIso ((colimit.post (D ⋙ MorphismProperty.Over.pullback P ⊤ uᵢ)
          (MorphismProperty.Over.pullback P ⊤ aux)).left) := hnAux
      haveI : IsIso (colimit.post D (MorphismProperty.Over.pullback P ⊤ uᵢ)) := by
        infer_instance
      haveI : IsIso ((MorphismProperty.Over.pullback P ⊤ aux).map
          (colimit.post D (MorphismProperty.Over.pullback P ⊤ uᵢ))) := by
        infer_instance
      have hmapLeft : IsIso (((MorphismProperty.Over.pullback P ⊤ aux).map
          (colimit.post D (MorphismProperty.Over.pullback P ⊤ uᵢ))).left) := by
        change IsIso (((MorphismProperty.Over.forget P ⊤ (𝒰X.X i) ⋙ Over.forget (𝒰X.X i)).map
          ((MorphismProperty.Over.pullback P ⊤ aux).map
            (colimit.post D (MorphismProperty.Over.pullback P ⊤ uᵢ)))))
        exact Functor.map_isIso (MorphismProperty.Over.forget P ⊤ (𝒰X.X i) ⋙
          Over.forget (𝒰X.X i)) _
      have hnLeft : IsIso ((colimit.post D
          (MorphismProperty.Over.pullback P ⊤ uᵢ ⋙
            MorphismProperty.Over.pullback P ⊤ aux)).left) := by
        erw [← colimit.post_post]
        rw [MorphismProperty.Comma.comp_left]
        exact @IsIso.comp_isIso Scheme _ _ _ _ _ _ hnAux hmapLeft
      have hn : IsIso (colimit.post D
          (MorphismProperty.Over.pullback P ⊤ uᵢ ⋙
            MorphismProperty.Over.pullback P ⊤ aux)) := by
        convert isIso_of_reflects_iso _
          (MorphismProperty.Over.forget P ⊤ (𝒰X.X i) ⋙ Over.forget (𝒰X.X i))
        exact hnLeft
      have hm : IsIso (colimit.post D
          (MorphismProperty.Over.pullback P ⊤ f ⋙
            MorphismProperty.Over.pullback P ⊤ (𝒰X.f i))) := by
        rw [← isomorphisms.iff]
        rw [(isomorphisms (P.Over ⊤ (𝒰X.X i))).arrow_mk_iso_iff e]
        rw [isomorphisms.iff]
        exact hn
      haveI : IsIso (colimit.post D
          (MorphismProperty.Over.pullback P ⊤ f ⋙
            MorphismProperty.Over.pullback P ⊤ (𝒰X.f i))) := hm
      infer_instance
    change IsIso ((colimit.post D
        (MorphismProperty.Over.pullback P ⊤ f ⋙
          MorphismProperty.Over.pullback P ⊤ (𝒰X.f i))).left)
    exact this
  · haveI : IsAffine X := H.1
    haveI : IsAffine Y := H.2
    haveI : PreservesColimitsOfShape J (MorphismProperty.Over.pullback P ⊤ f) := by
      apply preservesColimitsOfShape_pullback_affine (P := P) hQi f
    change IsIso (colimit.post D (MorphismProperty.Over.pullback P ⊤ f)).left
    infer_instance

end AffineAnd

end AlgebraicGeometry
