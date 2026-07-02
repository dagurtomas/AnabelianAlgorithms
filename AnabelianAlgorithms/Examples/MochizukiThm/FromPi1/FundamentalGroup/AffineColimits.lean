/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/

module

public import Mathlib.AlgebraicGeometry.ColimitsOver
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-
This file was copied and adapted from Christian Merten's `pi1` project
(<https://github.com/chrisflav/pi1>), commit `5c5c0171efc863ce9990171bdf46d7cb5fd582fb`.
-/
/-!
# Colimits of affine morphisms

This file contains the affine-over-a-base category used by the vendored finite-étale colimit API.
The finite-colimit construction is ported via affine-base global sections and gluing over the
base's directed affine cover.  Preservation of finite colimits by flat pullback remains a lower
boundary.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite
open CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

variable (S : Scheme.{u})

/-- The global-sections functor on schemes over `S`, contravariantly as a functor to rings under
`Γ(S, ⊤)`. -/
def Over.Γ : (Over S)ᵒᵖ ⥤ Under Γ(S, ⊤) where
  obj X := Under.mk X.unop.hom.appTop
  map {X Y} f :=
    Under.homMk f.unop.left.appTop <| by
      dsimp
      rw [← Scheme.Hom.comp_appTop, CategoryTheory.Over.w]

/-- The category of affine morphisms with target `S`. -/
def Affine : Type _ := MorphismProperty.Over @IsAffineHom ⊤ S

namespace Affine

abbrev mk {S X : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f] : Affine S :=
  MorphismProperty.Over.mk ⊤ f inferInstance

instance : Category (Affine S) :=
  inferInstanceAs <| Category (MorphismProperty.Over @IsAffineHom ⊤ S)

instance (X : Affine S) : IsAffineHom X.hom := X.prop

/-- The source of an affine morphism over an affine base is affine. -/
instance (X : Affine S) [IsAffine S] : IsAffine X.left :=
  @isAffine_of_isAffineHom X.left S X.hom X.prop inferInstance

instance (X : Affine S) [IsAffine S] : IsAffine ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs <| IsAffine X.left

/-- Global sections on affine schemes over `S`. -/
@[simps! map_right obj_hom]
def Γ : (Affine S)ᵒᵖ ⥤ Under Γ(S, ⊤) :=
  (MorphismProperty.Over.forget @IsAffineHom ⊤ S).op ⋙ Over.Γ S

variable {S}

/-- Pullback of affine morphisms. -/
abbrev pullback {T : Scheme.{u}} (f : T ⟶ S) : Affine S ⥤ Affine T :=
  MorphismProperty.Over.pullback _ _ f

section MapPullback

variable {T S : Scheme.{u}} (f : T ⟶ S)

/-- Post-composition of affine morphisms by an affine map. -/
abbrev map [IsAffineHom f] : Affine T ⥤ Affine S :=
  MorphismProperty.Over.map ⊤ ‹IsAffineHom f›

/-- Post-composition by an affine map is left adjoint to pullback. -/
abbrev mapPullbackAdjunction [IsAffineHom f] : map f ⊣ pullback f :=
  MorphismProperty.Over.mapPullbackAdj _ _ f _ trivial

instance [IsAffineHom f] : (map f).IsLeftAdjoint :=
  ⟨pullback f, ⟨mapPullbackAdjunction f⟩⟩

instance [IsAffineHom f] : (pullback f).IsRightAdjoint :=
  ⟨map f, ⟨mapPullbackAdjunction f⟩⟩

end MapPullback

section PullbackPushout

variable {X Y S : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsAffine S]
variable {f : X ⟶ S} {g : Y ⟶ S}

/-- Global sections sends a pullback square of affine schemes to a pushout square of rings. -/
lemma Γ_isPushout {P : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    (h : IsPullback fst snd f g) :
    IsPushout (f.app ⊤) (g.app ⊤) (fst.app ⊤) (snd.app ⊤) := by
  haveI : IsAffine (CategoryTheory.Limits.pullback f g) := inferInstance
  let iso : P ≅ CategoryTheory.Limits.pullback f g := h.isoPullback
  haveI : IsAffine P := .of_isIso iso.hom
  let h' : IsPullback (AffineScheme.ofHom fst) (AffineScheme.ofHom snd)
      (AffineScheme.ofHom f) (AffineScheme.ofHom g) := by
    apply IsPullback.of_map (F := AffineScheme.forgetToScheme.{u}) (ObjectProperty.hom_ext _ h.w)
    exact h
  exact AffineScheme.Γ.rightOp.map_isPullback h' |>.unop |>.flip

variable (f g)

/-- The global sections of the scheme-theoretic pullback of affine schemes is the pushout of the
corresponding rings. -/
def ΓpullbackIsoPushout : Γ(CategoryTheory.Limits.pullback f g, ⊤) ≅ pushout f.appTop g.appTop :=
  IsPushout.isoPushout (Γ_isPushout (f := f) (g := g) <| IsPullback.of_hasPullback f g)

@[reassoc (attr := simp)]
lemma inl_ΓpullbackIsoPushout_inv :
    pushout.inl f.appTop g.appTop ≫ (ΓpullbackIsoPushout f g).inv =
      (pullback.fst f g).appTop := by
  simp [ΓpullbackIsoPushout]

@[reassoc (attr := simp)]
lemma inr_ΓpullbackIsoPushout_inv :
    pushout.inr f.appTop g.appTop ≫ (ΓpullbackIsoPushout f g).inv =
      (pullback.snd f g).appTop := by
  simp [ΓpullbackIsoPushout]

@[reassoc (attr := simp)]
lemma app_fst_ΓpullbackIsoPushout_hom :
     (pullback.fst f g).appTop ≫ (ΓpullbackIsoPushout f g).hom =
        pushout.inl f.appTop g.appTop := by
  simp [ΓpullbackIsoPushout]

@[reassoc (attr := simp)]
lemma app_snd_ΓpullbackIsoPushout_hom :
     (pullback.snd f g).appTop ≫ (ΓpullbackIsoPushout f g).hom =
        pushout.inr f.appTop g.appTop := by
  simp [ΓpullbackIsoPushout]

end PullbackPushout

variable (S)

section AffineBase

variable [IsAffine S]

instance (X : Affine S) : IsAffine ((Functor.fromPUnit S).obj X.right) := ‹IsAffine S›

/-- Regard an affine morphism over an affine base as a morphism in the category of affine
schemes over that base. -/
def toAffine : Affine S ⥤ CategoryTheory.Over (AffineScheme.mk S inferInstance) where
  obj X := CategoryTheory.Over.mk (AffineScheme.ofHom X.hom)
  map {X Y} f := CategoryTheory.Over.homMk (AffineScheme.ofHom f.left) <| by
    apply ObjectProperty.hom_ext
    exact MorphismProperty.Over.w f

/-- The comparison with affine schemes over an affine base is fully faithful. -/
def toAffineFullyFaithful : (toAffine S).FullyFaithful where
  preimage {X Y} f := MorphismProperty.Over.homMk (by
      change (((toAffine S).obj X).left.obj ⟶ ((toAffine S).obj Y).left.obj)
      exact f.left.hom) (by
    change (by
      change (((toAffine S).obj X).left.obj ⟶ ((toAffine S).obj Y).left.obj)
      exact f.left.hom) ≫ Y.hom = X.hom
    exact congrArg InducedCategory.Hom.hom (CategoryTheory.Over.w f))
  map_preimage {X Y} f := by
    ext : 1
    rfl
  preimage_map {X Y} f := by
    apply MorphismProperty.Over.Hom.ext
    rfl

instance : (toAffine S).Faithful := (toAffineFullyFaithful S).faithful
instance : (toAffine S).Full := (toAffineFullyFaithful S).full

instance : (toAffine S).EssSurj where
  mem_essImage X := ⟨Affine.mk X.hom.hom, ⟨by
    refine CategoryTheory.Over.isoMk ?e ?_
    · exact Scheme.Spec.essImage.isoMk (Iso.refl X.left.obj)
    · apply ObjectProperty.hom_ext
      rfl⟩⟩

instance : (toAffine S).IsEquivalence where

/-- The affine-scheme global-sections equivalence, transported to over/under categories. -/
def Over.AffineΓ : CategoryTheory.Over (AffineScheme.mk S inferInstance) ⥤ (Under Γ(S, ⊤))ᵒᵖ :=
  CategoryTheory.Over.post AffineScheme.Γ.rightOp ⋙
    (CategoryTheory.Over.opEquivOpUnder _).functor

instance : (Over.AffineΓ S).IsEquivalence := inferInstanceAs <|
  (CategoryTheory.Over.post AffineScheme.Γ.rightOp ⋙
    (CategoryTheory.Over.opEquivOpUnder _).functor).IsEquivalence

/-- Over an affine base, global sections agrees with the equivalence through affine schemes. -/
def ΓRightOpIso : (Γ S).rightOp ≅ toAffine S ⋙ Over.AffineΓ S :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intro X Y f; rfl)

lemma Γ_eq : Γ S = (toAffine S ⋙ Over.AffineΓ S).leftOp := rfl

instance : (Γ S).IsEquivalence :=
  inferInstanceAs <| (toAffine S ⋙ Over.AffineΓ S).leftOp.IsEquivalence

variable {S}
variable {T : Scheme.{u}} (f : T ⟶ S) [IsAffine T]

/-- Pulling back an affine morphism over an affine base corresponds on global sections to pushout
along the base ring map. -/
@[simps! hom_right inv_right]
def pullbackIsoPushout (X : (Affine S)ᵒᵖ) :
    (Γ T).obj (op ((pullback f).obj X.unop)) ≅
      Under.mk (pushout.inr ((Γ S).obj X).hom (f.app ⊤)) :=
  Under.isoMk (ΓpullbackIsoPushout X.unop.hom f) <| by
    simp [Γ, Over.Γ, Affine.pullback]

@[reassoc (attr := simp)]
lemma pullbackIsoPushout_inl_inv (X : (Affine S)ᵒᵖ) :
    pushout.inl ((Γ S).obj X).hom (Scheme.Hom.app f ⊤) ≫
      Under.Hom.right (pullbackIsoPushout f X).inv =
        (pullback.fst X.unop.hom f).appTop := by
  simp [pullbackIsoPushout, Γ, Over.Γ]

@[reassoc (attr := simp)]
lemma pullbackIsoPushout_inr_inv (X : (Affine S)ᵒᵖ) :
    pushout.inr ((Γ S).obj X).hom (Scheme.Hom.app f ⊤) ≫
      Under.Hom.right (pullbackIsoPushout f X).inv =
        (pullback.snd X.unop.hom f).appTop := by
  simp [pullbackIsoPushout, Γ, Over.Γ]

@[reassoc (attr := simp)]
lemma pullbackIsoPushout_fst_hom (X : Affine S) :
    Scheme.Hom.appTop (pullback.fst X.hom f) ≫
      (ΓpullbackIsoPushout X.hom f).hom =
        pushout.inl (Scheme.Hom.appTop X.hom) (Scheme.Hom.app f ⊤) := by
  simp

@[reassoc (attr := simp)]
lemma pullbackIsoPushout_snd_hom (X : Affine S) :
    Scheme.Hom.appTop (pullback.snd X.hom f) ≫
      (ΓpullbackIsoPushout X.hom f).hom =
        pushout.inr (Scheme.Hom.appTop X.hom) (Scheme.Hom.app f ⊤) := by
  simp

/-- The global-sections description of pullback over affine bases. -/
def pullbackΓIso : (pullback f).op ⋙ Γ T ≅ Γ S ⋙ Under.pushout (f.app ⊤) :=
  NatIso.ofComponents (pullbackIsoPushout f) <| by
    intro X Y g
    ext : 1
    dsimp
    rw [← cancel_epi (Under.Hom.right (pullbackIsoPushout f X).inv)]
    apply pushout.hom_ext
    · erw [pullbackIsoPushout_inl_inv_assoc]
      conv_rhs => erw [pullbackIsoPushout_inl_inv_assoc]
      erw [← Scheme.Hom.comp_appTop_assoc]
      erw [pullback.lift_fst]
      erw [Scheme.Hom.comp_appTop_assoc]
      conv_lhs =>
        rhs
        erw [pullbackIsoPushout_fst_hom]
      erw [pullbackIsoPushout_fst_hom_assoc]
      erw [pushout.inl_desc]
    · erw [pullbackIsoPushout_inr_inv_assoc]
      conv_rhs => erw [pullbackIsoPushout_inr_inv_assoc]
      erw [← Scheme.Hom.comp_appTop_assoc]
      erw [pullback.lift_snd]
      erw [pullbackIsoPushout_snd_hom]
      erw [pullbackIsoPushout_snd_hom_assoc]
      erw [pushout.inr_desc]

end AffineBase

variable {S}

/-- Over an affine base, global sections is an equivalence, hence its opposite preserves finite
colimits. -/
lemma Γ_rightOp_preservesFiniteColimits (S : Scheme.{u}) [IsAffine S] :
    PreservesFiniteColimits (Γ S).rightOp := by
  exact preservesFiniteColimits_of_natIso (ΓRightOpIso S).symm

instance (S : Scheme.{u}) [IsAffine S] : PreservesFiniteColimits (Γ S).rightOp :=
  Γ_rightOp_preservesFiniteColimits S

section AffineBasePreservation

variable {T S : Scheme.{u}} [IsAffine S] [IsAffine T] (f : T ⟶ S)

instance [Flat f] : PreservesFiniteLimits (Under.pushout (f.app ⊤)) := by
  apply CommRingCat.Under.preservesFiniteLimits_of_flat (Scheme.Hom.app f ⊤)
  apply HasRingHomProperty.appTop (P := @Flat)
  infer_instance

instance preservesColimitsOfShapePullback {J : Type} [Category J]
    [PreservesLimitsOfShape Jᵒᵖ (CategoryTheory.Under.pushout (Scheme.Hom.app f ⊤))] :
    PreservesColimitsOfShape J (pullback f) := by
  haveI : PreservesLimitsOfShape Jᵒᵖ (Γ S) := inferInstance
  haveI : PreservesLimitsOfShape Jᵒᵖ
      (Γ S ⋙ CategoryTheory.Under.pushout (Scheme.Hom.app f ⊤)) :=
    CategoryTheory.Limits.comp_preservesLimitsOfShape (J := Jᵒᵖ)
      (Γ S) (CategoryTheory.Under.pushout (Scheme.Hom.app f ⊤))
  have : PreservesLimitsOfShape Jᵒᵖ ((pullback f).op ⋙ Γ T) :=
    preservesLimitsOfShape_of_natIso (J := Jᵒᵖ)
      (F := Γ S ⋙ CategoryTheory.Under.pushout (Scheme.Hom.app f ⊤))
      (G := (pullback f).op ⋙ Γ T) (pullbackΓIso f).symm
  have : PreservesLimitsOfShape Jᵒᵖ (pullback f).op :=
    preservesLimitsOfShape_of_reflects_of_preserves _ (Γ T)
  exact preservesColimitsOfShape_of_op J (pullback f)

instance [Flat f] : PreservesFiniteColimits (pullback f) where
  preservesFiniteColimits _ := inferInstance

/-- Pullback along a flat morphism between affine schemes preserves finite colimits of affine
morphisms. -/
theorem pullback_preservesFiniteColimits [Flat f] : PreservesFiniteColimits (pullback f) :=
  inferInstance

instance [Flat f] :
    PreservesFiniteColimits (MorphismProperty.Over.pullback @IsAffineHom ⊤ f) :=
  inferInstanceAs <| PreservesFiniteColimits (pullback f)

end AffineBasePreservation

/-- Affine morphisms over an affine base have finite colimits, because global sections identifies
this category with the opposite of a category of rings under `Γ(S, ⊤)`. -/
lemma hasFiniteColimits_of_isAffine (S : Scheme.{u}) [IsAffine S] :
    HasFiniteColimits (Affine S) := by
  constructor
  intro J _ _
  haveI : HasLimitsOfShape Jᵒᵖ (Under Γ(S, ⊤)) := inferInstance
  haveI : (Γ S).rightOp.IsEquivalence :=
    Functor.isEquivalence_of_iso (ΓRightOpIso S).symm
  haveI : HasColimitsOfShape J (Under Γ(S, ⊤))ᵒᵖ := inferInstance
  exact Adjunction.hasColimitsOfShape_of_equivalence (Γ S).rightOp

instance (S : Scheme.{u}) [IsAffine S] :
    HasFiniteColimits (MorphismProperty.Over @IsAffineHom ⊤ S) :=
  hasFiniteColimits_of_isAffine S

section Gluing

variable {J : Type} [SmallCategory J] [FinCategory J] (D : J ⥤ Affine S)

instance (i : S.directedAffineCover.I₀) : IsAffine (S.directedAffineCover.X i) := i.2

/-- The affine-open pieces of a finite diagram of affine morphisms have colimits, and these
colimits form gluing data over the directed affine cover of the base. -/
def colimitGluingData : S.directedAffineCover.ColimitGluingData D where
  cocone i :=
    colimit.cocone (D ⋙ MorphismProperty.Over.pullback @IsAffineHom ⊤
      (S.directedAffineCover.f i))
  isColimit i :=
    colimit.isColimit (D ⋙ MorphismProperty.Over.pullback @IsAffineHom ⊤
      (S.directedAffineCover.f i))
  prop_trans := by infer_instance

instance : HasColimit D where
  exists_colimit := by
    haveI {i j : S.directedAffineCover.I₀} (hij : i ⟶ j) :
        PreservesColimitsOfShape J (MorphismProperty.Over.pullback @IsAffineHom ⊤
          (S.directedAffineCover.trans hij)) :=
      inferInstance
    use (colimitGluingData D).gluedCocone
    exact (colimitGluingData D).isColimitGluedCocone

end Gluing

/-- Affine morphisms over any base have finite colimits, by gluing the affine-base construction
along the directed affine cover of the base. -/
lemma hasFiniteColimits (S : Scheme.{u}) : HasFiniteColimits (Affine S) where
  out J _ _ := { }

instance : HasFiniteColimits (Affine S) :=
  hasFiniteColimits S

/-- Pullback to an affine open preserves finite colimits of affine morphisms. -/
instance (V : S.affineOpens) : PreservesFiniteColimits (pullback V.1.ι) := by
  constructor
  intro J _ _
  constructor
  intro D
  haveI {U V : S.affineOpens} (hUV : U.1 ≤ V.1) :
      PreservesColimitsOfShape J (map (S.homOfLE hUV)) :=
    inferInstance
  haveI {U V : S.affineOpens} (hUV : U.1 ≤ V.1) :
      PreservesColimitsOfShape J (pullback (S.homOfLE hUV)) :=
    inferInstance
  let d := colimitGluingData D
  have hc := d.isColimitGluedCocone
  apply CategoryTheory.Limits.preservesColimit_of_preserves_colimit_cocone hc
  let iso : (Functor.mapCocone (pullback V.1.ι) d.gluedCocone) ≅ d.cocone V :=
    Cocone.ext (d.pullbackGluedIso V) (by
      intro j
      apply (cancel_mono (d.pullbackGluedIso V).inv).1
      erw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      apply MorphismProperty.Over.Hom.ext
      apply pullback.hom_ext
      · rw [Functor.mapCocone_ι_app]
        rw [MorphismProperty.Over.pullback_map_left]
        erw [pullback.lift_fst]
        change pullback.fst (D.obj j).hom V.1.ι ≫ (d.gluedCocone.ι.app j).left =
          (((d.cocone V).ι.app j).left ≫ (d.pullbackGluedIso V).inv.left) ≫
            pullback.fst d.glued.hom V.1.ι
        have hfst : (d.pullbackGluedIso V).inv.left ≫ pullback.fst d.glued.hom V.1.ι =
            colimit.ι d.relativeGluingData.functor V := by
          simpa [Scheme.directedAffineCover_f] using
            (Scheme.Cover.ColimitGluingData.pullbackGluedIso_inv_fst d V)
        conv_rhs => rw [Category.assoc]
        erw [hfst]
        simpa [Scheme.directedAffineCover_f] using
          (Scheme.Cover.ColimitGluingData.fst_gluedCocone_ι d j V)
      · rw [Functor.mapCocone_ι_app]
        rw [MorphismProperty.Over.pullback_map_left]
        erw [pullback.lift_snd]
        change pullback.snd (D.obj j).hom V.1.ι =
          (((d.cocone V).ι.app j).left ≫ (d.pullbackGluedIso V).inv.left) ≫
            pullback.snd d.glued.hom V.1.ι
        have hsnd : (d.pullbackGluedIso V).inv.left ≫ pullback.snd d.glued.hom V.1.ι =
            (d.cocone V).pt.hom := by
          simpa [Scheme.directedAffineCover_f] using
            (Scheme.Cover.ColimitGluingData.pullbackGluedIso_inv_snd d V)
        conv_rhs => rw [Category.assoc]
        erw [hsnd]
        simp [MorphismProperty.Over.pullback_obj_hom])
  exact (d.isColimit V).ofIsoColimit iso.symm

end Affine

end AlgebraicGeometry
