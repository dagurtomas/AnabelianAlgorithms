/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/

import AnabelianAlgorithms.Linter.NonstandardAxioms
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Algebra.Category.Ring.Under.Property
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.RingHom.LocallyStandardSmooth
import AnabelianAlgorithms.Mathlib.FromPi1.FundamentalGroup.AffineAnd
import AnabelianAlgorithms.Mathlib.RingTheory.FiniteEtale.Equalizer


/-
This file was copied and adapted from Christian Merten's `pi1` project
(<https://github.com/chrisflav/pi1>), commit `5c5c0171efc863ce9990171bdf46d7cb5fd582fb`.
-/
/-!
# Finite étale morphisms

We say a morphism is finite étale if it is finite and étale. The category `FiniteEtale X` is
the category of finite etale schemes over `X`.
-/

set_option linter.nonstandardAxioms false

noncomputable section

universe u

open CategoryTheory Limits

namespace Algebra

end Algebra

namespace RingHom

/-- A ring homomorphism is finite étale if the induced algebra is finite étale. -/
def FiniteEtale {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.FiniteEtale R S

lemma finiteEtale_algebraMap_iff {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).FiniteEtale ↔ Algebra.FiniteEtale R S := by
  simp only [RingHom.FiniteEtale]
  congr!
  exact Algebra.algebra_ext _ _ fun _ ↦ rfl

namespace FiniteEtale

lemma iff_finite_and_etale
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    f.FiniteEtale ↔ f.Etale ∧ f.Finite := by
  rw [FiniteEtale, Finite, Etale]
  rw [Algebra.finiteEtale_iff]

lemma eq_and :
    @FiniteEtale = (fun R S (_ : CommRing R) (_ : CommRing S) f ↦ f.Etale ∧ f.Finite) := by
  ext
  rw [iff_finite_and_etale]

lemma isStableUnderBaseChange : IsStableUnderBaseChange FiniteEtale := by
  rw [eq_and]
  exact Etale.isStableUnderBaseChange.and finite_isStableUnderBaseChange

lemma respectsIso : RespectsIso FiniteEtale := by
  rw [eq_and]
  apply Etale.respectsIso.and finite_respectsIso

lemma hasFiniteProducts : HasFiniteProducts FiniteEtale := by
  introv R _ hf
  simp_rw [finiteEtale_algebraMap_iff] at hf ⊢
  constructor

lemma hasEqualizers : HasEqualizers FiniteEtale := by
  introv R hS hT
  rw [finiteEtale_algebraMap_iff] at hS hT ⊢
  apply Algebra.Etale.equalizer

/-- Finite étale morphisms have stable equalizers.

The hard tensor-equalizer input is isolated as
`Algebra.tensorEqualizer_bijective_of_finite_of_etale`. -/
lemma hasStableEqualizers : HasStableEqualizers FiniteEtale := by
  intro R S A B _ _ _ _ _ _ _ f g hA hB
  rw [finiteEtale_algebraMap_iff] at hA hB
  exact Algebra.tensorEqualizer_bijective_of_finite_of_etale f g

instance : (toMorphismProperty RingHom.FiniteEtale).IsStableUnderCobaseChange := by
  rw [isStableUnderCobaseChange_toMorphismProperty_iff]
  exact isStableUnderBaseChange

end FiniteEtale

end RingHom

namespace AlgebraicGeometry

/-- A morphism is finite étale if it is finite and étale. -/
@[mk_iff]
class IsFiniteEtale {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop
  extends IsFinite f, Etale f

namespace IsFiniteEtale

open MorphismProperty

lemma eq_inf : @IsFiniteEtale = (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) := by
  ext f
  rw [isFiniteEtale_iff]
  rfl

instance : IsMultiplicative @IsFiniteEtale := by
  rw [eq_inf]
  infer_instance

instance : IsStableUnderBaseChange @IsFiniteEtale := by
  rw [eq_inf]
  infer_instance

instance : HasOfPostcompProperty @IsFiniteEtale @IsFiniteEtale := by
  have : HasOfPostcompProperty @Etale (@IsFinite ⊓ @Etale) := by
    apply HasOfPostcompProperty.of_le (Q := @Etale) (W := @Etale)
    exact inf_le_right
  have : HasOfPostcompProperty @IsFinite (@IsFinite ⊓ @Etale) := by
    apply HasOfPostcompProperty.of_le (Q := @IsSeparated) (W := @IsFinite)
    intro X Y f hf
    haveI : IsFinite f := hf.1
    exact inferInstanceAs (IsSeparated f)
  rw [eq_inf]
  infer_instance

instance : HasAffineProperty @IsFiniteEtale (affineAnd RingHom.FiniteEtale) := by
  rw [HasAffineProperty.iff, eq_inf]
  constructor
  · infer_instance
  · ext X Y f _
    simp only [affineAnd_apply, RingHom.FiniteEtale.iff_finite_and_etale]
    change _ ↔ IsFinite f ∧ Etale f
    simp only [HasAffineProperty.iff_of_isAffine (P := @IsFinite), and_assoc, and_congr_right_iff]
    intro h
    rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
    rw [RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero, and_comm]

instance {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsFiniteEtale f] [IsFiniteEtale g] :
    IsFiniteEtale (f ≫ g) where

lemma mono_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFiniteEtale f] :
    Mono f ↔ IsOpenImmersion f ∧ IsClosedImmersion f := by
  refine ⟨fun hf ↦ ⟨IsOpenImmersion.of_flat_of_mono f, ?_⟩, fun ⟨hfo, _⟩ ↦ inferInstance⟩
  rw [IsClosedImmersion.iff_isFinite_and_mono]
  exact ⟨inferInstance, inferInstance⟩

end IsFiniteEtale

/-- The category of schemes finite étale over `X`. -/
def FiniteEtale (X : Scheme.{u}) : Type _ :=
  MorphismProperty.Over @IsFiniteEtale ⊤ X

namespace FiniteEtale

variable (X : Scheme.{u})

instance : Category (FiniteEtale X) :=
  inferInstanceAs <| Category (MorphismProperty.Over @IsFiniteEtale ⊤ X)

/-- The forgetful functor from schemes finite étale over `X` to schemes over `X`. -/
def forget : FiniteEtale X ⥤ Over X :=
  MorphismProperty.Over.forget @IsFiniteEtale ⊤ X

/-- The forgetful functor from schemes finite étale over `X` to schemes over `X` is fully
faithful. -/
def forgetFullyFaithful : (FiniteEtale.forget X).FullyFaithful :=
  MorphismProperty.Comma.forgetFullyFaithful _ _ _

instance : (FiniteEtale.forget X).Full :=
  inferInstanceAs <| (MorphismProperty.Comma.forget _ _ _ _ _).Full
instance : (FiniteEtale.forget X).Faithful :=
  inferInstanceAs <| (MorphismProperty.Comma.forget _ _ _ _ _).Faithful

instance : HasTerminal (FiniteEtale X) :=
  inferInstanceAs <| HasTerminal (MorphismProperty.Over
    (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X)

instance : HasPullbacks (FiniteEtale X) :=
  inferInstanceAs <| HasPullbacks (MorphismProperty.Over
    (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X)

instance (f : FiniteEtale X) : IsFiniteEtale f.hom := f.2

/-- The empty scheme is finite étale over every base. -/
instance initialTo_isFiniteEtale : IsFiniteEtale (initial.to X) where

/-- The empty finite étale cover of `X`. -/
noncomputable def empty : FiniteEtale X :=
  MorphismProperty.Over.mk ⊤ (initial.to X) inferInstance

/-- The unique morphism from the empty finite étale cover. -/
noncomputable def emptyTo (Y : FiniteEtale X) : empty X ⟶ Y := by
  refine MorphismProperty.Over.homMk (initial.to Y.left) ?_
  apply initial.hom_ext

noncomputable instance emptyUnique (Y : FiniteEtale X) : Unique (empty X ⟶ Y) where
  default := emptyTo X Y
  uniq f := by
    apply MorphismProperty.Over.Hom.ext
    apply initial.hom_ext

/-- Finite étale covers have an initial object: the empty cover. -/
noncomputable instance hasInitial : HasInitial (FiniteEtale X) := by
  haveI := emptyUnique X
  exact (IsInitial.ofUnique (empty X)).hasInitial

/-- Finite colimits of finite étale covers, via the affine-gluing theorem for properties
of the form `affineAnd Q`. -/
lemma hasFiniteColimits (X : Scheme.{u}) : HasFiniteColimits (FiniteEtale X) :=
  AffineAnd.hasFiniteColimits (@IsFiniteEtale : MorphismProperty Scheme.{u})
    RingHom.FiniteEtale.respectsIso
    RingHom.FiniteEtale.hasFiniteProducts
    RingHom.FiniteEtale.hasEqualizers

instance : HasFiniteColimits (FiniteEtale X) :=
  hasFiniteColimits X

lemma hasPushouts (X : Scheme.{u}) : HasPushouts (FiniteEtale X) := by
  haveI := hasFiniteColimits X
  infer_instance

instance : HasPushouts (FiniteEtale X) :=
  hasPushouts X

lemma hom_left_isFiniteEtale (f g : FiniteEtale X) (i : f ⟶ g) :
    IsFiniteEtale i.hom.left := by
  apply MorphismProperty.of_postcomp @IsFiniteEtale (W' := @IsFiniteEtale) i.hom.left g.hom
  · exact g.2
  · change IsFiniteEtale ((Over.Hom.left i.hom) ≫ Over.hom g.toComma)
    rw [CategoryTheory.Over.w i.hom]
    exact f.2

instance (f g : FiniteEtale X) (i : f ⟶ g) : IsFiniteEtale i.hom.left :=
  hom_left_isFiniteEtale X f g i

lemma mono_iff (f g : FiniteEtale X) (i : f ⟶ g) :
    Mono i ↔ IsOpenImmersion i.hom.left ∧ IsClosedImmersion i.hom.left := by
  rw [← IsFiniteEtale.mono_iff]
  constructor
  · intro hi
    letI := hi
    let F : FiniteEtale X ⥤ Scheme.{u} :=
      MorphismProperty.Over.forget (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X ⋙
        Over.forget X
    haveI : F.PreservesMonomorphisms :=
      inferInstanceAs ((MorphismProperty.Over.forget
        (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X ⋙ Over.forget X).PreservesMonomorphisms)
    exact show Mono (F.map i) from F.map_mono i
  · intro hi
    exact (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mono_of_mono_map (f := i) hi

variable {X}

abbrev pullback {Y : Scheme.{u}} (f : X ⟶ Y) : FiniteEtale Y ⥤ FiniteEtale X :=
  MorphismProperty.Over.pullback _ _ f

def mk {T : Scheme.{u}} (f : T ⟶ X) [IsFiniteEtale f] : FiniteEtale X :=
  MorphismProperty.Over.mk ⊤ f inferInstance

@[simp]
lemma mk_hom {T : Scheme.{u}} (f : T ⟶ X) [IsFiniteEtale f] : (mk f).hom = f := rfl

@[simp]
lemma mk_left {T : Scheme.{u}} (f : T ⟶ X) [IsFiniteEtale f] : (mk f).left = T := rfl

/-- The pullback of an empty finite étale cover has initial underlying scheme. -/
noncomputable def pullbackEmptyLeftIsInitial {Y : Scheme.{u}} (f : X ⟶ Y) :
    IsInitial ((pullback f).obj (empty Y)).left := by
  haveI : IsIso (Limits.pullback.fst (initial.to Y) f) := inferInstance
  exact initialIsInitial.ofIso (asIso (Limits.pullback.fst (initial.to Y) f)).symm

/-- The pullback of the empty finite étale cover is the empty finite étale cover. -/
noncomputable def pullbackEmptyIso {Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullback f).obj (empty Y) ≅ empty X where
  hom := by
    refine MorphismProperty.Over.homMk (Limits.pullback.fst (initial.to Y) f) ?_
    exact (pullbackEmptyLeftIsInitial f).hom_ext _ _
  inv := emptyTo X _
  hom_inv_id := by
    apply MorphismProperty.Over.Hom.ext
    exact (pullbackEmptyLeftIsInitial f).hom_ext _ _
  inv_hom_id := by
    apply MorphismProperty.Over.Hom.ext
    apply initial.hom_ext

lemma pullback_preservesInitial {Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesColimitsOfShape (Discrete PEmpty.{1}) (pullback f) := by
  haveI := emptyUnique X
  haveI := emptyUnique Y
  let eX : ⊥_ (FiniteEtale X) ≅ empty X :=
    initialIsInitial.uniqueUpToIso (IsInitial.ofUnique (empty X))
  let eY : ⊥_ (FiniteEtale Y) ≅ empty Y :=
    initialIsInitial.uniqueUpToIso (IsInitial.ofUnique (empty Y))
  haveI : PreservesColimit (Functor.empty.{0} (FiniteEtale Y)) (pullback f) :=
    preservesInitial_of_iso (pullback f)
      (eX ≪≫ (pullbackEmptyIso f).symm ≪≫ ((pullback f).mapIso eY).symm)
  exact preservesColimitsOfShape_pempty_of_preservesInitial (pullback f)

lemma pullback_preservesFiniteColimits {Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (pullback f) := by
  have (R S : CommRingCat.{u}) (f : R ⟶ S) :
      PreservesFiniteLimits
        (MorphismProperty.Under.pushout
          (RingHom.toMorphismProperty RingHom.FiniteEtale) ⊤ f) := by
    exact RingHom.HasStableEqualizers.preservesFiniteLimits_pushout
      RingHom.FiniteEtale.respectsIso
      RingHom.FiniteEtale.hasFiniteProducts
      RingHom.FiniteEtale.hasEqualizers
      RingHom.FiniteEtale.hasStableEqualizers
      f
  exact AffineAnd.preservesFiniteColimits_pullback
    (@IsFiniteEtale : MorphismProperty Scheme.{u})
    RingHom.FiniteEtale.respectsIso
    RingHom.FiniteEtale.hasFiniteProducts
    RingHom.FiniteEtale.hasEqualizers
    f

lemma pullback_preservesPushouts {Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesColimitsOfShape WalkingSpan (pullback f) := by
  haveI := pullback_preservesFiniteColimits f
  infer_instance

instance {Y : Scheme.{u}} (f : X ⟶ Y) :
    PreservesFiniteColimits (pullback f) :=
  pullback_preservesFiniteColimits f

end FiniteEtale

end AlgebraicGeometry
