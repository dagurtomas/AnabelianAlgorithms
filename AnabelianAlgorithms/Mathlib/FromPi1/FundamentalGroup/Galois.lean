/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import AnabelianAlgorithms.Linter.NonstandardAxioms
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.CategoryTheory.Limits.FintypeCat
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.Topology.Connected.CardComponents
import AnabelianAlgorithms.Mathlib.RingTheory.Ideal.Quotient.Operations
import AnabelianAlgorithms.Mathlib.FromPi1.FundamentalGroup.FiniteEtale


/-!
# The category of finite étale morphisms over a connected base is a Galois category

This file was copied and adapted from Christian Merten's `pi1` project
(<https://github.com/chrisflav/pi1>), commit `5c5c0171efc863ce9990171bdf46d7cb5fd582fb`.
Corresponding source file in that project: `Pi1/FundamentalGroup/Galois.lean`.

This is the ported scheme-level proof that finite étale covers form a pre-Galois category, and
that over a connected base they form a Galois category with the geometric fiber functor.  Since
this file was vendored, several auxiliary `pi1` compatibility imports have been replaced by direct
mathlib APIs or moved into `AnabelianAlgorithms/Mathlib`.  The remaining `FromPi1` dependencies
are the scheme-level finite-étale category and finite-colimit/gluing construction in
`FiniteEtale`, `AffineAnd`, and `AffineColimits`.
-/

-- set_option linter.nonstandardAxioms false

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits TopologicalSpace

instance {C : Type*} [Category C] {G : Type*} [Group G] [Finite G] [HasFiniteColimits C] :
    HasColimitsOfShape (SingleObj G) C := by
  obtain ⟨G', hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.hasColimitsOfShape_of_equivalence e.toSingleObjEquiv.symm

instance {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {G : Type*} [Group G]
    [Finite G] [PreservesFiniteColimits F] : PreservesColimitsOfShape (SingleObj G) F := by
  obtain ⟨(G' : Type), hg, hf, ⟨e⟩⟩ := Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.preservesColimitsOfShape_of_equiv e.toSingleObjEquiv.symm F

namespace AlgebraicGeometry
namespace FiniteEtale

variable (X : Scheme.{u})

/-- The category of finite étale morphisms is a pre-Galois category.

This follows from finite colimits of finite étale covers and the open-and-closed complement
construction for monomorphisms. -/
instance preGaloisCategory (X : Scheme.{u}) : PreGaloisCategory (FiniteEtale X) where
  hasQuotientsByFiniteGroups G := inferInstance
  monoInducesIsoOnDirectSummand {f g} i hi := by
    rw [FiniteEtale.mono_iff] at hi
    obtain ⟨ho, hc⟩ := hi
    haveI : IsOpenImmersion i.hom.left := ho
    haveI : IsClosedImmersion i.hom.left := hc
    let A : Set g.left := Set.range i.hom.left.base
    have hA : IsClosed A := i.hom.left.isClosedEmbedding.isClosed_range
    let U : g.left.Opens := ⟨Aᶜ, hA.isOpen_compl⟩
    haveI : IsClosedImmersion U.ι := by
      apply IsClosedImmersion.of_isPreimmersion
      simp only [Scheme.Opens.range_ι, TopologicalSpace.Opens.coe_mk, isClosed_compl_iff, U, A]
      apply IsOpenImmersion.isOpen_range
    haveI : IsOpenImmersion U.ι := inferInstance
    haveI : IsFinite (U.ι ≫ g.hom) := by
      apply MorphismProperty.comp_mem
      · exact inferInstance
      · exact g.2.toIsFinite
    haveI : Etale (U.ι ≫ g.hom) := by
      apply MorphismProperty.comp_mem
      · exact inferInstance
      · exact g.2.toEtale
    let u : FiniteEtale X := ⟨Over.mk (U.ι ≫ g.hom), by
      change IsFiniteEtale (U.ι ≫ g.hom)
      exact ⟨⟩⟩
    refine ⟨u, MorphismProperty.Over.homMk U.ι, ⟨?_⟩⟩
    apply isColimitOfReflects (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _)
    apply (isColimitMapCoconeBinaryCofanEquiv _ _ _).invFun
    simp only [Functor.comp_obj, MorphismProperty.Comma.forget_obj, Over.forget_obj,
      Functor.comp_map, MorphismProperty.Comma.forget_map, Over.forget_map,
      MorphismProperty.Over.homMk_hom, Over.homMk_left]
    apply Nonempty.some
    change Nonempty (IsColimit <| BinaryCofan.mk i.hom.left U.ι)
    apply nonempty_isColimit_binaryCofanMk_of_isCompl
    constructor
    · rw [disjoint_iff]
      ext : 1
      simp [U, A]
    · rw [codisjoint_iff]
      ext : 1
      simp [U, A]

lemma finite_of_isEtale_of_isAffineHom (X : Scheme.{u}) {Ω : Type u} [Field Ω]
    (f : X ⟶ Spec (.of Ω)) [Etale f] [IsAffineHom f] : Finite X := by
  have : IsAffine X := isAffine_of_isAffineHom f
  have : Etale f := inferInstance
  rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)] at this
  let e : Γ(Spec (CommRingCat.of Ω), ⊤) ≃+* Ω :=
    (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv
  algebraize [(f.appTop.hom.comp e.symm.toRingHom)]
  have : Algebra.Etale Ω Γ(X, ⊤) := by
    change (f.appTop.hom.comp e.symm.toRingHom).Etale
    apply RingHom.Etale.respectsIso.2
    assumption
  rw [Algebra.Etale.iff_exists_algEquiv_prod Ω Γ(X, ⊤)] at this
  obtain ⟨I, hI, Ai, _, _, eq, h⟩ := this
  let eq2 : X ≅ ∐ fun i ↦ Spec (.of (Ai i)) :=
    X.isoSpec ≪≫ Scheme.Spec.mapIso eq.toRingEquiv.symm.toCommRingCatIso.op ≪≫
      (asIso (sigmaSpec (fun i ↦ .of (Ai i)))).symm
  let eq3 : X ≃ Σ i, Spec (.of <| Ai i) :=
    eq2.schemeIsoToHomeo.trans (sigmaMk _).symm
  apply Finite.of_equiv _ eq3.symm

instance {Ω : Type u} [Field Ω] (X : FiniteEtale (Spec (.of Ω))) : Fintype X.left := by
  let f : X.left ⟶ Spec (.of Ω) := X.hom
  haveI : Etale f := by
    dsimp [f]
    exact X.2.toEtale
  haveI : IsAffineHom f := by
    dsimp [f]
    exact X.2.toIsFinite.toIsAffineHom
  have : Finite X.left := finite_of_isEtale_of_isAffineHom X.left f
  exact Fintype.ofFinite X.left

/-- The forgetful functor from finite étale schemes over a field to finite types.

This is copied from `pi1`: it sends a finite étale cover of `Spec Ω` to its underlying finite set of
points. -/
@[simps]
def forgetScheme (Ω : Type u) [Field Ω] :
    FiniteEtale (Spec (.of Ω)) ⥤ FintypeCat.{u} where
  obj X := FintypeCat.of X.left
  map {X Y} f := { hom := TypeCat.ofHom (⇑f.left : X.left → Y.left) }

variable (Ω : Type u) [Field Ω]

lemma _root_.AlgebraicGeometry.IsFiniteEtale.SpecMap_iff {R S : CommRingCat.{u}} {f : R ⟶ S} :
    IsFiniteEtale (Spec.map f) ↔ f.hom.FiniteEtale := by
  have := RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.FiniteEtale.respectsIso
  simp only [HasAffineProperty.iff_of_isAffine (P := @IsFiniteEtale), affineAnd, and_iff_right]
  exact MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty RingHom.FiniteEtale)
    (arrowIsoΓSpecOfIsAffine f).symm

instance instSpecMapPi {ι : Type u} [Finite ι] (R : Type u) [CommRing R] :
    IsFiniteEtale (Spec.map <| CommRingCat.ofHom <| algebraMap R (ι → R)) := by
  rw [_root_.AlgebraicGeometry.IsFiniteEtale.SpecMap_iff]
  simp only [ConcreteCategory.hom_ofHom]
  rw [RingHom.finiteEtale_algebraMap_iff]
  constructor

@[simps]
def inventScheme (Ω : Type u) [Field Ω] : FintypeCat.{u} ⥤ FiniteEtale (Spec (.of Ω)) where
  obj S :=
    mk (Spec.map <| CommRingCat.ofHom <| algebraMap Ω (S → Ω))
  map {S T} f :=
    MorphismProperty.Over.homMk
      (Spec.map <| CommRingCat.ofHom <| RingHom.pi (fun s ↦ Pi.evalRingHom _ (f s))) <| by
      dsimp
      rw [← Spec.map_comp]
      rfl
  map_id S := by
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom (RingHom.pi fun s ↦ Pi.evalRingHom (fun _ ↦ Ω) s)) =
      𝟙 (Spec (.of (S.obj → Ω)))
    rw [← Spec.map_id]
    congr 1
  map_comp {S T W} f g := by
    apply MorphismProperty.Over.Hom.ext
    change Spec.map (CommRingCat.ofHom
        (RingHom.pi fun s ↦ Pi.evalRingHom (fun _ ↦ Ω) (g (f s)))) =
      Spec.map (CommRingCat.ofHom (RingHom.pi fun s ↦ Pi.evalRingHom (fun _ ↦ Ω) (f s))) ≫
        Spec.map (CommRingCat.ofHom (RingHom.pi fun s ↦ Pi.evalRingHom (fun _ ↦ Ω) (g s)))
    rw [← Spec.map_comp]
    congr 1

instance instFintypeSpecPi (S : FintypeCat.{u}) :
    Fintype (Spec (CommRingCat.of (S.obj → Ω))).toPresheafedSpace :=
  let f : Spec (CommRingCat.of (S.obj → Ω)) ⟶ Spec (.of Ω) :=
    Spec.map (CommRingCat.ofHom <| algebraMap Ω _)
  have : Etale f := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    simp only [CommRingCat.hom_ofHom, RingHom.etale_algebraMap]
    infer_instance
  have : Finite (Spec (CommRingCat.of (S.obj → Ω))).toPresheafedSpace :=
    finite_of_isEtale_of_isAffineHom _ f
  Fintype.ofFinite _

def specPiEquiv (ι : Type u) [Finite ι] (K : Type u) [Field K] :
    Spec (.of (ι → K)) ≃ ι :=
  ((asIso (sigmaSpec (fun _ : ι ↦ .of K))).schemeIsoToHomeo.toEquiv.symm.trans
      (sigmaMk (fun _ : ι ↦ Spec (.of K))).toEquiv.symm).trans
    (Equiv.sigmaUnique ι (fun _ : ι ↦ Spec (.of K)))

@[simp]
lemma specPiEquiv_symm_apply (ι : Type u) [Finite ι] (K : Type u) [Field K]
    (i : ι) : (specPiEquiv ι K).symm i =
      (Spec.map <| CommRingCat.ofHom <| Pi.evalRingHom _ i).base default := by
  simp [specPiEquiv, Iso.schemeIsoToHomeo, ← Scheme.Hom.comp_apply]

def inventForgetIso : inventScheme Ω ⋙ forgetScheme Ω ≅ 𝟭 FintypeCat :=
  Iso.symm <| NatIso.ofComponents
    (fun S ↦ FintypeCat.equivEquivIso (specPiEquiv S Ω).symm)
    (fun {S T} f ↦ by
      ext x
      change (specPiEquiv T.obj Ω).symm (f x) =
        (Spec.map (CommRingCat.ofHom
          (RingHom.pi fun s ↦ Pi.evalRingHom (fun _ ↦ Ω) (f s)))).base
            ((specPiEquiv S.obj Ω).symm x)
      rw [specPiEquiv_symm_apply]
      rw [specPiEquiv_symm_apply]
      rw [← Scheme.Hom.comp_apply, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl)

instance instAlgebraSection (X : Scheme.{u}) (R : CommRingCat.{u}) [X.Over (Spec R)]
    (U : X.Opens) : Algebra R Γ(X, U) :=
  ((((X ↘ Spec R)).appLE ⊤ U (by simp)).hom.comp
    (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm.toRingHom).toAlgebra

instance instAlgebraSectionOfType (X : Scheme.{u}) (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] (U : X.Opens) : Algebra R Γ(X, U) :=
  ((((X ↘ Spec (.of R))).appLE ⊤ U (by simp)).hom.comp
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.toRingHom).toAlgebra

@[simp]
lemma _root_.CategoryTheory.Iso.commRingCatIsoToRingEquiv_symm_apply {R S : CommRingCat.{u}}
    (e : R ≅ S) (x : S) :
    e.commRingCatIsoToRingEquiv.symm x = e.symm.hom x := rfl

@[simp]
lemma _root_.CategoryTheory.Iso.commRingCatIsoToRingEquiv_symm_toRingHom {R S : CommRingCat.{u}}
    (e : R ≅ S) :
    e.commRingCatIsoToRingEquiv.symm = e.symm.hom.hom := rfl

lemma appLE_comp_algebraMap {X Y : Scheme.{u}} (f : X ⟶ Y) (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] [Y.Over (Spec (.of R))] [f.IsOver (Spec (.of R))]
    (U : Y.Opens) (V : X.Opens) (hUV : V ≤ f ⁻¹ᵁ U) :
    (f.appLE U V hUV).hom.comp (algebraMap R Γ(Y, U)) = algebraMap R Γ(X, V) := by
  have hcomp : (Y ↘ Spec (.of R)).appLE ⊤ U (by simp) ≫ f.appLE U V hUV =
      (X ↘ Spec (.of R)).appLE ⊤ V (by simp) := by
    rw [Scheme.Hom.appLE_comp_appLE]
    have hfg : f ≫ Y ↘ Spec (.of R) = X ↘ Spec (.of R) :=
      (Scheme.Hom.isOver_iff (S := Spec (.of R))).mp inferInstance
    rw [hfg]
  ext r
  change ((Y ↘ Spec (.of R)).appLE ⊤ U (by simp) ≫ f.appLE U V hUV).hom
      ((Scheme.ΓSpecIso (.of R)).inv.hom r) =
    ((X ↘ Spec (.of R)).appLE ⊤ V (by simp)).hom
      ((Scheme.ΓSpecIso (.of R)).inv.hom r)
  rw [hcomp]

instance instAlgebraEtaleTop (X : Scheme.{u}) (R : Type u) [CommRing R]
    [X.Over (Spec (.of R))] [Etale (X ↘ Spec (.of R))]
    [IsAffineHom (X ↘ Spec (.of R))] : Algebra.Etale R Γ(X, ⊤) := by
  rw [← RingHom.etale_algebraMap, RingHom.algebraMap_toAlgebra]
  apply RingHom.Etale.respectsIso.2
  let f : X ⟶ Spec (.of R) := X ↘ Spec (.of R)
  have happ : f.appLE ⊤ ⊤ (by simp) = f.app ⊤ := by
    simpa [f] using (Scheme.Hom.appLE_eq_app (f := f) (U := ⊤))
  rw [happ]
  change (CommRingCat.Hom.hom (Scheme.Hom.appTop (X ↘ Spec (.of R)))).Etale
  have : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of R))
  apply HasRingHomProperty.appTop @Etale
  infer_instance

instance instModuleFiniteTop (X : Scheme.{u}) (R : Type u) [Field R]
    [X.Over (Spec (.of R))] [Etale (X ↘ Spec (.of R))]
    [IsAffineHom (X ↘ Spec (.of R))] : Module.Finite R Γ(X, ⊤) :=
  Algebra.FormallyUnramified.finite_of_free R Γ(X, ⊤)

def _root_.AlgebraicGeometry.IsFiniteEtale.isoSpecPi (X : Scheme.{u}) [X.Over (Spec (.of Ω))]
    [IsFiniteEtale (X ↘ Spec (.of Ω))] :
    X ≅ Spec (.of <| Π (m : MaximalSpectrum Γ(X, ⊤)), Γ(X, ⊤) ⧸ m.asIdeal) :=
  have : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of Ω))
  have := Algebra.FormallyUnramified.finite_of_free Ω Γ(X, ⊤)
  have := Algebra.FormallyUnramified.isReduced_of_field Ω Γ(X, ⊤)
  have : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower Ω inferInstance
  X.isoSpec ≪≫ Scheme.Spec.mapIso ((IsArtinianRing.equivPi _).symm.toCommRingCatIso).op

@[simp]
lemma appTop_left_comp_algebraMap {X Y : FiniteEtale (Spec <| .of Ω)} (f : X ⟶ Y) :
    f.left.appTop.hom.comp (algebraMap Ω Γ(Y.left, ⊤)) = algebraMap Ω Γ(X.left, ⊤) := by
  simp [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, appLE_comp_algebraMap]

@[simp]
lemma appTop_left_algebraMap {X Y : FiniteEtale (Spec <| .of Ω)} (f : X ⟶ Y) (x : Ω) :
    f.left.appTop.hom (algebraMap Ω Γ(Y.left, ⊤) x) = algebraMap Ω Γ(X.left, ⊤) x :=
  DFunLike.congr_fun (appTop_left_comp_algebraMap Ω f) x

instance instFiniteEtaleHom {S : Scheme.{u}} (X : FiniteEtale S) : IsFiniteEtale (X.left ↘ S) :=
  X.prop

instance instArtinianFiniteEtaleField (X : FiniteEtale (Spec (.of Ω))) :
    IsArtinianRing Γ(X.left, ⊤) :=
  isArtinian_of_tower Ω inferInstance

instance instReducedFiniteEtaleField (X : FiniteEtale (Spec (.of Ω))) :
    _root_.IsReduced Γ(X.left, ⊤) :=
  Algebra.FormallyUnramified.isReduced_of_field Ω Γ(X.left, ⊤)

def _root_.AlgebraicGeometry.IsFiniteEtale.isoSpecFun [IsSepClosed Ω] (X : Scheme.{u})
    [X.Over (Spec (.of Ω))] [IsFiniteEtale (X ↘ Spec (.of Ω))] :
    X ≅ Spec (.of <| X → Ω) :=
  have : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of Ω))
  let i1 := _root_.AlgebraicGeometry.IsFiniteEtale.isoSpecPi Ω X
  have : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower Ω inferInstance
  let e : X ≃ MaximalSpectrum Γ(X, ⊤) :=
    X.isoSpec.schemeIsoToHomeo.toEquiv.trans IsArtinianRing.primeSpectrumEquivMaximalSpectrum
  let R := Γ(X, ⊤)
  have : _root_.IsReduced R :=
    Algebra.FormallyUnramified.isReduced_of_field Ω R
  let eo : Γ(X, ⊤) ≃ₐ[Ω] _ := (IsArtinianRing.equivPi R).restrictScalars Ω
  have : Algebra.FormallyEtale Ω (Π (m : MaximalSpectrum R), (R ⧸ m.asIdeal)) :=
    Algebra.FormallyEtale.of_equiv eo
  have (m : MaximalSpectrum R) : Algebra.FormallyEtale Ω (R ⧸ m.asIdeal) := by
    rw [Algebra.FormallyEtale.pi_iff] at this
    exact this m
  let _ (m : MaximalSpectrum R) : Field (Γ(X, ⊤) ⧸ m.asIdeal) :=
    Ideal.Quotient.field m.asIdeal
  have (m : MaximalSpectrum R) : Algebra.IsSeparable Ω (R ⧸ m.asIdeal) := by
    rw [← Algebra.FormallyEtale.iff_isSeparable]
    infer_instance
  have hb (m : MaximalSpectrum R) :
      Function.Bijective (algebraMap Ω (Γ(X, ⊤) ⧸ m.asIdeal)) :=
    ⟨FaithfulSMul.algebraMap_injective _ _,
      IsSepClosed.algebraMap_surjective Ω (R ⧸ m.asIdeal)⟩
  let a (m : MaximalSpectrum R) : Γ(X, ⊤) ⧸ m.asIdeal ≃+* Ω :=
    (RingEquiv.ofBijective _ (hb m)).symm
  let o :
      (Π (m : MaximalSpectrum Γ(X, ⊤)), Γ(X, ⊤) ⧸ m.asIdeal) ≃+* (X → Ω) :=
    (RingEquiv.piCongrRight a).trans (RingEquiv.piCongrLeft (fun _ ↦ Ω) e.symm)
  i1 ≪≫ Scheme.Spec.mapIso o.toCommRingCatIso.symm.op

lemma algEquiv_symm_toRingEquiv_apply {R A B : Type*} [CommSemiring R]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
    (e : A ≃ₐ[R] B) (x : B) : e.symm.toRingEquiv x = e.symm x := rfl

-- lemma _root_.IsArtinianRing.equivPi_apply (R : Type*) [CommRing R] [IsArtinianRing R]
--     [_root_.IsReduced R] (x : R) (m : MaximalSpectrum R) :
--     (IsArtinianRing.equivPi R x) m = Ideal.Quotient.mk m.asIdeal x := rfl

@[reassoc (attr := simp)]
lemma _root_.AlgebraicGeometry.IsFiniteEtale.isoSpecFun_hom_SpecMap [IsSepClosed Ω]
    (X : Scheme.{u}) [X.Over (Spec (.of Ω))] [IsFiniteEtale (X ↘ Spec (.of Ω))] :
    (_root_.AlgebraicGeometry.IsFiniteEtale.isoSpecFun Ω X).hom ≫
      Spec.map (CommRingCat.ofHom <| algebraMap Ω (X → Ω)) = X ↘ Spec (.of Ω) := by
  have : IsAffine X := isAffine_of_isAffineHom (X ↘ Spec (.of Ω))
  rw [← cancel_epi X.isoSpec.inv]
  conv_rhs => rw [← Scheme.isoSpec_inv_naturality]
  simp only [_root_.AlgebraicGeometry.IsFiniteEtale.isoSpecFun,
    _root_.AlgebraicGeometry.IsFiniteEtale.isoSpecPi, Iso.trans_assoc, Iso.trans_hom,
    Functor.mapIso_hom, Iso.op_hom, RingEquiv.toCommRingCatIso_hom, Scheme.Spec_map,
    Quiver.Hom.unop_op, Iso.symm_hom, RingEquiv.toCommRingCatIso_inv, Category.assoc,
    Iso.inv_hom_id_assoc, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  congr 1
  have : IsArtinianRing Γ(X, ⊤) := isArtinian_of_tower Ω inferInstance
  have : _root_.IsReduced ↑Γ(X, ⊤) := Algebra.FormallyUnramified.isReduced_of_field Ω Γ(X, ⊤)
  ext x
  dsimp
  apply (IsArtinianRing.equivPi Γ(X, ⊤)).injective
  ext j
  simp only [AlgEquiv.apply_symm_apply, RingEquiv.piCongrRight_apply,
    RingEquiv.piCongrLeft_symm_apply, Equiv.symm_symm, RingEquiv.piCongrLeft'_apply,
    Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    RingEquiv.coe_ofBijective]
  rw [_root_.IsArtinianRing.equivPi_apply]
  change (Ideal.Quotient.mk j.asIdeal)
      ((((X ↘ Spec (.of Ω)).appLE ⊤ ⊤ (by simp)).hom.comp
        (Scheme.ΓSpecIso (.of Ω)).commRingCatIsoToRingEquiv.symm.toRingHom) x) =
    (Ideal.Quotient.mk j.asIdeal)
      ((CommRingCat.Hom.hom (Scheme.Hom.appTop (X ↘ Spec (CommRingCat.of Ω))))
        ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv) x))
  have happ : (X ↘ Spec (.of Ω)).appLE ⊤ ⊤ (by simp) =
      (X ↘ Spec (.of Ω)).app ⊤ := by
    simpa using (Scheme.Hom.appLE_eq_app (f := X ↘ Spec (.of Ω)) (U := ⊤))
  rw [happ]
  rfl

lemma _root_.IsArtinianRing.equivPi_naturality_apply (R S : Type*) [CommRing R] [CommRing S]
    [IsArtinianRing R] [IsArtinianRing S] [_root_.IsReduced R] [_root_.IsReduced S]
    (f : R →+* S) (x : R) :
    IsArtinianRing.equivPi S (f x) =
      RingHom.pi
        (fun m ↦ RingHom.comp
          (by exact Ideal.quotientMap m.asIdeal f (by simp))
          (Pi.evalRingHom _ ⟨Ideal.comap f m.asIdeal, IsArtinianRing.isMaximal_of_isPrime _⟩))
        (IsArtinianRing.equivPi R x) := by
  ext m
  simp [IsArtinianRing.equivPi, IsArtinianRing.quotNilradicalEquivPi]

instance (priority := 900) instIsAffineFiniteEtaleOfAffine [IsAffine X] (Y : FiniteEtale X) :
    IsAffine Y.left := by
  let f : Y.left ⟶ X := Y.hom
  haveI : IsAffineHom f := by
    dsimp [f]
    exact Y.2.toIsFinite.toIsAffineHom
  exact isAffine_of_isAffineHom f

set_option maxHeartbeats 400000 in
-- The naturality proof unfolds the explicit affine equivalence between finite étale covers over a
-- separably closed field and finite sets.
def forgetInventIso [IsSepClosed Ω] : 𝟭 (FiniteEtale _) ≅ forgetScheme Ω ⋙ inventScheme Ω :=
  NatIso.ofComponents (fun X ↦
    (MorphismProperty.Over.isoMk (_root_.AlgebraicGeometry.IsFiniteEtale.isoSpecFun Ω X.left) (by
      change (_root_.AlgebraicGeometry.IsFiniteEtale.isoSpecFun Ω X.left).hom ≫
          Spec.map (CommRingCat.ofHom <| algebraMap Ω (X.left → Ω)) = X.hom
      exact
        _root_.AlgebraicGeometry.IsFiniteEtale.isoSpecFun_hom_SpecMap Ω X.left))) <|
    fun {X Y} f ↦ by
      apply MorphismProperty.Over.Hom.ext
      change f.left ≫ (_root_.AlgebraicGeometry.IsFiniteEtale.isoSpecFun Ω Y.left).hom =
        (_root_.AlgebraicGeometry.IsFiniteEtale.isoSpecFun Ω X.left).hom ≫
          Spec.map (CommRingCat.ofHom <| RingHom.pi
            (fun s : X.left ↦ Pi.evalRingHom (fun _ : Y.left ↦ Ω) (f.left.base s)))
      simp only [_root_.AlgebraicGeometry.IsFiniteEtale.isoSpecFun, Iso.trans_hom,
        Functor.mapIso_hom, Iso.op_hom, Iso.symm_hom, RingEquiv.toCommRingCatIso_inv,
        Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc]
      simp only [_root_.AlgebraicGeometry.IsFiniteEtale.isoSpecPi, Iso.trans_hom,
        Functor.mapIso_hom, Iso.op_hom, RingEquiv.toCommRingCatIso_hom,
        Scheme.Spec_map, Quiver.Hom.unop_op, Category.assoc]
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rw [← Spec.map_comp, ← Spec.map_comp]
      rw [← Scheme.isoSpec_hom_naturality_assoc, ← Spec.map_comp]
      congr 2
      ext x
      simp only [CommRingCat.ofHom_comp, Category.assoc, CommRingCat.hom_comp,
        CommRingCat.hom_ofHom, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        RingEquiv.symm_trans_apply, RingEquiv.piCongrRight_symm, RingEquiv.symm_symm]
      apply (IsArtinianRing.equivPi Γ(X.left, ⊤)).injective
      ext j
      simp only [algEquiv_symm_toRingEquiv_apply, AlgEquiv.apply_symm_apply,
        RingEquiv.piCongrRight_apply, RingEquiv.piCongrLeft_symm_apply, Equiv.symm_symm,
        RingEquiv.piCongrLeft'_apply, Equiv.symm_trans_apply, Homeomorph.coe_symm_toEquiv,
        RingHom.pi_apply, Pi.evalRingHom_apply, RingEquiv.coe_ofBijective]
      rw [_root_.IsArtinianRing.equivPi_naturality_apply]
      simp only [AlgEquiv.apply_symm_apply, RingHom.pi_apply, RingHom.coe_comp, Function.comp_apply,
        Pi.evalRingHom_apply, RingEquiv.piCongrRight_apply, RingEquiv.piCongrLeft_symm_apply,
        Equiv.symm_symm, RingEquiv.piCongrLeft'_apply, Equiv.symm_trans_apply,
        Homeomorph.coe_symm_toEquiv, RingEquiv.coe_ofBijective, Ideal.quotientMap_algebraMap,
        appTop_left_algebraMap, Ideal.Quotient.mk_algebraMap, algebraMap.coe_inj]
      congr 1
      simp only [Iso.schemeIsoToHomeo, Scheme.homeoOfIso_symm, Scheme.homeoOfIso_apply,
        Iso.symm_hom]
      rw [← Scheme.Hom.comp_apply, ← Scheme.isoSpec_inv_naturality]
      rfl

def equivFintypeCat [IsSepClosed Ω] : FiniteEtale (Spec <| .of Ω) ≌ FintypeCat.{u} :=
  CategoryTheory.Equivalence.mk (forgetScheme Ω) (inventScheme Ω)
    (forgetInventIso Ω) (inventForgetIso Ω)

instance instForgetSchemeIsEquivalence [IsSepClosed Ω] : (forgetScheme Ω).IsEquivalence :=
  (equivFintypeCat Ω).isEquivalence_functor


variable {X}
variable {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- The fiber functor at a geometric point. -/
def fiber : FiniteEtale X ⥤ FintypeCat.{u} :=
  pullback ξ ⋙ forgetScheme Ω

/-- The point of the underlying finite étale cover corresponding to an element of the fiber. -/
def fiberPt {A : FiniteEtale X} (x : (fiber ξ).obj A) : A.left :=
  (Limits.pullback.fst A.hom ξ).base x

omit [IsSepClosed Ω] in
lemma pullback_preservesFiniteLimits : PreservesFiniteLimits (pullback ξ) :=
  inferInstanceAs <| PreservesFiniteLimits
    (MorphismProperty.Over.pullback (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ ξ)

attribute [instance] pullback_preservesFiniteLimits

lemma fiber_preservesFiniteLimits : PreservesFiniteLimits (fiber ξ) := by
  dsimp [fiber]
  exact Limits.comp_preservesFiniteLimits _ _

attribute [instance] fiber_preservesFiniteLimits

/-- Connected components of a locally connected space form a discrete space. -/
instance discreteTopology_connectedComponents (T : Type*) [TopologicalSpace T]
    [LocallyConnectedSpace T] : DiscreteTopology (ConnectedComponents T) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro i
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
  rw [← ConnectedComponents.isQuotientMap_coe.isOpen_preimage,
    connectedComponents_preimage_singleton]
  exact isOpen_connectedComponent

/-- The open subscheme associated to a connected component. -/
def _root_.AlgebraicGeometry.Scheme.connCompOpen {X : Scheme.{u}}
    [Finite (_root_.ConnectedComponents X)]
    (i : _root_.ConnectedComponents X) : X.Opens :=
  ⟨ConnectedComponents.mk ⁻¹' {i}, by
    rw [ConnectedComponents.isQuotientMap_coe.isOpen_preimage]
    exact isOpen_discrete {i}⟩

instance connectedSpace_connCompOpen {X : Scheme.{u}} [Finite (_root_.ConnectedComponents X)]
    (i : _root_.ConnectedComponents X) :
    ConnectedSpace (X.connCompOpen i) := by
  apply isConnected_iff_connectedSpace.mp
  simp only [Scheme.connCompOpen, TopologicalSpace.Opens.coe_mk]
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
  rw [connectedComponents_preimage_singleton]
  exact isConnected_connectedComponent

instance nonempty_connCompOpen {X : Scheme.{u}} [Finite (_root_.ConnectedComponents X)]
    (i : _root_.ConnectedComponents X) : Nonempty (X.connCompOpen i) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe i
  exact ⟨⟨x, by simp [Scheme.connCompOpen]⟩⟩

instance isClosedImmersion_connCompOpen {X : Scheme.{u}}
    [Finite (_root_.ConnectedComponents X)] (i : _root_.ConnectedComponents X) :
    IsClosedImmersion (X.connCompOpen i).ι where
  isClosedEmbedding := ⟨(X.connCompOpen i).ι.isOpenEmbedding.isEmbedding, by
    rw [Scheme.Opens.range_ι]
    change IsClosed (ConnectedComponents.mk ⁻¹' ({i} : Set (_root_.ConnectedComponents X)))
    rw [ConnectedComponents.isQuotientMap_coe.isClosed_preimage]
    exact isClosed_discrete {i}⟩

lemma _root_.AlgebraicGeometry.IsFiniteEtale.surjective_of_preconnected
    {X Y : Scheme.{u}} (f : X ⟶ Y) [PreconnectedSpace Y] [Nonempty X]
    [IsFiniteEtale f] : Surjective f := by
  rw [← Scheme.Hom.one_le_finrank_iff_surjective]
  obtain ⟨x⟩ := ‹Nonempty X›
  intro y
  rw [(f.isLocallyConstant_finrank).apply_eq_of_preconnectedSpace y (f.base x)]
  apply Scheme.Hom.one_le_finrank_map

instance finite_connectedComponents [ConnectedSpace X] (Y : FiniteEtale X) :
    Finite (_root_.ConnectedComponents Y.left) := by
  have : Finite (_root_.ConnectedComponents
      ↑↑((Functor.fromPUnit X).obj Y.right).toPresheafedSpace) := by
    change Finite (_root_.ConnectedComponents X)
    infer_instance
  exact Y.hom.isOpenMap.finite_connectedComponents_of_finite_preimage_singleton Y.hom.isClosedMap
    Y.hom.continuous (fun y ↦ Scheme.Hom.finite_preimage_singleton _ y)

lemma connCompOpen_comp_isFiniteEtale [ConnectedSpace X] (Y : FiniteEtale X)
    (i : _root_.ConnectedComponents Y.left) :
    IsFiniteEtale ((Y.left.connCompOpen i).ι ≫ Y.hom) := by
  haveI : IsFiniteEtale (Y.left.connCompOpen i).ι := IsFiniteEtale.mk
  haveI : IsFinite ((Y.left.connCompOpen i).ι ≫ Y.hom) := by
    apply MorphismProperty.comp_mem
    · infer_instance
    · exact Y.prop.toIsFinite
  haveI : Etale ((Y.left.connCompOpen i).ι ≫ Y.hom) := by
    apply MorphismProperty.comp_mem
    · infer_instance
    · exact Y.prop.toEtale
  exact IsFiniteEtale.mk

lemma connCompOpen_comp_surjective [ConnectedSpace X] (Y : FiniteEtale X)
    (i : _root_.ConnectedComponents Y.left) :
    Surjective ((Y.left.connCompOpen i).ι ≫ Y.hom) := by
  haveI : IsFiniteEtale ((Y.left.connCompOpen i).ι ≫ Y.hom) :=
    connCompOpen_comp_isFiniteEtale Y i
  have : PreconnectedSpace ↑↑((Functor.fromPUnit X).obj Y.right).toPresheafedSpace := by
    change PreconnectedSpace X
    infer_instance
  exact IsFiniteEtale.surjective_of_preconnected _

lemma connCompOpen_fiber_nonempty [ConnectedSpace X]
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X) (Y : FiniteEtale X)
    (i : _root_.ConnectedComponents Y.left) :
    Nonempty ↑(Limits.pullback ((Y.left.connCompOpen i).ι ≫ Y.hom) ξ : Scheme.{u}) := by
  let q := (Y.left.connCompOpen i).ι ≫ Y.hom
  letI : IsFiniteEtale q := connCompOpen_comp_isFiniteEtale Y i
  obtain ⟨y⟩ : Nonempty (Spec (.of Ω)) := inferInstance
  have hsurj : Surjective q := connCompOpen_comp_surjective Y i
  obtain ⟨z, hz⟩ := q.surjective (ξ.base y)
  obtain ⟨o, _⟩ := Scheme.Pullback.exists_preimage_pullback z y hz
  exact ⟨o⟩

lemma exists_fiberPoint_same_connectedComponent [ConnectedSpace X]
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X) (Y : FiniteEtale X) (b : Y.left) :
    ∃ t : (Limits.pullback Y.hom ξ : Scheme.{u}),
      _root_.ConnectedComponents.mk ((pullback.fst Y.hom ξ).base t) =
        _root_.ConnectedComponents.mk b := by
  let i : _root_.ConnectedComponents Y.left := _root_.ConnectedComponents.mk b
  have hne : Nonempty ↑(Limits.pullback ((Y.left.connCompOpen i).ι ≫ Y.hom) ξ : Scheme.{u}) :=
    connCompOpen_fiber_nonempty ξ Y i
  obtain ⟨z⟩ := hne
  let t : (Limits.pullback Y.hom ξ : Scheme.{u}) :=
    pullback.map ((Y.left.connCompOpen i).ι ≫ Y.hom) ξ Y.hom ξ
      (Y.left.connCompOpen i).ι (𝟙 _) (𝟙 _) (by simp) (by simp) z
  refine ⟨t, ?_⟩
  let m := pullback.map ((Y.left.connCompOpen i).ι ≫ Y.hom) ξ Y.hom ξ
      (Y.left.connCompOpen i).ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hm : m ≫ pullback.fst Y.hom ξ =
      pullback.fst ((Y.left.connCompOpen i).ι ≫ Y.hom) ξ ≫
        (Y.left.connCompOpen i).ι := by
    dsimp [m, pullback.map]
    rw [pullback.lift_fst]
  change _root_.ConnectedComponents.mk ((m ≫ pullback.fst Y.hom ξ).base z) =
    _root_.ConnectedComponents.mk b
  rw [hm]
  exact ((pullback.fst ((Y.left.connCompOpen i).ι ≫ Y.hom) ξ).base z).2

set_option linter.unnecessarySimpa false in
lemma pullbackMap_isPullback {Y : Scheme.{u}} (g : Y ⟶ X) {A B : FiniteEtale X}
    (f : A ⟶ B) :
    IsPullback (pullback.fst A.hom g) (((pullback g).map f).left)
      f.left (pullback.fst B.hom g) := by
  have hbottom : IsPullback (pullback.fst B.hom g) (pullback.snd B.hom g) B.hom g :=
    IsPullback.of_hasPullback _ _
  have houter : IsPullback (pullback.fst A.hom g)
      (((pullback g).map f).left ≫ pullback.snd B.hom g)
      (f.left ≫ B.hom) g := by
    convert (IsPullback.of_hasPullback A.hom g) using 1
    · rfl
    · change pullback.lift (pullback.fst A.hom g ≫ f.left) (pullback.snd A.hom g) _ ≫
          pullback.snd B.hom g = pullback.snd A.hom g
      exact pullback.lift_snd _ _ _
    · simpa using f.w
  have e : pullback.fst A.hom g ≫ f.left =
      ((pullback g).map f).left ≫ pullback.fst B.hom g := by
    change pullback.fst A.hom g ≫ f.left =
      pullback.lift (pullback.fst A.hom g ≫ f.left) (pullback.snd A.hom g) _ ≫
        pullback.fst B.hom g
    exact (pullback.lift_fst _ _ _).symm
  exact (IsPullback.paste_vert_iff hbottom e).mp houter

lemma isIso_left_of_pullback_map_isIso [ConnectedSpace X]
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X) {A B : FiniteEtale X} (f : A ⟶ B)
    [IsIso ((pullback ξ).map f)] : IsIso f.left := by
  haveI : IsFiniteEtale f.left := hom_left_isFiniteEtale X A B f
  have hFlat : Flat f.left := inferInstance
  have hFinite : IsFinite f.left := inferInstance
  haveI : Flat f.left := hFlat
  haveI : IsFinite f.left := hFinite
  haveI : LocallyOfFinitePresentation f.left := inferInstance
  haveI : IsFiniteEtale (((pullback ξ).map f).left) :=
    hom_left_isFiniteEtale (Spec (.of Ω)) ((pullback ξ).obj A) ((pullback ξ).obj B)
      ((pullback ξ).map f)
  haveI : Flat (((pullback ξ).map f).left) := inferInstance
  haveI : IsFinite (((pullback ξ).map f).left) := inferInstance
  haveI : LocallyOfFinitePresentation (((pullback ξ).map f).left) := inferInstance
  rw [f.left.isIso_iff_finrank_eq]
  ext b
  obtain ⟨t, ht⟩ := exists_fiberPoint_same_connectedComponent ξ B b
  have hmem : (pullback.fst B.hom ξ).base t ∈ connectedComponent b := by
    rw [← connectedComponents_preimage_singleton (x := b)]
    exact ht
  calc
    f.left.finrank b = f.left.finrank ((pullback.fst B.hom ξ).base t) := by
      exact (f.left.isLocallyConstant_finrank).apply_eq_of_isPreconnected
        isPreconnected_connectedComponent mem_connectedComponent hmem
    _ = (((pullback ξ).map f).left).finrank t := by
      exact (@Scheme.Hom.finrank_of_isPullback _ _ _ _
        (pullback.fst A.hom ξ) (((pullback ξ).map f).left)
        f.left (pullback.fst B.hom ξ) (pullbackMap_isPullback ξ f)
        hFlat hFinite t).symm
    _ = 1 := by
      have : IsIso (((pullback ξ).map f).left) := by
        have : IsIso (((forget (Spec (.of Ω)) ⋙ Over.forget (Spec (.of Ω))).map
            ((pullback ξ).map f))) := by infer_instance
        exact this
      exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso (((pullback ξ).map f).left)) t

lemma isIso_of_isIso_left {A B : FiniteEtale X} (f : A ⟶ B) [IsIso f.left] : IsIso f := by
  have : IsIso ((forget X ⋙ Over.forget X).map f) := ‹_›
  exact isIso_of_reflects_iso f (forget X ⋙ Over.forget X)

/-- The geometric fiber functor reflects isomorphisms over a connected base. -/
theorem fiber_reflectsIsomorphisms [ConnectedSpace X] : (fiber ξ).ReflectsIsomorphisms := by
  constructor
  intro A B f hf
  have : IsIso ((pullback ξ).map f) := by
    have : IsIso ((forgetScheme Ω).map ((pullback ξ).map f)) := hf
    exact isIso_of_reflects_iso ((pullback ξ).map f) (forgetScheme Ω)
  have : IsIso f.left := isIso_left_of_pullback_map_isIso ξ f
  exact isIso_of_isIso_left f

attribute [instance] fiber_reflectsIsomorphisms

lemma fiber_preservesFiniteColimits : PreservesFiniteColimits (fiber ξ) := by
  dsimp [fiber]
  exact Limits.comp_preservesFiniteColimits _ _

attribute [instance] fiber_preservesFiniteColimits

/-- If `X` is a connected scheme and `ξ : Spec Ω ⟶ X` is a geometric point,
taking fibers over `ξ` is a fiber functor. -/
lemma fiberFunctor [ConnectedSpace X] : PreGaloisCategory.FiberFunctor (fiber ξ) where
  preservesTerminalObjects := by infer_instance
  preservesPullbacks := by infer_instance
  preservesQuotientsByFiniteGroups _ := inferInstance

attribute [instance] fiberFunctor

/-- If `X` is a connected scheme, the category of finite étale schemes over `X`
is a Galois category. -/
instance galoisCategory (X : Scheme.{u}) [ConnectedSpace X] : GaloisCategory (FiniteEtale X) where
  hasFiberFunctor := by
    have : Nonempty X := inferInstance
    let x : X := ‹Nonempty X›.some
    let k : Type u := X.residueField x
    let Ω : Type u := AlgebraicClosure k
    let ξ : Spec (.of Ω) ⟶ X :=
      Spec.map (CommRingCat.ofHom <| algebraMap k Ω) ≫ X.fromSpecResidueField x
    exact ⟨fiber ξ, ⟨inferInstance⟩⟩

/-- The étale fundamental group of a connected scheme `X` at the geometric point `ξ` is
the automorphism group of the fiber functor at `ξ`. -/
notation:arg "π₁ᵉᵗ" "(" x ")" => Aut (fiber x)

example : IsTopologicalGroup π₁ᵉᵗ(ξ) := inferInstance
example : T2Space π₁ᵉᵗ(ξ) := inferInstance
example : TotallyDisconnectedSpace π₁ᵉᵗ(ξ) := inferInstance
example : CompactSpace π₁ᵉᵗ(ξ) := inferInstance

end FiniteEtale
end AlgebraicGeometry
