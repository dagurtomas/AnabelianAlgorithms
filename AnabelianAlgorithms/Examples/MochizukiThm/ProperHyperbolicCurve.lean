/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

module

public import AnabelianAlgorithms.Examples.MochizukiThm.StructureSheafCohomology
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.CategoryTheory.Widesubcategory
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.PicardGroup

/-!
# Proper hyperbolic curves over `p`-adic local fields

This file defines the category of proper hyperbolic curves used in the Mochizuki Hom-form example.
It also collects the dimension and finiteness lemmas used to bridge from the curve hypotheses to
finite morphisms between such curves.
-/

@[expose] public section

universe u uG

namespace Anabelian
namespace Examples
namespace MochizukiLocalProP
namespace ProperHyperbolicCurveHomStandalone

open CategoryTheory
open AlgebraicGeometry
open Opposite
open TopologicalSpace
open Order

/-! ## Proper hyperbolic curves -/

/-- The base scheme `Spec K`. -/
noncomputable abbrev baseScheme {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : Scheme.{u} :=
  Spec (.of K)

/-- Smooth proper geometrically connected curves of arithmetic genus at least two. -/
structure ProperHyperbolicCurveStructure {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : Over (baseScheme K)) : Prop where
  /-- The structure morphism is smooth. -/
  smooth : Smooth X.hom
  /-- The fibers are one-dimensional. -/
  smoothOfRelativeDimension : SmoothOfRelativeDimension 1 X.hom
  /-- The structure morphism is proper. -/
  proper : IsProper X.hom
  /-- The geometric fibers are connected. -/
  geometricallyConnected : GeometricallyConnected X.hom
  /-- Hyperbolicity in the proper case: arithmetic genus at least two. -/
  genus_ge_two : letI : IsProper X.hom := proper; 2 ≤ curveArithmeticGenus K X

/-- The object property of proper hyperbolic curves over `K`. -/
def properHyperbolicCurveObjectProperty {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : ObjectProperty (Over (baseScheme K)) :=
  fun X ↦ ProperHyperbolicCurveStructure K X

/-- The ambient full subcategory of proper hyperbolic curves over `K`. -/
abbrev ProperHyperbolicCurveAmbient {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : Type (u + 1) :=
  (properHyperbolicCurveObjectProperty K).FullSubcategory

/-- Dominance for morphisms between proper hyperbolic curves. -/
def dominantProperHyperbolicCurveMorphismProperty {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : MorphismProperty (ProperHyperbolicCurveAmbient K) :=
  fun _ _ f ↦ IsDominant f.hom.left

/-- Dominant proper-hyperbolic-curve morphisms are multiplicative. -/
instance dominantProperHyperbolicCurveMorphismProperty_isMultiplicative {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    (dominantProperHyperbolicCurveMorphismProperty K).IsMultiplicative where
  id_mem X := by
    dsimp [dominantProperHyperbolicCurveMorphismProperty]
    infer_instance
  comp_mem f g hf hg := by
    have : IsDominant f.hom.left := hf
    have : IsDominant g.hom.left := hg
    dsimp [dominantProperHyperbolicCurveMorphismProperty]
    infer_instance

/-- Proper hyperbolic curves over a finite extension of `ℚ_[p]`, with dominant morphisms. -/
abbrev ProperHyperbolicCurveOver {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : Type (u + 1) :=
  WideSubcategory (dominantProperHyperbolicCurveMorphismProperty K)

/-! ### Dimension lemmas for the Gap A2 curve bridge -/

/-- A localization has Krull dimension at most that of the original ring. -/
theorem ringKrullDim_le_of_isLocalization {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (M : Submonoid R) [IsLocalization M S] :
    ringKrullDim S ≤ ringKrullDim R := by
  rw [ringKrullDim_le_iff_height_le]
  intro p hp
  haveI : p.IsPrime := hp
  rw [← IsLocalization.height_under M p]
  exact Ideal.height_le_ringKrullDim_of_isPrime

/-- An integral extension has Krull dimension at most that of the base. -/
theorem ringKrullDim_le_of_isIntegral {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R := by
  refine krullDim_le_of_strictMono (fun p : PrimeSpectrum S ↦
    (⟨Ideal.comap (algebraMap R S) p.asIdeal, inferInstance⟩ : PrimeSpectrum R)) ?_
  intro p q hpq
  change Ideal.comap (algebraMap R S) p.asIdeal < Ideal.comap (algebraMap R S) q.asIdeal
  exact Ideal.IsIntegral.comap_lt_comap hpq

/-- A standard étale algebra has Krull dimension at most that of the base. -/
theorem standardEtalePair_ringKrullDim_le {R : Type u} [CommRing R]
    (P : StandardEtalePair R) : ringKrullDim P.Ring ≤ ringKrullDim R := by
  rw [ringKrullDim_eq_of_ringEquiv P.equivAwayAdjoinRoot.toRingEquiv]
  haveI : Module.Finite R (AdjoinRoot P.f) := P.monic_f.finite_adjoinRoot
  haveI : Algebra.IsIntegral R (AdjoinRoot P.f) :=
    Algebra.IsIntegral.of_finite R (AdjoinRoot P.f)
  exact (ringKrullDim_le_of_isLocalization (Submonoid.powers (AdjoinRoot.mk P.f P.g))).trans
    (ringKrullDim_le_of_isIntegral (S := AdjoinRoot P.f))

/-- A standard étale algebra has Krull dimension at most that of the base. -/
theorem isStandardEtale_ringKrullDim_le {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.IsStandardEtale R S] : ringKrullDim S ≤ ringKrullDim R := by
  let P : StandardEtalePresentation R S :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  rw [ringKrullDim_eq_of_ringEquiv P.equivRing.toRingEquiv]
  exact standardEtalePair_ringKrullDim_le P.P

/-- An étale algebra has Krull dimension at most that of the base. -/
theorem etale_ringKrullDim_le {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] : ringKrullDim S ≤ ringKrullDim R := by
  rw [ringKrullDim_le_iff_height_le]
  intro Q hQ
  haveI : Q.IsPrime := hQ
  haveI : Algebra.FinitePresentation R S := inferInstance
  haveI : Algebra.IsEtaleAt R Q := inferInstance
  obtain ⟨f, hfQ, hf⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := R) (S := S) Q
  let Qf : Ideal (Localization.Away f) := Q.map (algebraMap S (Localization.Away f))
  have hdisj : Disjoint (Submonoid.powers f : Set S) (Q : Set S) := by
    rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
    exact hfQ
  haveI : Qf.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers f)
    (Localization.Away f) Q hQ hdisj
  have hheight : Qf.height = Q.height := by
    exact IsLocalization.height_map_of_disjoint (Submonoid.powers f) Q hdisj
  rw [← hheight]
  exact (Ideal.height_le_ringKrullDim_of_isPrime (I := Qf)).trans
    (isStandardEtale_ringKrullDim_le (R := R) (S := Localization.Away f))

/-- If the base is noetherian of Krull dimension zero, a standard-smooth algebra of relative
 dimension one has Krull dimension at most one. -/
theorem isStandardSmoothOfRelativeDimension_one_ringKrullDim_le_of_base_dim_zero
    {R A : Type u} [CommRing R] [IsNoetherianRing R] [CommRing A] [Algebra R A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 R A]
    (hR : ringKrullDim R ≤ (0 : WithBot ℕ∞)) :
    ringKrullDim A ≤ (1 : WithBot ℕ∞) := by
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 R A
  letI : Algebra (MvPolynomial (Fin 1) R) A := g.toRingHom.toAlgebra
  haveI : IsScalarTower R (MvPolynomial (Fin 1) R) A :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  haveI : Algebra.Etale (MvPolynomial (Fin 1) R) A := RingHom.Etale.toAlgebra hg
  have hpoly : ringKrullDim (MvPolynomial (Fin 1) R) ≤ (1 : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
    rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin]
    norm_num
    calc
      ringKrullDim R + (1 : WithBot ℕ∞) = (1 : WithBot ℕ∞) + ringKrullDim R := by
        rw [add_comm]
      _ ≤ (1 : WithBot ℕ∞) + 0 := add_le_add_right hR (1 : WithBot ℕ∞)
      _ = 1 := by norm_num
  exact (etale_ringKrullDim_le (R := MvPolynomial (Fin 1) R) (S := A)).trans hpoly

/-- The unique nonempty open of the spectrum of a field has zero-dimensional ring of functions. -/
theorem spec_field_open_ringKrullDim_le_zero (K : Type u) [Field K]
    (U : (Spec (.of K)).Opens) {x : Spec (.of K)} (hx : x ∈ U) :
    ringKrullDim Γ(Spec (.of K), U) ≤ (0 : WithBot ℕ∞) := by
  have hU : U = ⊤ := by
    ext y
    constructor
    · intro; trivial
    · intro _
      have : y = x := Subsingleton.elim y x
      simpa [this] using hx
  subst hU
  rw [ringKrullDim_eq_of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv]
  simp

/-- Bound the topological Krull dimension of a scheme by bounding all point coheights. -/
theorem scheme_topologicalKrullDim_le_of_forall_coheight_le (X : Scheme.{u})
    {n : ℕ∞} (h : ∀ x : X, coheight x ≤ n) : topologicalKrullDim X ≤ (n : WithBot ℕ∞) := by
  rw [topologicalKrullDim, krullDim_eq_iSup_coheight]
  refine iSup_le ?_
  intro Z
  rw [← coheight_orderIso (irreducibleSetEquivPoints (α := X)) Z]
  exact WithBot.coe_mono (h _)

/-- On an affine open, a Krull-dimension bound for the coordinate ring bounds the coheight of
all points in that open. -/
theorem scheme_coheight_le_of_affine_open_ringKrullDim_le {X : Scheme.{u}} {x : X}
    {V : X.Opens} (hV : IsAffineOpen V) (hx : x ∈ V) {n : ℕ∞}
    (hdim : ringKrullDim Γ(X, V) ≤ (n : WithBot ℕ∞)) : coheight x ≤ n := by
  let xv : V := ⟨x, hx⟩
  letI := X.presheaf.algebra_section_stalk xv
  haveI : IsLocalization.AtPrime (↑(X.presheaf.stalk x)) (hV.primeIdealOf xv).asIdeal := by
    simpa [xv] using hV.isLocalization_stalk xv
  have hstalk : ringKrullDim ↑(X.presheaf.stalk x) ≤ ringKrullDim Γ(X, V) := by
    exact ringKrullDim_le_of_isLocalization (R := Γ(X, V)) (S := ↑(X.presheaf.stalk x))
      (hV.primeIdealOf xv).asIdeal.primeCompl
  have hcoh : (coheight x : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by
    rw [← ringKrullDim_stalk_eq_coheight (X := X) x]
    exact hstalk.trans hdim
  exact WithBot.coe_le_coe.mp hcoh

/-- A scheme smooth of relative dimension one over a field has topological Krull dimension at most
one. -/
theorem scheme_topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one_to_Spec_field
    (K : Type u) [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [SmoothOfRelativeDimension 1 f] : topologicalKrullDim X ≤ (1 : WithBot ℕ∞) := by
  apply scheme_topologicalKrullDim_le_of_forall_coheight_le
  intro x
  obtain ⟨U, hU, V, hV, hxV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) x
  have hxU : f x ∈ U := e hxV
  have hbase : ringKrullDim Γ(Spec (.of K), U) ≤ (0 : WithBot ℕ∞) :=
    spec_field_open_ringKrullDim_le_zero K U hxU
  haveI : IsNoetherianRing Γ(Spec (.of K), U) := by
    have hUtop : U = ⊤ := by
      ext y
      constructor
      · intro; trivial
      · intro _
        have : y = f x := Subsingleton.elim y (f x)
        simpa [this] using hxU
    subst hUtop
    exact isNoetherianRing_of_ringEquiv (CommRingCat.of K)
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  letI : Algebra Γ(Spec (.of K), U) Γ(X, V) := (f.appLE U V e).hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(Spec (.of K), U) Γ(X, V) := hf
  have hdim : ringKrullDim Γ(X, V) ≤ (1 : WithBot ℕ∞) :=
    isStandardSmoothOfRelativeDimension_one_ringKrullDim_le_of_base_dim_zero hbase
  exact scheme_coheight_le_of_affine_open_ringKrullDim_le hV hxV hdim

/-- The affine line over a domain is not a field. -/
theorem mvPolynomial_fin_one_not_isField (R : Type u) [CommRing R] [IsDomain R] :
    ¬ IsField (MvPolynomial (Fin 1) R) := by
  intro h
  let X0 : MvPolynomial (Fin 1) R := MvPolynomial.X 0
  have hX0 : X0 ≠ 0 := MvPolynomial.X_ne_zero (R := R) (0 : Fin 1)
  obtain ⟨p, hp⟩ := h.mul_inv_cancel hX0
  have hp0 : p ≠ 0 := right_ne_zero_of_mul_eq_one hp
  have hdeg := congrArg MvPolynomial.totalDegree hp
  rw [MvPolynomial.totalDegree_mul_of_isDomain hX0 hp0, MvPolynomial.totalDegree_X,
    MvPolynomial.totalDegree_one] at hdeg
  omega

/-- Every nonempty open subset of the affine line over a Jacobson domain contains at least two
points. -/
theorem primeSpectrum_affineLine_nonempty_open_nontrivial (R : Type u) [CommRing R]
    [IsDomain R] [IsJacobsonRing R]
    {U : Set (PrimeSpectrum (MvPolynomial (Fin 1) R))} (hUopen : IsOpen U)
    (hUne : U.Nonempty) : ∃ x y, x ∈ U ∧ y ∈ U ∧ x ≠ y := by
  let η : PrimeSpectrum (MvPolynomial (Fin 1) R) := ⟨⊥, inferInstance⟩
  obtain ⟨z, hzU⟩ := hUne
  have hηz : η ⤳ z := by
    exact (PrimeSpectrum.le_iff_specializes η z).mp bot_le
  have hηU : η ∈ U := hηz.mem_open hUopen hzU
  haveI : IsJacobsonRing (MvPolynomial (Fin 1) R) := inferInstance
  obtain ⟨y, hyU, hyClosed⟩ :=
    PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing U hUopen ⟨z, hzU⟩
  refine ⟨η, y, hηU, hyU, ?_⟩
  intro hηy
  have hηClosed : IsClosed ({η} : Set (PrimeSpectrum (MvPolynomial (Fin 1) R))) := by
    simpa [hηy] using hyClosed
  have hmax : (⊥ : Ideal (MvPolynomial (Fin 1) R)).IsMaximal := by
    simpa [η] using (PrimeSpectrum.isClosed_singleton_iff_isMaximal η).mp hηClosed
  exact mvPolynomial_fin_one_not_isField R
    ((Ring.isField_iff_maximal_bot (R := MvPolynomial (Fin 1) R)).2 hmax)

/-- A nonempty standard-smooth algebra of relative dimension one over a Jacobson domain has a
spectrum with at least two points. -/
theorem spec_of_standardSmoothOfRelativeDimension_one_nontrivial
    (R A : Type u) [CommRing R] [IsDomain R] [IsJacobsonRing R] [CommRing A]
    [Algebra R A] [Nontrivial A] [Algebra.IsStandardSmoothOfRelativeDimension 1 R A] :
    Nontrivial (Spec (.of A)) := by
  obtain ⟨g, hg⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 R A
  letI : Algebra (MvPolynomial (Fin 1) R) A := g.toRingHom.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin 1) R) A := RingHom.Etale.toAlgebra hg
  let φ : Spec (.of A) ⟶ Spec (.of (MvPolynomial (Fin 1) R)) :=
    Spec.map (CommRingCat.ofHom g.toRingHom)
  haveI : Flat φ := by
    dsimp [φ]
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (RingHom.Etale.iff_flat_and_formallyUnramified.mp hg).1
  haveI : LocallyOfFinitePresentation φ := by
    dsimp [φ]
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    exact (RingHom.Etale.iff_flat_and_formallyUnramified.mp hg).2.2
  haveI : UniversallyOpen φ := by infer_instance
  have hopen : IsOpenMap φ := φ.isOpenMap
  have himageOpen : IsOpen (Set.range φ) := hopen.isOpen_range
  have himageNonempty : (Set.range φ).Nonempty := by
    obtain ⟨x⟩ : Nonempty (Spec (.of A)) := inferInstance
    exact ⟨φ x, x, rfl⟩
  obtain ⟨a, b, ha, hb, hne⟩ :=
    primeSpectrum_affineLine_nonempty_open_nontrivial R himageOpen himageNonempty
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', hb⟩ := hb
  refine ⟨⟨a', b', ?_⟩⟩
  intro h
  exact hne (h ▸ hb)

/-- A nonempty scheme smooth of relative dimension one over a field has at least two points. -/
theorem scheme_nontrivial_of_smoothOfRelativeDimension_one_to_Spec_field
    (K : Type u) [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [Nonempty X]
    [SmoothOfRelativeDimension 1 f] : Nontrivial X := by
  let x : X := Classical.choice inferInstance
  obtain ⟨U, hU, V, hV, hxV, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) x
  have hxU : f x ∈ U := e hxV
  have hUtop : U = ⊤ := by
    ext y
    constructor
    · intro; trivial
    · intro _
      have : y = f x := Subsingleton.elim y (f x)
      simpa [this] using hxU
  subst hUtop
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  haveI : Nontrivial Γ(X, V) := Scheme.component_nontrivial X V
  haveI : IsDomain Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens)) := by
    let eΓ := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
    exact eΓ.symm.toMulEquiv.isDomain K
  haveI : IsJacobsonRing Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens)) := by
    let eΓ := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
    exact isJacobsonRing_of_surjective ⟨eΓ.toRingHom, eΓ.surjective⟩
  letI : Algebra Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens)) Γ(X, V) :=
    (f.appLE ⊤ V e).hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1
      Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens)) Γ(X, V) := hf
  have hspec : Nontrivial (Spec (.of Γ(X, V))) :=
    spec_of_standardSmoothOfRelativeDimension_one_nontrivial
      Γ(Spec (.of K), (⊤ : (Spec (.of K)).Opens)) Γ(X, V)
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Spec (.of Γ(X, V)))
  refine ⟨⟨hV.fromSpec a, hV.fromSpec b, ?_⟩⟩
  intro h
  exact hab (hV.fromSpec.isOpenEmbedding.injective h)

/-- A proper closed subset of an irreducible topological space of dimension at most one has
 topological Krull dimension at most zero. -/
theorem topologicalKrullDim_closed_subset_le_zero_of_irreducible
    {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]
    {Z : Set X} (hZclosed : IsClosed Z) (hZproper : Z ≠ Set.univ)
    (hXdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) :
    topologicalKrullDim Z ≤ (0 : WithBot ℕ∞) := by
  rw [topologicalKrullDim, krullDim_nonpos_iff_forall_isMax]
  intro B
  rw [isMax_iff_forall_not_lt]
  intro A hlt
  let BX : IrreducibleCloseds X := IrreducibleCloseds.map ((↑) : Z → X) continuous_subtype_val B
  let AX : IrreducibleCloseds X := IrreducibleCloseds.map ((↑) : Z → X) continuous_subtype_val A
  have hmaplt : BX < AX :=
    (IrreducibleCloseds.map_strictMono_of_isInducing (f := ((↑) : Z → X))
      Topology.IsInducing.subtypeVal) hlt
  have hAX_subset : (AX : Set X) ⊆ Z := by
    dsimp [AX]
    exact closure_minimal (by rintro x ⟨z, hz, rfl⟩; exact z.property) hZclosed
  have hAX_not_max : ¬ IsMax AX := by
    intro hmax
    let U : IrreducibleCloseds X :=
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
    have hle : U ≤ AX := hmax.eq_of_le (show AX ≤ U by intro x hx; trivial) ▸ le_rfl
    apply hZproper
    exact Set.eq_univ_iff_forall.mpr fun x ↦ hAX_subset (hle trivial)
  have horder : krullDim (IrreducibleCloseds X) ≤ (1 : WithBot ℕ∞) := hXdim
  have hcases := (krullDim_le_one_iff.mp horder) AX
  rcases hcases with hmin | hmax
  · exact (isMin_iff_forall_not_lt.mp hmin BX) hmaplt
  · exact hAX_not_max hmax

/-- A subsingleton topological space has topological Krull dimension at most zero. -/
theorem topologicalKrullDim_le_zero_of_subsingleton
    (X : Type u) [TopologicalSpace X] [Subsingleton X] :
    topologicalKrullDim X ≤ (0 : WithBot ℕ∞) := by
  rw [topologicalKrullDim]
  haveI : Subsingleton (IrreducibleCloseds X) := ⟨fun A B ↦ by
    apply IrreducibleCloseds.ext
    ext x
    constructor
    · intro _
      obtain ⟨b, hb⟩ := B.isIrreducible.nonempty
      have : x = b := Subsingleton.elim x b
      simpa [this] using hb
    · intro _
      obtain ⟨a, ha⟩ := A.isIrreducible.nonempty
      have : x = a := Subsingleton.elim x a
      simpa [this] using ha⟩
  exact krullDim_nonpos_of_subsingleton

/-- A zero-dimensional irreducible `T₀` topological space is a subsingleton. -/
theorem subsingleton_of_irreducibleSpace_of_topologicalKrullDim_le_zero
    (X : Type u) [TopologicalSpace X] [T0Space X] [IrreducibleSpace X]
    (hX : topologicalKrullDim X ≤ (0 : WithBot ℕ∞)) : Subsingleton X := by
  refine ⟨fun x y ↦ ?_⟩
  rw [topologicalKrullDim] at hX
  have hmax := krullDim_nonpos_iff_forall_isMax.mp hX
  let A : IrreducibleCloseds X :=
    ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
  let B : IrreducibleCloseds X :=
    ⟨closure ({y} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
  let U : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hAU : U ≤ A := hmax A (show A ≤ U by intro z hz; trivial)
  have hBU : U ≤ B := hmax B (show B ≤ U by intro z hz; trivial)
  have hxgen : IsGenericPoint x (Set.univ : Set X) := by
    rw [isGenericPoint_def]
    exact subset_antisymm (fun z hz ↦ trivial) hAU
  have hygen : IsGenericPoint y (Set.univ : Set X) := by
    rw [isGenericPoint_def]
    exact subset_antisymm (fun z hz ↦ trivial) hBU
  exact hxgen.eq hygen

/-- In an irreducible `T₀` quasi-sober space of dimension at most one, every non-generic point
is closed. -/
theorem isClosed_singleton_of_ne_genericPoint_of_topologicalKrullDim_le_one
    (X : Type u) [TopologicalSpace X] [T0Space X] [QuasiSober X] [IrreducibleSpace X]
    (hX : topologicalKrullDim X ≤ (1 : WithBot ℕ∞)) {x : X}
    (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) := by
  let Z : Set X := closure ({x} : Set X)
  have hZclosed : IsClosed Z := isClosed_closure
  have hZproper : Z ≠ Set.univ := by
    intro hZ
    apply hx
    have hxgen : IsGenericPoint x (Set.univ : Set X) := by
      rw [isGenericPoint_def]
      exact hZ
    exact hxgen.eq (genericPoint_spec X)
  have hZdim : topologicalKrullDim Z ≤ (0 : WithBot ℕ∞) :=
    topologicalKrullDim_closed_subset_le_zero_of_irreducible hZclosed hZproper hX
  haveI : IrreducibleSpace Z := Subtype.irreducibleSpace isIrreducible_singleton.closure
  haveI : Subsingleton Z :=
    subsingleton_of_irreducibleSpace_of_topologicalKrullDim_le_zero Z hZdim
  have hsubset : Z ⊆ ({x} : Set X) := by
    intro y hy
    have hxy : (⟨y, hy⟩ : Z) = ⟨x, subset_closure (by simp)⟩ := Subsingleton.elim _ _
    exact Set.mem_singleton_iff.mpr (congr_arg Subtype.val hxy)
  have hclosure : closure ({x} : Set X) = ({x} : Set X) :=
    subset_antisymm hsubset subset_closure
  simpa [hclosure] using (isClosed_closure : IsClosed (closure ({x} : Set X)))

/-- A dominant morphism between irreducible schemes sends the generic point to the generic point. -/
theorem schemeHom_map_genericPoint_of_isDominant {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace X] [IrreducibleSpace Y] [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  have hgen : IsGenericPoint (f (genericPoint X)) (Set.univ : Set Y) := by
    simpa [Set.image_univ, Scheme.Hom.denseRange f |>.closure_range] using
      (genericPoint_spec X).image f.continuous
  exact hgen.eq (genericPoint_spec Y)

/-- If the scheme-theoretic fiber has finitely many points, then the topological fiber is finite. -/
theorem schemeHom_finite_preimage_singleton_of_finite_fiber {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y) [Finite (f.fiber y)] :
    (f ⁻¹' {y}).Finite := by
  rw [← f.range_fiberι y]
  exact Set.finite_range (f.fiberι y)

/-- An Artinian scheme-theoretic fiber gives a finite topological fiber. -/
theorem schemeHom_finite_preimage_singleton_of_isArtinian_fiber {X Y : Scheme.{u}}
    (f : X ⟶ Y) (y : Y) [IsArtinianScheme (f.fiber y)] :
    (f ⁻¹' {y}).Finite :=
  schemeHom_finite_preimage_singleton_of_finite_fiber f y

/-- A proper morphism has finite topological fiber at `y` once the scheme-theoretic fiber over `y`
has topological Krull dimension zero.

This is the reusable reduction for Gap A2: the remaining hard curve-dimension bridge is to prove
`topologicalKrullDim (f.fiber y) ≤ 0` for dominant morphisms of smooth proper relative-dimension-one
curves. -/
theorem schemeHom_finite_preimage_singleton_of_topologicalKrullDim_fiber_le_zero
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y)
    (h : topologicalKrullDim (f.fiber y) ≤ 0) :
    (f ⁻¹' {y}).Finite := by
  haveI : LocallyOfFiniteType (f.fiberToSpecResidueField y) := by
    change LocallyOfFiniteType (Limits.pullback.snd f (Y.fromSpecResidueField y))
    infer_instance
  haveI : IsLocallyNoetherian (Spec (Y.residueField y)) := inferInstance
  haveI : IsLocallyNoetherian (f.fiber y) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)
  haveI : IsProper (f.fiberToSpecResidueField y) := by
    change IsProper (Limits.pullback.snd f (Y.fromSpecResidueField y))
    infer_instance
  haveI : UniversallyClosed (f.fiberToSpecResidueField y) := by infer_instance
  haveI : QuasiCompact (f.fiberToSpecResidueField y) := by infer_instance
  haveI : CompactSpace (Spec (Y.residueField y)) := inferInstance
  haveI : CompactSpace (f.fiber y) :=
    QuasiCompact.compactSpace_of_compactSpace (f.fiberToSpecResidueField y)
  haveI : IsLocallyArtinian (f.fiber y) :=
    IsLocallyArtinian.of_topologicalKrullDim_le_zero h
  haveI : IsArtinianScheme (f.fiber y) := by exact ⟨⟩
  exact schemeHom_finite_preimage_singleton_of_isArtinian_fiber f y

namespace ProperHyperbolicCurveOver

variable {p : ℕ} [Fact p.Prime] {K : PadicLocalFieldCat.{u} p}

/-- Forget to the object over `Spec K`. -/
noncomputable abbrev toOver (X : ProperHyperbolicCurveOver K) : Over (baseScheme K) :=
  X.obj.obj

/-- Forget to the underlying scheme. -/
noncomputable abbrev toScheme (X : ProperHyperbolicCurveOver K) : Scheme.{u} :=
  X.toOver.left

/-- The stored smoothness of the structure morphism. -/
theorem smooth (X : ProperHyperbolicCurveOver K) : Smooth X.toOver.hom :=
  X.obj.property.smooth

/-- The stored relative dimension-one smoothness of the structure morphism. -/
theorem smoothOfRelativeDimension (X : ProperHyperbolicCurveOver K) :
    SmoothOfRelativeDimension 1 X.toOver.hom :=
  X.obj.property.smoothOfRelativeDimension

/-- A proper hyperbolic curve has topological Krull dimension at most one. -/
theorem topologicalKrullDim_le_one (X : ProperHyperbolicCurveOver K) :
    topologicalKrullDim X.toScheme ≤ (1 : WithBot ℕ∞) := by
  haveI : SmoothOfRelativeDimension 1 X.toOver.hom := X.smoothOfRelativeDimension
  exact scheme_topologicalKrullDim_le_one_of_smoothOfRelativeDimension_one_to_Spec_field K
    X.toOver.hom

/-- The stored properness of the structure morphism. -/
theorem proper (X : ProperHyperbolicCurveOver K) : IsProper X.toOver.hom :=
  X.obj.property.proper

/-- The stored geometric connectedness of the structure morphism. -/
theorem geometricallyConnected (X : ProperHyperbolicCurveOver K) :
    GeometricallyConnected X.toOver.hom :=
  X.obj.property.geometricallyConnected

/-- The structure morphism of a proper hyperbolic curve is locally of finite type. -/
instance locallyOfFiniteType (X : ProperHyperbolicCurveOver K) :
    LocallyOfFiniteType X.toOver.hom := by
  haveI : IsProper X.toOver.hom := X.proper
  infer_instance

/-- The underlying topological space of a proper hyperbolic curve is compact. -/
instance compactSpace (X : ProperHyperbolicCurveOver K) : CompactSpace X.toScheme := by
  haveI : IsProper X.toOver.hom := X.proper
  haveI : UniversallyClosed X.toOver.hom := inferInstance
  haveI : QuasiCompact X.toOver.hom := inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace X.toOver.hom

/-- The underlying scheme of a proper hyperbolic curve is locally noetherian. -/
instance isLocallyNoetherian (X : ProperHyperbolicCurveOver K) :
    IsLocallyNoetherian X.toScheme :=
  LocallyOfFiniteType.isLocallyNoetherian X.toOver.hom

/-- The underlying scheme of a proper hyperbolic curve is noetherian. -/
instance isNoetherian (X : ProperHyperbolicCurveOver K) : IsNoetherian X.toScheme where

/-- The underlying topological space of a proper hyperbolic curve is noetherian. -/
instance noetherianSpace (X : ProperHyperbolicCurveOver K) : NoetherianSpace X.toScheme := by
  haveI : IsNoetherian X.toScheme := ProperHyperbolicCurveOver.isNoetherian X
  infer_instance

/-- The underlying topological space of a proper hyperbolic curve is Jacobson. -/
instance jacobsonSpace (X : ProperHyperbolicCurveOver K) : JacobsonSpace X.toScheme := by
  haveI : LocallyOfFiniteType X.toOver.hom := ProperHyperbolicCurveOver.locallyOfFiniteType X
  exact LocallyOfFiniteType.jacobsonSpace X.toOver.hom

/-- A proper hyperbolic curve has finitely many irreducible components. -/
theorem finite_irreducibleComponents (X : ProperHyperbolicCurveOver K) :
    (irreducibleComponents X.toScheme).Finite := by
  haveI : IsNoetherian X.toScheme := ProperHyperbolicCurveOver.isNoetherian X
  exact finite_irreducibleComponents_of_isNoetherian

/-- Morphisms in `ProperHyperbolicCurveOver K` are dominant by construction. -/
theorem hom_isDominant {X Y : ProperHyperbolicCurveOver K} (f : X ⟶ Y) :
    IsDominant f.hom.hom.left :=
  f.property

/-- The underlying scheme morphism of a morphism of proper hyperbolic curves is proper. -/
theorem hom_isProper {X Y : ProperHyperbolicCurveOver K} (f : X ⟶ Y) :
    IsProper f.hom.hom.left := by
  haveI : IsProper Y.toOver.hom := Y.proper
  haveI : IsProper (f.hom.hom.left ≫ Y.toOver.hom) := by
    rw [f.hom.hom.w]
    exact X.proper
  exact IsProper.of_comp f.hom.hom.left Y.toOver.hom

/-- A morphism of proper hyperbolic curves is surjective on underlying topological spaces. -/
theorem hom_surjective {X Y : ProperHyperbolicCurveOver K} (f : X ⟶ Y) :
    Surjective f.hom.hom.left := by
  haveI : IsProper f.hom.hom.left := hom_isProper f
  haveI : IsDominant f.hom.hom.left := hom_isDominant f
  infer_instance

/-- For morphisms of proper hyperbolic curves, local quasi-finiteness is equivalent to finiteness
of all topological fibers. -/
theorem hom_locallyQuasiFinite_iff_finite_preimage_singleton
    {X Y : ProperHyperbolicCurveOver K} (f : X ⟶ Y) :
    LocallyQuasiFinite f.hom.hom.left ↔ ∀ y, (f.hom.hom.left ⁻¹' {y}).Finite := by
  haveI : IsProper f.hom.hom.left := hom_isProper f
  exact locallyQuasiFinite_iff_finite_preimage_singleton

/-- For morphisms of proper hyperbolic curves, finiteness is equivalent to local
quasi-finiteness.  The forward direction is general; the reverse direction uses properness and
Zariski's Main Theorem. -/
theorem hom_isFinite_iff_locallyQuasiFinite {X Y : ProperHyperbolicCurveOver K} (f : X ⟶ Y) :
    IsFinite f.hom.hom.left ↔ LocallyQuasiFinite f.hom.hom.left := by
  constructor
  · intro h
    exact ((IsFinite.iff_isProper_and_locallyQuasiFinite (f := f.hom.hom.left)).mp h).2
  · intro h
    haveI : IsProper f.hom.hom.left := hom_isProper f
    haveI : LocallyQuasiFinite f.hom.hom.left := h
    exact IsFinite.of_isProper_of_locallyQuasiFinite f.hom.hom.left

/-- Zariski's Main Theorem reduces finiteness of a proper-hyperbolic-curve morphism to the
locally-quasi-finite step. -/
theorem hom_isFinite_of_locallyQuasiFinite {X Y : ProperHyperbolicCurveOver K}
    (f : X ⟶ Y) (h : LocallyQuasiFinite f.hom.hom.left) : IsFinite f.hom.hom.left :=
  (hom_isFinite_iff_locallyQuasiFinite f).2 h

/-- Finite-fiber reduction for dominant morphisms of proper hyperbolic curves.

The remaining A2 dimension bridge is the hypothesis: every scheme-theoretic fiber of the underlying
proper morphism should have topological Krull dimension zero.  Once that is available, the
scheme-theoretic fiber is Artinian and hence has finitely many points, giving the desired finite
preimage of each singleton. -/
theorem hom_finite_fibers_of_topologicalKrullDim_fibers_le_zero
    {X Y : ProperHyperbolicCurveOver K} (f : X ⟶ Y)
    (h : ∀ y : Y.toScheme, topologicalKrullDim (f.hom.hom.left.fiber y) ≤ 0) :
    ∀ y : Y.toScheme, (f.hom.hom.left ⁻¹' {y}).Finite := by
  intro y
  haveI : IsProper f.hom.hom.left := hom_isProper f
  exact schemeHom_finite_preimage_singleton_of_topologicalKrullDim_fiber_le_zero
    f.hom.hom.left y (h y)

/-- Conditional A2 dimension bridge: once the source and target curves are known to be
irreducible, and the target generic point is not closed, every scheme-theoretic fiber of a
dominant curve morphism has topological Krull dimension at most zero.

The closed-fiber case is a proper closed subset of the irreducible source.  The non-closed-fiber
case uses preservation of closed points for locally finite type morphisms to show the fiber is a
subsingleton. -/
theorem hom_topologicalKrullDim_fibers_le_zero_of_irreducible_of_generic_not_closed
    {X Y : ProperHyperbolicCurveOver K} (f : X ⟶ Y)
    [IrreducibleSpace X.toScheme] [IrreducibleSpace Y.toScheme]
    (hYgen : ¬ IsClosed ({genericPoint Y.toScheme} : Set Y.toScheme)) :
    ∀ y : Y.toScheme, topologicalKrullDim (f.hom.hom.left.fiber y) ≤ (0 : WithBot ℕ∞) := by
  intro y
  let φ : X.toScheme ⟶ Y.toScheme := f.hom.hom.left
  haveI : IsDominant φ := hom_isDominant f
  haveI : IsProper φ := hom_isProper f
  haveI : LocallyOfFiniteType φ := by infer_instance
  have hφgen : φ (genericPoint X.toScheme) = genericPoint Y.toScheme :=
    schemeHom_map_genericPoint_of_isDominant φ
  by_cases hy : IsClosed ({y} : Set Y.toScheme)
  · have hyne : y ≠ genericPoint Y.toScheme := by
      intro h
      exact hYgen (by simpa [h] using hy)
    let S : Set X.toScheme := φ ⁻¹' ({y} : Set Y.toScheme)
    have hSclosed : IsClosed S := hy.preimage φ.continuous
    have hSproper : S ≠ Set.univ := by
      intro hS
      have hmem : genericPoint X.toScheme ∈ S := by simp [hS]
      have : genericPoint Y.toScheme = y := by simpa [S, hφgen] using hmem
      exact hyne this.symm
    have hSdim : topologicalKrullDim S ≤ (0 : WithBot ℕ∞) :=
      topologicalKrullDim_closed_subset_le_zero_of_irreducible hSclosed hSproper
        (topologicalKrullDim_le_one X)
    have hhomeo := IsHomeomorph.topologicalKrullDim_eq (φ.fiberHomeo y)
      (φ.fiberHomeo y).isHomeomorph
    rwa [hhomeo]
  · let S : Set X.toScheme := φ ⁻¹' ({y} : Set Y.toScheme)
    have hSsub : Subsingleton S := by
      refine ⟨fun a b ↦ Subtype.ext ?_⟩
      have ha : a.1 = genericPoint X.toScheme := by
        by_contra hxa
        have hxaClosed : IsClosed ({a.1} : Set X.toScheme) :=
          isClosed_singleton_of_ne_genericPoint_of_topologicalKrullDim_le_one
            X.toScheme (topologicalKrullDim_le_one X) hxa
        have hyClosed' : IsClosed ({φ a.1} : Set Y.toScheme) := by
          exact φ.closePoints_subset_preimage_closedPoints hxaClosed
        have hφa : φ a.1 = y := a.2
        exact hy (by simpa [hφa] using hyClosed')
      have hb : b.1 = genericPoint X.toScheme := by
        by_contra hxb
        have hxbClosed : IsClosed ({b.1} : Set X.toScheme) :=
          isClosed_singleton_of_ne_genericPoint_of_topologicalKrullDim_le_one
            X.toScheme (topologicalKrullDim_le_one X) hxb
        have hyClosed' : IsClosed ({φ b.1} : Set Y.toScheme) := by
          exact φ.closePoints_subset_preimage_closedPoints hxbClosed
        have hφb : φ b.1 = y := b.2
        exact hy (by simpa [hφb] using hyClosed')
      exact ha.trans hb.symm
    have hSdim : topologicalKrullDim S ≤ (0 : WithBot ℕ∞) := by
      haveI : Subsingleton S := hSsub
      exact topologicalKrullDim_le_zero_of_subsingleton S
    have hhomeo := IsHomeomorph.topologicalKrullDim_eq (φ.fiberHomeo y)
      (φ.fiberHomeo y).isHomeomorph
    rwa [hhomeo]

/-- Conditional finite-fiber theorem from the irreducible/generic-not-closed curve bridge. -/
theorem hom_finite_fibers_of_irreducible_of_generic_not_closed
    {X Y : ProperHyperbolicCurveOver K} (f : X ⟶ Y)
    [IrreducibleSpace X.toScheme] [IrreducibleSpace Y.toScheme]
    (hYgen : ¬ IsClosed ({genericPoint Y.toScheme} : Set Y.toScheme)) :
    ∀ y : Y.toScheme, (f.hom.hom.left ⁻¹' {y}).Finite :=
  hom_finite_fibers_of_topologicalKrullDim_fibers_le_zero f
    (hom_topologicalKrullDim_fibers_le_zero_of_irreducible_of_generic_not_closed f hYgen)

end ProperHyperbolicCurveOver
end ProperHyperbolicCurveHomStandalone
end MochizukiLocalProP
end Examples
end Anabelian
