/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/

import AnabelianAlgorithms.Linter.NonstandardAxioms
import AnabelianAlgorithms.Examples.MochizukiThm.BaseGalois
import AnabelianLib.Framework.HomForm

/-!
# Standalone Hom-form statement for proper hyperbolic curves over `p`-adic local fields

This file is a self-contained extraction of the proper-hyperbolic-curve Hom-form statement. It
uses mathlib imports, the reusable Anabelian framework/profunctor-composition files, and the adapted
finite-étale fiber API from `Anabelian.FromPi1`. It includes only the scaffolding needed to state
the profunctorial reconstruction package.

The arithmetic étale `π₁` invariant/algorithm are now concrete profunctors built from
point-indexed finite-étale fiber data.  Geometric points appear only as ordinary input data for
pointed representatives; this file no longer selects curve base points by axiom.

The remaining named boundaries are theorem-shaped: comparison of the base absolute Galois group
with pointed `π₁(Spec K)`, point-indexed outer functoriality/openness, bookkeeping laws for the
current representative presentation, and the final Hom-form theorem.  The next refinement is to
replace the representative bookkeeping laws by an explicit quotient/torsor for change of geometric
point.
-/

set_option linter.nonstandardAxioms false

universe u uG

namespace ProfiniteGrp

open TopologicalSpace

/-- A profinite-group homomorphism is open if its range is open. -/
theorem isOpenMap_of_open_range {G H : ProfiniteGrp.{u}}
    (φ : G ⟶ H) (hφ : IsOpen (Set.range (φ : G → H))) : IsOpenMap φ := by
  let φrange : G →* φ.hom.range := φ.hom.toMonoidHom.rangeRestrict
  have hφ' : IsOpen (φ.hom.range : Set H) := by
    convert hφ
    ext y
    rfl
  haveI : BaireSpace φ.hom.range := hφ'.baireSpace
  have hφrange_surj : Function.Surjective φrange :=
    φ.hom.toMonoidHom.rangeRestrict_surjective
  have hφrange_cont : Continuous φrange := by
    change Continuous fun x : G ↦ (⟨φ x, x, rfl⟩ : φ.hom.range)
    exact φ.hom.continuous_toFun.subtype_mk (fun x ↦ ⟨x, rfl⟩)
  have hφrange_open : IsOpenMap φrange :=
    MonoidHom.isOpenMap_of_sigmaCompact φrange hφrange_surj hφrange_cont
  have hsubtype_open : IsOpenMap ((↑) : φ.hom.range → H) := hφ'.isOpenMap_subtype_val
  change IsOpenMap (((↑) : φ.hom.range → H) ∘ φrange)
  exact hsubtype_open.comp hφrange_open

/-- A profinite-group homomorphism has finite-index range if its range contains an open subgroup. -/
theorem finiteIndex_range_of_open_subgroup_le {G H : ProfiniteGrp.{u}} (φ : G ⟶ H)
    {U : Subgroup H} (hUopen : IsOpen (U : Set H))
    (hU : U ≤ MonoidHom.range φ.hom.toMonoidHom) :
    Subgroup.FiniteIndex (MonoidHom.range φ.hom.toMonoidHom) := by
  haveI : Subgroup.FiniteIndex U := by
    haveI : Finite (H ⧸ U) := U.quotient_finite_of_isOpen hUopen
    exact Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.finiteIndex_of_le hU

/-- In a profinite group, a closed subgroup can be separated from an outside element by an
open subgroup containing it. -/
theorem exists_open_subgroup_of_closed_subgroup_not_mem {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (R : Subgroup G) (hRclosed : IsClosed (R : Set G)) {σ : G} (hσ : σ ∉ R) :
    ∃ V : Subgroup G, IsOpen (V : Set G) ∧ R ≤ V ∧ σ ∉ V := by
  let Rclosed : ClosedSubgroup G := { toSubgroup := R, isClosed' := hRclosed }
  have hEq := ProfiniteGrp.closedSubgroup_eq_sInf_open Rclosed
  have hσsInf : σ ∉ sInf {N : Subgroup G | IsOpen (N : Set G) ∧ R ≤ N} := by
    intro hmem
    apply hσ
    have hmem' : σ ∈ (Rclosed : Subgroup G) := by
      rw [hEq]
      exact hmem
    exact hmem'
  rw [Subgroup.mem_sInf] at hσsInf
  push Not at hσsInf
  obtain ⟨V, hV⟩ := hσsInf
  exact ⟨V, hV.1.1, hV.1.2, hV.2⟩

/-- A profinite-group homomorphism with finite-index range is open. -/
theorem isOpenMap_of_finiteIndex_range {G H : ProfiniteGrp.{u}}
    (φ : G ⟶ H) [Subgroup.FiniteIndex (MonoidHom.range φ.hom.toMonoidHom)] :
    IsOpenMap φ := by
  have hcompact : IsCompact (φ.hom.range : Set H) := by
    convert isCompact_univ.image φ.hom.continuous_toFun using 1
    ext y
    simp
  have hopen : IsOpen (φ.hom.range : Set H) :=
    φ.hom.range.isOpen_of_isClosed_of_finiteIndex hcompact.isClosed
  apply isOpenMap_of_open_range φ
  convert hopen
  ext y
  rfl

end ProfiniteGrp

namespace Anabelian
namespace Examples
namespace MochizukiLocalProP
namespace ProperHyperbolicCurveHomStandalone

open CategoryTheory
open CategoryTheory.PreGaloisCategory
open AlgebraicGeometry
open Opposite
open TopologicalSpace
open Order
open scoped FintypeCatDiscrete

/-! ## Finite extensions of `ℚ_[p]` -/

/-- The object property on `ℚ_[p]`-algebras whose underlying ring is a finite field extension. -/
def padicLocalFieldObjectProperty (p : ℕ) [Fact p.Prime] :
    ObjectProperty (CommAlgCat.{u} ℚ_[p]) :=
  fun K ↦ ∃ hK : IsField K, letI : Field K := hK.toField; FiniteDimensional ℚ_[p] K

/-- Finite extensions of `ℚ_[p]`, as a full subcategory of `CommAlgCat ℚ_[p]`. -/
abbrev PadicLocalFieldCat (p : ℕ) [Fact p.Prime] : Type (u + 1) :=
  (padicLocalFieldObjectProperty.{u} p).FullSubcategory

namespace PadicLocalFieldCat

instance (p : ℕ) [Fact p.Prime] : CoeSort (PadicLocalFieldCat.{u} p) (Type u) :=
  ⟨fun K ↦ K.obj⟩

/-- The field structure on a `p`-adic local field object. -/
noncomputable instance field {p : ℕ} [Fact p.Prime] (K : PadicLocalFieldCat.{u} p) : Field K :=
  K.property.choose.toField

/-- The finite-dimensionality over `ℚ_[p]` stored in a `p`-adic local field object. -/
noncomputable instance finiteDimensional {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : FiniteDimensional ℚ_[p] K :=
  K.property.choose_spec

/-- A finite extension of `ℚ_[p]` has characteristic zero. -/
noncomputable instance charZero {p : ℕ} [Fact p.Prime] (K : PadicLocalFieldCat.{u} p) :
    CharZero K :=
  charZero_of_injective_algebraMap (RingHom.injective (algebraMap ℚ_[p] K))

end PadicLocalFieldCat

/-! ## Structure-sheaf cohomology and arithmetic genus -/

namespace ExtractedStructureSheafCohomology

universe w' w v

namespace LinearSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Type w) [CommRing R]
variable [J.HasSheafCompose (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})]

/-- Forget a sheaf of `R`-modules to its underlying abelian sheaf. -/
abbrev underlyingAdditiveSheaf (F : Sheaf J (ModuleCat.{w} R)) : Sheaf J AddCommGrpCat.{w} :=
  (sheafCompose J (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w})).obj F

namespace HModule

variable {R}

/-- The endomorphism of the underlying abelian sheaf given by scalar multiplication by `r`. -/
noncomputable def scalarEnd (F : Sheaf J (ModuleCat.{w} R)) (r : R) :
    underlyingAdditiveSheaf R F ⟶ underlyingAdditiveSheaf R F where
  hom :=
    { app U := AddCommGrpCat.ofHom ((LinearMap.lsmul R (F.obj.obj U) r).toAddMonoidHom)
      naturality := by
        intro U V i
        ext x
        let x' : F.obj.obj U := x
        let y' : F.obj.obj V := (F.obj.map i).hom x'
        change r • y' = (F.obj.map i).hom (r • x')
        exact ((F.obj.map i).hom.map_smul r x').symm }

@[simp]
lemma scalarEnd_zero (F : Sheaf J (ModuleCat.{w} R)) :
    scalarEnd (R := R) F 0 = 0 := by
  ext U x
  let x' : F.obj.obj U := x
  change (0 : R) • x' = 0
  simp

@[simp]
lemma scalarEnd_one (F : Sheaf J (ModuleCat.{w} R)) :
    scalarEnd (R := R) F 1 = 𝟙 _ := by
  ext U x
  let x' : F.obj.obj U := x
  change (1 : R) • x' = x'
  simp

@[simp]
lemma scalarEnd_add (F : Sheaf J (ModuleCat.{w} R)) (r s : R) :
    scalarEnd (R := R) F (r + s) = scalarEnd (R := R) F r + scalarEnd (R := R) F s := by
  ext U x
  let x' : F.obj.obj U := x
  change (r + s) • x' = r • x' + s • x'
  simp [add_smul]

@[simp]
lemma scalarEnd_mul (F : Sheaf J (ModuleCat.{w} R)) (r s : R) :
    scalarEnd (R := R) F (r * s) = scalarEnd (R := R) F s ≫ scalarEnd (R := R) F r := by
  ext U x
  let x' : F.obj.obj U := x
  change (r * s) • x' = r • s • x'
  rw [mul_smul]

end HModule

section Cohomology

variable [HasSheafify J AddCommGrpCat.{w}]
variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- The type underlying `R`-linear sheaf cohomology.

This is the cohomology of the underlying abelian sheaf, equipped below with the `R`-module
structure induced by scalar multiplication on the coefficient sheaf. -/
abbrev HModuleType (F : Sheaf J (ModuleCat.{w} R)) (n : ℕ) : Type w' :=
  (underlyingAdditiveSheaf R F).H n

namespace HModule

variable {R}

noncomputable instance instModuleHModuleType (F : Sheaf J (ModuleCat.{w} R)) (n : ℕ) :
    Module R (HModuleType R F n) where
  smul r x := CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F r) n x
  one_smul x := by
    change CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F 1) n x = x
    rw [scalarEnd_one]
    simp
  mul_smul r s x := by
    change CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F (r * s)) n x =
      CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F r) n
        (CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F s) n x)
    rw [scalarEnd_mul]
    simp [CategoryTheory.Sheaf.H.map_comp_apply]
  smul_zero r := map_zero _
  zero_smul x := by
    change CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F 0) n x = 0
    rw [scalarEnd_zero]
    simp [CategoryTheory.Sheaf.H.map_apply]
  add_smul r s x := by
    change CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F (r + s)) n x =
      CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F r) n x +
        CategoryTheory.Sheaf.H.map (scalarEnd (R := R) F s) n x
    rw [scalarEnd_add]
    simp [CategoryTheory.Sheaf.H.map_add_apply]
  smul_add r x y := map_add _ x y

end HModule

/-- `R`-linear sheaf cohomology as an object of `ModuleCat R`. -/
noncomputable def HModule (F : Sheaf J (ModuleCat.{w} R)) (n : ℕ) : ModuleCat.{w'} R :=
  ModuleCat.of R (HModuleType R F n)

end Cohomology

end LinearSheaf

/-- The map from the base ring to sections of the structure sheaf over an open set of `X`, induced
by a morphism `X ⟶ Spec R`. -/
noncomputable def structureSheafToOpen (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (.of R)) (U : X.Opens) : CommRingCat.of R ⟶ X.presheaf.obj (.op U) :=
  (Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U (by simp)

/-- The corresponding algebra map on sections of the structure sheaf over an open set. -/
noncomputable def structureSheafAlgebraMap (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (.of R)) (U : X.Opens) : R →+* X.presheaf.obj (.op U) :=
  (structureSheafToOpen R X f U).hom

@[reassoc (attr := simp)]
lemma structureSheafToOpen_naturality (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (.of R)) {U V : X.Opensᵒᵖ} (i : U ⟶ V) :
    structureSheafToOpen R X f U.unop ≫ X.presheaf.map i =
      structureSheafToOpen R X f V.unop := by
  dsimp [structureSheafToOpen]
  rw [Category.assoc, f.appLE_map]

/-- The structure presheaf of a scheme over `Spec R`, valued in `ModuleCat R`. -/
noncomputable def structureSheafModulePresheaf (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (.of R)) : X.Opensᵒᵖ ⥤ ModuleCat.{u} R where
  obj U :=
    letI : Algebra R (X.presheaf.obj U) := (structureSheafAlgebraMap R X f U.unop).toAlgebra
    ModuleCat.of R (X.presheaf.obj U)
  map {U V} i := by
    letI : Algebra R (X.presheaf.obj U) := (structureSheafAlgebraMap R X f U.unop).toAlgebra
    letI : Algebra R (X.presheaf.obj V) := (structureSheafAlgebraMap R X f V.unop).toAlgebra
    exact ModuleCat.ofHom
      { toFun := (X.presheaf.map i).hom
        map_add' := map_add _
        map_smul' := by
          intro r x
          change (X.presheaf.map i).hom ((structureSheafAlgebraMap R X f U.unop) r * x) =
            (structureSheafAlgebraMap R X f V.unop) r * (X.presheaf.map i).hom x
          rw [map_mul]
          congr 1
          have h := congr_arg (fun e : CommRingCat.of R ⟶ X.presheaf.obj V => e.hom r)
            (structureSheafToOpen_naturality R X f i)
          simpa only [structureSheafAlgebraMap, CommRingCat.hom_comp, RingHom.coe_comp,
            Function.comp_apply] using h }
  map_id U := by
    letI : Algebra R (X.presheaf.obj U) := (structureSheafAlgebraMap R X f U.unop).toAlgebra
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (X.presheaf.map (𝟙 U)).hom x = x
    simp
  map_comp {U V W} i j := by
    letI : Algebra R (X.presheaf.obj U) := (structureSheafAlgebraMap R X f U.unop).toAlgebra
    letI : Algebra R (X.presheaf.obj V) := (structureSheafAlgebraMap R X f V.unop).toAlgebra
    letI : Algebra R (X.presheaf.obj W) := (structureSheafAlgebraMap R X f W.unop).toAlgebra
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (X.presheaf.map (i ≫ j)).hom x =
      (X.presheaf.map j).hom ((X.presheaf.map i).hom x)
    simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using
      congr_arg (fun e : X.presheaf.obj U ⟶ X.presheaf.obj W => e.hom x)
        (X.presheaf.map_comp i j)

/-- Forgetting the `R`-module structure on `structureSheafModulePresheaf` recovers the underlying
presheaf of types of the usual structure sheaf. -/
noncomputable def structureSheafModulePresheafForgetIso (R : Type u) [CommRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of R)) :
    structureSheafModulePresheaf R X f ⋙ CategoryTheory.forget (ModuleCat.{u} R) ≅
      X.presheaf ⋙ CategoryTheory.forget CommRingCat.{u} :=
  Iso.refl _

/-- The structure sheaf of a scheme over `Spec R`, regarded as a sheaf of `R`-modules. -/
noncomputable def structureSheafModule (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (.of R)) :
    Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) where
  obj := structureSheafModulePresheaf R X f
  property := by
    rw [Presheaf.isSheaf_iff_isSheaf_comp (Opens.grothendieckTopology X)
      (structureSheafModulePresheaf R X f) (CategoryTheory.forget (ModuleCat.{u} R))]
    exact (Presheaf.isSheaf_of_iso_iff (J := Opens.grothendieckTopology X)
      (structureSheafModulePresheafForgetIso R X f)).mpr
      ((Presheaf.isSheaf_iff_isSheaf_comp (Opens.grothendieckTopology X) X.presheaf
        (CategoryTheory.forget CommRingCat.{u})).mp X.sheaf.property)

/-- Cohomology of the structure sheaf of a scheme over `Spec R`, with its natural `R`-module
structure. -/
noncomputable def structureSheafCohomologyModule (R : Type u) [CommRing R] (X : Scheme.{u})
    (f : X ⟶ Spec (.of R))
    [(Opens.grothendieckTopology X).HasSheafCompose
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (n : ℕ) : ModuleCat.{w'} R :=
  LinearSheaf.HModule R (structureSheafModule R X f) n

end ExtractedStructureSheafCohomology

/-- The structure-sheaf cohomology group `H^i(X, 𝒪_X)` of a scheme over a `p`-adic local field. -/
noncomputable abbrev structureSheafCohomology {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : Over (Spec (.of K))) (i : ℕ) : Type u :=
  ExtractedStructureSheafCohomology.structureSheafCohomologyModule K X.left X.hom i

namespace StructureSheafCohomology

/-- Coherent cohomology finiteness for the structure sheaf of a proper scheme over a field. -/
@[instance] axiom finiteDimensional_of_proper {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : Over (Spec (.of K))) [IsProper X.hom] (i : ℕ) :
    FiniteDimensional K (structureSheafCohomology K X i)

end StructureSheafCohomology

/-- The dimension `dim_K H^i(X, 𝒪_X)`, available for proper schemes over `K`. -/
noncomputable def structureSheafCohomologyRank {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : Over (Spec (.of K))) [IsProper X.hom]
    (i : ℕ) : ℕ :=
  Module.finrank K (structureSheafCohomology K X i)

/-- For curves, the arithmetic genus is `dim_K H¹(X, 𝒪_X)`. -/
noncomputable def curveArithmeticGenus {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : Over (Spec (.of K))) [IsProper X.hom] : ℕ :=
  structureSheafCohomologyRank K X 1

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
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
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

/-! ## Augmented profinite groups and outer morphisms -/

/-- Two morphisms of profinite groups are outer-equivalent if they differ by conjugation by an
 element of the target. -/
def profiniteGrpOuterRel : HomRel ProfiniteGrp.{u} :=
  fun {G H} f g ↦ ∃ h : H, ∀ x : G, g x = h * f x * h⁻¹

/-- Outer-equivalence is a congruence on the category of profinite groups. -/
instance profiniteGrpOuterRelCongruence : Congruence profiniteGrpOuterRel where
  comp_left := by
    intro _ _ _ f _ _ ⟨h, hh⟩
    exact ⟨h, fun x ↦ hh (f x)⟩
  comp_right := by
    intro _ _ _ _ _ g ⟨h, hh⟩
    exact ⟨g h, fun x ↦ by simp [hh x]⟩
  equivalence {_ _} := by
    refine ⟨fun _ ↦ ⟨1, fun x ↦ by simp⟩, ?_, ?_⟩
    · intro _ _ ⟨h, hh⟩
      exact ⟨h⁻¹, fun x ↦ by rw [hh x]; group⟩
    · intro _ _ _ ⟨h, hh⟩ ⟨i, hi⟩
      exact ⟨i * h, fun x ↦ by rw [hi x, hh x]; group⟩

/-- Profinite groups with morphisms quotiented by inner conjugation in the target. -/
abbrev ProfiniteGrpOuter : Type (u + 1) :=
  CategoryTheory.Quotient profiniteGrpOuterRel

/-- View an actual profinite group as an object of the outer quotient category. -/
noncomputable abbrev profiniteAsOuter (G : ProfiniteGrp.{u}) : ProfiniteGrpOuter.{u} :=
  (CategoryTheory.Quotient.functor profiniteGrpOuterRel).obj G

/-- Augmented profinite groups over a fixed profinite group. -/
abbrev AugProfiniteOver (G : ProfiniteGrp.{u}) : Type (u + 1) :=
  CostructuredArrow (𝟭 ProfiniteGrp.{u}) G

/-- Open continuous morphisms of augmented profinite groups over a fixed base. -/
def openAugProfiniteMorphismProperty (Γ : ProfiniteGrp.{u}) :
    MorphismProperty (AugProfiniteOver Γ) :=
  fun _ _ f ↦ IsOpenMap f.left

/-- Open augmented morphisms are multiplicative. -/
instance openAugProfiniteMorphismProperty_isMultiplicative (Γ : ProfiniteGrp.{u}) :
    (openAugProfiniteMorphismProperty Γ).IsMultiplicative where
  id_mem _ := .id
  comp_mem _ _ hf hg := hg.comp hf

/-- Augmented profinite groups over a fixed base, with only open morphisms. -/
abbrev OpenAugProfiniteOver (Γ : ProfiniteGrp.{u}) : Type (u + 1) :=
  WideSubcategory (openAugProfiniteMorphismProperty Γ)

namespace OpenAugProfiniteOver

/-- Forget to the ambient augmented profinite group. -/
noncomputable abbrev asAug {Γ : ProfiniteGrp.{u}} (A : OpenAugProfiniteOver Γ) :
    AugProfiniteOver Γ :=
  A.obj

/-- Forget to the underlying profinite group. -/
noncomputable abbrev asProfinite {Γ : ProfiniteGrp.{u}} (A : OpenAugProfiniteOver Γ) :
    ProfiniteGrp.{u} :=
  A.asAug.left

/-- The augmentation to the fixed base group. -/
noncomputable abbrev augmentation {Γ : ProfiniteGrp.{u}} (A : OpenAugProfiniteOver Γ) :
    A.asProfinite ⟶ Γ :=
  A.asAug.hom

/-- Morphisms commute with the augmentation. -/
@[reassoc (attr := simp)]
theorem hom_w {Γ : ProfiniteGrp.{u}} {A B : OpenAugProfiniteOver Γ} (f : A ⟶ B) :
    f.hom.left ≫ B.asAug.hom = A.asAug.hom :=
  f.hom.w

/-- The underlying continuous homomorphism of a data morphism is open. -/
theorem hom_isOpenMap {Γ : ProfiniteGrp.{u}} {A B : OpenAugProfiniteOver Γ}
    (f : A ⟶ B) : IsOpenMap f.hom.left :=
  f.property

end OpenAugProfiniteOver

/-- A morphism in the outer profinite-group category is open if it has an open representative before
quotienting by target conjugation. -/
def IsOpenOuterHom {G H : ProfiniteGrpOuter.{u}} (φ : G ⟶ H) : Prop :=
  ∃ f : G.as ⟶ H.as,
    (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map f = φ ∧ IsOpenMap f

/-- Identity outer morphisms are open. -/
theorem isOpenOuterHom_id (G : ProfiniteGrpOuter.{u}) : IsOpenOuterHom (𝟙 G) :=
  ⟨𝟙 G.as, rfl, .id⟩

/-- Open outer morphisms are closed under composition. -/
theorem isOpenOuterHom_comp {G H I : ProfiniteGrpOuter.{u}} {φ : G ⟶ H} {ψ : H ⟶ I}
    (hφ : IsOpenOuterHom φ) (hψ : IsOpenOuterHom ψ) : IsOpenOuterHom (φ ≫ ψ) := by
  obtain ⟨f, rfl, hf⟩ := hφ
  obtain ⟨g, rfl, hg⟩ := hψ
  exact ⟨f ≫ g, rfl, hg.comp hf⟩

/-- Augmented outer profinite groups over a fixed outer base. -/
abbrev AugProfiniteOuterOver (Γ : ProfiniteGrpOuter.{u}) : Type (u + 1) :=
  CostructuredArrow (𝟭 ProfiniteGrpOuter.{u}) Γ

/-- View an augmented profinite group as an augmented object in the outer quotient category. -/
noncomputable def augProfiniteAsOuter {Γ : ProfiniteGrp.{u}}
    (A : AugProfiniteOver Γ) : AugProfiniteOuterOver (profiniteAsOuter Γ) :=
  CostructuredArrow.mk ((CategoryTheory.Quotient.functor profiniteGrpOuterRel).map A.hom)

/-- The outer augmented morphism induced by a morphism of augmented profinite groups. -/
noncomputable def augProfiniteAsOuterMap {Γ : ProfiniteGrp.{u}}
    {A B : AugProfiniteOver Γ} (f : A ⟶ B) :
    augProfiniteAsOuter A ⟶ augProfiniteAsOuter B := by
  let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
  exact CostructuredArrow.homMk (Q.map f.left) (by
    change Q.map f.left ≫ Q.map B.hom = Q.map A.hom
    have hw : f.left ≫ B.hom = A.hom := by
      exact f.w
    rw [← Q.map_comp, hw]
    rfl)

@[simp]
theorem augProfiniteAsOuterMap_id {Γ : ProfiniteGrp.{u}} (A : AugProfiniteOver Γ) :
    augProfiniteAsOuterMap (𝟙 A) = 𝟙 (augProfiniteAsOuter A) := by
  apply CostructuredArrow.hom_ext
  simp [augProfiniteAsOuterMap]
  rfl

@[simp]
theorem augProfiniteAsOuterMap_comp {Γ : ProfiniteGrp.{u}}
    {A B C : AugProfiniteOver Γ} (f : A ⟶ B) (g : B ⟶ C) :
    augProfiniteAsOuterMap (f ≫ g) = augProfiniteAsOuterMap f ≫ augProfiniteAsOuterMap g := by
  apply CostructuredArrow.hom_ext
  simp [augProfiniteAsOuterMap]
  rfl

/-- View an open augmented profinite group as an augmented object in the outer quotient category. -/
noncomputable abbrev openAugProfiniteAsOuter {Γ : ProfiniteGrp.{u}}
    (A : OpenAugProfiniteOver Γ) : AugProfiniteOuterOver (profiniteAsOuter Γ) :=
  augProfiniteAsOuter A.asAug

/-- The outer augmented morphism induced by an open augmented morphism. -/
noncomputable abbrev openAugProfiniteAsOuterMap {Γ : ProfiniteGrp.{u}}
    {A B : OpenAugProfiniteOver Γ} (f : A ⟶ B) :
    openAugProfiniteAsOuter A ⟶ openAugProfiniteAsOuter B :=
  augProfiniteAsOuterMap f.hom

@[simp]
theorem openAugProfiniteAsOuterMap_id {Γ : ProfiniteGrp.{u}} (A : OpenAugProfiniteOver Γ) :
    openAugProfiniteAsOuterMap (𝟙 A) = 𝟙 (openAugProfiniteAsOuter A) := by
  simp [openAugProfiniteAsOuterMap]

@[simp]
theorem openAugProfiniteAsOuterMap_comp {Γ : ProfiniteGrp.{u}}
    {A B C : OpenAugProfiniteOver Γ} (f : A ⟶ B) (g : B ⟶ C) :
    openAugProfiniteAsOuterMap (f ≫ g) =
      openAugProfiniteAsOuterMap f ≫ openAugProfiniteAsOuterMap g := by
  simp [openAugProfiniteAsOuterMap]

/-- Outer morphisms of augmented profinite groups over the same base. -/
abbrev OuterHomOver {Γ : ProfiniteGrp.{u}} (A B : OpenAugProfiniteOver Γ) : Type u :=
  openAugProfiniteAsOuter A ⟶ openAugProfiniteAsOuter B

/-- Openness for outer morphisms over the base. -/
def IsOpenOuterHomOver {Γ : ProfiniteGrp.{u}} {A B : OpenAugProfiniteOver Γ}
    (φ : OuterHomOver A B) : Prop :=
  IsOpenOuterHom φ.left

/-- Open outer morphisms over the base are closed under composition. -/
theorem isOpenOuterHomOver_comp {Γ : ProfiniteGrp.{u}} {A B C : OpenAugProfiniteOver Γ}
    {φ : OuterHomOver A B} {ψ : OuterHomOver B C}
    (hφ : IsOpenOuterHomOver φ) (hψ : IsOpenOuterHomOver ψ) :
    IsOpenOuterHomOver (φ ≫ ψ) := by
  dsimp [IsOpenOuterHomOver] at hφ hψ ⊢
  simpa using isOpenOuterHom_comp hφ hψ

/-- Open augmented morphisms give open outer morphisms over the base. -/
theorem isOpenOuterHomOver_of_openAugProfiniteHom {Γ : ProfiniteGrp.{u}}
    {A B : OpenAugProfiniteOver Γ} (f : A ⟶ B) :
    IsOpenOuterHomOver (openAugProfiniteAsOuterMap f) := by
  dsimp [IsOpenOuterHomOver, openAugProfiniteAsOuterMap, augProfiniteAsOuterMap]
  exact ⟨f.hom.left, rfl, f.property⟩

/-! ## Arithmetic fundamental-group profunctors -/

/-- Precomposition with a functor is continuous on automorphism groups of finite-set-valued
functors. This is the left-whiskering analogue of mathlib's
`continuous_mapAut_whiskeringRight`. -/
lemma continuous_mapAut_whiskeringLeft {C D : Type*} [Category C] [Category D]
    (F : C ⥤ FintypeCat.{u}) (L : D ⥤ C) :
    Continuous (((Functor.whiskeringLeft D C FintypeCat).obj L).mapAut F) := by
  rw [Topology.IsInducing.continuous_iff (autEmbedding_isClosedEmbedding _).isInducing,
    continuous_pi_iff]
  intro Y
  change Continuous fun a ↦ autEmbedding F a (L.obj Y)
  fun_prop

/-- Conjugation by a natural isomorphism is continuous on automorphism groups. -/
lemma continuous_conjAut {C : Type*} [Category C] {F G : C ⥤ FintypeCat.{u}}
    (e : F ≅ G) : Continuous e.conjAut := by
  rw [Topology.IsInducing.continuous_iff (autEmbedding_isClosedEmbedding _).isInducing,
    continuous_pi_iff]
  intro X
  have hcont : Continuous (fun a : Aut F ↦ autEmbedding F a X) := by fun_prop
  have hc : Continuous (fun b : Aut (F.obj X) ↦ (e.app X).conjAut b) := by fun_prop
  convert hc.comp hcont using 1
  rfl

/-- The multiplicative homeomorphism from a small model of a profinite group to the group. -/
noncomputable def shrinkContinuousMulEquiv (G : ProfiniteGrp.{u + 1}) [Small.{u} G] :
    Shrink.{u} G ≃ₜ* G where
  __ := (Shrink.homeomorph G).symm
  map_mul' x y := by
    change (equivShrink G).symm (x * y) =
      (equivShrink G).symm x * (equivShrink G).symm y
    simp

noncomputable instance shrinkIsTopologicalGroup (G : ProfiniteGrp.{u + 1}) [Small.{u} G] :
    IsTopologicalGroup (Shrink.{u} G) :=
  (shrinkContinuousMulEquiv G).isTopologicalGroup

noncomputable instance shrinkCompactSpace (G : ProfiniteGrp.{u + 1}) [Small.{u} G] :
    CompactSpace (Shrink.{u} G) :=
  Homeomorph.compactSpace (Shrink.homeomorph G)

noncomputable instance shrinkTotallyDisconnectedSpace (G : ProfiniteGrp.{u + 1}) [Small.{u} G] :
    TotallyDisconnectedSpace (Shrink.{u} G) :=
  Homeomorph.totallyDisconnectedSpace (Shrink.homeomorph G)

/-- A small-universe profinite model of a profinite group living one universe higher. -/
noncomputable def shrinkProfiniteGrp (G : ProfiniteGrp.{u + 1}) [Small.{u} G] : ProfiniteGrp.{u} :=
  ProfiniteGrp.of (Shrink.{u} G)

/-- A continuous homomorphism induces a homomorphism between small-universe profinite models. -/
noncomputable def shrinkProfiniteGrpMap {G H : ProfiniteGrp.{u + 1}} [Small.{u} G]
    [Small.{u} H] (f : G ⟶ H) : shrinkProfiniteGrp G ⟶ shrinkProfiniteGrp H :=
  ProfiniteGrp.ofHom {
    toMonoidHom := {
      toFun x := equivShrink H (f ((equivShrink G).symm x))
      map_one' := by
        apply (equivShrink H).symm.injective
        simp
      map_mul' x y := by
        apply (equivShrink H).symm.injective
        simp [map_mul] }
    continuous_toFun := by
      change Continuous ((Shrink.homeomorph H) ∘ f ∘ (Shrink.homeomorph G).symm)
      fun_prop }

noncomputable instance uliftTotallyDisconnectedSpace (G : ProfiniteGrp.{u}) :
    TotallyDisconnectedSpace (ULift.{u + 1, u} G) :=
  Homeomorph.totallyDisconnectedSpace (Homeomorph.ulift.symm : G ≃ₜ ULift.{u + 1, u} G)

/-- A large-universe copy of a profinite group. -/
noncomputable def uliftProfiniteGrp (G : ProfiniteGrp.{u}) : ProfiniteGrp.{u + 1} :=
  ProfiniteGrp.of (ULift.{u + 1, u} G)

/-- A continuous homomorphism induces a homomorphism between large-universe copies. -/
noncomputable def uliftProfiniteGrpMap {G H : ProfiniteGrp.{u}} (f : G ⟶ H) :
    uliftProfiniteGrp G ⟶ uliftProfiniteGrp H :=
  ProfiniteGrp.ofHom {
    toMonoidHom := {
      toFun x := ULift.up (f x.down)
      map_one' := by
        ext
        simp
      map_mul' x y := by
        ext
        simp [map_mul] }
    continuous_toFun := by
      change Continuous (ULift.up ∘ (f : G → H) ∘ ULift.down)
      fun_prop }

@[simp]
theorem uliftProfiniteGrpMap_id (G : ProfiniteGrp.{u}) :
    uliftProfiniteGrpMap (𝟙 G) = 𝟙 (uliftProfiniteGrp G) := by
  ext x
  cases x
  rfl

@[simp]
theorem uliftProfiniteGrpMap_comp {G H I : ProfiniteGrp.{u}} (f : G ⟶ H) (g : H ⟶ I) :
    uliftProfiniteGrpMap (f ≫ g) = uliftProfiniteGrpMap f ≫ uliftProfiniteGrpMap g := by
  ext x
  cases x
  rfl

/-- Openness is preserved by passage to large-universe copies. -/
theorem uliftProfiniteGrpMap_isOpenMap {G H : ProfiniteGrp.{u}} (f : G ⟶ H)
    (hf : IsOpenMap f) : IsOpenMap (uliftProfiniteGrpMap f) := by
  change IsOpenMap (ULift.up ∘ (f : G → H) ∘ ULift.down)
  exact Homeomorph.ulift.symm.isOpenMap.comp (hf.comp Homeomorph.ulift.isOpenMap)

/-- The full pointed étale fundamental group of a pointed connected scheme. -/
noncomputable def pointedEtalePi1 {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X) :
    ProfiniteGrp.{u + 1} :=
  ProfiniteGrp.of (Aut (AlgebraicGeometry.FiniteEtale.fiber ξ))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pullback of finite étale covers identifies the fiber at `ξ ≫ f` with the pulled-back fiber. -/
noncomputable def fiberCompIso {X Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) :
    AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f) ≅
      AlgebraicGeometry.FiniteEtale.pullback f ⋙ AlgebraicGeometry.FiniteEtale.fiber ξ :=
  let e := MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) ξ f
  NatIso.ofComponents (fun A ↦ (AlgebraicGeometry.FiniteEtale.forgetScheme Ω).mapIso (e.app A))
    (fun {A B} g ↦ by
      dsimp [AlgebraicGeometry.FiniteEtale.fiber]
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg ((AlgebraicGeometry.FiniteEtale.forgetScheme Ω).map)
        (e.hom.naturality g))

/-- The homomorphism on full pointed étale fundamental groups induced by a scheme morphism. -/
noncomputable def pointedEtalePi1Map {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) :
    pointedEtalePi1 ξ ⟶ pointedEtalePi1 (ξ ≫ f) :=
  ProfiniteGrp.ofHom {
    toMonoidHom := (fiberCompIso ξ f).symm.conjAut.toMonoidHom.comp
      (Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
        ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Y)
          (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
          (AlgebraicGeometry.FiniteEtale.pullback f)))
    continuous_toFun := (continuous_conjAut (fiberCompIso ξ f).symm).comp
      (continuous_mapAut_whiskeringLeft (AlgebraicGeometry.FiniteEtale.fiber ξ)
        (AlgebraicGeometry.FiniteEtale.pullback f)) }

/-- Stabilizers of points in finite-étale fibers are open in the pointed étale fundamental group. -/
theorem pointedEtalePi1_stabilizer_isOpen {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] (ξ : Spec (.of Ω) ⟶ X)
    (A : AlgebraicGeometry.FiniteEtale X) (a : (AlgebraicGeometry.FiniteEtale.fiber ξ).obj A) :
    IsOpen (MulAction.stabilizer (Aut (AlgebraicGeometry.FiniteEtale.fiber ξ)) a :
      Set (Aut (AlgebraicGeometry.FiniteEtale.fiber ξ))) := by
  exact stabilizer_isOpen _ _

/-- If the range of a pointed étale `π₁` map contains a fiber-point stabilizer, then it has
finite index. -/
theorem pointedEtalePi1Map_finiteIndex_range_of_stabilizer_le
    {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y)
    (A : AlgebraicGeometry.FiniteEtale Y)
    (a : (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).obj A)
    (hstab : MulAction.stabilizer (Aut (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f))) a ≤
      MonoidHom.range (pointedEtalePi1Map ξ f).hom.toMonoidHom) :
    Subgroup.FiniteIndex (MonoidHom.range (pointedEtalePi1Map ξ f).hom.toMonoidHom) := by
  exact ProfiniteGrp.finiteIndex_range_of_open_subgroup_le (pointedEtalePi1Map ξ f)
    (pointedEtalePi1_stabilizer_isOpen (ξ ≫ f) A a) hstab

/-- A finite-étale morphism, viewed as a finite-étale cover of its target. -/
noncomputable def finiteEtaleCoverOfIsFiniteEtale {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFiniteEtale f] : AlgebraicGeometry.FiniteEtale Y :=
  MorphismProperty.Over.mk ⊤ f inferInstance

/-- The terminal finite-étale cover of a scheme, represented by the identity morphism. -/
noncomputable def finiteEtaleTerminal (X : Scheme.{u}) : AlgebraicGeometry.FiniteEtale X :=
  MorphismProperty.Over.mk ⊤ (𝟙 X)
    (MorphismProperty.id_mem (@IsFiniteEtale : MorphismProperty Scheme.{u}) X)

@[simp]
lemma finiteEtaleTerminal_hom (X : Scheme.{u}) : (finiteEtaleTerminal X).hom = 𝟙 X := rfl

@[simp]
lemma finiteEtaleTerminal_left (X : Scheme.{u}) : (finiteEtaleTerminal X).left = X := rfl

/-- The identity finite-étale cover is terminal. -/
noncomputable def finiteEtaleTerminal_isTerminal (X : Scheme.{u}) :
    CategoryTheory.Limits.IsTerminal (finiteEtaleTerminal X) := by
  refine CategoryTheory.Limits.IsTerminal.ofUniqueHom (fun A ↦ ?_) (fun A g ↦ ?_)
  · refine MorphismProperty.Over.homMk A.hom ?_
    exact Category.comp_id A.hom
  · apply MorphismProperty.Over.Hom.ext
    change g.left = A.hom
    have hw := g.w
    change g.left ≫ 𝟙 X = A.hom ≫ 𝟙 X at hw
    exact hw.trans (Category.comp_id A.hom)

/-- The fiber of the terminal finite-étale cover is a singleton. -/
@[reducible]
noncomputable def finiteEtaleTerminal_fiber_unique {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X) :
    Unique ((AlgebraicGeometry.FiniteEtale.fiber ξ).obj (finiteEtaleTerminal X)) := by
  have hT : CategoryTheory.Limits.IsTerminal (finiteEtaleTerminal X) :=
    finiteEtaleTerminal_isTerminal X
  have hFT : CategoryTheory.Limits.IsTerminal
      ((AlgebraicGeometry.FiniteEtale.fiber ξ).obj (finiteEtaleTerminal X)) :=
    CategoryTheory.Limits.IsTerminal.isTerminalObj
      (AlgebraicGeometry.FiniteEtale.fiber ξ) (finiteEtaleTerminal X) hT
  exact CategoryTheory.Limits.Concrete.uniqueOfTerminalOfPreserves
    ((AlgebraicGeometry.FiniteEtale.fiber ξ).obj (finiteEtaleTerminal X)) hFT

/-- The unique point of the fiber of the terminal finite-étale cover. -/
noncomputable def finiteEtaleTerminalFiberPoint {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X) :
    (AlgebraicGeometry.FiniteEtale.fiber ξ).obj (finiteEtaleTerminal X) := by
  letI := finiteEtaleTerminal_fiber_unique ξ
  exact default

/-- The diagonal section of the pullback of a finite-étale cover by itself. -/
noncomputable def finiteEtaleSelfPullbackDiagonal {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFiniteEtale f] :
    finiteEtaleTerminal X ⟶
      (AlgebraicGeometry.FiniteEtale.pullback f).obj (finiteEtaleCoverOfIsFiniteEtale f) := by
  refine MorphismProperty.Over.homMk (Limits.pullback.lift (𝟙 X) (𝟙 X) ?_) ?_
  · change 𝟙 X ≫ f = 𝟙 X ≫ f
    rfl
  · dsimp [AlgebraicGeometry.FiniteEtale.pullback, finiteEtaleCoverOfIsFiniteEtale,
      finiteEtaleTerminal]
    change Limits.pullback.lift (𝟙 X) (𝟙 X)
        (by simp : 𝟙 X ≫ f = 𝟙 X ≫ f) ≫ Limits.pullback.snd f f = 𝟙 X
    exact Limits.pullback.lift_snd _ _ _

/-- The canonical point of the fiber of a finite-étale cover `f : X ⟶ Y` above a point
`ξ : Spec Ω ⟶ X`, viewed over the composite point of `Y`. -/
noncomputable def finiteEtaleSelfFiberPoint {X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) [IsFiniteEtale f] :
    (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).obj (finiteEtaleCoverOfIsFiniteEtale f) :=
  (fiberCompIso ξ f).inv.app (finiteEtaleCoverOfIsFiniteEtale f)
    ((AlgebraicGeometry.FiniteEtale.fiber ξ).map (finiteEtaleSelfPullbackDiagonal f)
      (finiteEtaleTerminalFiberPoint ξ))

/-- The canonical finite-étale-cover stabilizer is open.  This is the open subgroup expected to
witness finite-index image in the finite-étale case once the stabilizer-containment step is
proved. -/
theorem finiteEtaleSelfFiberPoint_stabilizer_isOpen {X Y : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) [IsFiniteEtale f] :
    IsOpen (MulAction.stabilizer (Aut (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)))
      (finiteEtaleSelfFiberPoint ξ f) :
        Set (Aut (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)))) :=
  pointedEtalePi1_stabilizer_isOpen (ξ ≫ f) (finiteEtaleCoverOfIsFiniteEtale f)
    (finiteEtaleSelfFiberPoint ξ f)

/-- For a finite-étale morphism, containment of the canonical fiber-point stabilizer in the range
of the pointed `π₁` map implies finite-index image. -/
theorem pointedEtalePi1Map_finiteIndex_range_of_isFiniteEtale_of_stabilizer_le
    {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) [IsFiniteEtale f]
    (hstab : MulAction.stabilizer (Aut (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)))
      (finiteEtaleSelfFiberPoint ξ f) ≤
        MonoidHom.range (pointedEtalePi1Map ξ f).hom.toMonoidHom) :
    Subgroup.FiniteIndex (MonoidHom.range (pointedEtalePi1Map ξ f).hom.toMonoidHom) :=
  pointedEtalePi1Map_finiteIndex_range_of_stabilizer_le ξ f
    (finiteEtaleCoverOfIsFiniteEtale f) (finiteEtaleSelfFiberPoint ξ f) hstab

@[simp]
lemma pointedEtalePi1Map_hom_app {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y)
    (τ : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ))
    (A : AlgebraicGeometry.FiniteEtale Y) :
    ((pointedEtalePi1Map ξ f).hom τ).hom.app A =
      (fiberCompIso ξ f).hom.app A ≫
        τ.hom.app ((AlgebraicGeometry.FiniteEtale.pullback f).obj A) ≫
          (fiberCompIso ξ f).inv.app A :=
  rfl

set_option linter.unusedFintypeInType false in
/-- The finite quotient by an open subgroup, shrunk to a prescribed universe, is a continuous
finite action. -/
lemma quotientOpenSubgroup_shrink_action_isContinuous {G : Type uG}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : OpenSubgroup G) [Fintype (G ⧸ V.toSubgroup)] :
    (Action.FintypeCat.ofMulAction G
      (FintypeCat.of (Shrink.{u, uG} (G ⧸ V.toSubgroup)))).IsContinuous := by
  rw [Action.isContinuous_def]
  haveI : DiscreteTopology
      ↑((forget₂ (Action FintypeCat G) TopCat).obj
        (Action.FintypeCat.ofMulAction G
          (FintypeCat.of (Shrink.{u, uG} (G ⧸ V.toSubgroup))))) := ⟨rfl⟩
  rw [continuous_prod_of_discrete_right]
  intro y
  haveI : DiscreteTopology
      ↑((forget₂ FintypeCat TopCat).obj
        (Action.FintypeCat.ofMulAction G
          (FintypeCat.of (Shrink.{u, uG} (G ⧸ V.toSubgroup)))).V) := ⟨rfl⟩
  rw [continuous_discrete_rng]
  intro x
  obtain ⟨y', rfl⟩ := (equivShrink.{u, uG} (G ⧸ V.toSubgroup)).surjective y
  obtain ⟨x', rfl⟩ := (equivShrink.{u, uG} (G ⧸ V.toSubgroup)).surjective x
  induction y' using Quotient.inductionOn with
  | h a =>
      induction x' using Quotient.inductionOn with
      | h b =>
          have hopen : IsOpen ((fun m : G ↦ (m * a)⁻¹ * b) ⁻¹' (V.toSubgroup : Set G)) := by
            exact V.isOpen.preimage (by fun_prop)
          convert hopen using 1
          ext m
          simp only [Set.mem_preimage, Set.mem_singleton_iff]
          change (m • (equivShrink.{u, uG} (G ⧸ V.toSubgroup)
                (⟦a⟧ : G ⧸ V.toSubgroup)) =
              equivShrink.{u, uG} (G ⧸ V.toSubgroup) ⟦b⟧) ↔
            (m * a)⁻¹ * b ∈ V.toSubgroup
          rw [← equivShrink_smul]
          change (equivShrink.{u, uG} (G ⧸ V.toSubgroup)
              (⟦m * a⟧ : G ⧸ V.toSubgroup) =
              equivShrink.{u, uG} (G ⧸ V.toSubgroup) ⟦b⟧) ↔
            (m * a)⁻¹ * b ∈ V.toSubgroup
          rw [(equivShrink.{u, uG} (G ⧸ V.toSubgroup)).apply_eq_iff_eq]
          rw [Quotient.eq]
          rw [QuotientGroup.leftRel_apply]

/-- The finite quotient by an open subgroup as a continuous action in a prescribed universe. -/
noncomputable def quotientOpenSubgroupShrinkContAction {G : Type uG}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : OpenSubgroup G) [Fintype (G ⧸ V.toSubgroup)] :
    ContAction FintypeCat.{u} G :=
  ⟨Action.FintypeCat.ofMulAction G
      (FintypeCat.of (Shrink.{u, uG} (G ⧸ V.toSubgroup))),
    quotientOpenSubgroup_shrink_action_isContinuous V⟩

set_option linter.unusedFintypeInType false in
lemma quotientOpenSubgroupShrink_base_fixed_iff {G : Type uG}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (V : OpenSubgroup G) [Fintype (G ⧸ V.toSubgroup)] (g : G) :
    g • (equivShrink.{u, uG} (G ⧸ V.toSubgroup) (⟦(1 : G)⟧ : G ⧸ V.toSubgroup)) =
        equivShrink.{u, uG} (G ⧸ V.toSubgroup) (⟦(1 : G)⟧ : G ⧸ V.toSubgroup) ↔
      g ∈ V.toSubgroup := by
  rw [← equivShrink_smul]
  rw [(equivShrink.{u, uG} (G ⧸ V.toSubgroup)).apply_eq_iff_eq]
  change (⟦g * 1⟧ : G ⧸ V.toSubgroup) = ⟦(1 : G)⟧ ↔ g ∈ V.toSubgroup
  rw [Quotient.eq]
  rw [QuotientGroup.leftRel_apply]
  simp

/-- A fiber point fixed by the full pointed étale fundamental group comes from a section of the
finite-étale cover. -/
noncomputable def finiteEtaleSectionOfFixedFiberPoint {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (B : AlgebraicGeometry.FiniteEtale X)
    (b : (AlgebraicGeometry.FiniteEtale.fiber ξ).obj B)
    (hb : ∀ τ : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ), τ.hom.app B b = b) :
    finiteEtaleTerminal X ⟶ B := by
  let F := AlgebraicGeometry.FiniteEtale.fiber ξ
  let T := finiteEtaleTerminal X
  let h : (functorToAction F).obj T ⟶ (functorToAction F).obj B :=
    { hom := FintypeCat.homMk (fun _ ↦ b)
      comm := by
        intro τ
        ext t
        change b = τ.hom.app B b
        exact (hb τ).symm }
  exact (functorToAction F).preimage h

@[simp]
lemma finiteEtaleSectionOfFixedFiberPoint_fiber {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (B : AlgebraicGeometry.FiniteEtale X)
    (b : (AlgebraicGeometry.FiniteEtale.fiber ξ).obj B)
    (hb : ∀ τ : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ), τ.hom.app B b = b) :
    (AlgebraicGeometry.FiniteEtale.fiber ξ).map
      (finiteEtaleSectionOfFixedFiberPoint ξ B b hb) (finiteEtaleTerminalFiberPoint ξ) = b := by
  let F := AlgebraicGeometry.FiniteEtale.fiber ξ
  let T := finiteEtaleTerminal X
  let h : (functorToAction F).obj T ⟶ (functorToAction F).obj B :=
    { hom := FintypeCat.homMk (fun _ ↦ b)
      comm := by
        intro τ
        ext t
        change b = τ.hom.app B b
        exact (hb τ).symm }
  change (F.map ((functorToAction F).preimage h)) (finiteEtaleTerminalFiberPoint ξ) = b
  have hmap : (functorToAction F).map ((functorToAction F).preimage h) = h :=
    (functorToAction F).map_preimage h
  have hhom : ((functorToAction F).map ((functorToAction F).preimage h)).hom = h.hom :=
    congrArg Action.Hom.hom hmap
  exact ConcreteCategory.congr_hom hhom (finiteEtaleTerminalFiberPoint ξ)

/-- If a target automorphism fixes a point of a finite-étale cover, then the corresponding source
automorphism fixes the transported point on the pullback cover. -/
lemma pointedEtalePi1Map_fixed_pullback_point {X Y : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y)
    (A : AlgebraicGeometry.FiniteEtale Y)
    (b : (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).obj A)
    (τ : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ))
    (hb : ((pointedEtalePi1Map ξ f).hom τ).hom.app A b = b) :
    τ.hom.app ((AlgebraicGeometry.FiniteEtale.pullback f).obj A)
      ((fiberCompIso ξ f).hom.app A b) =
    (fiberCompIso ξ f).hom.app A b := by
  have hb' : ((fiberCompIso ξ f).hom.app A ≫
      τ.hom.app ((AlgebraicGeometry.FiniteEtale.pullback f).obj A) ≫
        (fiberCompIso ξ f).inv.app A) b = b := by
    simpa using hb
  have hcong := congrArg ((fiberCompIso ξ f).hom.app A) hb'
  let y := τ.hom.app ((AlgebraicGeometry.FiniteEtale.pullback f).obj A)
      ((fiberCompIso ξ f).hom.app A b)
  have hinvhom : (fiberCompIso ξ f).hom.app A ((fiberCompIso ξ f).inv.app A y) = y := by
    have h := ConcreteCategory.congr_hom (Iso.inv_hom_id ((fiberCompIso ξ f).app A)) y
    change (fiberCompIso ξ f).hom.app A ((fiberCompIso ξ f).inv.app A y) = y at h
    exact h
  change (fiberCompIso ξ f).hom.app A ((fiberCompIso ξ f).inv.app A y) =
    (fiberCompIso ξ f).hom.app A b at hcong
  rw [hinvhom] at hcong
  exact hcong

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A point of a finite-étale cover whose pullback fiber point is fixed by the source fundamental
group is the image of the canonical self-fiber point under a morphism out of the cover `f`. -/
lemma finiteEtaleSelfFiberPoint_map_of_fixed_pullback_point {X Y : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) [IsFiniteEtale f]
    (A : AlgebraicGeometry.FiniteEtale Y)
    (b : (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).obj A)
    (hx : ∀ τ : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ),
      τ.hom.app ((AlgebraicGeometry.FiniteEtale.pullback f).obj A)
        ((fiberCompIso ξ f).hom.app A b) = (fiberCompIso ξ f).hom.app A b) :
    ∃ m : finiteEtaleCoverOfIsFiniteEtale f ⟶ A,
      (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).map m (finiteEtaleSelfFiberPoint ξ f) = b := by
  let adj := MorphismProperty.Over.mapPullbackAdj (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ f
    (show IsFiniteEtale f from inferInstance) trivial
  let s := finiteEtaleSectionOfFixedFiberPoint ξ ((AlgebraicGeometry.FiniteEtale.pullback f).obj A)
    ((fiberCompIso ξ f).hom.app A b) hx
  let m : finiteEtaleCoverOfIsFiniteEtale f ⟶ A :=
    (adj.homEquiv (finiteEtaleTerminal X) A).symm s
  refine ⟨m, ?_⟩
  have hdiag :
      finiteEtaleSelfPullbackDiagonal f ≫
        (AlgebraicGeometry.FiniteEtale.pullback f).map m = s := by
    have hm : adj.unit.app (finiteEtaleTerminal X) ≫
        (AlgebraicGeometry.FiniteEtale.pullback f).map m = s := by
      simpa [m] using (adj.homEquiv_unit (finiteEtaleTerminal X) A m).symm
    have hunit : adj.unit.app (finiteEtaleTerminal X) = finiteEtaleSelfPullbackDiagonal f := rfl
    rw [← hunit]
    exact hm
  have hs_fiber :
      (AlgebraicGeometry.FiniteEtale.fiber ξ).map s (finiteEtaleTerminalFiberPoint ξ) =
        (show (AlgebraicGeometry.FiniteEtale.fiber ξ).obj
            ((AlgebraicGeometry.FiniteEtale.pullback f).obj A) from
          (fiberCompIso ξ f).hom.app A b) := by
    simp [s]
  have hself : (fiberCompIso ξ f).hom.app (finiteEtaleCoverOfIsFiniteEtale f)
      (finiteEtaleSelfFiberPoint ξ f) =
      (AlgebraicGeometry.FiniteEtale.fiber ξ).map (finiteEtaleSelfPullbackDiagonal f)
        (finiteEtaleTerminalFiberPoint ξ) := by
    let z := (AlgebraicGeometry.FiniteEtale.fiber ξ).map (finiteEtaleSelfPullbackDiagonal f)
        (finiteEtaleTerminalFiberPoint ξ)
    change (fiberCompIso ξ f).hom.app (finiteEtaleCoverOfIsFiniteEtale f)
      ((fiberCompIso ξ f).inv.app (finiteEtaleCoverOfIsFiniteEtale f) z) = z
    have h := ConcreteCategory.congr_hom
      (Iso.inv_hom_id ((fiberCompIso ξ f).app (finiteEtaleCoverOfIsFiniteEtale f))) z
    change (fiberCompIso ξ f).hom.app (finiteEtaleCoverOfIsFiniteEtale f)
      ((fiberCompIso ξ f).inv.app (finiteEtaleCoverOfIsFiniteEtale f) z) = z at h
    exact h
  have hright : ((fiberCompIso ξ f).hom.app (finiteEtaleCoverOfIsFiniteEtale f) ≫
        (AlgebraicGeometry.FiniteEtale.fiber ξ).map
          ((AlgebraicGeometry.FiniteEtale.pullback f).map m))
        (finiteEtaleSelfFiberPoint ξ f) = (fiberCompIso ξ f).hom.app A b := by
    change (AlgebraicGeometry.FiniteEtale.fiber ξ).map
        ((AlgebraicGeometry.FiniteEtale.pullback f).map m)
      ((fiberCompIso ξ f).hom.app (finiteEtaleCoverOfIsFiniteEtale f)
        (finiteEtaleSelfFiberPoint ξ f)) = _
    rw [hself]
    calc
      (AlgebraicGeometry.FiniteEtale.fiber ξ).map
          ((AlgebraicGeometry.FiniteEtale.pullback f).map m)
          ((AlgebraicGeometry.FiniteEtale.fiber ξ).map (finiteEtaleSelfPullbackDiagonal f)
            (finiteEtaleTerminalFiberPoint ξ))
          = (AlgebraicGeometry.FiniteEtale.fiber ξ).map
              (finiteEtaleSelfPullbackDiagonal f ≫ (AlgebraicGeometry.FiniteEtale.pullback f).map m)
                (finiteEtaleTerminalFiberPoint ξ) := by
              rw [Functor.map_comp_apply]
      _ = (AlgebraicGeometry.FiniteEtale.fiber ξ).map s (finiteEtaleTerminalFiberPoint ξ) := by
              rw [hdiag]
      _ = (fiberCompIso ξ f).hom.app A b := hs_fiber
  have hnat := (fiberCompIso ξ f).hom.naturality m
  have h_congr := ConcreteCategory.congr_hom hnat (finiteEtaleSelfFiberPoint ξ f)
  have hhom : (fiberCompIso ξ f).hom.app A
      ((AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).map m (finiteEtaleSelfFiberPoint ξ f)) =
      (fiberCompIso ξ f).hom.app A b := by
    change (fiberCompIso ξ f).hom.app A
        ((AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).map m (finiteEtaleSelfFiberPoint ξ f)) =
      ((fiberCompIso ξ f).hom.app (finiteEtaleCoverOfIsFiniteEtale f) ≫
        (AlgebraicGeometry.FiniteEtale.fiber ξ).map
          ((AlgebraicGeometry.FiniteEtale.pullback f).map m))
        (finiteEtaleSelfFiberPoint ξ f) at h_congr
    exact h_congr.trans hright
  have hinj : Function.Injective (fun x ↦ (fiberCompIso ξ f).hom.app A x) := by
    intro x y hxy
    have h := congrArg ((fiberCompIso ξ f).inv.app A) hxy
    change (fiberCompIso ξ f).inv.app A ((fiberCompIso ξ f).hom.app A x) =
      (fiberCompIso ξ f).inv.app A ((fiberCompIso ξ f).hom.app A y) at h
    have hx' : (fiberCompIso ξ f).inv.app A ((fiberCompIso ξ f).hom.app A x) = x := by
      have h' := ConcreteCategory.congr_hom (Iso.hom_inv_id ((fiberCompIso ξ f).app A)) x
      change (fiberCompIso ξ f).inv.app A ((fiberCompIso ξ f).hom.app A x) = x at h'
      exact h'
    have hy' : (fiberCompIso ξ f).inv.app A ((fiberCompIso ξ f).hom.app A y) = y := by
      have h' := ConcreteCategory.congr_hom (Iso.hom_inv_id ((fiberCompIso ξ f).app A)) y
      change (fiberCompIso ξ f).inv.app A ((fiberCompIso ξ f).hom.app A y) = y at h'
      exact h'
    rw [hx', hy'] at h
    exact h
  exact hinj hhom

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For a finite-étale morphism, the stabilizer of the canonical self-fiber point is contained in
the image of the pointed étale `π₁` map. -/
theorem finiteEtaleSelfFiberPoint_stabilizer_le_range {X Y : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) [IsFiniteEtale f] :
    MulAction.stabilizer (Aut (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)))
        (finiteEtaleSelfFiberPoint ξ f) ≤
      MonoidHom.range (pointedEtalePi1Map ξ f).hom.toMonoidHom := by
  intro σ hσ
  let FY := AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)
  let FX := AlgebraicGeometry.FiniteEtale.fiber ξ
  let G := Aut FY
  let R : Subgroup G := MonoidHom.range (pointedEtalePi1Map ξ f).hom.toMonoidHom
  by_contra hσR
  have hRclosed : IsClosed (R : Set G) := by
    have hcompact : IsCompact (R : Set G) := by
      change IsCompact (Set.range ((pointedEtalePi1Map ξ f).hom : Aut FX → G))
      simpa [Set.image_univ] using
        isCompact_univ.image (pointedEtalePi1Map ξ f).hom.continuous_toFun
    exact hcompact.isClosed
  obtain ⟨Vsub, hVopen, hRV, hσV⟩ :=
    ProfiniteGrp.exists_open_subgroup_of_closed_subgroup_not_mem R hRclosed hσR
  let V : OpenSubgroup G := ⟨Vsub, hVopen⟩
  haveI : Finite (G ⧸ V.toSubgroup) := V.toSubgroup.quotient_finite_of_isOpen V.isOpen'
  haveI : Fintype (G ⧸ V.toSubgroup) := Fintype.ofFinite _
  let Q : ContAction FintypeCat.{u} G := quotientOpenSubgroupShrinkContAction.{u, u+1} V
  obtain ⟨A, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := functorToContAction FY) Q
  let q0 : Q.obj.V := equivShrink.{u, u+1} (G ⧸ V.toSubgroup) (⟦(1 : G)⟧ : G ⧸ V.toSubgroup)
  let b : FY.obj A := e.inv.hom.hom q0
  have hpre_fixed (τ : Aut FX) : ((pointedEtalePi1Map ξ f).hom τ).hom.app A b = b := by
    have hmemR : (pointedEtalePi1Map ξ f).hom τ ∈ R := ⟨τ, rfl⟩
    have hmemV : (pointedEtalePi1Map ξ f).hom τ ∈ V.toSubgroup := hRV hmemR
    have hq : ((pointedEtalePi1Map ξ f).hom τ : G) • q0 = q0 := by
      exact (quotientOpenSubgroupShrink_base_fixed_iff.{u, u+1} V
        ((pointedEtalePi1Map ξ f).hom τ)).mpr hmemV
    have hcomm := e.inv.hom.comm ((pointedEtalePi1Map ξ f).hom τ)
    have h := ConcreteCategory.congr_hom hcomm q0
    change e.inv.hom.hom (ConcreteCategory.hom (Q.obj.ρ ((pointedEtalePi1Map ξ f).hom τ)) q0) =
        ((pointedEtalePi1Map ξ f).hom τ).hom.app A (e.inv.hom.hom q0) at h
    rw [show ConcreteCategory.hom (Q.obj.ρ ((pointedEtalePi1Map ξ f).hom τ)) q0 =
        ((pointedEtalePi1Map ξ f).hom τ : G) • q0 by rfl, hq] at h
    exact h.symm
  have hx : ∀ τ : Aut FX,
      τ.hom.app ((AlgebraicGeometry.FiniteEtale.pullback f).obj A)
        ((fiberCompIso ξ f).hom.app A b) = (fiberCompIso ξ f).hom.app A b := by
    intro τ
    exact pointedEtalePi1Map_fixed_pullback_point ξ f A b τ (hpre_fixed τ)
  obtain ⟨m, hm⟩ := finiteEtaleSelfFiberPoint_map_of_fixed_pullback_point ξ f A b hx
  have hbσ : σ.hom.app A b = b := by
    have hnat := σ.hom.naturality m
    have h := ConcreteCategory.congr_hom hnat (finiteEtaleSelfFiberPoint ξ f)
    change σ.hom.app A
        ((AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).map m (finiteEtaleSelfFiberPoint ξ f)) =
      (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f)).map m
        (σ.hom.app (finiteEtaleCoverOfIsFiniteEtale f) (finiteEtaleSelfFiberPoint ξ f)) at h
    have hσa : σ.hom.app (finiteEtaleCoverOfIsFiniteEtale f) (finiteEtaleSelfFiberPoint ξ f) =
        finiteEtaleSelfFiberPoint ξ f := by
      exact (MulAction.mem_stabilizer_iff.mp hσ)
    rw [hm, hσa, hm] at h
    exact h
  have hqσ : (σ : G) • q0 = q0 := by
    have hcomm := e.hom.hom.comm σ
    have h := ConcreteCategory.congr_hom hcomm b
    change e.hom.hom.hom (σ.hom.app A b) =
        ConcreteCategory.hom (Q.obj.ρ σ) (e.hom.hom.hom b) at h
    rw [hbσ] at h
    have hinv : e.hom.hom.hom b = q0 := by
      have h' := ConcreteCategory.congr_hom
        (congrArg (fun k : Q ⟶ Q ↦ k.hom.hom) e.inv_hom_id) q0
      change ((e.inv.hom.hom ≫ e.hom.hom.hom) : Q.obj.V ⟶ Q.obj.V) q0 = q0 at h'
      simpa [b] using h'
    rw [hinv] at h
    change q0 = (σ : G) • q0 at h
    exact h.symm
  exact hσV ((quotientOpenSubgroupShrink_base_fixed_iff.{u, u+1} V σ).mp hqσ)

/-- Finite-étale morphisms induce finite-index image on pointed étale fundamental groups. -/
theorem pointedEtalePi1Map_finiteIndex_range_of_isFiniteEtale
    {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) [IsFiniteEtale f] :
    Subgroup.FiniteIndex (MonoidHom.range (pointedEtalePi1Map ξ f).hom.toMonoidHom) :=
  pointedEtalePi1Map_finiteIndex_range_of_isFiniteEtale_of_stabilizer_le ξ f
    (finiteEtaleSelfFiberPoint_stabilizer_le_range ξ f)

section PointedEtalePi1OuterFunctoriality

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- Pullback of finite-étale covers along the identity is naturally isomorphic to the identity
functor. -/
noncomputable def finiteEtalePullbackIdIso (X : Scheme.{u}) :
    AlgebraicGeometry.FiniteEtale.pullback (𝟙 X) ≅ 𝟭 (AlgebraicGeometry.FiniteEtale X) :=
  NatIso.ofComponents (fun A ↦
    MorphismProperty.Over.isoMk (asIso (Limits.pullback.fst A.hom (𝟙 X))) (by
      simpa using (Limits.pullback.condition :
        Limits.pullback.fst A.hom (𝟙 X) ≫ A.hom =
          Limits.pullback.snd A.hom (𝟙 X) ≫ 𝟙 X)))
    (fun {A B} g ↦ by
      apply MorphismProperty.Over.Hom.ext
      change ((AlgebraicGeometry.FiniteEtale.pullback (𝟙 X)).map g).left ≫
          (asIso (Limits.pullback.fst B.hom (𝟙 X))).hom =
        (asIso (Limits.pullback.fst A.hom (𝟙 X))).hom ≫ g.left
      rw [MorphismProperty.Over.pullback_map_left]
      simp)

/-- The induced comparison between the pulled-back fiber functor along `𝟙 X` and the original
fiber functor. -/
noncomputable def finiteEtalePullbackIdFiberIso {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X) :
    AlgebraicGeometry.FiniteEtale.pullback (𝟙 X) ⋙
        AlgebraicGeometry.FiniteEtale.fiber ξ ≅ AlgebraicGeometry.FiniteEtale.fiber ξ :=
  Functor.isoWhiskerRight (finiteEtalePullbackIdIso X)
      (AlgebraicGeometry.FiniteEtale.fiber ξ) ≪≫
    Functor.leftUnitor (AlgebraicGeometry.FiniteEtale.fiber ξ)

lemma mapAut_finiteEtalePullbackId {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (x : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ)) :
    Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
      ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale X)
        (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
        (AlgebraicGeometry.FiniteEtale.pullback (𝟙 X))) x =
      (finiteEtalePullbackIdFiberIso ξ).symm.conjAut x := by
  ext A a
  simp [Functor.mapAut, Iso.conj_apply, finiteEtalePullbackIdFiberIso,
    finiteEtalePullbackIdIso]

/-- The inner automorphism measuring the identity coherence for `pointedEtalePi1Map`. -/
noncomputable def pointedEtalePi1MapIdConjugator {X : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X) :
    Aut (AlgebraicGeometry.FiniteEtale.fiber ξ) :=
  fiberCompIso ξ (𝟙 X) ≪≫ finiteEtalePullbackIdFiberIso ξ

lemma pointedEtalePi1Map_id_apply {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (x : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ)) :
    (pointedEtalePi1Map ξ (𝟙 X)) x =
      (pointedEtalePi1MapIdConjugator ξ).symm.conjAut x := by
  change (fiberCompIso ξ (𝟙 X)).symm.conjAut
      (Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
        ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale X)
          (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
          (AlgebraicGeometry.FiniteEtale.pullback (𝟙 X))) x) =
    (pointedEtalePi1MapIdConjugator ξ).symm.conjAut x
  rw [mapAut_finiteEtalePullbackId]
  simp [pointedEtalePi1MapIdConjugator, Iso.trans_conjAut]
  rfl

/-- Pulling back finite-étale covers along a composite identifies with the iterated pullback,
after whiskering by the source fiber functor. -/
noncomputable def finiteEtalePullbackCompFiberIso {X Y Z : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    AlgebraicGeometry.FiniteEtale.pullback (f ≫ g) ⋙
        AlgebraicGeometry.FiniteEtale.fiber ξ ≅
      AlgebraicGeometry.FiniteEtale.pullback g ⋙
        AlgebraicGeometry.FiniteEtale.pullback f ⋙
          AlgebraicGeometry.FiniteEtale.fiber ξ :=
  Functor.isoWhiskerRight
      (MorphismProperty.Over.pullbackComp (P := @IsFiniteEtale) (Q := ⊤) f g)
      (AlgebraicGeometry.FiniteEtale.fiber ξ) ≪≫
    Functor.associator (AlgebraicGeometry.FiniteEtale.pullback g)
      (AlgebraicGeometry.FiniteEtale.pullback f)
      (AlgebraicGeometry.FiniteEtale.fiber ξ)

lemma mapAut_finiteEtalePullbackComp {X Y Z : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ)) :
    Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
      ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
        (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
        (AlgebraicGeometry.FiniteEtale.pullback (f ≫ g))) x =
      (finiteEtalePullbackCompFiberIso ξ f g).symm.conjAut
        (Functor.mapAut
          (AlgebraicGeometry.FiniteEtale.pullback f ⋙
            AlgebraicGeometry.FiniteEtale.fiber ξ)
          ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
            (AlgebraicGeometry.FiniteEtale Y) FintypeCat).obj
            (AlgebraicGeometry.FiniteEtale.pullback g))
          (Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
            ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Y)
              (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
              (AlgebraicGeometry.FiniteEtale.pullback f)) x)) := by
  ext A a
  simp [Functor.mapAut, Iso.conj_apply, finiteEtalePullbackCompFiberIso]

/-- The middle automorphism obtained by functoriality of `mapAut` along two pullbacks. -/
noncomputable def pointedEtalePi1MapCompMiddle {X Y Z : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ)) :
    Aut (AlgebraicGeometry.FiniteEtale.pullback g ⋙
      AlgebraicGeometry.FiniteEtale.pullback f ⋙
        AlgebraicGeometry.FiniteEtale.fiber ξ) :=
  Functor.mapAut
    (AlgebraicGeometry.FiniteEtale.pullback f ⋙
      AlgebraicGeometry.FiniteEtale.fiber ξ)
    ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
      (AlgebraicGeometry.FiniteEtale Y) FintypeCat).obj
      (AlgebraicGeometry.FiniteEtale.pullback g))
    (Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
      ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Y)
        (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
        (AlgebraicGeometry.FiniteEtale.pullback f)) x)

/-- The one-step path from the iterated pullback fiber functor to the fiber of `ξ ≫ (f ≫ g)`. -/
noncomputable def pointedEtalePi1MapCompIsoLeft {X Y Z : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    AlgebraicGeometry.FiniteEtale.pullback g ⋙
        AlgebraicGeometry.FiniteEtale.pullback f ⋙
          AlgebraicGeometry.FiniteEtale.fiber ξ ≅
      AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ (f ≫ g)) :=
  (finiteEtalePullbackCompFiberIso ξ f g).symm ≪≫ (fiberCompIso ξ (f ≫ g)).symm

/-- The two-step path from the iterated pullback fiber functor through `ξ ≫ f` to the final
fiber functor. -/
noncomputable def pointedEtalePi1MapCompIsoRight {X Y Z : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    AlgebraicGeometry.FiniteEtale.pullback g ⋙
        AlgebraicGeometry.FiniteEtale.pullback f ⋙
          AlgebraicGeometry.FiniteEtale.fiber ξ ≅
      AlgebraicGeometry.FiniteEtale.fiber ((ξ ≫ f) ≫ g) :=
  (((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
      (AlgebraicGeometry.FiniteEtale Y) FintypeCat).obj
      (AlgebraicGeometry.FiniteEtale.pullback g)).mapIso (fiberCompIso ξ f)).symm ≪≫
    (fiberCompIso (ξ ≫ f) g).symm

lemma pointedEtalePi1Map_comp_left_apply {X Y Z : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Z]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ)) :
    (pointedEtalePi1Map ξ (f ≫ g)) x =
      (pointedEtalePi1MapCompIsoLeft ξ f g).conjAut
        (pointedEtalePi1MapCompMiddle ξ f g x) := by
  change (fiberCompIso ξ (f ≫ g)).symm.conjAut
      (Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
        ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
          (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
          (AlgebraicGeometry.FiniteEtale.pullback (f ≫ g))) x) =
    (pointedEtalePi1MapCompIsoLeft ξ f g).conjAut
      (pointedEtalePi1MapCompMiddle ξ f g x)
  rw [mapAut_finiteEtalePullbackComp]
  simp [pointedEtalePi1MapCompIsoLeft, pointedEtalePi1MapCompMiddle, Iso.trans_conjAut]

lemma mapAut_finiteEtalePullback_conj_fiberCompIso {X Y Z : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Aut (AlgebraicGeometry.FiniteEtale.pullback f ⋙
      AlgebraicGeometry.FiniteEtale.fiber ξ)) :
    Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f))
      ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
        (AlgebraicGeometry.FiniteEtale Y) FintypeCat).obj
        (AlgebraicGeometry.FiniteEtale.pullback g))
      ((fiberCompIso ξ f).symm.conjAut x) =
    ((((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
          (AlgebraicGeometry.FiniteEtale Y) FintypeCat).obj
          (AlgebraicGeometry.FiniteEtale.pullback g)).mapIso
        (fiberCompIso ξ f)).symm).conjAut
      (Functor.mapAut (AlgebraicGeometry.FiniteEtale.pullback f ⋙
          AlgebraicGeometry.FiniteEtale.fiber ξ)
        ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
          (AlgebraicGeometry.FiniteEtale Y) FintypeCat).obj
          (AlgebraicGeometry.FiniteEtale.pullback g)) x) := by
  exact
    (Functor.map_conjAut
      ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
        (AlgebraicGeometry.FiniteEtale Y) FintypeCat).obj
        (AlgebraicGeometry.FiniteEtale.pullback g))
      (fiberCompIso ξ f).symm x)

lemma pointedEtalePi1Map_comp_right_apply {X Y Z : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y] [ConnectedSpace Z]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Aut (AlgebraicGeometry.FiniteEtale.fiber ξ)) :
    (pointedEtalePi1Map ξ f ≫ pointedEtalePi1Map (ξ ≫ f) g) x =
      (pointedEtalePi1MapCompIsoRight ξ f g).conjAut
        (pointedEtalePi1MapCompMiddle ξ f g x) := by
  change (pointedEtalePi1Map (ξ := ξ ≫ f) g)
      ((fiberCompIso ξ f).symm.conjAut
        (Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
          ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Y)
            (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
            (AlgebraicGeometry.FiniteEtale.pullback f)) x)) =
    (pointedEtalePi1MapCompIsoRight ξ f g).conjAut
      (pointedEtalePi1MapCompMiddle ξ f g x)
  change (fiberCompIso (ξ ≫ f) g).symm.conjAut
      (Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ f))
        ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Z)
          (AlgebraicGeometry.FiniteEtale Y) FintypeCat).obj
          (AlgebraicGeometry.FiniteEtale.pullback g))
        ((fiberCompIso ξ f).symm.conjAut
          (Functor.mapAut (AlgebraicGeometry.FiniteEtale.fiber ξ)
            ((Functor.whiskeringLeft (AlgebraicGeometry.FiniteEtale Y)
              (AlgebraicGeometry.FiniteEtale X) FintypeCat).obj
              (AlgebraicGeometry.FiniteEtale.pullback f)) x))) =
    (pointedEtalePi1MapCompIsoRight ξ f g).conjAut
      (pointedEtalePi1MapCompMiddle ξ f g x)
  rw [mapAut_finiteEtalePullback_conj_fiberCompIso]
  simp [pointedEtalePi1MapCompIsoRight, pointedEtalePi1MapCompMiddle, Iso.trans_conjAut]

/-- The inner automorphism comparing the one-step and two-step pullback paths for composition. -/
noncomputable def pointedEtalePi1MapCompConjugator {X Y Z : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    Aut (AlgebraicGeometry.FiniteEtale.fiber (ξ ≫ (f ≫ g))) :=
  (pointedEtalePi1MapCompIsoLeft ξ f g).symm ≪≫
    pointedEtalePi1MapCompIsoRight ξ f g

/-- `pointedEtalePi1Map` sends identity morphisms to identity morphisms in the outer quotient. -/
theorem pointedEtalePi1Map_id_outer {X : Scheme.{u}} [ConnectedSpace X]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X) :
    let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
    Q.map (pointedEtalePi1Map ξ (𝟙 X)) = Q.map (𝟙 (pointedEtalePi1 ξ)) := by
  intro Q
  apply CategoryTheory.Quotient.sound
  dsimp [profiniteGrpOuterRel]
  use pointedEtalePi1MapIdConjugator ξ
  intro x
  dsimp [pointedEtalePi1] at x ⊢
  change (ContinuousMonoidHom.id (Aut (AlgebraicGeometry.FiniteEtale.fiber ξ))) x =
    Iso.symm (pointedEtalePi1MapIdConjugator ξ) ≪≫
      (pointedEtalePi1Map ξ (𝟙 X)) x ≪≫ pointedEtalePi1MapIdConjugator ξ
  rw [pointedEtalePi1Map_id_apply]
  ext
  simp [Iso.conj_apply]

/-- `pointedEtalePi1Map` is functorial for composition in the outer quotient. -/
theorem pointedEtalePi1Map_comp_outer {X Y Z : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y] [ConnectedSpace Z]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
    Q.map (pointedEtalePi1Map ξ (f ≫ g)) =
      Q.map (pointedEtalePi1Map ξ f ≫ pointedEtalePi1Map (ξ ≫ f) g) := by
  intro Q
  apply CategoryTheory.Quotient.sound
  dsimp [profiniteGrpOuterRel]
  use pointedEtalePi1MapCompConjugator ξ f g
  intro x
  dsimp [pointedEtalePi1] at x ⊢
  change (pointedEtalePi1Map ξ f ≫ pointedEtalePi1Map (ξ ≫ f) g) x =
    Iso.symm (pointedEtalePi1MapCompConjugator ξ f g) ≪≫
      (pointedEtalePi1Map ξ (f ≫ g)) x ≪≫
        pointedEtalePi1MapCompConjugator ξ f g
  rw [pointedEtalePi1Map_comp_left_apply, pointedEtalePi1Map_comp_right_apply]
  dsimp [pointedEtalePi1]
  ext
  simp [pointedEtalePi1MapCompConjugator, Iso.conj_apply]

end PointedEtalePi1OuterFunctoriality

/-- The separable-closure geometric point of the base `Spec K`. -/
noncomputable def baseGeometricPoint {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : Spec (.of (AlgebraicClosure K)) ⟶ baseScheme K :=
  Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K)))

/-- The large-universe full pointed étale fundamental group of `Spec K`. -/
noncomputable def basePointedEtalePi1Large {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : ProfiniteGrp.{u + 1} :=
  pointedEtalePi1 (baseGeometricPoint K)

/-- The base absolute Galois group.  The comparison with the pointed étale
`π₁(Spec K, Spec K̄)` is a theorem-level comparison, not a global base-point choice in this
Hom-form statement. -/
noncomputable def baseGalois {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : ProfiniteGrp.{u} :=
  InfiniteGalois.profiniteGalGrp K (AlgebraicClosure K)

/-- The large-universe copy of the base absolute Galois group. -/
noncomputable def baseGaloisLarge {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : ProfiniteGrp.{u + 1} :=
  uliftProfiniteGrp (baseGalois K)

/-- Comparison between the usual absolute Galois group and the pointed finite-étale
`π₁(Spec K, Spec K̄)`. -/
noncomputable def baseGaloisPointedEtalePi1Iso {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : baseGaloisLarge K ≅ basePointedEtalePi1Large K :=
  show AlgebraicGeometry.FiniteEtale.uliftProfiniteGrp
      (AlgebraicGeometry.FiniteEtale.galProfiniteGrp K (AlgebraicClosure K)) ≅
    ProfiniteGrp.of (Aut (AlgebraicGeometry.FiniteEtale.fiber
      (AlgebraicGeometry.FiniteEtale.baseGeom K (AlgebraicClosure K)))) from
    AlgebraicGeometry.FiniteEtale.galUliftAutFiberIso K (AlgebraicClosure K)

namespace ProperHyperbolicCurveOver

variable {p : ℕ} [Fact p.Prime] {K : PadicLocalFieldCat.{u} p}

/-- Proper hyperbolic curves are connected as schemes. -/
instance connectedSpace (X : ProperHyperbolicCurveOver K) : ConnectedSpace X.toScheme := by
  letI : GeometricallyConnected X.toOver.hom := X.obj.property.geometricallyConnected
  exact GeometricallyConnected.connectedSpace_of_subsingleton (f := X.toOver.hom)

/-- A proper hyperbolic curve has at least two points. -/
instance nontrivialSpace (X : ProperHyperbolicCurveOver K) : Nontrivial X.toScheme := by
  haveI : SmoothOfRelativeDimension 1 X.toOver.hom := X.smoothOfRelativeDimension
  exact scheme_nontrivial_of_smoothOfRelativeDimension_one_to_Spec_field K X.toOver.hom

/-- In an irreducible proper hyperbolic curve, the generic point is not closed. -/
theorem genericPoint_not_isClosed (X : ProperHyperbolicCurveOver K)
    [IrreducibleSpace X.toScheme] :
    ¬ IsClosed ({genericPoint X.toScheme} : Set X.toScheme) := by
  intro hclosed
  have hclosure : closure ({genericPoint X.toScheme} : Set X.toScheme) =
      ({genericPoint X.toScheme} : Set X.toScheme) := hclosed.closure_eq
  have huniv : closure ({genericPoint X.toScheme} : Set X.toScheme) = Set.univ :=
    (genericPoint_spec X.toScheme).def
  have hsingle_univ : ({genericPoint X.toScheme} : Set X.toScheme) = Set.univ := by
    rw [← hclosure, huniv]
  have hsub : Subsingleton X.toScheme := ⟨fun x y ↦ by
    have hx : x ∈ ({genericPoint X.toScheme} : Set X.toScheme) := by
      rw [hsingle_univ]
      trivial
    have hy : y ∈ ({genericPoint X.toScheme} : Set X.toScheme) := by
      rw [hsingle_univ]
      trivial
    rw [Set.mem_singleton_iff] at hx hy
    exact hx.trans hy.symm⟩
  exact not_subsingleton X.toScheme hsub

/-- Finite fibers for dominant morphisms of proper hyperbolic curves, conditional only on the
remaining irreducibility bridge for the two curves. -/
theorem hom_finite_fibers_of_irreducible
    {X Y : ProperHyperbolicCurveOver K} (f : X ⟶ Y)
    [IrreducibleSpace X.toScheme] [IrreducibleSpace Y.toScheme] :
    ∀ y : Y.toScheme, (f.hom.hom.left ⁻¹' {y}).Finite :=
  hom_finite_fibers_of_irreducible_of_generic_not_closed f (genericPoint_not_isClosed Y)

/-- Local quasi-finiteness for dominant morphisms of proper hyperbolic curves, conditional on the
remaining irreducibility bridge for the two curves. -/
theorem hom_locallyQuasiFinite_of_irreducible
    {X Y : ProperHyperbolicCurveOver K} (f : X ⟶ Y)
    [IrreducibleSpace X.toScheme] [IrreducibleSpace Y.toScheme] :
    LocallyQuasiFinite f.hom.hom.left :=
  (hom_locallyQuasiFinite_iff_finite_preimage_singleton f).2
    (hom_finite_fibers_of_irreducible f)

/-- Finiteness for dominant morphisms of proper hyperbolic curves, conditional on the remaining
irreducibility bridge for the two curves. -/
theorem hom_isFinite_of_irreducible
    {X Y : ProperHyperbolicCurveOver K} (f : X ⟶ Y)
    [IrreducibleSpace X.toScheme] [IrreducibleSpace Y.toScheme] :
    IsFinite f.hom.hom.left :=
  hom_isFinite_of_locallyQuasiFinite f (hom_locallyQuasiFinite_of_irreducible f)

end ProperHyperbolicCurveOver

/-- A geometric point of a proper hyperbolic curve over the fixed algebraic closure of `K`.

This is ordinary input data, not a globally selected base point.  The unpointed arithmetic `π₁`
profunctors below must package the usual independence of this choice. -/
structure CurveGeometricPointOver {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : ProperHyperbolicCurveOver K) where
  point : Spec (.of (AlgebraicClosure K)) ⟶ X.toScheme
  map_to_base : point ≫ X.toOver.hom = baseGeometricPoint K

namespace CurveGeometricPointOver

variable {p : ℕ} [Fact p.Prime] {K : PadicLocalFieldCat.{u} p}
variable {X Y Z : ProperHyperbolicCurveOver K}

/-- Push a geometric point forward along a morphism of curves over `K`. -/
noncomputable def map (ξ : CurveGeometricPointOver K X) (f : X ⟶ Y) :
    CurveGeometricPointOver K Y where
  point := ξ.point ≫ f.hom.hom.left
  map_to_base := by
    rw [Category.assoc]
    rw [f.hom.hom.w]
    exact ξ.map_to_base

@[simp]
theorem map_id (ξ : CurveGeometricPointOver K X) : map ξ (𝟙 X) = ξ :=
  rfl

@[simp]
theorem map_comp (ξ : CurveGeometricPointOver K X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    map ξ (f ≫ g) = map (map ξ f) g :=
  rfl

end CurveGeometricPointOver

/-- The large-universe pointed étale `π₁` attached to a chosen geometric point.  This is useful
for describing the intended semantics of the point-free profunctor, but the Hom-form statement does
not select such a point globally. -/
noncomputable def properHyperbolicCurvePointedEtalePi1Large {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : ProperHyperbolicCurveOver K)
    (ξ : CurveGeometricPointOver K X) : ProfiniteGrp.{u + 1} :=
  pointedEtalePi1 ξ.point

/-- The large-universe augmentation from a pointed curve `π₁` to the pointed base `π₁`. -/
noncomputable def properHyperbolicCurvePointedEtalePi1ToBaseLarge {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : ProperHyperbolicCurveOver K)
    (ξ : CurveGeometricPointOver K X) :
    properHyperbolicCurvePointedEtalePi1Large K X ξ ⟶ basePointedEtalePi1Large K :=
  show pointedEtalePi1 ξ.point ⟶ pointedEtalePi1 (baseGeometricPoint K) from
    pointedEtalePi1Map ξ.point X.toOver.hom ≫
      (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base) :
        pointedEtalePi1 (ξ.point ≫ X.toOver.hom) ⟶ pointedEtalePi1 (baseGeometricPoint K))

@[simp]
theorem properHyperbolicCurvePointedEtalePi1ToBaseLarge_eq {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : ProperHyperbolicCurveOver K)
    (ξ : CurveGeometricPointOver K X) :
    properHyperbolicCurvePointedEtalePi1ToBaseLarge K X ξ =
      pointedEtalePi1Map ξ.point X.toOver.hom ≫
        (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base) :
          pointedEtalePi1 (ξ.point ≫ X.toOver.hom) ⟶ pointedEtalePi1 (baseGeometricPoint K)) :=
  rfl

/-- Transport a pointed `π₁` map across an equality of scheme morphisms by the matching
`eqToHom` on the target pointed `π₁`. -/
lemma pointedEtalePi1Map_eqToHom {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (ξ : Spec (.of Ω) ⟶ X) {f g : X ⟶ Y} (h : f = g) :
    pointedEtalePi1Map ξ f ≫
      (eqToHom (congrArg pointedEtalePi1 (congrArg (fun t : X ⟶ Y ↦ ξ ≫ t) h)) :
        pointedEtalePi1 (ξ ≫ f) ⟶ pointedEtalePi1 (ξ ≫ g)) =
    pointedEtalePi1Map ξ g := by
  subst h
  simp

/-- Raw compatibility of the curve-to-base pointed `π₁` maps with morphisms over the base,
with the dependent target equalities expressed by `eqToHom`. -/
theorem pointedEtalePi1Map_toBase_raw {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X Y : ProperHyperbolicCurveOver K}
    (ξ : CurveGeometricPointOver K X) (f : X ⟶ Y) :
    pointedEtalePi1Map ξ.point (f.hom.hom.left ≫ Y.toOver.hom) ≫
        (eqToHom (congrArg pointedEtalePi1 (ξ.map f).map_to_base) :
          pointedEtalePi1 ((ξ.map f).point ≫ Y.toOver.hom) ⟶
            pointedEtalePi1 (baseGeometricPoint K)) =
      pointedEtalePi1Map ξ.point X.toOver.hom ≫
        (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base) :
          pointedEtalePi1 (ξ.point ≫ X.toOver.hom) ⟶
            pointedEtalePi1 (baseGeometricPoint K)) := by
  let e : ξ.point ≫ (f.hom.hom.left ≫ Y.toOver.hom) = ξ.point ≫ X.toOver.hom :=
    congrArg (fun t : X.toScheme ⟶ baseScheme K ↦ ξ.point ≫ t) f.hom.hom.w
  calc
    pointedEtalePi1Map ξ.point (f.hom.hom.left ≫ Y.toOver.hom) ≫
        (eqToHom (congrArg pointedEtalePi1 (ξ.map f).map_to_base) :
          pointedEtalePi1 ((ξ.map f).point ≫ Y.toOver.hom) ⟶
            pointedEtalePi1 (baseGeometricPoint K))
        = pointedEtalePi1Map ξ.point (f.hom.hom.left ≫ Y.toOver.hom) ≫
          ((eqToHom (congrArg pointedEtalePi1 e) :
              pointedEtalePi1 (ξ.point ≫ (f.hom.hom.left ≫ Y.toOver.hom)) ⟶
                pointedEtalePi1 (ξ.point ≫ X.toOver.hom)) ≫
            (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base) :
              pointedEtalePi1 (ξ.point ≫ X.toOver.hom) ⟶
                pointedEtalePi1 (baseGeometricPoint K))) := by
            rw [eqToHom_trans]
            rfl
    _ = (pointedEtalePi1Map ξ.point (f.hom.hom.left ≫ Y.toOver.hom) ≫
          (eqToHom (congrArg pointedEtalePi1 e) :
              pointedEtalePi1 (ξ.point ≫ (f.hom.hom.left ≫ Y.toOver.hom)) ⟶
                pointedEtalePi1 (ξ.point ≫ X.toOver.hom))) ≫
            (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base) :
              pointedEtalePi1 (ξ.point ≫ X.toOver.hom) ⟶
                pointedEtalePi1 (baseGeometricPoint K)) := by
          rw [Category.assoc]
    _ = pointedEtalePi1Map ξ.point X.toOver.hom ≫
        (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base) :
          pointedEtalePi1 (ξ.point ≫ X.toOver.hom) ⟶
            pointedEtalePi1 (baseGeometricPoint K)) := by
          rw [pointedEtalePi1Map_eqToHom ξ.point f.hom.hom.w]

/-- In the outer quotient, the chosen curve-to-base augmentation is represented by the raw
scheme-map `π₁` morphism followed by the `eqToHom` transport to the fixed base point. -/
theorem properHyperbolicCurvePointedEtalePi1ToBaseLarge_outer_map {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X : ProperHyperbolicCurveOver K}
    (ξ : CurveGeometricPointOver K X) :
    (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map
        (properHyperbolicCurvePointedEtalePi1ToBaseLarge K X ξ) =
      (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map
          (pointedEtalePi1Map ξ.point X.toOver.hom) ≫
        (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map
          (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base)) := by
  let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
  change Q.map
      (show pointedEtalePi1 ξ.point ⟶ pointedEtalePi1 (baseGeometricPoint K) from
        pointedEtalePi1Map ξ.point X.toOver.hom ≫
          (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base) :
            pointedEtalePi1 (ξ.point ≫ X.toOver.hom) ⟶ pointedEtalePi1 (baseGeometricPoint K))) = _
  rw [Q.map_comp]

/-! ## Proper-hyperbolic-curve Hom-form statement -/

/-- The augmented profinite data category over the base Galois group `Γ_K`. -/
abbrev properHyperbolicCurveData {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) : Type (u + 1) :=
  OpenAugProfiniteOver (baseGalois K)

/-- A data object, transported to the large universe used by pointed finite-étale `π₁`. -/
noncomputable def openAugProfiniteULift {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (G : properHyperbolicCurveData K) :
    OpenAugProfiniteOver (baseGaloisLarge K) :=
  { obj := CostructuredArrow.mk (uliftProfiniteGrpMap G.asAug.hom) }

/-- A data morphism, transported to the large universe used by pointed finite-étale `π₁`. -/
noncomputable def openAugProfiniteULiftMap {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {G H : properHyperbolicCurveData K} (f : G ⟶ H) :
    openAugProfiniteULift K G ⟶ openAugProfiniteULift K H :=
  { hom := CostructuredArrow.homMk (uliftProfiniteGrpMap f.hom.left) (by
      change uliftProfiniteGrpMap f.hom.left ≫ uliftProfiniteGrpMap H.asAug.hom =
        uliftProfiniteGrpMap G.asAug.hom
      rw [← uliftProfiniteGrpMap_comp]
      exact congrArg uliftProfiniteGrpMap f.hom.w)
    property := uliftProfiniteGrpMap_isOpenMap f.hom.left f.property }

@[simp]
theorem openAugProfiniteULiftMap_id {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} (G : properHyperbolicCurveData K) :
    openAugProfiniteULiftMap (𝟙 G) = 𝟙 (openAugProfiniteULift K G) := by
  ext x
  cases x
  rfl

@[simp]
theorem openAugProfiniteULiftMap_comp {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {G H I : properHyperbolicCurveData K}
    (f : G ⟶ H) (g : H ⟶ I) :
    openAugProfiniteULiftMap (f ≫ g) = openAugProfiniteULiftMap f ≫ openAugProfiniteULiftMap g := by
  ext x
  cases x
  rfl

/-- The pointed arithmetic `π₁` object associated to an explicit geometric point, in the same
large-universe augmented category as lifted data objects. -/
noncomputable def pointedEtalePi1ObjLarge {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) (X : ProperHyperbolicCurveOver K)
    (ξ : CurveGeometricPointOver K X) : OpenAugProfiniteOver (baseGaloisLarge K) :=
  { obj := CostructuredArrow.mk
      (properHyperbolicCurvePointedEtalePi1ToBaseLarge K X ξ ≫
        (baseGaloisPointedEtalePi1Iso K).inv) }

/-- Outer homomorphisms over the large-universe base comparison. -/
abbrev LargeOuterHomOver {p : ℕ} [Fact p.Prime] (K : PadicLocalFieldCat.{u} p)
    (A B : OpenAugProfiniteOver (baseGaloisLarge K)) : Type (u + 1) :=
  OuterHomOver A B

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- The pointed curve-to-base augmentation is compatible with morphisms of curves after
quotienting profinite-group morphisms by target inner conjugacy. -/
theorem pointedEtalePi1Map_toBase_outer {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X Y : ProperHyperbolicCurveOver K}
    (ξ : CurveGeometricPointOver K X) (f : X ⟶ Y) :
    let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
    Q.map (pointedEtalePi1Map ξ.point f.hom.hom.left) ≫
        Q.map (properHyperbolicCurvePointedEtalePi1ToBaseLarge K Y (ξ.map f)) =
      Q.map (properHyperbolicCurvePointedEtalePi1ToBaseLarge K X ξ) := by
  intro Q
  change (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map
        (pointedEtalePi1Map ξ.point f.hom.hom.left) ≫
      (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map
        (properHyperbolicCurvePointedEtalePi1ToBaseLarge K Y (ξ.map f)) =
    (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map
      (properHyperbolicCurvePointedEtalePi1ToBaseLarge K X ξ)
  rw [properHyperbolicCurvePointedEtalePi1ToBaseLarge_outer_map (K := K) (X := Y)
    (ξ := ξ.map f)]
  rw [properHyperbolicCurvePointedEtalePi1ToBaseLarge_outer_map (K := K) (X := X) (ξ := ξ)]
  let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
  change Q.map (pointedEtalePi1Map ξ.point f.hom.hom.left) ≫
      (Q.map (pointedEtalePi1Map (ξ.map f).point Y.toOver.hom) ≫
        Q.map (eqToHom (congrArg pointedEtalePi1 (ξ.map f).map_to_base))) =
    Q.map (pointedEtalePi1Map ξ.point X.toOver.hom) ≫
      Q.map (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base))
  rw [← Category.assoc]
  rw [← Q.map_comp]
  change Q.map (pointedEtalePi1Map ξ.point f.hom.hom.left ≫
        pointedEtalePi1Map (ξ.point ≫ f.hom.hom.left) Y.toOver.hom) ≫
      Q.map (eqToHom (congrArg pointedEtalePi1 (ξ.map f).map_to_base)) =
    Q.map (pointedEtalePi1Map ξ.point X.toOver.hom) ≫
      Q.map (eqToHom (congrArg pointedEtalePi1 ξ.map_to_base))
  have hcomp := pointedEtalePi1Map_comp_outer ξ.point f.hom.hom.left Y.toOver.hom
  dsimp only at hcomp
  rw [← hcomp]
  rw [← Q.map_comp, ← Q.map_comp]
  apply congrArg Q.map
  exact pointedEtalePi1Map_toBase_raw ξ f

/-- The point-indexed outer `π₁` map induced by a morphism of curves.

This is point-indexed functoriality: the source point is input data and the target point is its
pushforward.  No curve base point is selected globally. -/
noncomputable def pointedEtalePi1OuterMapLarge {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X Y : ProperHyperbolicCurveOver K}
    (ξ : CurveGeometricPointOver K X) (f : X ⟶ Y) :
    LargeOuterHomOver K (pointedEtalePi1ObjLarge K X ξ)
      (pointedEtalePi1ObjLarge K Y (ξ.map f)) := by
  let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
  exact CostructuredArrow.homMk (Q.map (pointedEtalePi1Map ξ.point f.hom.hom.left)) (by
    change Q.map (pointedEtalePi1Map ξ.point f.hom.hom.left) ≫
        Q.map ((properHyperbolicCurvePointedEtalePi1ToBaseLarge K Y (ξ.map f)) ≫
          (baseGaloisPointedEtalePi1Iso K).inv) =
      Q.map ((properHyperbolicCurvePointedEtalePi1ToBaseLarge K X ξ) ≫
        (baseGaloisPointedEtalePi1Iso K).inv)
    rw [Q.map_comp, Q.map_comp]
    rw [← Category.assoc]
    have h := pointedEtalePi1Map_toBase_outer ξ f
    dsimp only at h
    rw [h])

/-- Point-indexed arithmetic `π₁` maps are open. -/
axiom pointedEtalePi1OuterMapLarge_isOpen {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X Y : ProperHyperbolicCurveOver K}
    (ξ : CurveGeometricPointOver K X) (f : X ⟶ Y) :
    IsOpenOuterHomOver (pointedEtalePi1OuterMapLarge ξ f)

/-- Point-indexed arithmetic `π₁` sends identity morphisms to identity outer morphisms. -/
@[simp]
theorem pointedEtalePi1OuterMapLarge_id {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X : ProperHyperbolicCurveOver K}
    (ξ : CurveGeometricPointOver K X) :
    pointedEtalePi1OuterMapLarge ξ (𝟙 X) =
      𝟙 (openAugProfiniteAsOuter (pointedEtalePi1ObjLarge K X ξ)) := by
  apply CostructuredArrow.hom_ext
  change (CategoryTheory.Quotient.functor profiniteGrpOuterRel).map
      (pointedEtalePi1Map ξ.point (𝟙 X.toScheme)) =
    𝟙 ((CategoryTheory.Quotient.functor profiniteGrpOuterRel).obj (pointedEtalePi1 ξ.point))
  have h := pointedEtalePi1Map_id_outer ξ.point
  dsimp only at h
  simpa using h

/-- Point-indexed arithmetic `π₁` maps are functorial for composition. -/
@[simp]
theorem pointedEtalePi1OuterMapLarge_comp {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X Y Z : ProperHyperbolicCurveOver K}
    (ξ : CurveGeometricPointOver K X) (f : X ⟶ Y) (g : Y ⟶ Z) :
    pointedEtalePi1OuterMapLarge ξ (f ≫ g) =
      pointedEtalePi1OuterMapLarge ξ f ≫ pointedEtalePi1OuterMapLarge (ξ.map f) g := by
  apply CostructuredArrow.hom_ext
  let Q := CategoryTheory.Quotient.functor profiniteGrpOuterRel
  change Q.map (pointedEtalePi1Map ξ.point (f.hom.hom.left ≫ g.hom.hom.left)) =
    Q.map (pointedEtalePi1Map ξ.point f.hom.hom.left) ≫
      Q.map (pointedEtalePi1Map (ξ.point ≫ f.hom.hom.left) g.hom.hom.left)
  rw [← Q.map_comp]
  have h := pointedEtalePi1Map_comp_outer ξ.point f.hom.hom.left g.hom.hom.left
  dsimp only at h
  simpa using h

set_option backward.defeqAttrib.useBackward false
set_option backward.isDefEq.respectTransparency true

/-- Pointed representatives for maps from a data object to the unpointed arithmetic `π₁` of `X`.

A representative chooses a geometric point as ordinary element data.  The remaining construction
boundary is the quotient/change-of-point torsor identifying these representatives up to inner
conjugacy; no representative is selected by axiom. -/
abbrev PointedInvariantDatum {p : ℕ} [Fact p.Prime] (K : PadicLocalFieldCat.{u} p)
    (X : ProperHyperbolicCurveOver K) (G : properHyperbolicCurveData K) : Type (u + 1) :=
  Σ ξ : CurveGeometricPointOver K X,
    LargeOuterHomOver K (openAugProfiniteULift K G) (pointedEtalePi1ObjLarge K X ξ)

/-- Map pointed invariant representatives along a curve morphism and a data morphism. -/
noncomputable def pointedInvariantDatumMap {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X Y : ProperHyperbolicCurveOver K}
    {G H : properHyperbolicCurveData K} (f : X ⟶ Y) (g : G ⟶ H) :
    PointedInvariantDatum K X H ⟶ PointedInvariantDatum K Y G :=
  ↾fun a ↦ ⟨a.1.map f,
    openAugProfiniteAsOuterMap (openAugProfiniteULiftMap g) ≫ a.2 ≫
      pointedEtalePi1OuterMapLarge a.1 f⟩

/-- Identity law for `pointedInvariantDatumMap`. -/
@[simp]
theorem pointedInvariantDatumMap_id {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} (X : ProperHyperbolicCurveOver K)
    (G : properHyperbolicCurveData K) :
    pointedInvariantDatumMap (𝟙 X) (𝟙 G) = 𝟙 (PointedInvariantDatum K X G) := by
  ext ⟨ξ, φ⟩ <;> simp [pointedInvariantDatumMap]

/-- Composition law for `pointedInvariantDatumMap`. -/
theorem pointedInvariantDatumMap_comp {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {X Y Z : ProperHyperbolicCurveOver K}
    {G H I : properHyperbolicCurveData K} (f : X ⟶ Y) (f' : Y ⟶ Z)
    (g : G ⟶ H) (g' : H ⟶ I) :
    pointedInvariantDatumMap (f ≫ f') (g ≫ g') =
      pointedInvariantDatumMap f g' ≫ pointedInvariantDatumMap f' g := by
  ext ⟨ξ, φ⟩ <;> simp [pointedInvariantDatumMap]

/-- Pointwise representatives for open maps out of the unpointed arithmetic `π₁` of `X`.

Using pointwise families avoids choosing a lift of a target geometric point when precomposing along
`X ⟶ Y`: a family over all points of `Y` can be evaluated at the pushed-forward point of `X`. -/
abbrev PointwiseAlgorithmDatum {p : ℕ} [Fact p.Prime] (K : PadicLocalFieldCat.{u} p)
    (G : properHyperbolicCurveData K) (X : ProperHyperbolicCurveOver K) : Type (u + 1) :=
  (ξ : CurveGeometricPointOver K X) →
    { φ : LargeOuterHomOver K (pointedEtalePi1ObjLarge K X ξ) (openAugProfiniteULift K G) //
      IsOpenOuterHomOver φ }

/-- Map pointwise algorithm representatives along a data morphism and a curve morphism. -/
noncomputable def pointwiseAlgorithmDatumMap {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {G H : properHyperbolicCurveData K}
    {X Y : ProperHyperbolicCurveOver K} (f : G ⟶ H) (g : X ⟶ Y) :
    PointwiseAlgorithmDatum K G Y ⟶ PointwiseAlgorithmDatum K H X :=
  ↾fun a ξ ↦
    ⟨pointedEtalePi1OuterMapLarge ξ g ≫ (a (ξ.map g)).1 ≫
        openAugProfiniteAsOuterMap (openAugProfiniteULiftMap f), by
      have hpre : IsOpenOuterHomOver
          (pointedEtalePi1OuterMapLarge ξ g ≫ (a (ξ.map g)).1) :=
        isOpenOuterHomOver_comp (pointedEtalePi1OuterMapLarge_isOpen ξ g) (a (ξ.map g)).2
      have hcomp := isOpenOuterHomOver_comp
        (φ := pointedEtalePi1OuterMapLarge ξ g ≫ (a (ξ.map g)).1)
        (ψ := openAugProfiniteAsOuterMap (openAugProfiniteULiftMap f))
        hpre (isOpenOuterHomOver_of_openAugProfiniteHom (openAugProfiniteULiftMap f))
      simpa using hcomp⟩

/-- Identity law for `pointwiseAlgorithmDatumMap`. -/
@[simp]
theorem pointwiseAlgorithmDatumMap_id {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} (G : properHyperbolicCurveData K)
    (X : ProperHyperbolicCurveOver K) :
    pointwiseAlgorithmDatumMap (𝟙 G) (𝟙 X) = 𝟙 (PointwiseAlgorithmDatum K G X) := by
  apply ConcreteCategory.hom_ext
  intro a
  funext ξ
  apply Subtype.ext
  apply CostructuredArrow.hom_ext
  change (pointedEtalePi1OuterMapLarge ξ (𝟙 X) ≫ (a (ξ.map (𝟙 X))).1 ≫
      openAugProfiniteAsOuterMap (openAugProfiniteULiftMap (𝟙 G))).left = (a ξ).1.left
  simp

/-- Composition law for `pointwiseAlgorithmDatumMap`. -/
theorem pointwiseAlgorithmDatumMap_comp {p : ℕ} [Fact p.Prime]
    {K : PadicLocalFieldCat.{u} p} {G H I : properHyperbolicCurveData K}
    {X Y Z : ProperHyperbolicCurveOver K} (f : G ⟶ H) (f' : H ⟶ I)
    (g : X ⟶ Y) (g' : Y ⟶ Z) :
    pointwiseAlgorithmDatumMap (f ≫ f') (g ≫ g') =
      pointwiseAlgorithmDatumMap f g' ≫ pointwiseAlgorithmDatumMap f' g := by
  apply ConcreteCategory.hom_ext
  intro a
  funext ξ
  apply Subtype.ext
  apply CostructuredArrow.hom_ext
  change (pointedEtalePi1OuterMapLarge ξ (g ≫ g') ≫
      (a (ξ.map (g ≫ g'))).1 ≫
      openAugProfiniteAsOuterMap (openAugProfiniteULiftMap (f ≫ f'))).left =
    (pointedEtalePi1OuterMapLarge ξ g ≫
      (pointedEtalePi1OuterMapLarge (ξ.map g) g' ≫
        (a ((ξ.map g).map g')).1 ≫
        openAugProfiniteAsOuterMap (openAugProfiniteULiftMap f)) ≫
      openAugProfiniteAsOuterMap (openAugProfiniteULiftMap f')).left
  simp [openAugProfiniteULiftMap_comp]

/-- The full arithmetic étale `π₁` invariant profunctor for proper hyperbolic curves over `K`.

This is no longer an opaque axiom: its values are pointed representatives, and the named remaining
boundaries say how those representatives descend to the unpointed/change-of-point torsor. -/
noncomputable def properHyperbolicCurveInvariant {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    Profunctor.{u + 1} (ProperHyperbolicCurveOver K) (properHyperbolicCurveData K) :=
  .ofCore {
    obj X G := PointedInvariantDatum K X G
    map f g := pointedInvariantDatumMap f g
    map_id X G := pointedInvariantDatumMap_id X G
    map_comp f f' g g' := pointedInvariantDatumMap_comp f f' g g' }

/-- The open-outer-hom algorithm profunctor attached to full arithmetic étale `π₁`.

This is no longer an opaque axiom: its values are pointwise open outer maps out of each pointed
fiber-functor representative. -/
noncomputable def properHyperbolicCurveAlgorithm {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    Profunctor.{u + 1} (properHyperbolicCurveData K) (ProperHyperbolicCurveOver K) :=
  .ofCore {
    obj G X := PointwiseAlgorithmDatum K G X
    map f g := pointwiseAlgorithmDatumMap f g
    map_id G X := pointwiseAlgorithmDatumMap_id G X
    map_comp f f' g g' := pointwiseAlgorithmDatumMap_comp f f' g g' }

/-- The geometric target profunctor. Its morphisms are dominant because the category was built with
only dominant morphisms. -/
noncomputable abbrev properHyperbolicCurveDominantTarget {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    Profunctor.{u + 1} (ProperHyperbolicCurveOver K) (ProperHyperbolicCurveOver K) :=
  (Profunctor.id (C := ProperHyperbolicCurveOver K)).ulift1

/-- The composite profunctor whose elements are coend classes of open outer homomorphisms
`π₁(X) → π₁(Y)` over `Γ_K`. -/
noncomputable abbrev properHyperbolicCurveComposite {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    Profunctor.{u + 1} (ProperHyperbolicCurveOver K) (ProperHyperbolicCurveOver K) :=
  Profunctor.comp.{u + 1} (properHyperbolicCurveInvariant K) (properHyperbolicCurveAlgorithm K)

/-- Special case of Mochizuki's Hom-form theorem for proper hyperbolic curves over `K`. -/
axiom properHyperbolicCurveHomDecodeIso {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    properHyperbolicCurveComposite K ≅ properHyperbolicCurveDominantTarget K

/-- The standalone profunctor reconstruction package for the proper-curve special case. -/
noncomputable def properHyperbolicCurveHomChallenge {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    ProfunctorReconstruction
      (ProperHyperbolicCurveOver K) (properHyperbolicCurveData K) where
  invariant := properHyperbolicCurveInvariant K
  target := properHyperbolicCurveDominantTarget K
  algorithm := properHyperbolicCurveAlgorithm K
  decodeIso := properHyperbolicCurveHomDecodeIso K

/-- The same statement in the standard Hom-form package. -/
noncomputable def properHyperbolicCurveHomFormPackage {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    HomFormPackage (ProperHyperbolicCurveOver K) (properHyperbolicCurveData K) where
  invariant := properHyperbolicCurveInvariant K
  algorithm := properHyperbolicCurveAlgorithm K
  homIso := properHyperbolicCurveHomDecodeIso K

/-- The Hom-form package uses the specified full étale `π₁` invariant. -/
theorem properHyperbolicCurveHomFormPackage_invariant {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    (properHyperbolicCurveHomFormPackage K).invariant = properHyperbolicCurveInvariant K :=
  rfl

/-- The Hom-form package uses the open-outer-hom algorithm. -/
theorem properHyperbolicCurveHomFormPackage_algorithm {p : ℕ} [Fact p.Prime]
    (K : PadicLocalFieldCat.{u} p) :
    (properHyperbolicCurveHomFormPackage K).algorithm = properHyperbolicCurveAlgorithm K :=
  rfl

end ProperHyperbolicCurveHomStandalone
end MochizukiLocalProP
end Examples
end Anabelian
